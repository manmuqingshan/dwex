# Support for DWARF v1.1 in a way that will be more or less compatible with pyelftools

from io import BytesIO
from collections import OrderedDict, namedtuple
from bisect import bisect_left, bisect_right
from elftools.dwarf.dwarfinfo import DwarfConfig, DebugSectionDescriptor
from elftools.dwarf.die import AttributeValue
from elftools.dwarf.structs import DWARFStructs
from elftools.common.utils import struct_parse
from elftools.dwarf.enums import ENUM_DW_TAG, ENUM_DW_AT, ENUM_DW_FORM
from elftools.construct import CString
from elftools.dwarf.lineprogram import LineProgramEntry, LineState
from elftools.dwarf.dwarf_expr import DWARFExprOp

LineTableHeader = namedtuple('LineTableHeader', 'version file_entry')
CUv1Header = namedtuple('CUv1Header', 'version unit_length debug_abbrev_offset address_size')

TAG_reverse = dict((v, k) for k, v in ENUM_DW_TAG.items())
ATTR_reverse = dict((v, k) for k, v in ENUM_DW_AT.items())
FORM_reverse = dict((v, k) for k, v in ENUM_DW_FORM.items())

ENUM_FMT = dict(
   FMT_FT_C_C = 0,
   FMT_FT_C_X = 1,
   FMT_FT_X_C = 2,
   FMT_FT_X_X = 3,
   FMT_UT_C_C = 4,
   FMT_UT_C_X = 5,
   FMT_UT_X_C = 6,
   FMT_UT_X_X = 7,
   FMT_ET     = 8
)

ENUM_FMT_reverse = dict((v, k) for k, v in ENUM_FMT.items())

ENUM_FUND_TYPE = dict(
    FT_char             = 0x0001,
    FT_signed_char      = 0x0002,
    FT_unsigned_char    = 0x0003,
    FT_short            = 0x0004,
    FT_signed_short     = 0x0005,
    FT_unsigned_short   = 0x0006,
    FT_integer          = 0x0007,
    FT_signed_integer   = 0x0008,
    FT_unsigned_integer = 0x0009,
    FT_long             = 0x000a,
    FT_signed_long      = 0x000b,
    FT_unsigned_long    = 0x000c,
    FT_pointer          = 0x000d,
    FT_float            = 0x000e,
    FT_dbl_prec_float   = 0x000f,
    FT_ext_prec_float   = 0x0010,
    FT_complex          = 0x0011,
    FT_dbl_prec_complex = 0x0012,
    FT_void             = 0x0014,
    FT_boolean          = 0x0015,
    FT_ext_prec_complex = 0x0016,
    FT_label            = 0x0017,
    FT_lo_user          = 0x8000,
    FT_hi_user          = 0xffff    
)

ENUM_FUND_TYPE_reverse = dict((v, k) for k, v in ENUM_FUND_TYPE.items())

DW_OP_name2opcode = dict(
    DW_OP_reg     = 0x01,
    DW_OP_basereg = 0x02,
    DW_OP_addr    = 0x03,
    DW_OP_const   = 0x04,
    DW_OP_deref2  = 0x05,
    DW_OP_deref   = 0x06,
    DW_OP_deref4  = 0x06,
    DW_OP_add     = 0x07,
    DW_OP_user_0x80 = 0x80 #Extension op, not sure what's the deal with that
)

DW_OP_opcode2name = dict((v, k) for k, v in DW_OP_name2opcode.items())

ENUM_MOD = dict(
    MOD_pointer_to   = 0x01,
    MOD_reference_to = 0x02,
    MOD_const        = 0x03,
    MOD_volatile     = 0x04,
    MOD_lo_user      = 0x80,
    MOD_hi_user      = 0xff
)

ENUM_MOD_reverse = dict((v, k) for k, v in ENUM_MOD.items())

# Takes code or string
def fundamental_type_size(ft, die):
    if isinstance(ft, str):
        if ft.startswith('FT_user_'):
            ft = int(ft[8:], 16)
        else:
            ft = ENUM_FUND_TYPE[ft]

    if 1 <= ft <= 3:
        return 1
    elif ft <=6:
         return 2
    elif ft <= 0x9:
        return 4
    elif ft <= 0xd: # Long and pointer; 64 on Linux/64
        return die.cu.header.address_size
    elif ft == 0xe: # float
        return 4
    elif ft == 0xf: # double
        return 8
    elif ft == 0x10: # extended precision float
        return 10
    elif ft == 0x11: # complex  
        return 8
    elif ft == 0x12: # double precision complex
        return 16
    elif ft == 0x15: # boolean ?
        return 1
    elif ft == 0x16: # extended precision complex   
        return 20
    elif ft >= 0x8000 and (ft & 0xFF) != 0:
        return ft & 0xFF
    
# index_type is a fundamental type name from ENUM_FUND_TYPE or FT_user_XXXX or a DIE offset (int)
# low, high are either int or list of int for expressin blobs. Expressions are not parsed.
ArraySubDimension = namedtuple('ArraySubDimension', ('fmt', 'index_type', 'low', 'high')) 

# elem_type is driven by attr/form
# fundamental: string from the ENUM_FUND_TYPE or FT_user_XXXX
# user-defined: DIE offset, int
# modified: (tuple of modifiers followed by one of the above)
ArraySubElementType = namedtuple('ArraySubElementType', ('fmt', 'attr', 'form', 'elem_type'))

def fund_type_name(ft):
    return ENUM_FUND_TYPE_reverse[ft] if ft in ENUM_FUND_TYPE_reverse else f'FT_user_{ft:X}'

# Given a blob with modifiers followed by a fundamental type, returns a tuple of modifier names followed by the fundamental type name
def parse_mod_fund_type(value, die):
    le = die.cu.structs.little_endian
    bo = 'little' if le else 'big'
    return tuple(ENUM_MOD_reverse[b] for b in value[:-2]) + (fund_type_name(int.from_bytes(value[-2:], bo)),)

# Given a blob with modifiers followed by a fundamental type, returns a tuple of modifier names followed by the offset
def parse_mod_user_type(value, die):
    le = die.cu.structs.little_endian
    bo = 'little' if le else 'big'
    asz = die.cu.header.address_size # Should be DWARF offset size, but irrelevant for V1
    offset = int.from_bytes(value[-asz:], bo)
    return tuple(ENUM_MOD_reverse[b] for b in value[:-asz]) + (offset,)

def mods_have_pointer(mods):
    return any(m for m in mods if m in ('MOD_pointer_to', 'MOD_reference_to'))

# For parsing the value of AT_subscr_data attribute in DWARFv1.
# Returns a list of ArraySubDimension and AraySubElementType
def parse_array_subscripts(subs, die):
    result = list()
    stm = BytesIO(bytes(subs))
    structs = die.cu.structs
    while stm.tell() < len(subs):
        fmt = ENUM_FMT_reverse[struct_parse(structs.Dwarf_uint8(''), stm)]
        if fmt == 'FMT_ET': # Element type
            # Followed by an attribute/form code, form in low nybble, attribute code in high 3 nybbles 
            # Follosed by the data encoded according to the form - either block or UInt16 for fundamental types
            elem_attr = struct_parse(structs.Dwarf_uint16(''), stm)
            elem_form = FORM_reverse[elem_attr & 0xf]
            elem_attr = ATTR_reverse[elem_attr >> 4]
            value = struct_parse(structs.Dwarf_dw_form[elem_form], stm)
            if elem_attr == 'DW_AT_mod_fund_type':
                value = parse_mod_fund_type(value, die)
            elif elem_attr == 'DW_AT_mod_u_d_type':
                value = parse_mod_user_type(value, die)
            elif elem_attr == 'DW_AT_fund_type':
                value = fund_type_name(value)
            result.append(ArraySubElementType(fmt, elem_attr, elem_form, elem_type=value))
        else: # Subscript description, like FMT_FT_C_C
            index_type = struct_parse((structs.Dwarf_uint16 if fmt[4] == 'F' else structs.Dwarf_offset)(''), stm)
            # Constants are long sizes in the spec, assume same as pointer
            # The format of dynamic locations is not specified explicitly
            low = struct_parse(structs.Dwarf_target_addr('') if fmt[7] == 'C' else structs.Dwarf_dw_form['DW_FORM_block2'], stm)
            high = struct_parse(structs.Dwarf_target_addr('') if fmt[9] == 'C' else structs.Dwarf_dw_form['DW_FORM_block2'], stm)
            result.append(ArraySubDimension(fmt, ENUM_FUND_TYPE_reverse[index_type] if fmt[4] == 'F' else index_type, low, high))
    return result

# Returns (count, size)
# decode_size is a function that take a DIE - for getting user defined type size
def decode_array_subscripts(subs, die, decode_size):
    count = elem_size = None
    asz = die.cu.header.address_size
    bo = 'little' if die.cu.structs.little_endian else 'big'
    for l in parse_array_subscripts(subs, die):
        if isinstance(l, ArraySubDimension):
            if l.fmt[7] == 'C' and l.fmt[9] == 'C':
                if count is None:
                    count = 1
                count *= l.high - l.low + 1
            else:
                return (None, None) # Non-const subscripts are a deal breaker - dynamic array
        elif isinstance(l, ArraySubElementType):
            elem_attr = l.attr
            value = l.elem_type
            if elem_attr == 'DW_AT_fund_type':
                elem_size = fundamental_type_size(value, die)
            elif elem_attr == 'DW_AT_user_def_type':
                elem_size = decode_size(die.get_DIE_at_offset(value))
            elif elem_attr == 'DW_AT_mod_fund_type':
                if mods_have_pointer(value[:-1]):
                    elem_size = asz # Pointer or reference
                else:
                    elem_size = fundamental_type_size(value[-1], die)
            elif elem_attr == 'DW_AT_mod_u_d_type':
                if mods_have_pointer(value[:-1]):
                    elem_size = asz # Pointer or reference
                else:
                    elem_size = decode_size(die.get_DIE_at_offset(value[-1]))
            else:
                raise ValueError(f"Unsupported element type attribute in array subscript element type descriptor: {elem_attr}")
        else:
            raise ValueError(f"Unsupported element in array subscript descriptor: {l}")
    return (count, elem_size)


class DIEV1(object):
    def __init__(self, stm, cu, di):
        self.cu = cu
        self.dwarfinfo = di
        self.stream = stm
        self.offset = stm.tell()
        self.attributes = OrderedDict()
        self.tag = None
        self.has_children = None
        self.abbrev_code = None
        self.size = 0
        # Null DIE terminator. It can be used to obtain offset range occupied
        # by this DIE including its whole subtree.
        self._terminator = None
        self._parent = None

        structs = self.dwarfinfo.structs
        self.size = struct_parse(structs.Dwarf_uint32(''), stm)
        # Size 8+  can be padding if the tag is 0. No attributes in those.
        # DW_TAG_null and DW_TAG_padding are both code zero
        if self.size < 8:
            self.tag = 'DW_TAG_null' # Null terminates the sibling chain
            self.has_children = False
        else:
            tag_code = struct_parse(structs.Dwarf_uint16(''), stm)
            # Do what pyelftools does, leave tag as int if unknown
            self.tag = TAG_reverse[tag_code] if tag_code in TAG_reverse else tag_code 
            if self.tag == 'DW_TAG_null': # TAG_padding in DWARF1 spec
                self.tag == 'DW_TAG_padding' #Doesn't count for is_null
                # No attributes, just advance the stream
                stm.seek(self.size-6, 1)
                self.has_children = False
            else:
                while stm.tell() < self.offset + self.size:
                    attr_offset = self.stream.tell()
                    attr = struct_parse(structs.Dwarf_uint16(''), stm)
                    form = FORM_reverse[attr & 0xf]
                    attr >>= 4
                    if attr in ATTR_reverse:
                        name = ATTR_reverse[attr]
                    elif 0x200 <= attr <= 0x3ff: #DW_AT_MIPS represented as 0x204???
                        name = 'DW_AT_user_0x%x' % attr
                    else: # Do what pyelftools does, leave tag as int if unknown
                        name = attr

                    raw_value = struct_parse(structs.Dwarf_dw_form[form], stm)
                    value = raw_value

                    self.attributes[name] = AttributeValue(
                        name=name,
                        form=form,
                        value=value,
                        raw_value=raw_value,
                        offset=attr_offset,
                        indirection_length = 0)
                self.has_children = self.attributes['DW_AT_sibling'].value >= self.offset + self.size + 8

    def get_parent(self):
        return self._parent

    def is_null(self):
        return self.tag == 'DW_TAG_null'

    def iter_children(self):
        return self.cu.iter_children(self)

    def sibling(self):
        return self.attributes['DW_AT_sibling'].value
    
    # offset is absolute, cross-CU navigation is supported
    def get_DIE_at_offset(self, offset):
        cu = self.cu
        if cu.cu_offset <= offset < cu.cu_offset + cu.header.unit_length:
            return cu.DIE_at_offset(offset)
        else:
            # Take advantage of the CU cache here
            di = cu.dwarfinfo
            i = bisect_right(di._CU_offsets, offset) - 1
            if 0 <= i < len(di._CU_offsets):
                target_cu = di._unsorted_CUs[i]            
                return target_cu.DIE_at_offset(offset)
    
    def get_DIE_from_attribute(self, attr_name):
        if attr_name in self.attributes:
            v = self.attributes[attr_name].value
            if attr_name == 'DW_AT_mod_u_t_type': # Modifiers followed by offset
                al = self.cu.header.address_size
                v = v[-al:]
                offset = int.from_bytes(v, byteorder='little' if self.cu.structs.little_endian else 'big')
            target_die = self.get_DIE_at_offset(self.attributes[attr_name].value)
            if target_die is None:
                raise ValueError(f"Attribute {attr_name} with offset 0x{offset:X} is out of bounds.")
            else:
                return target_die
        return None

class CompileUnitV1(object):
    def __init__(self, di, top_die):
        self.dwarfinfo = di
        self.structs = di.structs
        end_offset = top_die.attributes['DW_AT_sibling'].value
        self.header = CUv1Header(version = 1, unit_length = end_offset - top_die.offset, debug_abbrev_offset = None, address_size = 4)
        self._dielist = [top_die]
        self._diemap = [top_die.offset]
        # For compatibility with v2+ CU
        self.cu_offset = top_die.offset
        self.cu_die_offset = top_die.offset

    def get_top_DIE(self):
        return self._dielist[0]

    def __getitem__(self, name):
        return self.header._asdict()[name]
    
    @property
    def size(self):
        return self.header.unit_length # No CU header here

    # Caches
    def DIE_at_offset(self, offset):
        i = bisect_left(self._diemap, offset)
        if i < len(self._diemap) and offset == self._diemap[i]:
            die = self._dielist[i]
        else:
            die = self.dwarfinfo.DIE_at_offset(offset, self)
            self._dielist.insert(i, die)
            self._diemap.insert(i, offset)
        return die

    # pyelftools' iter_DIEs sets parent on discovered DIEs, we should too
    def iter_DIEs(self):
        offset = self.cu_offset
        parent = None
        parent_stack = list()
        end_offset = self.get_top_DIE().attributes['DW_AT_sibling'].value
        # Dump the whole section into locals to catch 1610
        if end_offset - offset <= 4096:
            stm = self.dwarfinfo.stm
            stm.seek(offset, 0)
            import base64
            section_dump = base64.encodebytes(stm.read(end_offset - offset)).decode('ASCII')
        while offset < end_offset:
            die = self.DIE_at_offset(offset)

            if die._parent is None:
                die._parent = parent

            if not die.is_null():
                yield die
                offset += die.size
                if offset != die.sibling(): # Start of a subtree
                    parent_stack.append(parent)
                    parent = die
            else: # null - end of a sibling chain
                # Catching 1610
                size = die.size
                tag = die.tag
                parent = parent_stack.pop() # Throws IndexError
                offset += die.size
            prev_die_tag = die.tag

    def iter_children(self, parent_die):
        offset = parent_die.offset + parent_die.size
        parent_sibling_offset = parent_die.attributes['DW_AT_sibling'].value if 'DW_AT_sibling' in parent_die.attributes else None
        section_size = self.dwarfinfo.section_size
        while offset < section_size:
            die = self.DIE_at_offset(offset)

            if die._parent is None:
                die._parent = parent_die
            if not die.is_null():
                yield die
                # Troubleshooting #1497
                
                tag = die.tag
                attr = die.attributes
                off = die.offset
                size = die.size
                has_children = die.has_children
                offset = die.attributes['DW_AT_sibling'].value # will throw KeyError if none
                prev_die = die
                #offset = die.sibling()
            else:
                break
            
    def iter_DIE_children(self, die):
        if not die.has_children:
            return
        
        # `cur_offset` tracks the stream offset of the next DIE to yield
        # as we iterate over our children,
        cur_offset = die.offset + die.size

        while True:
            child = self.DIE_at_offset(cur_offset)

            if child._parent is None:
                child._parent = die

            if child.is_null():
                die._terminator = child
                return

            yield child

            if not child.has_children:
                cur_offset += child.size
            elif "DW_AT_sibling" in child.attributes:
                sibling = child.attributes["DW_AT_sibling"]
                if sibling.form == 'DW_FORM_ref':
                    cur_offset = sibling.value
                else:
                    raise NotImplementedError('sibling in form %s' % sibling.form)
            else:
                # If no DW_AT_sibling attribute is provided by the producer
                # then the whole child subtree must be parsed to find its next
                # sibling. There is one zero byte representing null DIE
                # terminating children list. It is used to locate child subtree
                # bounds.

                # If children are not parsed yet, this instruction will manage
                # to recursive call of this function which will result in
                # setting of `_terminator` attribute of the `child`.
                if child._terminator is None:
                    for _ in self.iter_DIE_children(child):
                        pass

                cur_offset = child._terminator.offset + child._terminator.size

    def get_DIE_from_refaddr(self, refaddr):
        return self.DIE_at_offset(refaddr)

class LineTableV1(object):
    def __init__(self, stm, structs, len, pc):
        self.stm = stm
        self.structs = structs
        self.len = len
        self.pc = pc
        self._decoded_entries = None
        self.header = LineTableHeader(1, (None))

    def get_entries(self):
        if self._decoded_entries is None:
            stm = self.stm
            offset = stm.tell()
            end_offset = offset + self.len
            structs = self.structs
            entries = []
            pc = self.pc
            while offset < end_offset:
                line = struct_parse(structs.Dwarf_uint32(''), stm)
                col = struct_parse(structs.Dwarf_uint16(''), stm)
                pc_delta = struct_parse(structs.Dwarf_uint32(''), stm)
                if line == 0:
                    break
                state = LineState(True)
                state.file = 0
                state.line = line
                state.column = col if col != 0xffff else None
                state.address = pc
                entries.append(LineProgramEntry(0, False, [], state))
                pc += pc_delta
            self._decoded_entries = entries
        return self._decoded_entries
    
    def __getitem__(self, name):
        return self.header[name]

def bytelist2string(bytelist):
    """ Convert a list of byte values (e.g. [0x10 0x20 0x00]) to a bytes object
        (e.g. b'\x10\x20\x00').
    """
    return b''.join(bytes((b,)) for b in bytelist)

class DWARFExprParserV1(object):
    def __init__(self, structs):
        self.structs = structs
        
    def parse_expr(self, expr):
        stm = BytesIO(bytelist2string(expr))
        parsed = []

        while True:
            # Get the next opcode from the stream. If nothing is left in the
            # stream, we're done.
            byte = stm.read(1)
            if len(byte) == 0:
                break

            # Decode the opcode and its name.
            op = ord(byte)
            op_name = DW_OP_opcode2name.get(op, 'OP:0x%x' % op)

            if op <= 4 or op == 0x80:
                args = [struct_parse(self.structs.Dwarf_target_addr(''), stm),]
            else:
                args = []

            parsed.append(DWARFExprOp(op=op, op_name=op_name, args=args, offset=stm.tell()))

        return parsed

class DWARFInfoV1(object):
    def __init__(self, elffile):
        section = elffile.get_section_by_name(".debug")
        section_data = section.data()
        # TODO: relocation? Compression?
        self.section_size = len(section_data)
        self.stm = BytesIO(section_data)

        lsection = elffile.get_section_by_name(".line")
        if lsection:
            self.linestream = BytesIO(lsection.data())
        # Sections .debug_pubnames, .debug_aranges also in the spec -
        # those are indices into info, we ignore them

        self.config = DwarfConfig(
            little_endian = elffile.little_endian,
            default_address_size = elffile.elfclass // 8,
            machine_arch = elffile.get_machine_arch()
        )

        self.structs = DWARFStructs(
            little_endian = self.config.little_endian,
            dwarf_format = 32,
            address_size = self.config.default_address_size)

    def iter_CUs(self):
        offset = 0
        while offset < self.section_size:
            die = self.DIE_at_offset(offset, None)
            if not die.is_null():
                if die.cu is None:
                    die.cu = cu = CompileUnitV1(self, die)
                    cu.cu_offset = offset
                yield die.cu
                offset = die.attributes['DW_AT_sibling'].value
            else:
                break

    # Does not cache
    def DIE_at_offset(self, offset, cu):
        self.stm.seek(offset, 0)
        return DIEV1(self.stm, cu, self)

    def location_lists(self):
        return None

    def line_program_for_CU(self, cu):
        top_DIE = cu.get_top_DIE()
        if 'DW_AT_stmt_list' in top_DIE.attributes:
            stm = self.linestream
            stm.seek(top_DIE.attributes['DW_AT_stmt_list'].value, 0)
            structs = self.structs
            len = struct_parse(structs.Dwarf_uint32(''), stm)
            pc = struct_parse(structs.Dwarf_target_addr(''), stm)
            return LineTableV1(stm, structs, len, pc)
        else:
            return None
        
    def range_lists(self):
        return None
    
    def get_aranges(self):
        return None
    
    def has_CFI(self):
        return False
    
    def has_CFI(self):
        return False
    
    def has_EH_CFI(self):
        return False

def parse_dwarf1(elffile):
    return DWARFInfoV1(elffile)
