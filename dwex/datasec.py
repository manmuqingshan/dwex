from bisect import bisect_left
from PyQt6.QtCore import Qt
from PyQt6.QtWidgets import *
from elftools.dwarf.locationlists import LocationExpr, LocationParser
from elftools.dwarf.dwarf_expr import DWARFExprParser
from elftools.dwarf.enums import ENUM_DW_LANG

from .dwarfutil import top_die_file_name
from .locals import LoadedModuleDlgBase
from .gather import GatherThread
from .details import GenericTableModel
from .dwarfone import DWARFExprParserV1, decode_array_subscripts, fundamental_type_size, mods_have_pointer, parse_mod_fund_type, parse_mod_user_type
from .die import safe_DIE_name
from .fx import italic_font, ltgrey_brush

def get_lang(cu):
    attr = cu.get_top_DIE().attributes
    if 'DW_AT_language' in attr:
        lang = attr['DW_AT_language'].value
        lang_name = next((k for k, v in ENUM_DW_LANG.items() if v == lang), None)
        if lang_name:
            return lang_name[8:]

one_based_langs = ('Fortran', 'Pascal', 'Ada', 'Modula', 'PLI', 'Cobol', 'Julia')
def one_based_lang(lang):
    return lang and any(l for l in one_based_langs if lang.startswith(l))

def array_count(die):
    count = 1
    #got_subranges = False
    for subrange_die in die.iter_children():
        if subrange_die.tag == 'DW_TAG_subrange_type':
            #got_subranges = True
            if 'DW_AT_count' in subrange_die.attributes:
                count *= subrange_die.attributes['DW_AT_count'].value
            elif 'DW_AT_upper_bound' in subrange_die.attributes:
                upper = subrange_die.attributes['DW_AT_upper_bound'].value
                if 'DW_AT_lower_bound' in subrange_die.attributes:
                    lower = subrange_die.attributes['DW_AT_lower_bound'].value
                else:
                    lower = 1 if one_based_lang(get_lang(die.cu)) else 0 
                count *= (upper - lower + 1)
            else:
                return None # Subrange DIE with neither upper nor count
    # No subranges at all means 1. Is that correct?
    return count

# Chases the type chain to something with a size.
def decode_size(die):
    attr = die.attributes
    if 'DW_AT_byte_size' in attr: # Primitives, structs, classes, unions
        return attr['DW_AT_byte_size'].value

    # Modifiers and aliases
    if die.tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_member'):
        if 'DW_AT_type' in attr:
            return decode_size(die.get_DIE_from_attribute('DW_AT_type'))
        elif 'DW_AT_user_def_type' in attr:
            return decode_size(die.get_DIE_from_attribute('DW_AT_user_def_type'))
    
    # Pointers are easy
    # Subroutine (v1) as type means function pointer
    if die.tag in ('DW_TAG_pointer_type', 'DW_TAG_subroutine_type'):
        return die.cu.header.address_size
        
    if die.tag == 'DW_TAG_array_type':
        ta = elem_size = count = None
        if 'DW_AT_type' in attr:
            ta = 'DW_AT_type'
        elif 'DW_AT_user_def_type' in attr: 
            ta = 'DW_AT_user_def_type'
        elif 'DW_AT_mod_u_d_type' in attr: 
            mut = parse_mod_user_type(attr['DW_AT_mod_u_d_type'].value, die)
            if mods_have_pointer(mut[:-1]):
                elem_size = die.cu.header.address_size
            else:
                ta = 'DW_AT_mod_u_d_type'
        elif 'DW_AT_mod_fund_type' in attr:
            mft = parse_mod_fund_type(attr['DW_AT_mod_fund_type'].value, die)
            if mods_have_pointer(mut[:-1]):
                elem_size = die.cu.header.address_size
            else:
                elem_size = fundamental_type_size(mft[-1], die)
        elif 'DW_AT_fund_type' in attr:
            ft = die.get_DIE_from_attribute('DW_AT_fund_type').value
            elem_size = fundamental_type_size(ft, die)
        elif die.cu.header.version == 1 and 'DW_AT_subscr_data' in attr:
            (count, elem_size) = decode_array_subscripts(die.attributes['DW_AT_subscr_data'].value, die, decode_size)
            if elem_size is not None and count is not None:
                return count * elem_size
            else:
                return None
        # Moving on to parsing the pointed-at type for element size
        if ta:
            elem_size = decode_size(die.get_DIE_from_attribute(ta))

        if not elem_size:
            return None
        
        return array_count(die) * elem_size

# Context is a format specifier string that takes name
def get_context(die):
    context = []
    context_die = die.get_parent()
    while context_die:
        if context_die.tag == 'DW_TAG_subprogram': # Static variable in a function or a method
            if 'DW_AT_abstract_origin' in context_die.attributes: # Inlined function - skip to the real thing
                context_die = context_die.get_DIE_from_attribute('DW_AT_abstract_origin')

            if 'DW_AT_specification' in context_die.attributes: # Method
                func_spec_die = context_die.get_DIE_from_attribute('DW_AT_specification')
            else:
                func_spec_die = context_die
            # TODO: overloaded function arguments disambig :(
            func_name = safe_DIE_name(func_spec_die)
            func_context = get_context(func_spec_die)
            if func_context:
                func_name = func_context % (func_name,)
            # Maybe class static in a function-local class? Why not.
            prefix = ''.join(f'{c}::' for c in context) if context else ''
            return f'{prefix}%s in {func_name}()'
        if context_die.tag in ('DW_TAG_class_type', 'DW_TAG_structure_type', 'DW_TAG_namespace'):
            context.insert(0, safe_DIE_name(context_die))
        context_die = context_die.get_parent()
    if context:
        prefix = ''.join(f'{c}::' for c in context)
        return f'{prefix}%s'

# returns (display_name, size). Size can be None.
def decode_var(die):
    size = None
    type_die = None # May be defined in spec
    spec_die = None # If no explicit spec, then self

    if 'DW_AT_abstract_origin' in die.attributes: # Inside inlined_subroutine, jump to the abstract subtree - that's where the type and the spec are
        die = die.get_DIE_from_attribute('DW_AT_abstract_origin')
    attr = die.attributes

    # In v2+, the size is never in the variable. In v1, it sometimes is.
    if die.cu.header.version == 1:
        if 'DW_AT_fund_type' in attr:
            size = fundamental_type_size(attr['DW_AT_fund_type'].value, die)
        elif 'DW_AT_mod_fund_type' in attr:
            mft = parse_mod_fund_type(attr['DW_AT_mod_fund_type'].value, die)
            size = die.cu.header.address_size if mods_have_pointer(mft[:-1]) else fundamental_type_size(mft[-1], die)
        elif 'DW_AT_mod_u_d_type' in attr:
            mut = parse_mod_user_type(attr['DW_AT_mod_u_d_type'].value, die)
            if mods_have_pointer(mut[:-1]):
                size = die.cu.header.address_size
            type_die = die.get_DIE_at_offset(mut[-1])
        elif 'DW_AT_user_def_type' in attr:
            type_die = die.get_DIE_from_attribute('DW_AT_user_def_type')

    if 'DW_AT_type' in attr:
        type_die = die.get_DIE_from_attribute('DW_AT_type')

    if 'DW_AT_specification' in attr:
        spec_die = die.get_DIE_from_attribute('DW_AT_specification')
        if not type_die and 'DW_AT_type' in spec_die.attributes:
            type_die = spec_die.get_DIE_from_attribute('DW_AT_type')
    else:
        spec_die = die

    if size is None and type_die:
        size = decode_size(type_die)

    # ----------------- Now the name
    
    # No lexical block disambig
    # No overloaded function disambig
    # If not none, context is a format string for var name
    context = get_context(spec_die)

    name = safe_DIE_name(die, False)
    if not name and spec_die != die:
        name = safe_DIE_name(spec_die, False)
    if not name and 'DW_AT_linkage_name' in attr:
        name = attr['DW_AT_linkage_name'].value.decode('utf-8', errors='ignore')
    if not name:
        name = '<unknown>'

    if context:
        name = context % name
    return (name, size)

def under_function(die):
    die = die.get_parent()
    while die:
        if die.tag == 'DW_TAG_subroutine':
            return True
        die = die.get_parent()
    return False

class DataSpan:
    def __init__(self, addr, size, die = None, name = None, module = None):
        self.addr = addr
        self.size = size
        self.end = end = addr if size is None else addr + size - 1
        self.die = die
        self._display = (hex(addr), hex(end), name if die else '<gap>', module if die else '')

    def __getitem__(self, i):
        return self._display[i]

class DataSpanModel(GenericTableModel):
    def data(self, index, role):
        span = index.internalPointer()
        die = span.die
        if role == Qt.ItemDataRole.BackgroundRole:
            if die is None:
                return ltgrey_brush
        elif role == Qt.ItemDataRole.FontRole:
            if span.size is None:
                return italic_font()
        elif role == Qt.ItemDataRole.ToolTipRole:
            if index.column() <= 2:
                return 'Length cannot be determined' if span.size is None else f'Length : {span.size}'
        else:
            return super().data(index, role)

class GatherStaticDataThread(GatherThread):
    def __init__(self, parent, di):
        super().__init__(parent, di)
        if not di._locparser:
            di._locparser = LocationParser(self.dwarfinfo.location_lists())

    def on_cu(self, cu):
        # TODO: cache further
        self._cu_header = cu_header = cu.header
        self._ver = ver = cu_header.version
        self._expr_parser = DWARFExprParser(cu.structs) if ver > 1 else DWARFExprParserV1(cu.structs)

    def on_die(self, die, vars):
        attr = die.attributes
        if (die.tag in ('DW_TAG_variable', 'DW_TAG_global_variable') or
            (self._ver == 1 and die.tag == 'DW_TAG_local_variable' and not under_function(die))) and 'DW_AT_location' in attr:
            self.progress.emit(die.offset)

            cu = die.cu
            la = attr['DW_AT_location']
            if LocationParser.attribute_has_location(la, self._ver):
                ll = cu.dwarfinfo._locparser.parse_from_attribute(la, self._ver, die) # Either a list or a LocationExpr
            elif la.form.startswith('DW_FORM_block'): # Some special cases on the edges of the format: block type location in V4
                ll = LocationExpr(la.value)
            else:
                raise ValueError(f"Unsupported location attribute format {la.form}")

            if isinstance(ll, LocationExpr):
                expr = self._expr_parser.parse_expr(ll.loc_expr)
                addr = None
                if len(expr) == 1 and expr[0].op_name == 'DW_OP_addr':
                    addr = expr[0].args[0]
                elif len(expr) == 1 and expr[0].op_name == 'DW_OP_addrx':
                    addr = self.dwarfinfo.get_addr(die.cu, expr[0].args[0])

                if addr is not None:
                    (name, size) = decode_var(die)

                    i = bisect_left(vars, addr, key=lambda ds: ds.addr)
                    # Full matches possible with inlines
                    # TODO: deal with overlaps
                    if i < len(vars) and vars[i].addr == addr: # Same addr - allow for greater size override
                        if size and (not vars[i].size or vars[i].size < size):
                            vars[i] = DataSpan(addr, size, die, name, top_die_file_name(cu.get_top_DIE()))
                    else:
                        vars.insert(i, DataSpan(addr, size, die, name, top_die_file_name(cu.get_top_DIE())))

    def postprocess(self, result):
        n = len(result)
        i = 1
        while i < n:
            if result[i].addr > result[i-1].end + 1:
                result.insert(i, DataSpan(result[i-1].end + 1, result[i].addr - result[i-1].end - 1))
                n += 1
                i += 1
            i += 1

class DataSectionDlg(LoadedModuleDlgBase):
    def __init__(self, win, hex, vars):
        super().__init__(win)
        self.selected_die = None
        model = DataSpanModel(('Start address', 'End address', 'Name', 'Module'), vars)

        self.resize(500, 650)
        ly = QVBoxLayout()

        self.the_table = QTableView()
        self.the_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.the_table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.the_table.setModel(model)
        self.the_table.selectionModel().currentChanged.connect(self.on_sel)
        self.the_table.doubleClicked.connect(self.navigate_to_index)
        self.the_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        ly.addWidget(self.the_table)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Close, Qt.Orientation.Horizontal, self)
        self.nav_bu = QPushButton("Navigate", self)
        self.nav_bu.clicked.connect(lambda: self.navigate_to_index(self.the_table.currentIndex()))
        self.nav_bu.setEnabled(False)
        buttons.addButton(self.nav_bu, QDialogButtonBox.ButtonRole.ApplyRole)
        # Do we even need export???
        #self.export_bu = QPushButton("Export", self)
        #self.export_bu.clicked.connect(self.export_funcs)
        #buttons.addButton(self.export_bu, QDialogButtonBox.ButtonRole.ApplyRole)
        buttons.accepted.connect(self.reject)
        buttons.rejected.connect(self.reject)
        ly.addWidget(buttons)

        self.setWindowTitle('Data Section')
        self.setLayout(ly)

    def on_sel(self, index, prev = None):
        self.nav_bu.setEnabled(index.isValid() and index.internalPointer().die is not None)        

    def navigate_to_index(self, index):
        row = index.row()
        self.selected_die = self.the_table.model().values[row].die
        self.done(QDialog.DialogCode.Accepted)