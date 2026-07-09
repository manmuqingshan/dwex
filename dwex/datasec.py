from bisect import bisect_left
from PyQt6.QtCore import Qt
from PyQt6.QtWidgets import *
from elftools.dwarf.locationlists import LocationExpr, LocationParser
from elftools.dwarf.dwarf_expr import DWARFExprParser

from .dwarfutil import top_die_file_name
from .locals import LoadedModuleDlgBase
from .gather import GatherThread
from .details import GenericTableModel
from .dwarfone import DWARFExprParserV1
from .die import safe_DIE_name
from .fx import italic_font, ltgrey_brush

# Chases the type chain to something with a size.
def decode_size(die):
    attr = die.attributes
    if 'DW_AT_byte_size' in attr: # Primitives, structs, classes, unions
        return attr['DW_AT_byte_size'].value

    # Modifiers and aliases
    if die.tag in ('DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type', 'DW_TAG_member') and 'DW_AT_type' in attr:
        return decode_size(die.get_DIE_from_attribute('DW_AT_type'))
    
    # Pointers are easy
    if die.tag == 'DW_TAG_pointer_type':
        return die.cu.header.address_size
        
    # Arrays specify their size in different ways...
    # TODO: multidim arrays
    if die.tag == 'DW_TAG_array_type' and 'DW_AT_type' in attr:
        elem_size = decode_size(die.get_DIE_from_attribute('DW_AT_type'))
        if not elem_size:
            return None
        subrange_die = next((d for d in die.iter_children() if d.tag == 'DW_TAG_subrange_type'), False)
        # TODO: maybe not always subrange
        if subrange_die:
            if 'DW_AT_count' in subrange_die.attributes:
                return elem_size * subrange_die.attributes['DW_AT_count'].value
             
            if 'DW_AT_upper_bound' in subrange_die.attributes:
                upper = subrange_die.attributes['DW_AT_upper_bound'].value
            else:
                return None # Neither upper nor count
            
            if 'DW_AT_lower_bound' in subrange_die.attributes:
                lower = subrange_die.attributes['DW_AT_lower_bound'].value
            else:
                lower = 0
            
            return elem_size * (upper - lower + 1)

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

def decode_var(die):
    size = None
    type_die = None # May be defined in spec
    spec_die = None # If no explicit spec, then self

    if 'DW_AT_abstract_origin' in die.attributes: # Inside inlined_subroutine, jump to the abstract subtree - that's where the type and the spec are
        die = die.get_DIE_from_attribute('DW_AT_abstract_origin')
    attr = die.attributes

    if 'DW_AT_type' in attr:
        type_die = die.get_DIE_from_attribute('DW_AT_type')

    if 'DW_AT_specification' in attr:
        spec_die = die.get_DIE_from_attribute('DW_AT_specification')
        if not type_die and 'DW_AT_type' in spec_die.attributes:
            type_die = spec_die.get_DIE_from_attribute('DW_AT_type')
    else:
        spec_die = die

    size = decode_size(type_die) if type_die else None
    
    # No lexical block disambig
    # No overloaded function disambig
    context = get_context(spec_die)

    name = safe_DIE_name(die, False)
    if not name and spec_die != die:
        name = safe_DIE_name(spec_die, False)
    if not name and 'DW_AT_linkage_name' in attr:
        name = attr['DW_AT_linkage_name'].value.decode('utf-8', errors='ignore')
    if not name:
        name = '<unknown>'

    # TODO: function level statics not displayed right
    if context:
        name = context % name
    return (name, size)

class DataSpan:
    def __init__(self, addr, size, die = None, name = None, module = None):
        self.addr = addr
        self.size = size
        self.end = addr + (0 if size is None else size-1)
        self.die = die
        self._display = (hex(addr), hex(self.end), name if die else '<gap>', module if die else '')

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

    def on_die(self, die, vars):
        attr = die.attributes
        if die.tag == 'DW_TAG_variable' and 'DW_AT_location' in attr:
            self.progress.emit(die.offset)

            cu = die.cu
            ll = cu.dwarfinfo._locparser.parse_from_attribute(attr['DW_AT_location'], cu['version'], die) # Either a list or a LocationExpr
            if isinstance(ll, LocationExpr):
                expr = (DWARFExprParser(cu.structs) if cu['version'] > 1 else DWARFExprParserV1(cu.structs)).parse_expr(ll.loc_expr)
                if len(expr) == 1 and expr[0].op_name == 'DW_OP_addr':
                    addr = expr[0].args[0]
                    (name, size) = decode_var(die)

                    i = bisect_left(vars, addr, key=lambda ds: ds.addr)
                    # Full matches possible with inlines
                    # TODO: deal with overlaps
                    if i < len(vars) and vars[i].addr == addr: # Same addr - allow for greater size override
                        if size and (not vars[i].size or vars[i].size < size):
                            vars[i] = DataSpan(addr, size, die, name, top_die_file_name(cu.get_top_DIE()))
                    else:
                        vars.insert(i, DataSpan(addr, size, die, name, top_die_file_name(cu.get_top_DIE())))

    def postprocess(self, vars):
        n = len(vars)
        i = 1
        while i < n:
            if vars[i].addr > vars[i-1].end + 1:
                vars.insert(i, DataSpan(vars[i-1].end + 1, vars[i].addr - vars[i-1].end - 1))
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