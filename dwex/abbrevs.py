from PyQt6.QtCore import Qt, QAbstractTableModel, QSize
from PyQt6.QtWidgets import *
from .details import GenericTableModel
from .dwarfutil import format_tag

class AbbrevsDlg(QDialog):
    def __init__(self, win, cu, ll, hex, prefix):
        QDialog.__init__(self, win, Qt.WindowType.Dialog)
        self.hex = hex
        self.low_level = ll
        self.prefix = prefix

        self.resize(500, 400)

        spl = QSplitter(Qt.Orientation.Vertical)

        top_pane = QVBoxLayout()
        top_pane.setContentsMargins(0, 0, 0, 0)        
        w = QWidget()
        w.setLayout(top_pane)
        abbrevs = QTableView()
        abbrevs.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        abbrevs.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        # TODO: offset, and show in order
        abbrevs.setModel(GenericTableModel(
            ('Code', 'Tag', 'Children?'),
            tuple((hex(code) if hex else str(code), format_tag(ab.decl['tag'], self.prefix), 'Y' if ab.has_children() else '', ab)
                  for (code, ab) in cu.get_abbrev_table()._abbrev_map.items()), self.tip))
        top_pane.addWidget(abbrevs)
        abbrevs.selectionModel().currentChanged.connect(self.on_abbrev)
        spl.addWidget(w)

        bottom_pane = QVBoxLayout()
        bottom_pane.setContentsMargins(0, 0, 0, 0)
        attributes = self.attributes = QTableView()
        attributes.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        attributes.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        bottom_pane.addWidget(attributes)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Close, Qt.Orientation.Horizontal, self)
        buttons.accepted.connect(self.reject)
        buttons.rejected.connect(self.reject)
        bottom_pane.addWidget(buttons)

        w = QWidget()
        w.setLayout(bottom_pane)
        spl.addWidget(w)

        spl.setStretchFactor(0, 1)
        spl.setStretchFactor(1, 0)
        ly = QVBoxLayout()
        ly.addWidget(spl)
        self.setLayout(ly)

        self.setWindowTitle('Abbreviations')

    def tip(self, row, col, data):
        pass

    def on_abbrev(self, index, prev = None):
        ab = index.internalPointer()[-1]
        self.attributes.setModel(GenericTableModel(('Attribute', 'Form', 'Value'),
            tuple((self.format_attr(a[0]), self.format_form(a[1]), a[2] if len(a) > 2 else None) for a in ab.iter_attr_specs())))
        
    def format_attr(self, attr):
        return attr if self.prefix or not str(attr).startswith('DW_AT_') else attr[6:]
    
    def format_form(self, form):
        return form if self.prefix or not str(form).startswith('DW_FORM_') else form[8:]
