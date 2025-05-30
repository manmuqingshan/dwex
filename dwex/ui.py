import os
from PyQt6.QtCore import Qt, QRectF, QSizeF, QPointF, QByteArray
from PyQt6.QtGui import QKeySequence, QAction, QImage, QPixmap, QPainter, QIcon, QFont
from PyQt6.QtWidgets import *
from PyQt6.QtSvg import QSvgRenderer

def setup_menu(win):
    menu = win.menuBar()
    file_menu = menu.addMenu("&File")
    open_menuitem = file_menu.addAction("Open...")
    open_menuitem.setShortcut(QKeySequence.StandardKey.Open)
    open_menuitem.triggered.connect(win.on_open)
    win.switchslice_menuitem = file_menu.addAction("Switch file slice...")
    win.switchslice_menuitem.triggered.connect(win.on_switchslice)
    win.switchslice_menuitem.setEnabled(False)
    win.savesection_menuitem = file_menu.addAction("Save a section as...")
    win.savesection_menuitem.triggered.connect(win.on_savesection)
    win.savesection_menuitem.setEnabled(False)
    win.loadexec_menuitem = file_menu.addAction("Load companion executable...")
    win.loadexec_menuitem.triggered.connect(win.on_loadexec)
    win.loadexec_menuitem.setEnabled(False)
    win.mru_menu = file_menu.addMenu("Recent files")
    if len(win.mru):
        win.populate_mru_menu()
    else:
        win.mru_menu.setEnabled(False)
    exit_menuitem = file_menu.addAction("E&xit")
    exit_menuitem.setMenuRole(QAction.MenuRole.QuitRole)
    exit_menuitem.setShortcut(QKeySequence.StandardKey.Quit)
    exit_menuitem.triggered.connect(win.on_exit)
    if os.environ.get("DWEX_DEBUG") is not None:
        file_menu.addAction("Debug").triggered.connect(win.on_debug)
    #########
    view_menu = menu.addMenu("View")
    win.prefix_menuitem = view_menu.addAction("DWARF prefix")
    win.prefix_menuitem.setCheckable(True)
    win.prefix_menuitem.setChecked(win.prefix)
    win.prefix_menuitem.triggered.connect(win.on_view_prefix)
    win.lowlevel_menuitem = view_menu.addAction("Low level")
    win.lowlevel_menuitem.setCheckable(True)
    win.lowlevel_menuitem.setChecked(win.lowlevel)
    win.lowlevel_menuitem.triggered.connect(win.on_view_lowlevel)
    win.hex_menuitem = view_menu.addAction("Hexadecimal")
    win.hex_menuitem.setCheckable(True)
    win.hex_menuitem.setChecked(win.hex)
    win.hex_menuitem.triggered.connect(win.on_view_hex)
    win.regnames_menuitem = view_menu.addAction("DWARF register names")
    win.regnames_menuitem.setCheckable(True)
    win.regnames_menuitem.setChecked(win.dwarfregnames)
    win.regnames_menuitem.triggered.connect(win.on_view_regnames)
    view_menu.addSeparator()
    win.sortcus_menuitem = view_menu.addAction("Sort CUs")
    win.sortcus_menuitem.setCheckable(True)
    win.sortcus_menuitem.setChecked(win.sortcus)
    win.sortcus_menuitem.triggered.connect(win.on_sortcus)
    win.sortdies_menuitem = view_menu.addAction("Sort DIEs")
    win.sortdies_menuitem.setCheckable(True)
    win.sortdies_menuitem.setChecked(win.sortdies)
    win.sortdies_menuitem.triggered.connect(win.on_sortdies)
    view_menu.addSeparator()
    win.highlightcode_menuitem = view_menu.addAction("Highlight code")
    win.highlightcode_menuitem.setCheckable(True)
    win.highlightcode_menuitem.setEnabled(False)
    win.highlightcode_menuitem.triggered.connect(win.on_highlight_code)
    win.highlightsubstring_menuitem = view_menu.addAction("Highlight by substring...")
    win.highlightsubstring_menuitem.setCheckable(True)
    win.highlightsubstring_menuitem.setEnabled(False)
    win.highlightsubstring_menuitem.triggered.connect(win.on_highlight_substring)
    win.highlightcondition_menuitem = view_menu.addAction("Highlight by condition...")
    win.highlightcondition_menuitem.setCheckable(True)
    win.highlightcondition_menuitem.setEnabled(False)
    win.highlightcondition_menuitem.triggered.connect(win.on_highlight_condition)
    win.highlightnothing_menuitem = view_menu.addAction("Remove highlighting")
    win.highlightnothing_menuitem.setEnabled(False)
    win.highlightnothing_menuitem.triggered.connect(win.on_highlight_nothing)
    view_menu.addSeparator()
    win.cuproperties_menuitem = view_menu.addAction("CU properties...")
    win.cuproperties_menuitem.setEnabled(False)
    win.cuproperties_menuitem.triggered.connect(win.on_cuproperties)
    view_menu.addSeparator()
    theme_menuitem = view_menu.addAction("Theme...")
    theme_menuitem.triggered.connect(win.on_changetheme)
    #########
    edit_menu = menu.addMenu("Edit")
    win.copy_menuitem = edit_menu.addAction("Copy value")
    win.copy_menuitem.setShortcut(QKeySequence.StandardKey.Copy)
    win.copy_menuitem.setEnabled(False)
    win.copy_menuitem.triggered.connect(win.on_copyvalue)
    win.copyline_menuitem = edit_menu.addAction("Copy line")
    win.copyline_menuitem.setEnabled(False)
    win.copyline_menuitem.triggered.connect(win.on_copyline)        
    win.copytable_menuitem = edit_menu.addAction("Copy table")
    win.copytable_menuitem.setEnabled(False)
    win.copytable_menuitem.triggered.connect(win.on_copytable)  
    #########
    nav_menu = menu.addMenu("Navigate")
    win.back_menuitem = nav_menu.addAction("Back")
    win.back_menuitem.setShortcut(QKeySequence.StandardKey.Back)
    win.back_menuitem.setEnabled(False);
    win.back_menuitem.triggered.connect(lambda: win.on_nav(1))
    win.forward_menuitem = nav_menu.addAction("Forward")
    win.forward_menuitem.setShortcut(QKeySequence.StandardKey.Forward)
    win.forward_menuitem.setEnabled(False);
    win.forward_menuitem.triggered.connect(lambda: win.on_nav(-1))
    win.followref_menuitem = nav_menu.addAction("Follow the ref")
    win.followref_menuitem.setEnabled(False);
    win.followref_menuitem.setShortcut(QKeySequence(Qt.Modifier.CTRL | Qt.Key.Key_Return))
    win.followref_menuitem.triggered.connect(win.on_followref)
    nav_menu.addSeparator()
    win.nexthl_menuitem = nav_menu.addAction("To next highlight")
    win.nexthl_menuitem.setEnabled(False)
    win.nexthl_menuitem.triggered.connect(win.on_nexthl)
    win.prevhl_menuitem = nav_menu.addAction("To previous highlight")
    win.prevhl_menuitem.setEnabled(False)
    win.prevhl_menuitem.triggered.connect(win.on_prevhl)
    nav_menu.addSeparator()
    win.byoffset_menuitem = nav_menu.addAction("DIE by offset...")
    win.byoffset_menuitem.setEnabled(False)
    win.byoffset_menuitem.triggered.connect(win.on_byoffset)
    win.find_menuitem = nav_menu.addAction("Find...")
    win.find_menuitem.setEnabled(False)
    win.find_menuitem.setShortcut(QKeySequence.StandardKey.Find)
    win.find_menuitem.triggered.connect(win.on_find)
    win.findip_menuitem = nav_menu.addAction("Find code address...")
    win.findip_menuitem.setEnabled(False)
    win.findip_menuitem.triggered.connect(win.on_findip)
    win.findbycondition_menuitem = nav_menu.addAction("Find by condition...")
    win.findbycondition_menuitem.setEnabled(False)
    win.findbycondition_menuitem.triggered.connect(win.on_findbycondition)
    win.findnext_menuitem = nav_menu.addAction("Find next")
    win.findnext_menuitem.setEnabled(False)
    win.findnext_menuitem.setShortcut(QKeySequence.StandardKey.FindNext)
    win.findnext_menuitem.triggered.connect(win.on_findnext)
    ########
    ana_menu = menu.addMenu("Analysis")
    win.localsat_menuitem = ana_menu.addAction("Locals at address...")
    win.localsat_menuitem.setEnabled(False)
    win.localsat_menuitem.triggered.connect(win.on_localsat)
    win.funcmap_menuitem = ana_menu.addAction("Function map...")
    win.funcmap_menuitem.setEnabled(False)
    win.funcmap_menuitem.triggered.connect(win.on_funcmap)
    ana_menu.addSeparator()
    win.aranges_menuitem = ana_menu.addAction("Aranges...")
    win.aranges_menuitem.setEnabled(False)
    win.aranges_menuitem.triggered.connect(win.on_aranges)
    win.frames_menuitem = ana_menu.addAction("Frames...")
    win.frames_menuitem.setEnabled(False)
    win.frames_menuitem.triggered.connect(win.on_frames)
    win.unwind_menuitem = ana_menu.addAction("Unwind info...")
    win.unwind_menuitem.setEnabled(False)
    win.unwind_menuitem.triggered.connect(win.on_unwind)
    ########
    help_menu = menu.addMenu("Help")
    about_menuitem = help_menu.addAction("About...")
    about_menuitem.setMenuRole(QAction.MenuRole.AboutRole)
    about_menuitem.triggered.connect(win.on_about) 
    help_menu.addAction('Check for updates...').triggered.connect(win.on_updatecheck)
    help_menu.addAction('Report an issue').triggered.connect(win.on_issue)
    help_menu.addAction('Homepage').triggered.connect(win.on_homepage)

back_svg = b'<path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="round" stroke-linecap="round" d="M 40 20 L 10 50 L 40 80 M 10 50 h 60"/>'
fwd_svg = b'<path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="round" stroke-linecap="round" d="M 60 20 L 90 50 L 60 80 M 90 50 h -60"/>'
open_svg = b'<path fill="none" stroke="#000" stroke-width="5" d="M 10 20 v 60 h 80 v -45 h -35 l -15 -15 z"/>'
fwref_svg = b'<path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="round" stroke-linecap="round" d="M20 5v90h40M20 65h40M20 35h15"/><path fill="none" stroke="#000" stroke-width="5" stroke-linecap="round" d="M70 95q30-30-20-60"/><path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="butt" stroke-linecap="round" d="M54 54l-5-20 20-2"/>'
copy_svg = b'<path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="round" d="M15 25h45v60H15zm20 0V15h45v60H60"/>'
byoffset_svg = b'<path fill="none" stroke="#000" stroke-width="5" stroke-linejoin="round" d="M40 5v75h40M40 25h20M40 50h30M10 5v35H5l10 10 10-10h-5V5z"/>'
find_svg = b'<path stroke="#000" fill="#000" fill-rule="evenodd" d="M40 60a25 25 0 1112-8l16 25-12 7zM15 36a15 15 0 1135 0 15 15 0 11-35 0"/>'
nexthl_svg = b'<g stroke="#000" fill="none" stroke-width="5" stroke-linecap="round"><path stroke-linejoin="round" d="M5 20h75L65 5m15 15L65 35"/><path d="M5 60h17M13.787 38.787l12.02 12.02M35 30v17M56.213 38.787l-12.02 12.02M65 60H48M56.213 81.213l-12.02-12.02M35 90V73M13.787 81.213l12.02-12.02"/></g>'
prevhl_svg = b'<g stroke="#000" fill="none" stroke-width="5" stroke-linecap="round"><path stroke-linejoin="round" d="M95 20H20L35 5M20 20l15 15"/><path d="M78 60h17M74.192 69.192l12.021 12.021M65 73v17M55.808 69.192L43.787 81.213M52 60H35M55.808 50.808L43.787 38.787M65 47V30M74.192 50.808l12.021-12.021"/></g>'

def setup_toolbar(win):
    tb = win.addToolBar("Main")
   
    sz = tb.iconSize()
    rc = QRectF(QPointF(0, 0), QSizeF(sz.width(), sz.height()))

    def make_icon(svg_body):
        img = QImage(sz, QImage.Format.Format_ARGB32)
        img.fill(0)
        svg = b'<svg width="100" height="100">' + svg_body + b'</svg>'
        renderer = QSvgRenderer(QByteArray(svg))
        pixmap = QPixmap.fromImage(img, Qt.ImageConversionFlag.NoFormatConversion)
        with QPainter(pixmap) as painter:
            renderer.render(painter, rc)
        return QIcon(pixmap)
    
    tb.setFloatable(False)
    tb.setMovable(False)

    win.back_tbitem = tb.addAction("Back")
    win.back_tbitem.triggered.connect(lambda: win.on_nav(1))
    win.back_tbitem.setEnabled(False)
    win.back_tbitem.setIcon(make_icon(back_svg))
    win.back_tbitem.setToolTip("Navigate to the previous DIE")
    win.forward_tbitem = tb.addAction("Forward")
    win.forward_tbitem.triggered.connect(lambda: win.on_nav(-1))
    win.forward_tbitem.setEnabled(False)
    win.forward_tbitem.setIcon(make_icon(fwd_svg))
    win.forward_tbitem.setToolTip("Navigate to the DIE that you went back from")
    tb.addSeparator()

    ac = tb.addAction("Open")
    ac.triggered.connect(win.on_open)
    ac.setIcon(make_icon(open_svg))
    ac.setToolTip("Open a compiled executable, object, or library file to see its debug information")
    tb.addSeparator()

    win.copy_tbitem = tb.addAction("Copy")
    win.copy_tbitem.setIcon(make_icon(copy_svg))
    win.copy_tbitem.setEnabled(False)
    win.copy_tbitem.setToolTip("Copy the current attribute's value to the clipboard")
    win.copy_tbitem.triggered.connect(win.on_copyvalue)
    tb.addSeparator()
    win.followref_tbitem = tb.addAction("Follow")
    win.followref_tbitem.setEnabled(False)
    win.followref_tbitem.setIcon(make_icon(fwref_svg))
    win.followref_tbitem.triggered.connect(win.on_followref)
    win.followref_tbitem.setToolTip("Navigate to the DIE that the current attribute is referencing")
    win.byoffset_tbitem = tb.addAction("By offset")
    win.byoffset_tbitem.setEnabled(False)
    win.byoffset_tbitem.setIcon(make_icon(byoffset_svg))
    win.byoffset_tbitem.triggered.connect(win.on_byoffset)
    win.byoffset_tbitem.setToolTip("Navigate to the DIE by the hex offset of the DIE in the info section")
    win.find_tbitem = tb.addAction("Find")
    win.find_tbitem.setEnabled(False)
    win.find_tbitem.setIcon(make_icon(find_svg))
    win.find_tbitem.triggered.connect(win.on_find)
    win.find_tbitem.setToolTip("Find the next DIE in the tree by tag/attribute/value substring")
    win.nexthl_tbitem = tb.addAction("Next highlight")
    win.nexthl_tbitem.setEnabled(False)
    win.nexthl_tbitem.setIcon(make_icon(nexthl_svg))
    win.nexthl_tbitem.triggered.connect(win.on_nexthl)
    win.nexthl_tbitem.setToolTip("Navigate to the next highlighted DIE in the tree")
    win.prevhl_tbitem = tb.addAction("Previous highlight")
    win.prevhl_tbitem.setEnabled(False)
    win.prevhl_tbitem.setIcon(make_icon(prevhl_svg))
    win.prevhl_tbitem.triggered.connect(win.on_prevhl)
    win.prevhl_tbitem.setToolTip("Navigate to the previous highlighted DIE in the tree")

def setup_explorer(win):
    # Set up the left pane and the right pane
    tree = win.the_tree = QTreeView()
    tree.header().hide()
    tree.setUniformRowHeights(True)
    
    rpane = QSplitter(Qt.Orientation.Vertical)
    die_table = win.die_table = QTableView()
    die_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
    die_table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
    die_table.doubleClicked.connect(win.on_attribute_dclick)
    rpane.addWidget(die_table)
    
    rbpane = QVBoxLayout()
    rbpane.setContentsMargins(0, 0, 0, 0)
    details_warning = win.details_warning = QLabel()
    details_warning.setVisible(False)
    rbpane.addWidget(details_warning)
    details_table = win.details_table = QTableView()
    details_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
    details_table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
    details_table.doubleClicked.connect(win.on_details_dclick)
    rbpane.addWidget(details_table)
    rbp = QWidget()
    rbp.setLayout(rbpane)
    rpane.addWidget(rbp)
    # All the resizing goes into the bottom pane
    rpane.setStretchFactor(0, 0)
    rpane.setStretchFactor(1, 1)

    spl = QSplitter()
    spl.addWidget(win.the_tree)
    spl.addWidget(rpane)
    # All the resizing goes into the right pane by default
    spl.setStretchFactor(0, 0)
    spl.setStretchFactor(1, 1) 
    win.setCentralWidget(spl)

def setup_splash(win):
    l = QLabel()
    l.setText("Drag\na file\nhere")
    l.setAlignment(Qt.AlignmentFlag.AlignCenter)
    f = QFont("Verdana", 50)
    f.setStyleHint(QFont.StyleHint.SansSerif)
    l.setFont(f)
    l.setEnabled(False)
    win.setCentralWidget(l)

def setup_ui(win):
    setup_menu(win)
    setup_toolbar(win)
    setup_splash(win)

    win.setWindowTitle("DWARF Explorer")
    win.resize(win.font_metrics.averageCharWidth() * 250, win.font_metrics.height() * 60)
