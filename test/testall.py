import os, sys
from time import time
from PyQt6.QtCore import Qt, QAbstractItemModel, QAbstractTableModel, QModelIndex
sys.path.insert(1, os.getcwd()) # To make sure dwex resolves to local path
from elftools.dwarf.locationlists import LocationParser, LocationExpr
from dwex.formats import read_dwarf
from dwex.die import DIETableModel
from dwex.dwarfutil import strip_path
from dwex.datasec import GatherStaticDataThread

def test_render(di):
    m = False
    dummy_index = QModelIndex()
    for (i, CU) in enumerate(di._CUs):
        top_die = CU.get_top_DIE()
        print("%s" % strip_path(top_die.attributes['DW_AT_name'].value.decode('utf-8', errors='ignore')) if 'DW_AT_name' in top_die.attributes else "(no name)")
        CU._lineprogram = None
        CU._exprparser = None
        for die in CU.iter_DIEs():
            if not die.is_null():
                assert die.tag.startswith('DW_TAG_')

                if not m:
                    # With prefix, with low level data, decimal
                    m = DIETableModel(die, True, True, False, True) 
                else:
                    m.display_DIE(die)

                rc = m.rowCount(dummy_index)
                cc = m.columnCount(dummy_index)
                keys = list(die.attributes.keys())
                # Assuming rows correspond to attributes; 
                # if we introduce non-attribute metadata into the DIE table, this will break
                for r in range(m.meta_count, rc):
                    key = keys[r - m.meta_count]
                    attr = die.attributes[key]
                    form = attr.form
                    value = attr.value
                    # Check the elftools' results first

                    # Check if the key is interpreted properly
                    assert str(key).startswith('DW_AT_')
                    assert str(form).startswith('DW_FORM_')

                    # Check if attributes with locations are all found
                    if form == 'DW_FORM_exprloc':
                        assert LocationParser.attribute_has_location(attr, CU['version'])
                    # The converse is not true; on DWARF2, location expressions can have form DW_FORM_block1

                    # Now check the spell out logic
                    for c in range(0, cc):
                        m.data(m.index(r, c, dummy_index), Qt.ItemDataRole.DisplayRole)
                    # Low level details, if any
                    details = m.get_attribute_details(m.index(r, 0, dummy_index))
                    if form == 'DW_FORM_section_offset':
                        assert details is not None
                    # Check the high level spell out logic too
                    m.set_lowlevel(False, dummy_index)
                    details = m.get_attribute_details(m.index(r, 0, dummy_index))
                    m.set_lowlevel(True, dummy_index)

# The logic of tracking down the type is more involved
# This is just for a quick dump
def get_var_DIE_type(die):
    if 'DW_AT_abstract_origin' in die.attributes: # Inside inlined_subroutine, jump to the abstract subtree - that's where the type and the spec are
        die = die.get_DIE_from_attribute('DW_AT_abstract_origin')
    type_die = None
    if 'DW_AT_type' in die.attributes:
        type_die = die.get_DIE_from_attribute('DW_AT_type')

    if 'DW_AT_specification' in die.attributes:
        spec_die = die.get_DIE_from_attribute('DW_AT_specification')
        if not type_die and 'DW_AT_type' in spec_die.attributes:
            type_die = spec_die.get_DIE_from_attribute('DW_AT_type')
        
    if type_die:
        return type_die.tag[7:]

def test_datasection(di):
    class FakeThread(GatherStaticDataThread):
        def yieldCurrentThread(self):
            pass

    def decorate_cu(cu, i):
        cu._i = i
        cu._lineprogram = None
        cu._exprparser = None
        return cu
    
    di._unsorted_CUs = CUs = [decorate_cu(cu, i) for (i, cu) in enumerate(di.iter_CUs())]
    thread = FakeThread(None, di)
    last_CU = CUs[-1]
    end_offset = last_CU.cu_offset + last_CU.size
    ts = time()
    def on_progress(v):
        nonlocal ts
        ts_now = time()
        if ts_now - ts >= 10:
            print(f"{(v*100)//end_offset}%")
            ts = ts_now
    thread.progress.connect(on_progress)
    thread.run()
    if thread.exc:
        print(f"Exception occurred: {thread.exc.message}")
    elif not len(thread.result):
        print(f"No results")
    else:
        #if next((s for s in thread.result if s.size is None), False):
        #    print("Warning: Some lines have undefined size.")
        for s in thread.result:
            if s.size is None:
                print(f"0x{s.die.offset:X} {get_var_DIE_type(s.die)}")

def test_dwarfinfo(di):
    # Some global cache setup in line with the app proper
    di._ranges = None
    di._CUs = [cu for cu in di.iter_CUs()]
    di._locparser = None

    #test_render(di)
    test_datasection(di)


def test_file_for(filename, on_di):    
    print("=================== " + filename)
    arches = False
    def save_arches(a, _, __):
        nonlocal arches
        arches = a
        return None # Cancel out of loading
    try:
        di = read_dwarf(filename, save_arches)
        if arches: # Fat binary - go through all through architectures
            for arch_no in range(0, len(arches)):
                print("----------- " + arches[arch_no])
                di = read_dwarf(filename, lambda arches, _, __:arch_no)
                if di:
                    on_di(di)
        elif di and di.debug_info_sec:
            on_di(di)
    except Exception as e:
        print(f"Exception while loading: {e}")

def test_file(filename):
    test_file_for(filename, test_dwarfinfo)

def test_tree_for(path, on_di):
    for f in os.listdir(path):
        full_path = os.path.join(path, f)
        # See what can be done about JiPad ones
        if f.endswith('.dSYM') or f.endswith('.o') or f.endswith('.elf') or (f.endswith('.so') and not f.endswith('libJiPadLib.so')):
            test_file_for(full_path, on_di)
        elif os.path.isdir(full_path):
            test_tree_for(full_path, on_di)        

def test_tree(path):
    test_tree_for(path, test_dwarfinfo)




# Caught on GNU_call_site_value

# All sec_offsets must be parsed

# All expressions must be parsed - which forms are expressions?