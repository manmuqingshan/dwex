from PyQt6.QtCore import Qt
from PyQt6.QtCore import QThread, pyqtSignal
from PyQt6.QtWidgets import QProgressDialog, QDialog

def gather_to_dialog(win, dwarfinfo, thread_class, dlg_class, hex, progress_text):
    th = thread_class(win, dwarfinfo)
    def done():
        if not pd.wasCanceled():
            pd.close()

        if th.result:
            dlg = dlg_class(win, hex, th.result)
            if dlg.exec() == QDialog.DialogCode.Accepted and dlg.selected_die:
                win.navigate_to_die(dlg.selected_die)
        elif th.exc:
            win.show_warning(f"Sorry, an error occurred while analyzing this binary. Consider reporting this to the author.\n\n{th.exc}")
        else:
            win.show_warning('None found. Could be a deficiency of the analysis.')

    last_CU = dwarfinfo._unsorted_CUs[-1]
    pd = QProgressDialog(progress_text, 'Cancel', 0, last_CU.cu_offset + last_CU.size, win, Qt.WindowType.Dialog)
    pd.setWindowTitle('Please wait')
    pd.canceled.connect(th.cancel)
    pd.show()
    th.progress.connect(pd.setValue)
    th.finished.connect(done)
    th.start() # Will continue in done

class GatherThread(QThread):
    def __init__(self, parent, di):
        super().__init__(parent)
        self.cancelled = False
        self.result = None
        self.exc = None
        self.dwarfinfo = di

    progress = pyqtSignal(int)

    def cancel(self):
        self.cancelled = True

    # Override this
    def postprocess(self, result):
        pass

    # Override this
    def on_cu(self, cu):
        pass

    def run(self):
        try:
            result = []
            for cu in self.dwarfinfo._unsorted_CUs:
                self.on_cu(cu)
                for die in cu.iter_DIEs():
                    self.yieldCurrentThread()
                    if self.cancelled:
                        return
                    try:
                        self.on_die(die, result)
                    except Exception as exc:
                        raise exc
            self.postprocess(result)
            self.result = result
        except Exception as exc:
            self.exc = exc