import os
import signal
import subprocess
import sys

if sys.version_info >= (3, 0):
    Popen = subprocess.Popen
else:
    class Popen(subprocess.Popen):
        def __init__(self, *args, **kwargs):
            kwargs.pop('encoding', None)
            super(Popen, self).__init__(*args, **kwargs)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            try:
                self.stderr.close()
            except:
                pass
            try:
                self.stdout.close()
            except:
                pass
            try:
                self.stdin.close()
            finally:
                try:
                    subprocess.signal = signal
                    subprocess.os = os
                    try:
                        self.wait()
                    except:
                        self.kill()
                except:
                    pass
