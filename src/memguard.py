"""Memory monitoring plus a watchdog thread that aborts the process if memory exceeds a hard cap.

Portable version for publication: uses the Windows process-memory API when available and falls back to the
POSIX `resource` module (or /proc) elsewhere. It only guards memory; it plays no role in any mathematical check.
"""
import os, sys, threading, time

try:  # Windows
    import ctypes
    from ctypes import wintypes

    class PROCESS_MEMORY_COUNTERS(ctypes.Structure):
        _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                    ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                    ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                    ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                    ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]

    def _counters():
        pmc = PROCESS_MEMORY_COUNTERS()
        pmc.cb = ctypes.sizeof(PROCESS_MEMORY_COUNTERS)
        k32 = ctypes.WinDLL('kernel32'); psapi = ctypes.WinDLL('psapi')
        k32.GetCurrentProcess.restype = wintypes.HANDLE
        psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESS_MEMORY_COUNTERS), wintypes.DWORD]
        psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
        if not psapi.GetProcessMemoryInfo(k32.GetCurrentProcess(), ctypes.byref(pmc), pmc.cb):
            raise OSError('GetProcessMemoryInfo failed')
        return pmc

    def mem_gb():
        """current private bytes in GB"""
        return _counters().PagefileUsage / 1e9

    def peak_gb():
        c = _counters()
        return max(c.PeakPagefileUsage, c.PeakWorkingSetSize) / 1e9

except (ImportError, AttributeError, OSError, ValueError):  # Linux / macOS
    def mem_gb():
        try:
            with open('/proc/self/status') as fh:
                for line in fh:
                    if line.startswith('VmRSS:'):
                        return int(line.split()[1]) * 1024 / 1e9
        except OSError:
            pass
        return peak_gb()

    def peak_gb():
        try:
            import resource
            r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            return (r if sys.platform == 'darwin' else r * 1024) / 1e9
        except Exception:
            return 0.0


def start_watchdog(cap_gb=6.0, period=0.5):
    def run():
        while True:
            m = mem_gb()
            if m > cap_gb:
                sys.stderr.write(f"\n[memguard] memory {m:.2f} GB > cap {cap_gb} GB -> aborting\n")
                sys.stderr.flush()
                os._exit(3)
            time.sleep(period)
    th = threading.Thread(target=run, daemon=True)
    th.start()
    return th
