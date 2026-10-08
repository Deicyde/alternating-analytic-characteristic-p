#!/usr/bin/env python3 -I
"""Compile Lean files of this repository one at a time per lock slot, holding one of
NSLOTS global lock slots so that at most NSLOTS lean processes run on this machine
(each `lake env lean` of a file importing the library needs about 2.4 GB).
Usage, from anywhere: python3 -I scripts/run_lean.py <path-relative-to-repo-root> [more files...]
Exit code: 0 if every file compiled without errors (warnings allowed), else 1.
Prints the full lean output for each file."""
import fcntl, os, subprocess, sys, time
EXPORT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NSLOTS = 4
def acquire():
    os.makedirs(os.path.join(EXPORT, '_locks'), exist_ok=True)
    while True:
        for i in range(NSLOTS):
            fd = os.open(os.path.join(EXPORT, '_locks', f'slot{i}.lock'), os.O_CREAT | os.O_RDWR)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return fd
            except OSError:
                os.close(fd)
        time.sleep(3)
ok = True
for f in sys.argv[1:]:
    fd = acquire()
    try:
        t0 = time.time()
        p = subprocess.run(['lake', 'env', 'lean', f], cwd=EXPORT, capture_output=True, text=True, timeout=1500)
        dt = time.time() - t0
        out = (p.stdout or '') + (p.stderr or '')
        errors = [l for l in out.splitlines() if ': error:' in l or l.startswith('error:')]
        print(f'=== {f}: exit {p.returncode}, {dt:.0f}s, {len(errors)} error line(s)')
        print(out[-12000:] if len(out) > 12000 else out)
        if p.returncode != 0 or errors:
            ok = False
    except subprocess.TimeoutExpired:
        print(f'=== {f}: TIMEOUT'); ok = False
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN); os.close(fd)
sys.exit(0 if ok else 1)
