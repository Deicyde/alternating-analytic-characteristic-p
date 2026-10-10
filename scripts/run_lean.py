#!/usr/bin/env -S python3 -I
"""Run Lean on this repository without exceeding the machine's memory.

Each `lake env lean` of a file that imports the library needs about 2.4 GB, so at most
NSLOTS such processes run at once, machine-wide, coordinated by lock files in `_locks/`.

Usage, from anywhere (paths are relative to the repository root):
  python3 -I scripts/run_lean.py FILE.lean [FILE.lean ...]
      Elaborate each file with `lake env lean`, holding one slot.
  python3 -I scripts/run_lean.py --build MODULE [MODULE ...]
      Run `lake build MODULE ...` (e.g. AlternatingAnalytic.Scalar.ChainGap or
      Solutions.LemF_3), holding ALL slots, so that the build runs alone.
      On a machine with less than about 32 GB of memory, build named modules this way
      rather than running a bare `lake build`.

Exit code: 0 if everything succeeded without errors (warnings allowed), else 1.
"""
import fcntl, os, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOCKS = os.path.join(ROOT, '_locks')
NSLOTS = 4


def slot_fd(i):
    os.makedirs(LOCKS, exist_ok=True)
    return os.open(os.path.join(LOCKS, f'slot{i}.lock'), os.O_CREAT | os.O_RDWR)


def acquire_one():
    while True:
        for i in range(NSLOTS):
            fd = slot_fd(i)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return [fd]
            except OSError:
                os.close(fd)
        time.sleep(3)


def acquire_all():
    # Blocking acquisition in a fixed order: no deadlock between builders, and a waiting
    # builder gets each slot as soon as it is released.
    fds = []
    for i in range(NSLOTS):
        fd = slot_fd(i)
        fcntl.flock(fd, fcntl.LOCK_EX)
        fds.append(fd)
    return fds


def release(fds):
    for fd in fds:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def run(cmd, label, timeout):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print(f'=== {label}: TIMEOUT after {timeout}s')
        return False
    out = (p.stdout or '') + (p.stderr or '')
    errors = [l for l in out.splitlines() if ': error' in l or l.startswith('error')]
    print(f'=== {label}: exit {p.returncode}, {time.time() - t0:.0f}s, {len(errors)} error line(s)')
    print(out[-20000:] if len(out) > 20000 else out)
    return p.returncode == 0 and not errors


def main(argv):
    if not argv:
        print(__doc__)
        return 1
    if argv[0] == '--build':
        mods = argv[1:]
        if not mods:
            print('--build needs at least one module name')
            return 1
        fds = acquire_all()
        try:
            return 0 if run(['lake', 'build'] + mods, 'lake build ' + ' '.join(mods), 3600) else 1
        finally:
            release(fds)
    ok = True
    for f in argv:
        fds = acquire_one()
        try:
            ok = run(['lake', 'env', 'lean', f], f, 1800) and ok
        finally:
            release(fds)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
