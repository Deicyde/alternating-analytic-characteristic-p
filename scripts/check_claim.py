#!/usr/bin/env -S python3 -I
"""Check that a ledger claim is proved.

Usage: python3 -I scripts/check_claim.py ID

Checks, in order, and prints one JSON object (also written to work/checks/ID.json):
  1. The code of Challenges/ID.lean, with comments and docstrings removed, is unchanged since
     the ledger was created (git tag `ledger-base`).
  2. Solutions/ID.lean exists and contains no `sorry`, `admit`, `native_decide` or `axiom`.
  3. Challenges/ID.json exists and names every theorem of the challenge.
  4. `lake build Challenges.ID Solutions.ID` succeeds (through scripts/run_lean.py --build).
  5. `#print axioms` of every theorem in the solution shows only propext, Classical.choice,
     Quot.sound.
  6. With pp.all, `#check @thm` of every theorem and `#print` of every definition give the same
     output when importing Challenges.ID and when importing Solutions.ID.
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUN = [sys.executable, '-I', os.path.join(ROOT, 'scripts', 'run_lean.py')]
OK_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BASE = 'ledger-base'
# Statements written after the ledger was created, with the commit that added them.
STATEMENT_ADDED = {'Thm2_1': '7c9f61c'}


def sh(cmd):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return p.returncode, (p.stdout or '') + (p.stderr or '')


def strip_comments(src):
    """Remove Lean comments and docstrings (nested block comments included); keep strings."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth:
            if src.startswith('/-', i):
                depth += 1; i += 2
            elif src.startswith('-/', i):
                depth -= 1; i += 2
            else:
                i += 1
        elif src.startswith('/-', i):
            depth = 1; i += 2
        elif src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1
        else:
            out.append(src[i]); i += 1
    return ''.join(out)


def code_of(src):
    """The code of a Lean file: comments removed, whitespace collapsed."""
    return ' '.join(strip_comments(src).split())


def theorems_and_defs(src):
    code = strip_comments(src)
    ns = re.search(r'^namespace\s+(\S+)', code, re.M)
    ns = ns.group(1) if ns else ''
    thms = re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?theorem\s+([^\s(:{\[]+)', code, re.M)
    defs = re.findall(r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?(?:def|abbrev|structure|class|inductive)\s+([^\s(:{\[]+)', code, re.M)
    q = lambda n: n if n.startswith(ns + '.') or not ns else f'{ns}.{n}'
    return [q(t) for t in thms], [q(d) for d in defs]


def main(argv):
    if not argv:
        print(__doc__); return 1
    cid = argv[0]
    res = {'id': cid, 'ok': False, 'steps': {}}
    chal = os.path.join(ROOT, 'Challenges', f'{cid}.lean')
    sol = os.path.join(ROOT, 'Solutions', f'{cid}.lean')
    cfg = os.path.join(ROOT, 'Challenges', f'{cid}.json')
    os.makedirs(os.path.join(ROOT, 'work', 'checks'), exist_ok=True)

    def finish(ok):
        res['ok'] = ok
        out = json.dumps(res, indent=1)
        open(os.path.join(ROOT, 'work', 'checks', f'{cid}.json'), 'w').write(out)
        print(out)
        return 0 if ok else 1

    base = STATEMENT_ADDED.get(cid, BASE)
    rc, old = sh(['git', 'show', f'{base}:Challenges/{cid}.lean'])
    res['steps']['challenge_unchanged'] = rc == 0 and code_of(old) == code_of(open(chal).read())
    if not res['steps']['challenge_unchanged']:
        res['error'] = f'the code of Challenges/{cid}.lean differs from {base}; challenge statements must not change'
        return finish(False)
    if not os.path.exists(sol):
        res['error'] = 'no solution file'; return finish(False)
    scode = strip_comments(open(sol).read())
    bad = [w for w in ('sorry', 'admit', 'native_decide') if re.search(r'\b' + w + r'\b', scode)]
    if re.search(r'^\s*axiom\s', scode, re.M):
        bad.append('axiom')
    res['steps']['no_forbidden_tokens'] = not bad
    if bad:
        res['error'] = f'solution contains {bad}'; return finish(False)
    if re.search(r'^\s*import\s+Challenges', scode, re.M):
        res['error'] = 'solution imports a Challenges module'; return finish(False)
    thms, defs = theorems_and_defs(open(chal).read())
    res['theorems'] = thms
    res['definitions'] = defs
    if not thms:
        res['error'] = 'challenge has no theorem'; return finish(False)
    if not os.path.exists(cfg):
        res['error'] = f'missing Challenges/{cid}.json'; return finish(False)
    names = json.load(open(cfg)).get('theorem_names', [])
    missing = [t for t in thms if t not in names]
    res['steps']['config_names_all_theorems'] = not missing
    if missing:
        res['error'] = f'Challenges/{cid}.json lacks {missing}'; return finish(False)

    rc, out = sh(RUN + ['--build', f'Challenges.{cid}', f'Solutions.{cid}'])
    res['steps']['build'] = rc == 0
    if rc != 0:
        res['error'] = 'build failed'; res['build_tail'] = out[-6000:]; return finish(False)

    cdir = os.path.join(ROOT, 'work', 'checks', cid)
    os.makedirs(cdir, exist_ok=True)
    ax = os.path.join(cdir, 'Axioms.lean')
    open(ax, 'w').write(f'import Solutions.{cid}\n' + ''.join(f'#print axioms {t}\n' for t in thms))
    rc, out = sh(RUN + [os.path.relpath(ax, ROOT)])
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out.replace('\n', ' '))
    nonstd = {n: a for n, a in found if not set(x.strip() for x in a.split(',') if x.strip()) <= OK_AXIOMS}
    no_axioms = [t for t in thms if t not in {n for n, _ in found}
                 and f"'{t}' does not depend on any axioms" not in out]
    res['steps']['axioms_standard'] = rc == 0 and not nonstd and not no_axioms
    if not res['steps']['axioms_standard']:
        res['error'] = 'axiom check failed'; res['axioms'] = {'nonstandard': nonstd, 'unreported': no_axioms,
                                                            'tail': out[-3000:]}
        return finish(False)

    body = 'set_option pp.all true\nset_option pp.proofs false\n'
    body += ''.join(f'#check @{t}\n' for t in thms) + ''.join(f'#print {d}\n' for d in defs)
    outs = {}
    for side, mod in (('C', 'Challenges'), ('S', 'Solutions')):
        f = os.path.join(cdir, f'Id{side}.lean')
        open(f, 'w').write(f'import {mod}.{cid}\n' + body)
        rc, o = sh(RUN + [os.path.relpath(f, ROOT)])
        o = re.sub(r'work/checks/' + re.escape(cid) + r'/Id[CS]\.lean:\d+:\d+: ', '', o)
        o = re.sub(r'^=== .*$', '', o, flags=re.M)
        outs[side] = (rc, o)
    same = outs['C'][0] == 0 and outs['S'][0] == 0 and outs['C'][1] == outs['S'][1]
    res['steps']['statements_identical'] = same
    if not same:
        a, b = outs['C'][1].splitlines(), outs['S'][1].splitlines()
        diff = [f'line {i}: C={x[:200]} | S={y[:200]}' for i, (x, y) in enumerate(zip(a, b)) if x != y][:10]
        res['error'] = 'challenge and solution statements differ under pp.all'
        res['identity_diff'] = diff or [f'lengths {len(a)} vs {len(b)}']
        return finish(False)
    return finish(True)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
