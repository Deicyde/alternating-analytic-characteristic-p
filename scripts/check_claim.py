#!/usr/bin/env python3 -I
"""Check that a ledger claim is proved.

Usage: python3 -I scripts/check_claim.py ID [--allow-challenge-edit]

Checks, in order, and prints one JSON object (also written to work/checks/ID.json):
  1. Challenges/ID.lean is unchanged relative to the commit `ledger-base` (git tag or ref),
     unless --allow-challenge-edit is given.
  2. Solutions/ID.lean exists and contains no `sorry`, `admit`, `native_decide`, new `axiom`.
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


def sh(cmd):
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    return p.returncode, (p.stdout or '') + (p.stderr or '')


def strip_comments(src):
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)


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
    allow_edit = '--allow-challenge-edit' in argv
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

    rc, out = sh(['git', 'diff', '--quiet', BASE, '--', f'Challenges/{cid}.lean'])
    res['steps']['challenge_unchanged'] = (rc == 0) or allow_edit
    if not res['steps']['challenge_unchanged']:
        res['error'] = f'Challenges/{cid}.lean differs from {BASE}; challenge statements must not change'
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
