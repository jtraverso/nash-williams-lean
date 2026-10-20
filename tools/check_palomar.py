"""Checks to run after `lake build` of the ported tree (see tools/port_to_module.py).

usage (from the repository root):  python -I tools/check_palomar.py

1. Proof-dependency audit: runs `tools/audit/AuditPaperIIAssembly.lean.in` (a non-module script
   importing the built modules) from a temporary file outside the repository; it must print
   PASS_PAPERII_PROOF_DEPENDENCIES and only standard axioms in its six queries.
2. Challenge/Solution identity: prints the three theorems (`#check`, pp.all) and the seven
   reproduced definitions (`#print`, pp.all) once importing `Challenge` and once importing
   `Solution`; the outputs (without docstrings) must be identical.
3. Axioms of the three Solution theorems: only propext, Classical.choice, Quot.sound.
4. No `sorry`, `admit`, `native_decide` or `axiom` outside comments in the project sources.
Writes tools/check_report.txt and exits non-zero on any failure.
"""
import os, re, subprocess, sys, tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
THMS = ['NashWilliamsTheorem.nash_williams', 'NashWilliamsTheorem.fractional_nash_williams',
        'NashWilliamsTheorem.fractional_stability']
DEFS = ['NashWilliams.IsTriangle', 'NashWilliams.IsTriangleDecomposition',
        'NashWilliams.HasTriangleDecomposition', 'NashWilliams.IsTriangleDivisible',
        'NashWilliams.IsFractionalTriangleDecomposition',
        'NashWilliams.HasFractionalTriangleDecomposition', 'NashWilliams18.cutSize',
        'NashWilliams18.IsExtremal']
STD = '[propext, Classical.choice, Quot.sound]'
report, ok = [], True


def lean(text):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, 'Check.lean')
        open(p, 'w', encoding='utf-8', newline='\n').write(text)
        r = subprocess.run(['lake', 'env', 'lean', p], cwd=ROOT, capture_output=True, text=True,
                           encoding='utf-8', errors='replace')
        return r.returncode, r.stdout + r.stderr


def fail(msg):
    global ok
    ok = False
    report.append('FAIL ' + msg)


# 1. audit
audit = open(os.path.join(ROOT, 'tools', 'audit', 'AuditPaperIIAssembly.lean.in'), encoding='utf-8').read()
rc, out = lean(audit)
report.append('--- audit output ---\n' + out.strip())
if rc != 0 or 'PASS_PAPERII_PROOF_DEPENDENCIES' not in out:
    fail('audit did not pass')
for line in re.findall(r"depends on axioms: \[[^\]]*\]", out):
    if line != 'depends on axioms: ' + STD:
        fail('audit axioms: ' + line)
if len(re.findall(r'depends on axioms', out)) != 6:
    fail('audit: expected 6 axiom queries')

# 2. identity
def dump(mod):
    body = f'import {mod}\nset_option pp.all true\n'
    body += ''.join(f'#check @{t}\n' for t in THMS) + ''.join(f'#print {d}\n' for d in DEFS)
    rc, out = lean(body)
    out = re.sub(r'/--.*?-/', '', out, flags=re.S)
    return rc, [l.rstrip() for l in out.splitlines() if l.strip()]
rc1, a = dump('Challenge')
rc2, b = dump('Solution')
if rc1 or rc2 or any('error' in l for l in a + b):
    fail('identity dump had errors')
if a != b:
    fail('Challenge and Solution declarations differ')
    import difflib
    report.extend(list(difflib.unified_diff(a, b, lineterm=''))[:60])
else:
    report.append(f'TYPES AND DEFINITIONS IDENTICAL ({len(a)} lines)')

# 3. axioms
rc, out = lean('import Solution\n' + ''.join(f'#print axioms {t}\n' for t in THMS))
report.append('--- solution axioms ---\n' + out.strip())
axl = re.findall(r"depends on axioms: \[[^\]]*\]", re.sub(r'\s+', ' ', out))
if len(axl) != 3 or any(x != 'depends on axioms: ' + STD for x in axl):
    fail('solution axioms')

# 4. forbidden tokens outside comments
bad = []
for top in ('RequestProject', 'PartitionedTriangleAbsorption'):
    for dp, _, fs in os.walk(os.path.join(ROOT, top)):
        for f in fs:
            if f.endswith('.lean'):
                s = open(os.path.join(dp, f), encoding='utf-8').read()
                t = re.sub(r'/-.*?-/', '', s, flags=re.S)
                t = re.sub(r'--[^\n]*', '', t)
                if re.search(r'\b(sorry|admit|native_decide)\b', t) or re.search(r'^\s*axiom\s', t, re.M):
                    bad.append(os.path.join(top, f))
for f in ('Solution.lean',):
    if re.search(r'\bsorry\b', open(os.path.join(ROOT, f), encoding='utf-8').read()):
        bad.append(f)
if bad:
    fail('forbidden tokens in ' + ', '.join(bad[:10]))
else:
    report.append('no sorry/admit/native_decide/axiom in the library or Solution')

report.append('ALL CHECKS PASSED' if ok else 'CHECKS FAILED')
open(os.path.join(ROOT, 'tools', 'check_report.txt'), 'w', encoding='utf-8', newline='\n').write('\n'.join(report) + '\n')
print('\n'.join(report))
sys.exit(0 if ok else 1)
