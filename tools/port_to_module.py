"""Port the Paper I tree to the Lean module system (required by Palomar).

usage (from the repository root):  python -I tools/port_to_module.py

For every project `.lean` file (RequestProject/, PartitionedTriangleAbsorption/,
PartitionedTriangleAbsorption.lean, Challenge.lean, Solution.lean):
  * insert `module` after the initial copyright comment;
  * turn every `import X` into `public import X`;
  * open `@[expose] public section` right after the import block, so that every declaration is
    public and every definition can be unfolded by importing modules, as before the port.
The proof-dependency audit `RequestProject/NW18/AuditPaperIIAssembly.lean` (a `run_cmd` script,
not imported by any other module) is moved to `tools/audit/AuditPaperIIAssembly.lean.in`; it is
run after the build by `tools/check_palomar.py`. `lakefile.toml` gets `requiresModuleSystem = true`.
Lean statements and proofs are not changed. The script is idempotent and writes
`tools/port_manifest.json` (per-file SHA-256 before and after).
"""
import hashlib, json, os, re, shutil, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..'))
AUDIT = os.path.join('RequestProject', 'NW18', 'AuditPaperIIAssembly.lean')
sha = lambda b: hashlib.sha256(b).hexdigest()


def project_files():
    out = []
    for top in ('RequestProject', 'PartitionedTriangleAbsorption'):
        for dp, _, fs in os.walk(os.path.join(ROOT, top)):
            out += [os.path.join(dp, f) for f in fs if f.endswith('.lean')]
    for f in ('PartitionedTriangleAbsorption.lean', 'Challenge.lean', 'Solution.lean'):
        if os.path.exists(os.path.join(ROOT, f)):
            out.append(os.path.join(ROOT, f))
    return sorted(out)


def port(text):
    if re.search(r'^module\s*$', text, re.M):
        return text  # already ported
    lines = text.split('\n')
    i = 0
    # skip the initial copyright comment `/- ... -/` (not a `/-!` docstring)
    if lines and lines[0].startswith('/-') and not lines[0].startswith('/-!'):
        while not lines[i].rstrip().endswith('-/'):
            i += 1
        i += 1
    head, rest = lines[:i], lines[i:]
    # the import block: blank lines and import lines from the start of `rest`
    j = 0
    while j < len(rest) and (rest[j].strip() == '' or rest[j].startswith('import ')):
        j += 1
    imports = [l for l in rest[:j] if l.startswith('import ')]
    body = rest[j:]
    new_imports = ['public ' + l for l in imports]
    out = head + ['module', ''] + new_imports + ['', '@[expose] public section', ''] + body
    return '\n'.join(out)


def main():
    manifest = {}
    audit_src = os.path.join(ROOT, AUDIT)
    if os.path.exists(audit_src):
        dst = os.path.join(ROOT, 'tools', 'audit', 'AuditPaperIIAssembly.lean.in')
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.move(audit_src, dst)
        manifest[AUDIT.replace(os.sep, '/')] = {'moved_to': 'tools/audit/AuditPaperIIAssembly.lean.in'}
    for p in project_files():
        raw = open(p, 'rb').read()
        text = raw.decode('utf-8')
        new = port(text)
        rel = os.path.relpath(p, ROOT).replace(os.sep, '/')
        if new != text:
            open(p, 'w', encoding='utf-8', newline='\n').write(new)
        manifest[rel] = {'before': sha(raw), 'after': sha(new.encode('utf-8'))}
    lf = os.path.join(ROOT, 'lakefile.toml')
    s = open(lf, encoding='utf-8').read()
    if 'requiresModuleSystem' not in s:
        s = s.replace('defaultTargets =', 'requiresModuleSystem = true\ndefaultTargets =', 1)
        open(lf, 'w', encoding='utf-8', newline='\n').write(s)
    json.dump(manifest, open(os.path.join(ROOT, 'tools', 'port_manifest.json'), 'w', encoding='utf-8'),
              indent=1, sort_keys=True)
    n = sum(1 for v in manifest.values() if 'before' in v)
    print(f'ported {n} files; audit moved: {AUDIT.replace(os.sep, "/") in manifest}')


if __name__ == '__main__':
    sys.exit(main())
