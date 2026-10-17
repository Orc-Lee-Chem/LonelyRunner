from pathlib import Path
import csv, hashlib
root=Path(__file__).resolve().parents[1]
with (root/'ReleaseSHA256.tsv').open(encoding='utf-8',newline='') as stream:
    rows=list(csv.DictReader(stream,delimiter='\t'))
for row in rows:
    path=root/row['RelativePath']
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual!=row['SHA256']:
        raise SystemExit('SHA256 mismatch: '+row['RelativePath'])
expected={r['RelativePath'] for r in rows}
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and '.git' not in p.relative_to(root).parts and '.lake' not in p.relative_to(root).parts and p.name!='ReleaseSHA256.tsv'}
if actual!=expected:
    raise SystemExit('File inventory mismatch; missing='+str(sorted(expected-actual))+'; extra='+str(sorted(actual-expected)))
print('Verified '+str(len(rows))+' release files (manifest excludes itself and Git internals).')
