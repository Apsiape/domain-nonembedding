from pathlib import Path
import os
r=Path('/opt/domain-nonembedding-lean/project/.lake/packages').resolve()
assert str(r)=='/opt/domain-nonembedding-lean/project/.lake/packages'
count=0
for directory,subdirs,files in os.walk(r):
    for name in files:
        p=Path(directory)/name
        if p.is_symlink(): continue
        try:
            with p.open('rb') as f:os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
            count+=1
        except OSError:pass
print(f'Released file-cache hints for {count} own copied dependency files; no file contents changed.')
