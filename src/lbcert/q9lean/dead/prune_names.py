"""Remove named declarations from a Solution.lean (names from prune.py's OUT.names).
A declaration is its head line `(def|theorem|lemma|abbrev) NAME` at column 0, with a preceding
`/-- ... -/` doc comment, up to the next line that starts at column 0 with anything but `|`.
    python prune_names.py IN.lean NAMES OUT.lean"""
import re
import sys


def prune(src, names):
    lines = src.split('\n')
    drop = [False] * len(lines)
    found = set()
    for k, ln in enumerate(lines):
        m = re.match(r'(?:private |protected |noncomputable |nonrec )*(def|theorem|lemma|abbrev)\s+(\S+)', ln)
        if not m or m.group(2) not in names:
            continue
        found.add(m.group(2))
        a = k
        while a > 0 and lines[a - 1] == '' and a - 2 >= 0 and lines[a - 2].rstrip().endswith('-/') and lines[a - 2].lstrip().startswith(('/--', '')):
            a -= 1
        if a > 0 and lines[a - 1].rstrip().endswith('-/') and not lines[a - 1].startswith('-/'):
            b = a - 1
            while b > 0 and not lines[b].startswith('/-') and lines[b] != '':
                b -= 1
            if lines[b].startswith('/--'):
                a = b
        e = k + 1
        while e < len(lines) and (lines[e] == '' or lines[e][0] in ' |'):
            e += 1
        while e > k + 1 and lines[e - 1] == '':
            e -= 1
        for t in range(a, e):
            drop[t] = True
    return '\n'.join(l for l, d in zip(lines, drop) if not d), names - found


if __name__ == '__main__':
    src = open(sys.argv[1]).read()
    names = set(x for x in open(sys.argv[2]).read().split() if x)
    out, missing = prune(src, names)
    open(sys.argv[3], 'w').write(out)
    print('removed', len(names) - len(missing), 'missing', sorted(missing), len(src.encode()), '->', len(out.encode()))
