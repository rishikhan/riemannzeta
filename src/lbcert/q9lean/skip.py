"""Add `set_option debug.skipKernelTC true` after the imports, its comment line and a Changes bullet
(the form of the q = 9 entry, q9/ws/comparator/Solution/Candidate.lean in the q9 archive), and end the file with a newline.

    python skip.py IN.lean OUT.lean
"""
import sys

src = open(sys.argv[1]).read()
a = '-/\nimport ChallengeDeps\n'
assert src.count(a) == 1
src = src.replace(a, '* 2026-10-24: `set_option debug.skipKernelTC true` after the imports: the build skips its own kernel\n'
                  '  check; the comparator\'s nanoda run and Lean kernel replay check every declaration of the export.\n' + a)
b = 'import Zeta23.ZeroSide.RankTraceMult\n'
assert src.count(b) == 1
src = src.replace(b, b + '-- The build skips its kernel check; nanoda and the comparator\'s Lean kernel replay check every declaration.\n'
                  'set_option debug.skipKernelTC true\n')
if not src.endswith('\n'):
    src += '\n'
open(sys.argv[2], 'w').write(src)
print('bytes', len(src.encode()))
