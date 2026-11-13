"""Apply the edits that the q = 9 entry carries over gen9.py's output:
the pack namespace ZeroForgePack -> PackDec (ZeroForgePackedNat unchanged) and the 2026-10-24 Changes lines.

    python postfix.py IN.lean OUT.lean [--adjlam] [--sparse]

--adjlam: the Changes line says the adjacent-term λ values are stored (gen9 --opt adjlam).
--sparse: one more Changes line for the sparse leaf check (gen9 --opt sparse).
--ptn N: one more Changes line for the N-point table with per-point piece counts (gen9 --ptn).
--leaf2 OPTS: Changes lines for the q9leaf2 leaf-check levers (gen9 --opt leaf2=OPTS; y, p and b).
--ptb: one more Changes line for the balanced point tree (gen9 --opt ptb).
"""
import re
import sys

src = open(sys.argv[1]).read()
adjlam = '--adjlam' in sys.argv or '--sparse' in sys.argv
sparse = '--sparse' in sys.argv
ptn = int(sys.argv[sys.argv.index('--ptn') + 1]) if '--ptn' in sys.argv else 0
leaf2 = sys.argv[sys.argv.index('--leaf2') + 1] if '--leaf2' in sys.argv else ''
ptb = '--ptb' in sys.argv
src = re.sub(r'ZeroForgePack(?!edNat)', 'PackDec', src)
anchor = '  decoded at elaboration time into the same declarations.\n'
assert src.count(anchor) == 1
lam = ('every term\'s λ value is stored in the walk words.' if adjlam else
       'adjacent-term λ values are computed in the leaf check, not stored.')
src = src.replace(anchor, anchor + '* 2026-10-24: the walk words are written as one range-coded zfE payload (namespace PackDec), decoded at\n'
                  '  elaboration time into the WL constants; %s\n' % lam
                  + ('* 2026-10-24: sparse leaf check: a leaf lists only its nonzero terms (a presence mask, then each listed\n'
                     '  term\'s kind, anchors and λ) and folds them into running sums (mleafZ, tzG, zfin); its soundness\n'
                     '  (mleafZ_ok) goes through the fold invariant ZInv and the per-term bound of mtermTI.\n' if sparse else '')
                  + ('* 2026-10-24: tangent point table of {:,} points; each point\'s interval is cut to the hull of the ranges its\n'
                     '  leaves use, and each entry carries its own zside piece count n above bit 140 (payload zfPTTN). The table is\n'
                     '  checked by ptOkTN / ptTN_sound, which take ptlOkD / ptTD_sound\'s place.\n'.format(ptn) if ptn else '')
                  + ('* 2026-10-24: leaf check: a multiplier step reads its pair\'s bounds A_c, B_c and gap sum x_c from the state\n'
                     '  through a 36-way dispatch (ycs, yupdS2; equal to yupdS for c < 36), in place of sumR / List.getD on toCl s.\n'
                     if 'y' in leaf2 else '')
                  + ('* 2026-10-24: leaf check: the gaps\' slope sums are two packed naturals of 256-bit lanes (TZ = CVP, CN, VP,\n'
                     '  VN); a listed term adds to lanes i .. j - 1 with one multiplication by lmask i j and fails the leaf unless\n'
                     '  mw ≤ 2048 and sl ≤ 2^43, so no lane overflows; zchk reads the lanes. mleafZ_ok keeps its statement.\n'
                     if 'p' in leaf2 else '')
                  + ('* 2026-10-24: leaf check: tzv dispatches to one definition per term kind (tzk0 .. tzk4) and tzG\'s listed\n'
                     '  path is a definition of its own (tzL), so each step unfolds only the code it runs.\n' if 'b' in leaf2 else '')
                  + ('* 2026-10-24: the tangent point table is a balanced binary tree over the points (inductive PTB, payload\n'
                     '  zfPTB in the zfPTTN encoding); a leaf holds the looked-up word, and a point\'s check is unchanged (ptOkB /\n'
                     '  ptTB_sound in place of ptOkTN / ptTN_sound).\n' if ptb else ''))
assert 'addAndCompile (Declaration.defnDecl' in src and 'liftCoreM <| addDecl' not in src
if '--fixed' in sys.argv:
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'q9fixed'))
    import patch
    src = patch.apply(src)
open(sys.argv[2], 'w').write(src)
print('bytes', len(src.encode()))
