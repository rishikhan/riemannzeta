"""Fixed-cost patch for the q = 9 Solution file (applied after q9lean/postfix.py).

    python patch.py IN.lean OUT.lean

Every edit is an exact text replacement that must match the stated number of times; the script fails
otherwise, so a changed generator output is noticed instead of patched wrongly. The edits change kernel
terms only where noted, never a statement that the leaves or the final assembly use.
"""
import os
import re
import sys

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
EDITS = []
FUNCS = []


def edit(old, new, count=1):
    EDITS.append((old, new, count))


# 1. Symbolic whnf traps. In proofs about a variable cell c, the kernel reduces stuck terms such as
#    `Nat.ble 65536 (Nat.add X 32768)` by peeling the literal one successor at a time (32,768 steps,
#    about 1.3 s per occurrence and declaration). With the literal as the first argument, Nat.add / Nat.mul
#    recurse on the symbolic argument and stop at once. Same values (GMP on literals).
edit('def k (c : CellA) : ℕ := Nat.div (Nat.add (Nat.mul 2 (Nat.add c.LN c.UN)) SC) (Nat.mul 2 SC)',
     'def k (c : CellA) : ℕ := Nat.div (Nat.add SC (Nat.mul 2 (Nat.add c.LN c.UN))) (Nat.mul 2 SC)')
edit('def side (c : CellA) : Bool := Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)',
     'def side (c : CellA) : Bool := Nat.ble (Nat.mul SC c.k) (Nat.mul 2 c.LN)')
edit('   && Bool.rec (motive := fun _ => Bool) (Nat.ble (Nat.mul 2 c.UN) (Nat.mul c.k SC)) (Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)) c.side',
     '   && Bool.rec (motive := fun _ => Bool) (Nat.ble (Nat.mul 2 c.UN) (Nat.mul SC c.k)) (Nat.ble (Nat.mul SC c.k) (Nat.mul 2 c.LN)) c.side')
edit('have : ((2 * c.UN : ℕ) : ℝ) ≤ ((c.k * SC : ℕ) : ℝ) := by exact_mod_cast hside',
     'have : ((2 * c.UN : ℕ) : ℝ) ≤ ((c.k * SC : ℕ) : ℝ) := by rw [Nat.mul_comm c.k SC]; exact_mod_cast hside', 2)
edit('have : ((c.k * SC : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by exact_mod_cast hside',
     'have : ((c.k * SC : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by rw [Nat.mul_comm c.k SC]; exact_mod_cast hside', 2)
edit('Nat.shiftRight (Nat.add p 16384) 15', 'Nat.shiftRight (Nat.add 16384 p) 15', 6)


# 2. Positive-variation check (pvCheck_AM, 15 s of kernel time in each of build, nanoda and replay). The sine
#    table becomes one packed natural (O(1) lookups instead of a list walk), and the j != 0 terms of the cell
#    sums are evaluated in Z (lean/pvz.lean); pvCheck2_eq proves the integer form equal to pvCheck, so the
#    statement of pvCheck_AM and everything that uses it are unchanged.
TAB_OLD_TI = ('def tabI (q : ℕ) : ℚ × ℚ :=\n'
              ' (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)\n')
TAB_W, TAB_B = 36, 1 << 35


def pack_table(src):
    m = re.search(r'^def sinTabZ : List \(ℤ × ℤ\) := \[(.*)\]\n', src, re.M)
    assert m and src.count('def sinTabZ') == 1 and src.count(TAB_OLD_TI) == 1
    ents = [(int(a), int(b)) for a, b in re.findall(r'\((-?\d+), (-?\d+)\)', m.group(1))]
    assert len(ents) == 257
    v = 0
    for q, (lo, hi) in enumerate(ents):
        assert -TAB_B < lo <= hi < TAB_B
        v |= (lo + TAB_B) << (2 * TAB_W * q) | (hi + TAB_B) << (2 * TAB_W * q + TAB_W)
    M = (1 << TAB_W) - 1
    new = ('/-- the 257 sine table entries (lo, hi) · 10¹⁰, packed: entry q at bits 72q (lo + 2³⁵) and 72q + 36 (hi + 2³⁵) -/\n'
           'def sinTabP : ℕ := %d\n'
           'def tabZ (q : ℕ) : ℤ × ℤ :=\n'
           ' (((Nat.land (Nat.shiftRight sinTabP (Nat.mul 72 q)) %d : ℕ) : ℤ) - %d,\n'
           '  ((Nat.land (Nat.shiftRight sinTabP (Nat.add (Nat.mul 72 q) 36)) %d : ℕ) : ℤ) - %d)\n'
           'def tabI (q : ℕ) : ℚ × ℚ :=\n'
           ' (((tabZ q).1 : ℚ) / 10000000000, ((tabZ q).2 : ℚ) / 10000000000)\n') % (v, M, TAB_B, M, TAB_B)
    return src[:m.start()] + new + src[m.end():].replace(TAB_OLD_TI, '', 1)


FUNCS.append(pack_table)
edit('set_option maxRecDepth 100000 in\ntheorem pvCheck_AM : pvCheck (1 / 25) = true := by decide +kernel\n',
     open(os.path.join(HERE, 'lean', 'pvz.lean')).read())


# 3. zfE decoder (elaboration only, about 21 s): faster primitives with the same names and results
#    (lean/zfe_prims.py); the format-specific `root` is unchanged.
sys.path.insert(0, os.path.join(HERE, 'lean'))
import zfe_prims  # noqa: E402
for _a, _b in zfe_prims.PAIRS:
    edit(_a, _b)


# 4. Elaboration only: nlinarith calls in deleted_strips and strips_le (about 7 s) replaced by the products they
#    search for, followed by linarith.
edit("""         exact mul_le_mul_of_nonneg_left this (by linarith)
       nlinarith""", """         exact mul_le_mul_of_nonneg_left this (by linarith)
       have h16 := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 1600 * A₀)
       linarith""")
edit("""       apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
       nlinarith""", """       apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
       have hπL := mul_le_mul_of_nonneg_left hL1 (by positivity : (0:ℝ) ≤ 2 * Real.pi)
       linarith""")
edit("""       have hL0 : 0 ≤ L := by linarith
       nlinarith""", """       have hL0 : 0 ≤ L := by linarith
       have := mul_le_mul_of_nonneg_right h2 hL0
       linarith""")
edit("""   have := mul_le_mul_of_nonneg_left hN hε.le
   nlinarith [hkey]""", """   have := mul_le_mul_of_nonneg_left hN hε.le
   linarith [hkey]""")
edit("""   rw [div_le_iff₀ hLpos]; nlinarith""", """   rw [div_le_iff₀ hLpos]
   have := mul_le_mul_of_nonneg_left (mul_le_mul hL1 hL1 zero_le_one hLpos.le) (by positivity : (0:ℝ) ≤ 2 * Real.pi)
   linarith""")
edit("""   rw [abs_of_pos (by linarith), hM]; nlinarith""", """   rw [abs_of_pos (by linarith), hM]
   have := mul_le_mul_of_nonneg_left hLT (by positivity : (0:ℝ) ≤ 2 * Real.pi)
   have := mul_nonneg hπ.le (by linarith : (0:ℝ) ≤ T)
   linarith""")
edit("""   rw [hM]; nlinarith""", """   rw [hM]
   have := mul_le_mul_of_nonneg_left hLT (by positivity : (0:ℝ) ≤ 8 * Real.pi)
   have := mul_nonneg hπ.le (by linarith : (0:ℝ) ≤ T)
   linarith""")
edit("""   have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
   nlinarith""", """   have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
   have := mul_le_mul_of_nonneg_left hL1 (by positivity : (0:ℝ) ≤ 10 * Real.pi)
   linarith""")
edit("""\n have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith""",
     """\n have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by linarith""")
edit("""\n have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith""",
     """\n have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by
   have := mul_le_mul hπ4.le hπ4.le hπ.le (by norm_num)
   linarith""")

CHANGES = """\
* 2026-10-24, fixed-cost changes: (a) CellA.k, CellA.side and CellA.ok put the literal operand of Nat.add and
  Nat.mul first, and treadU, treadD, treadUF, treadDF and tcheckZC write Nat.add 16384 p (same values); the four
  cast lines of base_sound and sep that read the side condition commute the product. The kernel then stops
  unfolding these literals one successor at a time when it reduces the terms for a symbolic cell. (b) pvCheck_AM
  is proved through pvCheck2 and pvCheck2_eq: the sine table is one packed natural (sinTabP, tabZ; tabI reads it),
  the j ≠ 0 terms of the cell sums are summed in ℤ (termZ, sumZ), and sinPiI2 skips the interval that sinPiI
  multiplies by a zero coefficient of csA. (c) The zfE decoder's primitives norm, tree, direct and put are
  written without loops; they return the same values.
"""


def add_changes(src):
    a = src.index('Changes (Apache-2.0 §4(b)), 2026-10-23, by Rishi Khan')
    b = src.index('\n-/\n', a) + 1
    return src[:b] + CHANGES + src[b:]


def apply(src):
    for f in FUNCS:
        src = f(src)
    src = add_changes(src)
    for old, new, n in EDITS:
        c = src.count(old)
        assert c == n, 'edit expected %d matches, found %d: %s' % (n, c, old[:80])
        src = src.replace(old, new)
    return src


if __name__ == '__main__':
    src = apply(open(sys.argv[1]).read())
    open(sys.argv[2], 'w').write(src)
    print('edits', len(EDITS), 'bytes', len(src.encode()))
