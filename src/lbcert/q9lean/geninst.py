"""Emit the Q-gap instance module (namespace AMW.Cert.PC9XA) of the attempt-031 checker.

The text follows the unrolled instance layer of attempt-031 / v3 (bridge-port's genpcell4
layout): a cell is a curried state of 2Q + 2 NP + 1 naturals (gap bounds l_r u_r, pair bounds
A_ij B_ij, unused M), and cuH, colK*, rowK*, splG, qs_*, tm, yupdS, mcheckP, mleafP/V are the
unrolled forms of the generic PCell definitions.  For Q = 8 and v3's data `emit(spec)`
reproduces v3's module byte for byte (t_geninst.py).

spec fields: Q, PR, TS (i, j, a, k), BS, SL, BND, cN, SIG, SA, ADJ, plus options
  wmask_bits (walk word mask), half (attempt-032's half-space multiplier row c = NP),
  pb (pair-index bits of a multiplier record; default 5 as in attempt-031),
  sparse (the sparse leaf check of src/lbcert/q9sparse in place of mcheckP / mleafP).
  leaf2=OPTS (with sparse: the leaf check of src/lbcert/q9leaf2/zlean2.py with levers OPTS, e.g. yp).
"""
import os
import sys

KK = 'Bool.rec (motive := fun _ => ℕ)'


def names(n):
    """Binder names of the curried state: a..z, A..Z, aa.. (skipping k p q, keywords)."""
    one = [c for c in 'abcdefghijlmnorstuvwxyz'] + [c for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ']
    two = []
    for f in 'abcdefgh':
        for s in 'abcdefghijlmnoruvwxyz':
            if f + s in ('by', 'do', 'if', 'in', 'fi'):
                continue
            two.append(f + s)
    out = (one + two)[:n]
    assert len(out) == n
    return out


class Inst:
    def __init__(self, spec):
        self.sp = spec
        Q = self.Q = spec['Q']
        self.PR = [tuple(p) for p in spec['PR']]
        self.NP = len(self.PR)
        self.TS = [tuple(t) for t in spec['TS']]
        self.NT = len(self.TS)
        # state fields
        f = []
        for r in range(Q):
            f += ['l%d' % r, 'u%d' % r]
        for (i, j) in self.PR:
            f += ['A%d%d' % (i, j), 'B%d%d' % (i, j)]
        f.append('M')
        self.F = f
        self.NF = len(f)
        self.V = names(self.NF)          # positional binder names
        self.pos = {x: k for k, x in enumerate(f)}
        self.pk = {p: k for k, p in enumerate(self.PR)}
        self.TB = 8796093022208
        self.BB = 4398046511104
        self.tag = ['%d%d' % (t[0], t[1]) for t in self.TS]

    # ------------------------------------------------------------------ helpers
    def lo(self, a, b, v=None):
        """binder (or field) name of the lower bound of slot (a, b), a < b"""
        x = ('l%d' % a) if b == a + 1 else ('A%d%d' % (a, b))
        return v[self.pos[x]] if v else x

    def hi(self, a, b, v=None):
        x = ('u%d' % a) if b == a + 1 else ('B%d%d' % (a, b))
        return v[self.pos[x]] if v else x

    def args(self, v=None):
        return ' '.join(v or self.V)

    def sfields(self, pre='s.'):
        return ' '.join(pre + x for x in self.F)

    def nest_add(self, xs):
        """left-nested Nat.add of a non-empty list"""
        e = xs[0]
        for x in xs[1:]:
            e = '(Nat.add %s %s)' % (e, x)
        return e

    def nest_add0(self, xs):
        e = '0'
        for x in xs:
            e = '(Nat.add %s %s)' % (e, x)
        return e

    def sumL(self, i, j, pre='s.l'):
        if self.sp.get('helpers') and j >= i + 2 and pre in ('s.l', 's.u'):
            return '(%s%d%d s)' % ('x' if pre == 's.l' else 'y', i, j)
        e = pre + str(i)
        for r in range(i + 1, j):
            e = '(Nat.add %s %s%d)' % (e, pre, r)
        return e

    def eL(self, t):
        i, j = t[0], t[1]
        if j == i + 1:
            return 's.l%d' % i
        if self.sp.get('helpers'):
            return '(e%d%d s)' % (i, j)
        return '(nmax s.A%d%d %s)' % (i, j, self.sumL(i, j))

    def eU(self, t):
        i, j = t[0], t[1]
        if j == i + 1:
            return 's.u%d' % i
        if self.sp.get('helpers'):
            return '(f%d%d s)' % (i, j)
        return '(nmin s.B%d%d %s)' % (i, j, self.sumL(i, j, 's.u'))

    def tvars(self, t):
        g = '%d%d' % (t[0], t[1])
        return ['k' + g, 'm' + g, 'p' + g, 'r' + g]

    def kmpr(self):
        return ' '.join(' '.join(self.tvars(t)) for t in self.TS)

    def ylist(self, pre='y.'):
        Q = self.Q
        return '[%s] [%s] %sCp %sCm' % (', '.join('%sP%d' % (pre, r) for r in range(Q)),
                                        ', '.join('%sS%d' % (pre, r) for r in range(Q)), pre, pre)

    # ------------------------------------------------------------------ head
    def head(self):
        sp, Q = self.sp, self.Q
        L = []
        L.append('def cN : ℕ := %d' % sp['cN'])
        L.append('def SIG : ℕ := %d' % sp['SIG'])
        L.append('def PR : List (ℕ × ℕ) := [%s]' % ', '.join('(%d, %d)' % p for p in self.PR))
        L.append('theorem hPR : PRok %d PR := by decide' % Q)
        L.append('def BS : List ℕ := [%s]' % ', '.join(str(b) for b in sp['BS']))
        L.append('def TS : List Term := [%s]' % ', '.join('(%d, %d, %d, %d)' % t for t in self.TS))
        L.append('theorem hTS : TSok %d PR TS := by decide' % Q)
        L.append('def SL : List ℕ := [%s]' % ', '.join(str(x) for x in sp['SL']))
        L.append('theorem hSL : SLok %d PR SL := by decide' % Q)
        L.append('def BND : List ℕ := [%s]' % ', '.join(str(x) for x in sp['BND']))
        L.append('def fracQ (lo hi md : ℕ) : ℕ :=')
        L.append('  Nat.add lo (Nat.shiftRight (Nat.mul (Nat.sub hi lo) (%s md (Nat.sub md 1) (Nat.ble md 4))) 3)' % KK)
        L.append('def SA : ℕ := %d' % sp['SA'])
        g = ' '.join('g%d' % r for r in range(Q))
        L.append('def G (%s : ℝ) : ℝ :=' % g)
        L.append('  ' + ' + '.join('(%d / (SA:ℝ)) * g%d' % (sp['BS'][r], r) for r in range(Q)))
        aw = {(t[0], t[1]): t[2] for t in self.TS}
        terms = []
        for i in range(Q + 1):
            for j in range(i + 1, Q + 1):
                terms.append('(%d / (SA:ℝ)) * wfun (%s)' % (aw.get((i, j), 0), ' + '.join('g%d' % r for r in range(i, j))))
        L.append('    + ' + ' + '.join(terms))
        x = ' '.join('x%d' % r for r in range(Q))
        L.append('theorem Fg_G (%s : ℝ) : Fg %d BS TS (fun r => [%s].getD r 0) = (SA : ℝ) * G %s := by'
                 % (x, Q, ', '.join('x%d' % r for r in range(Q)), x))
        L.append('  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]')
        L.append('  ring')
        L.append('abbrev Covered : Cl → Prop := CovBy %d PR (Pg cN %d BS TS)' % (Q, Q))
        L.append('structure St where')
        L.append('  (%s : ℕ)' % ' '.join(self.F))
        L.append('def toCl (s : St) : Cl :=')
        L.append('  ⟨[%s], [%s],' % (', '.join('s.l%d' % r for r in range(Q)), ', '.join('s.u%d' % r for r in range(Q))))
        L.append('   [%s], [%s]⟩' % (', '.join('s.A%d%d' % p for p in self.PR), ', '.join('s.B%d%d' % p for p in self.PR)))
        L.append('def ofCl (c : Cl) (m : ℕ) : St :=')
        it = []
        for r in range(Q):
            it += ['c.L.getD %d 0' % r, 'c.U.getD %d 0' % r]
        for k in range(self.NP):
            it += ['c.A.getD %d 0' % k, 'c.B.getD %d 0' % k]
        it.append('m')
        L.append('  ⟨%s⟩' % ', '.join(it))
        L.append('theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = %d) (h2 : c.U.length = %d) (h3 : c.A.length = %d) (h4 : c.B.length = %d) :'
                 % (Q, Q, self.NP, self.NP))
        L.append('    toCl (ofCl c m) = c := by')
        L.append('  obtain ⟨L, U, A, B⟩ := c')
        L.append('  show Cl.mk _ _ _ _ = _')
        L.append('  congr 1')
        L.append('  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]')
        if self.sp.get('helpers'):
            L += self.helper_defs()
        if self.sp.get('kfmt') and not self.sp.get('adjlam'):
            L += LAMDEFS.split('\n')
        L.append('abbrev ST : Type := %s' % ' → '.join(['ℕ'] * (self.NF + 1)))
        L.append('def U (k : ST) (s : St) : ℕ := k %s' % self.sfields())
        L.append('def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)')
        L.append('abbrev WF : Type := ℕ → ST')
        L.append('def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)')
        L.append('def zK : ST := fun %s => 0' % ' '.join(['_'] * self.NF))
        L.append('theorem zK_ok : CovK zK := fun _ h => absurd rfl h')
        L.append('theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = %d) (h2 : c.U.length = %d) (h3 : c.A.length = %d)'
                 % (Q, Q, self.NP))
        L.append('    (h4 : c.B.length = %d) (h : U k (ofCl c m) ≠ 0) : Covered c :=' % self.NP)
        L.append('  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h')
        return L

    # ------------------------------------------------------------------ closure split
    def slots(self):
        """slot order of the state: gaps (r, r+1) then PR pairs"""
        return [(r, r + 1) for r in range(self.Q)] + self.PR

    def split(self):
        Q, V, TB, BB = self.Q, self.V, self.TB, self.BB
        L = []
        xs = ' '.join('x%d' % x for x in range(Q + 1))
        ys = ' '.join('y%d' % x for x in range(Q + 1))
        L.append('def cuH (k : ST) (%s %s %s : ℕ) : ℕ :=' % (xs, ys, self.args()))
        body = []
        for (a, b) in self.slots():
            body.append('(nmax %s (Nat.sub %d (Nat.add x%d y%d)))' % (self.lo(a, b, V), TB, b, a))
            body.append('(nmin %s (Nat.sub (Nat.add x%d y%d) %d))' % (self.hi(a, b, V), a, b, TB))
        body.append(V[-1])
        L.append('  k ' + body[0])
        for x in body[1:]:
            L.append('    ' + x)
        L.append('def cuL (k : ST) (X Y : List ℕ) (s : St) : ℕ :=')
        L.append('  cuH k %s %s' % (' '.join('(X.getD %d 0)' % x for x in range(Q + 1)), ' '.join('(Y.getD %d 0)' % x for x in range(Q + 1))))
        L.append('    ' + self.sfields())
        L.append('theorem cuL_eq (k : ST) (X Y : List ℕ) (s : St) : cuL k X Y s = U k (ofCl (cuB %d PR (toCl s) X Y) s.M) := by' % Q)
        L.append('  simp only [cuL, U, ofCl, cuB, toCl, PR, List.length_cons, List.length_nil, List.range_succ, List.range_zero,')
        L.append('    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, pI, pJ]')
        L.append('  rfl')
        L.append('theorem cuH_ok {k : ST} (hk : CovK k) (X Y : List ℕ) (s : St) (h : cuL k X Y s ≠ 0) :')
        L.append('    Covered (cuB %d PR (toCl s) X Y) :=' % Q)
        L.append('  ofCl_ok hk (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR]) (by simp [cuB, PR]) (m := s.M) (by rw [← cuL_eq]; exact h)')
        c1 = 'cuL (ih pos) (colB %d SL (toCl s) i) (rowB %d SL (toCl s) (Nat.add BB q) j) s' % (Q, Q)
        L.append('theorem spH_ok {ih : WF} (hih : WalkOK ih) {pos : ℕ} (i j : ℕ) (hij : i < j) (hj : j ≤ %d) {s : St} {q : ℕ}' % Q)
        L.append('    (h : %s' % KK)
        L.append('      (cuL (ih (%s)) (colB %d SL (toCl s) j) (rowB %d SL (toCl s) (Nat.sub BB q) i) s) 0' % (c1, Q, Q))
        L.append('      (Nat.beq (%s) 0) ≠ 0) : Covered (toCl s) := by' % c1)
        L.append('  have hc := cov_splitB (P := Pg cN %d BS TS) (c := toCl s) hSL hPR hij hj q' % Q)
        L.append('  cases hp : Nat.beq (%s) 0' % c1)
        L.append('  · rw [hp] at h')
        L.append('    exact hc (cuH_ok (hih _) _ _ s fun h0 => by rw [h0] at hp; exact absurd hp (by decide)) (cuH_ok (hih _) _ _ s h)')
        L.append('  · rw [hp] at h; exact absurd rfl h')
        kt = '(kk : %s)' % ' → '.join(['ℕ'] * (Q + 2))
        for s in range(Q + 1):
            L.append('def colK%d %s (%s : ℕ) : ℕ :=' % (s, kt, self.args()))
            it = []
            for x in range(Q + 1):
                if x < s:
                    it.append('(Nat.add qb %s)' % self.hi(x, s, V))
                elif x == s:
                    it.append('qb')
                else:
                    it.append('(Nat.sub qb %s)' % self.lo(s, x, V))
            L.append('  let qb := %d; kk %s' % (BB, ' '.join(it)))
        for t in range(Q + 1):
            L.append('def rowK%d (ee : ℕ) %s (%s : ℕ) : ℕ :=' % (t, kt, self.args()))
            it = []
            for x in range(Q + 1):
                if x < t:
                    it.append('(Nat.sub ee %s)' % self.lo(x, t, V))
                elif x == t:
                    it.append('ee')
                else:
                    it.append('(Nat.add ee %s)' % self.hi(t, x, V))
            L.append('  kk %s' % ' '.join(it))
        ft = '(%s)' % ' → '.join(['ℕ'] * (Q + 2))
        A = self.args()
        L.append('def splG (ih : WF) (pos : ℕ) (qs : ST) (cA : %s → ST) (rA : ℕ → %s → ST) (cB : %s → ST)' % (ft, ft, ft))
        L.append('    (rB : ℕ → %s → ST) : ST := fun %s =>' % (ft, A))
        L.append('  let q := qs %s; let qe := Nat.add %d q; let qf := Nat.sub %d q;' % (A, BB, BB))
        L.append('  let pp := cA (fun %s => rA qe (fun %s => cuH (ih pos) %s %s %s) %s) %s'
                 % (xs, ys, xs, ys, A, A, A))
        L.append('  %s (cB (fun %s => rB qf (fun %s => cuH (ih pp) %s %s %s) %s) %s) 0 (Nat.beq pp 0)'
                 % (KK, xs, ys, xs, ys, A, A, A))
        if self.sp.get('gsplit'):
            return L + self.split_generic(A)
        oks = []
        for ax, (a, b) in enumerate(self.slots()):
            nm = ('gsplit%d' % a) if b == a + 1 else ('ssplit%d%d' % (a, b))
            lo, hi = self.lo(a, b, V), self.hi(a, b, V)
            L.append('def qs_%s (md %s : ℕ) : ℕ := %s (%s (Nat.shiftRight (Nat.add %s %s) 1) (bcutL BND 64 %s %s) (Nat.beq md 1)) (fracQ %s %s md) (Nat.ble 2 md)'
                     % (nm, A, KK, KK, lo, hi, lo, hi, lo, hi))
            L.append('def %s (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_%s md) colK%d rowK%d colK%d rowK%d' % (nm, nm, a, b, b, a))
            oks.append((nm, a, b))
        L.append('section')
        L.append('variable {ih : WF} (hih : WalkOK ih) (md pos : ℕ)')
        L.append('include hih')
        for (nm, a, b) in oks:
            L.append('theorem %s_ok : CovK (%s ih md pos) := fun s h => spH_ok hih %d %d (by decide) (by decide) (s := s) h' % (nm, nm, a, b))
        L.append('end')
        n = len(oks)
        e = '(zK)'
        for ax in range(n - 1, -1, -1):
            e = '(motive := fun _ => ST) %s (%s ih md pos) (Nat.beq ax %d)' % (e, oks[ax][0], ax)
            e = '(Bool.rec ' + e + ')'
        L.append('def splitAx (ih : WF) (md pos ax : ℕ) : ST :=')
        L.append('  ' + e[1:-1])
        e = '(fun _ => zK_ok)'
        for ax in range(n - 1, -1, -1):
            e = '(fun _ => brec_dep %s (fun _ => %s_ok hih md pos))' % (e, oks[ax][0])
        L.append('theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=')
        L.append('  ' + e[len('(fun _ => '):-1])
        return L

    def split_generic(self, A):
        """One split definition for every axis: the cut is read from the state by slot index,
        the column / row builders are chosen by endpoint (colD, rowD); soundness by cases on
        the endpoints (spD_ok)."""
        Q, V = self.Q, self.V
        n = len(self.slots())
        kt = '(%s)' % ' → '.join(['ℕ'] * (Q + 2))
        L = []
        slt = 'S' in str(self.sp.get('leaf2', ''))     # q9leaf2: slot pair and col/row dispatch by balanced trees
        if not slt:
            L.append('def SLOTS : List (ℕ × ℕ) := [%s]' % ', '.join('(%d, %d)' % p for p in self.slots()))
        else:
            sl = self.slots()

            def stree(lo, hi, f):
                if hi - lo == 1:
                    return str(sl[lo][f])
                mid = (lo + hi) // 2
                return '(Bool.rec (motive := fun _ => ℕ) %s %s (Nat.blt ax %d))' % (stree(mid, hi, f), stree(lo, mid, f), mid)
            L.append('def slI (ax : ℕ) : ℕ := %s' % stree(0, n, 0))
            L.append('def slJ (ax : ℕ) : ℕ := %s' % stree(0, n, 1))

        def disp(nm, pre, arg):
            if slt:
                def tr(lo, hi):
                    if hi - lo == 1:
                        return '%s%d' % (pre, lo)
                    mid = (lo + hi) // 2
                    return '(Bool.rec (motive := fun _ => %s) %s %s (Nat.blt i %d))' % (arg, tr(mid, hi), tr(lo, mid), mid)
                return 'def %s (i : ℕ) : %s := %s' % (nm, arg, tr(0, Q + 1))
            e = '%s%d' % (pre, Q)
            for i in range(Q - 1, -1, -1):
                e = 'Bool.rec (motive := fun _ => %s) (%s) %s%d (Nat.beq i %d)' % (arg, e, pre, i, i)
            return 'def %s (i : ℕ) : %s := %s' % (nm, arg, e)
        L.append(disp('colD', 'colK', '%s → ST' % kt))
        L.append(disp('rowD', 'rowK', 'ℕ → %s → ST' % kt))
        assert 'k' not in V and 'md' not in V and 'lo' not in V and 'hi' not in V
        L.append('def qsAx (md k : ℕ) : ST := fun %s =>' % A)
        cut = '%s (%s (Nat.shiftRight (Nat.add %%s %%s) 1) (bcutL BND 64 %%s %%s) (Nat.beq md 1)) (fracQ %%s %%s md) (Nat.ble 2 md)' % (KK, KK)
        L.append('  ' + self.seltree(0, n, lambda ax: 'cutQ md %s %s' % (V[2 * ax], V[2 * ax + 1])))
        L.insert(-2, 'def cutQ (md lo hi : ℕ) : ℕ := ' + cut % ('lo', 'hi', 'lo', 'hi', 'lo', 'hi'))
        L.append('def splitAx (ih : WF) (md pos ax : ℕ) : ST :=')
        L.append('  forceT (slI ax) fun i => forceT (slJ ax) fun j =>' if slt else
                 '  forceT (SLOTS.getD ax (0, 0)).1 fun i => forceT (SLOTS.getD ax (0, 0)).2 fun j =>')
        L.append('  Bool.rec (motive := fun _ => ST) zK (splG ih pos (qsAx md ax) (colD i) (rowD j) (colD j) (rowD i)) (Nat.blt ax %d)' % n)
        L.append('theorem spD_ok {ih : WF} (hih : WalkOK ih) {pos : ℕ} {qs : ST} (i j : ℕ) (hij : i < j) (hj : j ≤ %d) :' % Q)
        L.append('    CovK (splG ih pos qs (colD i) (rowD j) (colD j) (rowD i)) := by')
        L.append('  intro s h')
        L.append('  interval_cases j <;> interval_cases i <;> exact spH_ok hih _ _ hij hj h')
        if slt:
            L.append('theorem hSLOTS : ∀ ax < %d, slI ax < slJ ax ∧ slJ ax ≤ %d := by decide' % (n, Q))
        else:
            L.append('theorem hSLOTS : ∀ ax < %d, (SLOTS.getD ax (0, 0)).1 < (SLOTS.getD ax (0, 0)).2 ∧ (SLOTS.getD ax (0, 0)).2 ≤ %d := by decide' % (n, Q))
        L.append('theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) := by')
        L.append('  unfold splitAx')
        L.append('  simp only [forceT_eq]')
        L.append('  cases hb : Nat.blt ax %d' % n)
        L.append('  · exact zK_ok')
        L.append('  · exact spD_ok hih _ _ (hSLOTS ax (Nat.blt_eq.mp hb)).1 (hSLOTS ax (Nat.blt_eq.mp hb)).2')
        return L

    def seltree(self, lo, hi, f):
        """balanced Bool.rec tree over k in [lo, hi) with leaf text f(k) : ℕ"""
        if hi - lo == 1:
            return f(lo)
        mid = (lo + hi) // 2
        return 'Bool.rec (motive := fun _ => ℕ) (%s) (%s) (Nat.blt k %d)' % (self.seltree(mid, hi, f), self.seltree(lo, mid, f), mid)

    # ------------------------------------------------------------------ tm
    def tmatc(self):
        Q, V = self.Q, self.V
        L = []
        L.append('def tm (k : ST) (%s : ℕ) : ℕ :=' % self.args())
        out = list(V)
        for (i, j) in self.PR:
            a, b = self.lo(i, j, V), self.hi(i, j, V)
            sl = self.nest_add([self.lo(r, r + 1, V) for r in range(i, j)])
            su = self.nest_add([self.hi(r, r + 1, V) for r in range(i, j)])
            L.append('  forceR (nmax %s %s) fun %s\' => forceR (nmin %s %s) fun %s\' =>' % (a, sl, a, b, su, b))
            out[self.pos['A%d%d' % (i, j)]] = a + "'"
            out[self.pos['B%d%d' % (i, j)]] = b + "'"
        L.append('  k ' + ' '.join(out))
        L.append('theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by')
        L.append('  have h\' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h')
        L.append('  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h\' g')
        L.append('    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2')
        return L

    # ------------------------------------------------------------------ multipliers
    def ya(self, o='o\'', pmod=None, smod=None, cp=None, cm=None):
        Q = self.Q
        P = ['y.P%d' % r for r in range(Q)]
        S = ['y.S%d' % r for r in range(Q)]
        if pmod:
            for r, e in pmod.items():
                P[r] = e
        if smod:
            for r, e in smod.items():
                S[r] = e
        return '⟨%s, %s, %s, %s, %s⟩' % (o, ', '.join(P), ', '.join(S), cp or 'y.Cp', cm or 'y.Cm')

    def yleaf(self, c):
        i, j = self.PR[c]
        sl = self.sumL(i, j)
        pm = {r: '(Nat.add y.P%d (Nat.mul Ylo 1))' % r for r in range(i, j)}
        sm = {r: '(Nat.add y.S%d (Nat.mul Yhi 1))' % r for r in range(i, j)}
        cp = '(Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub %s s.A%d%d))) (Nat.mul Yhi (Nat.sub s.B%d%d %s)))' % (sl, i, j, i, j, sl)
        cm = '(Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub s.A%d%d %s))) (Nat.mul Yhi (Nat.sub %s s.B%d%d)))' % (i, j, sl, sl, i, j)
        return self.ya(pmod=pm, smod=sm, cp=cp, cm=cm)

    def ytree(self, lo, hi):
        if hi - lo == 1:
            return self.yleaf(lo)
        mid = (lo + hi) // 2
        return '(Bool.rec (motive := fun _ => YA) %s %s (Nat.blt c %d))' % (self.ytree(mid, hi), self.ytree(lo, mid), mid)

    def yproof(self, lo, hi, ind, MO):
        if hi - lo == 1:
            return ['%s(fun _ => mul_step%s (k := %d) hPR rfl rfl h (by decide) Ylo Yhi)' % (' ' * ind, MO[1], lo)]
        mid = (lo + hi) // 2
        a = self.yproof(mid, hi, ind + 2, MO)
        b = self.yproof(lo, mid, ind + 2, MO)
        b[-1] += ')'
        return ['%s(fun _ => brec_dep (P := %s s)' % (' ' * ind, MO[0])] + a + b

    def mult(self):
        Q, NP = self.Q, self.NP
        half = self.sp.get('half', False)
        pb = self.sp.get('pb', 5)
        L = []
        L.append('structure YA where')
        L.append('  (o %s %s Cp Cm : ℕ)' % (' '.join('P%d' % r for r in range(Q)), ' '.join('S%d' % r for r in range(Q))))
        if half:
            if self.sp.get('yrow'):
                L += self.yrow_def()
            else:
                L.append('def yupdS (c : ℕ) (s : St) (Ylo Yhi : ℕ) (y : YA) (o\' : ℕ) : YA :=')
                L.append('  ' + self.ytree(0, NP))
            return L + self.mult_half(*self.yconsts(pb))
        L.append('def MulOK (s : St) (y : YA) : Prop :=')
        L.append('  MulOKg %d PR (toCl s) %s' % (Q, self.ylist()))
        z = '⟨o, %s⟩' % ', '.join(['0'] * (2 * Q + 2))
        L.append('theorem MulOK_zero (s : St) (o : ℕ) : MulOK s %s := fun _ _ => by simp' % z)
        L.append('def yupdS (c : ℕ) (s : St) (Ylo Yhi : ℕ) (y : YA) (o\' : ℕ) : YA :=')
        L.append('  ' + self.ytree(0, NP))
        yo, ye, mask, pb = self.yconsts(pb)
        L.append('def ystepS (s : St) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=')
        L.append('  forceT y.o fun o => Bool.rec (motive := fun _ => YA) %s' % yo)
        L.append('    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) %d) fun c => forceT (Nat.add o %d) fun o1 =>' % (mask, pb + 1))
        L.append('     Bool.rec (motive := fun _ => YA) %s' % ye)
        L.append('      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>')
        L.append('       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>')
        L.append('       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>')
        L.append('       ih (yupdS c s Ylo Yhi y (Nat.add o1 (Nat.add qb 1))))')
        L.append('      (Nat.blt c %d))' % NP)
        L.append('    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)')
        L.append('def ydecS (s : St) (qb w fuel : ℕ) : YA → YA :=')
        L.append('  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystepS s qb w ih) fuel')
        L.append('theorem yupdS_ok (s : St) (y : YA) (h : MulOK s y) (c : ℕ) (Ylo Yhi o\' : ℕ) :')
        L.append('    MulOK s (yupdS c s Ylo Yhi y o\') := by')
        L.append('  unfold yupdS')
        mid = NP // 2
        a = self.yproof(mid, NP, 4, ('MulOK', ''))
        b = self.yproof(0, mid, 4, ('MulOK', ''))
        L.append('  exact brec_dep (P := MulOK s)')
        L += a + b
        L.append('theorem ystepS_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :')
        L.append('    MulOK s (ystepS s qb w ih y) := by')
        L.append('  unfold ystepS')
        L.append('  simp only [forceT_eq]')
        L.append('  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (yupdS_ok s y h _ _ _ _)')
        L.append('theorem ydecS_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydecS s qb w fuel y)')
        L.append('  | 0, _, h => h')
        L.append('  | n + 1, y, h => ystepS_ok s qb w (ydecS_ok s qb w n) y h')
        return L

    def yconsts(self, pb):
        Q = self.Q
        rest = ', '.join(['y.P%d' % r for r in range(Q)] + ['y.S%d' % r for r in range(Q)] + ['y.Cp', 'y.Cm'])
        return '⟨(Nat.add o 1), %s⟩' % rest, '⟨(Nat.add o1 (Nat.add qb 1)), %s⟩' % rest, (1 << pb) - 1, pb

    def yrow_def(self):
        """yupdS for every pair at once: the record of mul_stepH, read through pI / pJ / getD."""
        Q = self.Q
        ij = '(pI PR c) (pJ PR c)'
        sl = '(sumR (toCl s).L (pI PR c) (pJ PR c - pI PR c))'
        a, b = '((toCl s).A.getD c 0)', '((toCl s).B.getD c 0)'
        P = ['(Nat.add y.P%d (Nat.mul Ylo (ind (inr %d %s))))' % (r, r, ij) for r in range(Q)]
        S = ['(Nat.add y.S%d (Nat.mul Yhi (ind (inr %d %s))))' % (r, r, ij) for r in range(Q)]
        cp = '(Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub %s %s))) (Nat.mul Yhi (Nat.sub %s %s)))' % (sl, a, b, sl)
        cm = '(Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub %s %s))) (Nat.mul Yhi (Nat.sub %s %s)))' % (a, sl, sl, b)
        return ['def yupdS (c : ℕ) (s : St) (Ylo Yhi : ℕ) (y : YA) (o\' : ℕ) : YA :=',
                '  ⟨o\', %s, %s, %s, %s⟩' % (', '.join(P), ', '.join(S), cp, cm)]

    def mult_half(self, yo, ye, mask, pb):
        """attempt-032's PCellHalf instance part (am-cert), generated for Q gaps"""
        Q, NP = self.Q, self.NP
        L = []
        L.append('def MulOKH (s : St) (y : YA) : Prop :=')
        L.append('  MulOKgH %d PR (toCl s) %s' % (Q, self.ylist()))
        cp = '(Nat.add y.Cp (Nat.mul Y (Nat.sub s.l%d s.l0)))' % (Q - 1)
        cm = '(Nat.add y.Cm (Nat.mul Y (Nat.sub s.l0 s.l%d)))' % (Q - 1)
        L.append('def yhalf (s : St) (Y : ℕ) (y : YA) (o\' : ℕ) : YA :=')
        L.append('  ' + self.ya(pmod={Q - 1: '(Nat.add y.P%d (Nat.mul Y 1))' % (Q - 1)}, smod={0: '(Nat.add y.S0 (Nat.mul Y 1))'}, cp=cp, cm=cm))
        L.append('def ystepH (s : St) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=')
        L.append('  forceT y.o fun o => Bool.rec (motive := fun _ => YA) %s' % yo)
        L.append('    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) %d) fun c => forceT (Nat.add o %d) fun o1 =>' % (mask, pb + 1))
        L.append('     Bool.rec (motive := fun _ => YA)')
        L.append('      (Bool.rec (motive := fun _ => YA) %s' % ye)
        L.append('        (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>')
        L.append('         ih (yhalf s Y y (Nat.add o1 (Nat.add qb 1))))')
        L.append('        (Nat.beq c %d))' % NP)
        L.append('      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>')
        L.append('       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>')
        L.append('       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>')
        L.append('       ih (yupdS c s Ylo Yhi y (Nat.add o1 (Nat.add qb 1))))')
        L.append('      (Nat.blt c %d))' % NP)
        L.append('    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)')
        L.append('def ydecH (s : St) (qb w fuel : ℕ) : YA → YA :=')
        L.append('  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystepH s qb w ih) fuel')
        z = '⟨o, %s⟩' % ', '.join(['0'] * (2 * Q + 2))
        L.append('theorem MulOK_zeroH (s : St) (o : ℕ) : MulOKH s %s := fun _ _ _ => by simp' % z)
        if self.sp.get('yrow'):
            L.append('theorem yupdSH_ok (s : St) (y : YA) (h : MulOKH s y) (c : ℕ) (hc : c < %d) (Ylo Yhi o\' : ℕ) :' % NP)
            L.append('    MulOKH s (yupdS c s Ylo Yhi y o\') :=')
            L.append('  mul_stepH hPR rfl rfl h hc Ylo Yhi')
        else:
            L.append('theorem yupdSH_ok (s : St) (y : YA) (h : MulOKH s y) (c : ℕ) (Ylo Yhi o\' : ℕ) :')
            L.append('    MulOKH s (yupdS c s Ylo Yhi y o\') := by')
            L.append('  unfold yupdS')
            mid = NP // 2
            a = self.yproof(mid, NP, 4, ('MulOKH', 'H'))
            b = self.yproof(0, mid, 4, ('MulOKH', 'H'))
            L.append('  exact brec_dep (P := MulOKH s)')
            L += a + b
        L.append('theorem yhalf_ok (s : St) (y : YA) (h : MulOKH s y) (Y o\' : ℕ) : MulOKH s (yhalf s Y y o\') :=')
        L.append('  half_stepH (Q := %d) (by decide) rfl rfl h Y' % Q)
        L.append('theorem ystepH_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOKH s y → MulOKH s (ih y)) (y : YA) (h : MulOKH s y) :')
        L.append('    MulOKH s (ystepH s qb w ih y) := by')
        L.append('  unfold ystepH')
        L.append('  simp only [forceT_eq]')
        L.append('  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => brec_dep (fun _ => h) fun _ => hih _ (yhalf_ok s y h _ _))')
        L.append(('    fun hc => hih _ (yupdSH_ok s y h _ (Nat.blt_eq.mp hc) _ _ _)') if self.sp.get('yrow') else '    fun _ => hih _ (yupdSH_ok s y h _ _ _ _)')
        L.append('theorem ydecH_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOKH s y → MulOKH s (ydecH s qb w fuel y)')
        L.append('  | 0, _, h => h')
        L.append('  | n + 1, y, h => ystepH_ok s qb w (ydecH_ok s qb w n) y h')
        return L

    # ------------------------------------------------------------------ leaf check
    def mcheck_body(self):
        Q, TS, BS = self.Q, self.TS, self.sp['BS']
        tv = [self.tvars(t) for t in TS]
        aw = self.wname
        L0 = [self.sumL(t[0], t[1]) for t in TS]
        mcn = self.nest_add0(['(Nat.mul %s (mcK (tf f) false %s %s))' % (aw(t), L0[n], ' '.join(tv[n])) for n, t in enumerate(TS)])
        ng = []
        for r in range(Q):
            cov = [n for n, t in enumerate(TS) if t[0] <= r < t[1]]
            W, SL = self.gapsums(r, 'f')
            ng.append('(Nat.mul (Nat.sub s.u%d s.l%d) (Nat.sub (Nat.add (Nat.mul 2000000000 %s) P%d) (Nat.add (Nat.add (Nat.mul 1024000000000 %d) %s) S%d)))'
                      % (r, r, W, r, BS[r], SL, r))
        lhs = '(Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add %s Cp) %s)))' % (mcn, self.nest_add0(ng))
        bl = self.nest_add0(['(Nat.mul %d s.l%d)' % (BS[r], r) for r in range(Q)])
        mv = self.nest_add0(['(Nat.mul %s (mvKF top bk (tf f) %s (uc %s %s) %s))' % (aw(t), self.eL(t), self.eL(t), self.eU(t), ' '.join(tv[n]))
                             for n, t in enumerate(TS)])
        mcp = self.nest_add0(['(Nat.mul %s (mcK (tf f) true %s %s))' % (aw(t), L0[n], ' '.join(tv[n])) for n, t in enumerate(TS)])
        rhs = '(Nat.add (Nat.add (Nat.mul 10240000000000 %s) (Nat.mul 32768 %s)) (Nat.mul 10 (Nat.add %s Cm)))' % (bl, mv, mcp)
        ok = '(true)'
        for n, t in enumerate(TS):
            ok = '(Bool.rec (motive := fun _ => Bool) false (mokI2 f %s %s %s) %s)' % (self.eL(t), self.eU(t), ' '.join(tv[n]), ok)
        box = '(true)'
        for r in range(Q):
            box = '(Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l%d s.u%d) %s)' % (r, r, box)
        return 'Bool.rec (motive := fun _ => Bool) false (Nat.ble %s %s) (Bool.rec (motive := fun _ => Bool) false %s %s)' % (lhs, rhs, ok, box)

    def wname(self, t):
        return ('a%d%d' % (t[0], t[1])) if self.sp.get('helpers') else str(t[2])

    def helper_defs(self):
        """named prefix sums, term ranges and weights used by mcheckP / mleafP (option helpers)"""
        L = []
        need = sorted({(t[0], j) for t in self.TS for j in range(t[0] + 2, t[1] + 1)})
        for (i, j) in need:
            for v, f in (('x', 'l'), ('y', 'u')):
                prev = 's.%s%d' % (f, i) if j == i + 2 else '(%s%d%d s)' % (v, i, j - 1)
                L.append('def %s%d%d (s : St) : ℕ := Nat.add %s s.%s%d' % (v, i, j, prev, f, j - 1))
        for t in self.TS:
            i, j = t[0], t[1]
            if j > i + 1:
                L.append('def e%d%d (s : St) : ℕ := nmax s.A%d%d (x%d%d s)' % (i, j, i, j, i, j))
                L.append('def f%d%d (s : St) : ℕ := nmin s.B%d%d (y%d%d s)' % (i, j, i, j, i, j))
        for t in self.TS:
            L.append('def a%d%d : ℕ := %d' % (t[0], t[1], t[2]))
        return L

    def mcheck_body_shared(self):
        """mcheckP with shared subterms (forceT binders): prefix sums x_ij / y_ij of L / U,
        term ranges e_ij / f_ij, slope weights w_ij and slope claims t_ij.  `simp only
        [forceT_eq]` turns it back into mcheck_body's text."""
        Q, TS, BS = self.Q, self.TS, self.sp['BS']
        tv = [self.tvars(t) for t in TS]
        need = sorted({(t[0], j) for t in TS for j in range(t[0] + 2, t[1] + 1)})
        B = []
        for (i, j) in need:
            px = 's.l%d' % i if j == i + 2 else 'x%d%d' % (i, j - 1)
            py = 's.u%d' % i if j == i + 2 else 'y%d%d' % (i, j - 1)
            B.append('forceT (Nat.add %s s.l%d) fun x%d%d =>' % (px, j - 1, i, j))
            B.append('forceT (Nat.add %s s.u%d) fun y%d%d =>' % (py, j - 1, i, j))
        X, E, F = [], [], []
        for n, t in enumerate(TS):
            i, j = t[0], t[1]
            g = '%d%d' % (i, j)
            if j == i + 1:
                X.append('s.l%d' % i); E.append('s.l%d' % i); F.append('s.u%d' % i)
            else:
                X.append('x' + g)
                B.append('forceT (nmax s.A%s x%s) fun e%s => forceT (nmin s.B%s y%s) fun f%s =>' % (g, g, g, g, g, g))
                E.append('e' + g); F.append('f' + g)
            B.append('forceT (Nat.mul %d (mwT %s %s)) fun w%s => forceT (Nat.mul %d (mslK (tf f) %s)) fun t%s =>'
                     % (t[2], tv[n][0], tv[n][1], g, t[2], ' '.join(tv[n]), g))
        mcn = self.nest_add0(['(Nat.mul %d (mcK (tf f) false %s %s))' % (t[2], X[n], ' '.join(tv[n])) for n, t in enumerate(TS)])
        ng = []
        for r in range(Q):
            cov = [n for n, t in enumerate(TS) if t[0] <= r < t[1]]
            W = self.nest_add0(['w%d%d' % (TS[n][0], TS[n][1]) for n in cov])
            SL = self.nest_add0(['t%d%d' % (TS[n][0], TS[n][1]) for n in cov])
            ng.append('(Nat.mul (Nat.sub s.u%d s.l%d) (Nat.sub (Nat.add (Nat.mul 2000000000 %s) P%d) (Nat.add (Nat.add (Nat.mul 1024000000000 %d) %s) S%d)))'
                      % (r, r, W, r, BS[r], SL, r))
        lhs = '(Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add %s Cp) %s)))' % (mcn, self.nest_add0(ng))
        bl = self.nest_add0(['(Nat.mul %d s.l%d)' % (BS[r], r) for r in range(Q)])
        mv = self.nest_add0(['(Nat.mul %d (mvKF top bk (tf f) %s (uc %s %s) %s))' % (t[2], E[n], E[n], F[n], ' '.join(tv[n]))
                             for n, t in enumerate(TS)])
        mcp = self.nest_add0(['(Nat.mul %d (mcK (tf f) true %s %s))' % (t[2], X[n], ' '.join(tv[n])) for n, t in enumerate(TS)])
        rhs = '(Nat.add (Nat.add (Nat.mul 10240000000000 %s) (Nat.mul 32768 %s)) (Nat.mul 10 (Nat.add %s Cm)))' % (bl, mv, mcp)
        ok = '(true)'
        for n, t in enumerate(TS):
            ok = '(Bool.rec (motive := fun _ => Bool) false (mokI2 f %s %s %s) %s)' % (E[n], F[n], ' '.join(tv[n]), ok)
        box = '(true)'
        for r in range(Q):
            box = '(Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l%d s.u%d) %s)' % (r, r, box)
        body = 'Bool.rec (motive := fun _ => Bool) false (Nat.ble %s %s) (Bool.rec (motive := fun _ => Bool) false %s %s)' % (lhs, rhs, ok, box)
        return '\n  '.join(B + [body])

    def leaf(self):
        Q, TS = self.Q, self.TS
        if self.sp.get('sparse') and self.sp.get('leaf2'):
            # sparse leaf check with the q9leaf2 levers (src/lbcert/q9leaf2/zlean2.py)
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'q9leaf2'))
            import zlean2
            mh = '\n'.join(self.mult_half(*self.yconsts(self.sp.get('pb', 5))))
            return zlean2.text(Q, TS, self.sp['BS'], pt=self.fname(), opts=str(self.sp['leaf2']), src=mh).rstrip('\n').split('\n')
        if self.sp.get('sparse'):
            # sparse leaf check (src/lbcert/q9sparse/zlean.py): listed terms only, folded into accumulators
            sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'q9sparse'))
            import zlean
            return zlean.text_m(Q, TS, self.sp['BS'], pt=self.fname()).rstrip('\n').split('\n')
        half = self.sp.get('half', False)
        yfuel = self.sp.get('yfuel', 42)
        PS = ' '.join('P%d' % r for r in range(Q)) + ' ' + ' '.join('S%d' % r for r in range(Q))
        L = []
        sig = '(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)'
        fs = '[%s]' % ', '.join('(%s)' % ', '.join(self.tvars(t)) for t in TS)
        gleaf = self.sp.get('gleaf')
        if gleaf:
            L += ['def mcheckP %s (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ) : Bool :=' % sig,
                  '  mcheckGX (mokI f) top bk (tf f) %d BS TS cN (toCl s) FS P S Cp Cm' % Q]
        else:
            L += self.mcheckP_unrolled(sig, fs, PS)
        return L + self.leaf_rest(fs, gleaf)

    def lam_rule(self):
        """K-format: forceR binders that replace each adjacent term's lambda (kinds 2, 3) by the
        checker rule of q9enc/FORMAT.md section 3.2 (lamR).  Text inside mleafP's continuation."""
        Q, TS, BS = self.Q, self.TS, self.sp['BS']
        tv = [self.tvars(t) for t in TS]
        out = []
        for g in range(Q):
            n = next(k for k, t in enumerate(TS) if t[0] == g and t[1] == g + 1)
            k, m, p, r = tv[n]
            a = self.wname(TS[n])
            cov = [i for i, t in enumerate(TS) if t[0] <= g < t[1]]
            W, SL = self.gapsums(g, self.fname())
            Ip = '(Nat.add (Nat.mul 2000000000 %s) y.P%d)' % (W, g)
            In = '(Nat.add (Nat.add (Nat.mul 1024000000000 %d) %s) y.S%d)' % (BS[g], SL, g)
            L0, U0 = 's.l%d' % g, 's.u%d' % g
            out.append(('forceR (Bool.rec (motive := fun _ => ℕ) %s (lamR %s %s (lamV top bk (tf pb) %s %s %s %s 1024 0 %s %s) (lamV top bk (tf pb) %s %s %s %s 0 1024 %s %s) (lamI (tf pb) %s %s 1024 0 %s %s) (lamI (tf pb) %s %s 0 1024 %s %s) (Nat.mul 10 (Nat.sub %s %s))) (Nat.ble 2 %s)) fun %s =>'
                        % (m, Ip, In, a, L0, U0, k, p, r, a, L0, U0, k, p, r, a, k, p, r, a, k, p, r, U0, L0, k, m)).replace('(tf pb)', '(tf %s)' % self.fname()))
        return '\n  '.join(out) + '\n  '

    def fname(self):
        return 'f' if self.sp.get('notn') else 'pb'

    def gapsums(self, g, fn):
        """(sum of a·mwT, sum of a·mslK) over the terms covering gap g, or their notation names"""
        if self.sp.get('notn'):
            return 'Wg%d' % g, 'Tg%d' % g
        return self.gapsums_text(g, fn)

    def gapsums_text(self, g, fn):
        TS = self.TS
        tv = [self.tvars(t) for t in TS]
        cov = [i for i, t in enumerate(TS) if t[0] <= g < t[1]]
        W = self.nest_add0(['(Nat.mul %s (mwT %s %s))' % (self.wname(TS[i]), tv[i][0], tv[i][1]) for i in cov])
        SL = self.nest_add0(['(Nat.mul %s (mslK (tf %s) %s))' % (self.wname(TS[i]), fn, ' '.join(tv[i])) for i in cov])
        return W, SL

    def gap_notations(self):
        L = []
        for g in range(self.Q):
            W, SL = self.gapsums_text(g, 'f')
            L += ['set_option hygiene false in', 'local notation "Wg%d" => %s' % (g, W),
                  'set_option hygiene false in', 'local notation "Tg%d" => %s' % (g, SL)]
        return L

    def mcheckP_unrolled(self, sig, fs, PS):
        Q, TS = self.Q, self.TS
        L = self.gap_notations() if self.sp.get('notn') else []
        L.append('def mcheckP %s' % sig)
        L.append('    (%s : ℕ) (%s Cp Cm : ℕ) : Bool :=' % (self.kmpr(), PS))
        L.append('  ' + (self.mcheck_body_shared() if self.sp.get('share') else self.mcheck_body()))
        L.append('theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)')
        L.append('    (%s : ℕ) (%s Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s %s %s Cp Cm = true) :' % (self.kmpr(), PS, self.kmpr(), PS))
        L.append('    mcheckGX (mokI f) top bk (tf f) %d BS TS cN (toCl s) %s' % (Q, fs))
        L.append('      [%s] [%s] Cp Cm = true := by' % (', '.join('P%d' % r for r in range(Q)), ', '.join('S%d' % r for r in range(Q))))
        L.append('  simp only [mcheckP, %smvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq, mokI2_eq] at h; exact h' % ('forceT_eq, ' if self.sp.get('share') else ''))
        return L

    def leaf_rest(self, fs, gleaf):
        Q, TS = self.Q, self.TS
        half = self.sp.get('half', False)
        yfuel = self.sp.get('yfuel', 42)
        L = []
        z = '⟨o%d, %s⟩' % (self.NT, ', '.join(['0'] * (2 * Q + 2)))

        def decs():
            out = ['  forceR 0 fun o0 =>']
            kf = self.sp.get('kfmt')
            for n, t in enumerate(TS):
                lb = 0 if (kf and t[1] == t[0] + 1 and not self.sp.get('adjlam')) else 10
                out.append('  dec4QG 3 %d w o%d %s %s fun %s o%d =>' % (lb, n, self.eL(t), self.eU(t), ' '.join(self.tvars(t)), n + 1))
            return out
        lsig = '(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ'
        L.append('def mleafP %s :=' % lsig.replace('(pb :', '(%s :' % self.fname()))
        L += decs()
        if gleaf:
            L.append('  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s %s %s))' % (fs, self.ylist()))
        else:
            rule = self.lam_rule() if self.sp.get('kfmt') and not self.sp.get('adjlam') else ''
            L.append(('  (fun y : YA => %sBool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s %s %s y.Cp y.Cm))'.replace(' pb R s', ' %s R s' % self.fname()))
                     % (rule, self.kmpr(), ' '.join('y.P%d' % r for r in range(Q)) + ' ' + ' '.join('y.S%d' % r for r in range(Q))))
        L.append('  (%s s 14 w %d %s)' % ('ydecH' if half else 'ydecS', yfuel, z))
        hyp = '(hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true)'
        imp = '{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}'
        L.append('theorem mleafP_ok %s' % imp)
        L.append('    %s (w : ℕ) (s : St)' % hyp)
        L.append('    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by')
        L.append('  unfold mleafP at h')
        L.append('  repeat (first | refine forceR_cov (fun _ h => ?_) h | refine dec4QG_cov (fun _ _ _ _ _ h => ?_) h)')
        nargs = 4 * self.NT + 2 * Q + 2 + 1
        sound = 'mcheckGX_soundH' if half else 'mcheckGX_sound'
        zero = 'MulOK_zeroH' if half else 'MulOK_zero'
        yd = 'ydecH_ok' if half else 'ydecS_ok'
        if gleaf:
            L.append('  exact %s (f := tf pb) (mtermTI hlb hpt) hPR hTS (%s s 14 w %d _ (%s s _)) (brec_ne h)' % (sound, yd, yfuel, zero))
        else:
            L.append('  exact %s (f := tf pb) (mtermTI hlb hpt) hPR hTS (%s s 14 w %d _ (%s s _)) (mcheckP_ok %s (brec_ne h))'
                     % (sound, yd, yfuel, zero, ' '.join(['_'] * nargs)))
        if self.sp.get('novar'):
            return L
        L.append('def TB : List (ℕ × ℕ × ℕ) := [%s]' % ', '.join('(%d, %d, %s)' % (b0, n, hex(t)) for (b0, n, t) in self.sp.get('TB', [])))
        L.append('theorem TB_ok : AMW.Cert.PCell.Var.tbOk TB = true := by decide +kernel')
        L.append('def mleafV %s :=' % lsig)
        L += decs()
        L.append('  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (AMW.Cert.PCell.Var.mcheckW (AMW.Cert.PCell.Var.vbW TB) (mokI pb) top bk (tf pb) %d BS TS cN (toCl s) %s' % (Q, fs))
        L.append('      %s))' % self.ylist())
        L.append('  (%s s 14 w %d %s)' % ('ydecH' if half else 'ydecS', yfuel, z))
        L.append('theorem mleafV_ok %s' % imp)
        L.append('    %s (w : ℕ) (s : St)' % hyp)
        L.append('    (h : mleafV top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by')
        L.append('  unfold mleafV at h')
        L.append('  repeat (first | refine forceR_cov (fun _ h => ?_) h | refine dec4QG_cov (fun _ _ _ _ _ h => ?_) h)')
        sw = 'mcheckW_soundH' if half else 'mcheckW_sound'
        L.append('  exact AMW.Cert.PCell.Var.%s (f := tf pb) (AMW.Cert.PCell.Var.mtermTIW hlb hpt TB_ok) hPR hTS (%s s 14 w %d _ (%s s _)) (brec_ne h)'
                 % (sw, yd, yfuel, zero))
        return L

    # ------------------------------------------------------------------ walk
    def walk(self):
        Q, F = self.Q, self.F
        sig = '(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ))'
        imp = '{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}'
        hyp = '(hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true)'
        st = '⟨%s⟩' % ', '.join(F)
        q1 = Q - 1
        L = []
        if self.sp.get('novar'):
            L += self.leafstep_novar(sig, imp, hyp, st, q1)
        else:
            L += self.leafstep_var(sig, imp, hyp, st, q1)
        return L + self.walk_rest(sig, imp, hyp, st)

    def leafstep_var(self, sig, imp, hyp, st, q1):
        F = self.F
        L = []
        L.append('def leafStep %s (pos w : ℕ) : ST :=' % sig)
        L.append('  fun %s => Bool.rec (motive := fun _ => ℕ)' % ' '.join(F))
        L.append('    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) %s)' % st)
        L.append('        (mleafV top bk tD bD pb R (Nat.shiftRight w 2) %s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>' % st)
        L.append('      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))')
        L.append('    (Nat.add pos 1) (Nat.blt u%d l0)' % q1)
        L.append('theorem leafStep_ok %s' % imp)
        L.append('    %s (pos w : ℕ) :' % hyp)
        L.append('    CovK (leafStep top bk tD bD pb R pos w) := by')
        L.append('  intro s h')
        L.append('  have h\' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)')
        L.append('      (mleafV top bk tD bD pb R (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>')
        L.append('      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u%d s.l0) ≠ 0 := h' % q1)
        L.append('  cases hs : Nat.blt s.u%d s.l0' % q1)
        L.append('  · rw [hs, forceR_eq] at h\'')
        L.append('    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1')
        L.append('    · rw [hk] at h\'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h\'; exact h\' rfl')
        L.append('    · rw [hk] at h\'; exact mleafV_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h\'; exact h\' rfl')
        L += self.refl_tail(q1)
        return L

    def refl_tail(self, q1):
        L = []
        L.append('  · intro g hg')
        L.append('    right')
        L.append('    have h1 : g %d ≤ (s.u%d : ℝ) / SC := (hg.1 %d (by norm_num)).2' % (q1, q1, q1))
        L.append('    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1')
        L.append('    have : (s.u%d : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos' % q1)
        L.append('    show g %d < g 0' % q1)
        L.append('    linarith')
        return L

    def leafstep_novar(self, sig, imp, hyp, st, q1):
        L = []
        ml = 'mleafZ' if self.sp.get('sparse') else 'mleafP'
        L.append('def leafStep %s (pos w : ℕ) : ST :=' % sig)
        L.append('  fun %s => Bool.rec (motive := fun _ => ℕ)' % ' '.join(self.F))
        sh = 1 if self.sp.get('kfmt') else 2
        L.append('    (forceR (%s top bk tD bD pb R (Nat.shiftRight w %d) %s) fun n =>' % (ml, sh, st))
        L.append('      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add %d n)) 0 (Nat.beq n 0))' % sh)
        L.append('    (Nat.add pos 1) (Nat.blt u%d l0)' % q1)
        L.append('theorem leafStep_ok %s' % imp)
        L.append('    %s (pos w : ℕ) :' % hyp)
        L.append('    CovK (leafStep top bk tD bD pb R pos w) := by')
        L.append('  intro s h')
        L.append('  have h\' : Bool.rec (motive := fun _ => ℕ) (forceR (%s top bk tD bD pb R (Nat.shiftRight w %d) s) fun n =>' % (ml, sh))
        L.append('      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add %d n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u%d s.l0) ≠ 0 := h' % (sh, q1))
        L.append('  cases hs : Nat.blt s.u%d s.l0' % q1)
        L.append('  · rw [hs, forceR_eq] at h\'')
        if self.sp.get('sparse'):
            L.append('    exact mleafZ_ok hlb hpt _ s fun h0 => by rw [h0] at h\'; exact h\' rfl')
        else:
            L.append('    exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h\'; exact h\' rfl')
        L += self.refl_tail(q1)
        return L

    def walk_rest(self, sig, imp, hyp, st):
        Q, F = self.Q, self.F
        L = []
        wb = self.sp.get('wmask_bits', 600)
        L.append('def WMASK : ℕ := zfNat64 %d "%s"' % (wb, wmask_payload(wb)))
        L.append('def rdw (f : ℕ → ℕ) (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (f (Nat.div pos 32768)) (Nat.mod pos 32768)) WMASK')
        L.append('def node %s (bits : ℕ → ℕ) (ih : WF) (pos : ℕ) : ST :=' % sig)
        L.append('  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (bits pos))')
        L.append('    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 7) (Nat.add pos 10) (Nat.land (Nat.shiftRight (bits pos) 1) 63))')
        L.append('    (Nat.beq (Nat.land (bits pos) 1) 1)')
        L.append('def walkC %s (bits : ℕ → ℕ) (fuel : ℕ) : WF :=' % sig)
        L.append('  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel')
        L.append('def walk %s (bits : ℕ → ℕ) (fuel : ℕ) : WF :=' % sig)
        L.append('  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)')
        L.append('theorem walkC_ok %s' % imp)
        L.append('    %s (bits : ℕ → ℕ) :' % hyp)
        L.append('    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)')
        L.append('  | 0 => fun _ => zK_ok')
        L.append('  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from')
        L.append('      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>')
        L.append('      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)')
        L.append('theorem walk_ok %s' % imp)
        L.append('    %s (bits : ℕ → ℕ) :' % hyp)
        L.append('    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=')
        L.append('  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)')
        L.append('theorem covered_of_walk %s' % imp)
        L.append('    %s (bits : ℕ → ℕ) (fuel e : ℕ) (s : St)' % hyp)
        L.append('    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=')
        L.append('  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)')
        L.append('def stEq (a b : St) : Bool := %s' % ' && '.join('Nat.beq a.%s b.%s' % (x, x) for x in F))
        L.append('theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by')
        L.append('  cases a; cases b')
        L.append('  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h')
        e = 'h0'
        for k in range(1, len(F)):
            e = '⟨%s, h%d⟩' % (e, k)
        L.append('  obtain %s := h' % e)
        L.append('  subst_vars; rfl')
        L.append('theorem covered_of_walkCP %s' % imp)
        L.append('    %s (bits : ℕ → ℕ) (fuel pos e : ℕ) (s : St)' % hyp)
        L.append('    (h : U (walkC top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=')
        L.append('  walkC_ok hlb hD hpt hR bits fuel pos s (h ▸ he)')
        L.append('def kEqE (t : St) (e : ℕ) : ST := fun %s => Bool.rec (motive := fun _ => ℕ) 0 e (stEq %s t)' % (' '.join(F), st))
        L += KEQ_TAIL.split('\n')
        L.append('def ADJ : List ℕ := [%s]' % ', '.join(str(x) for x in self.sp['ADJ']))
        L.append('theorem hADJ : ∀ r < %d, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide' % Q)
        L.append('theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < %d, cN * SC ≤ BS.getD r 0 * Smax r)' % Q)
        L.append('    (hcov : ∀ r < %d, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)' % Q)
        L.append('    (hwin : ∀ r < %d, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : %d * KB ≤ W)' % (Q, Q))
        L.append('    (hrun : ∀ idx : ℕ → ℕ, (∀ r < %d, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl %d %d W cov idx)) :' % (Q, Q, self.NP))
        L.append('    ∀ g : ℕ → ℝ, (∀ r < %d, 0 ≤ g r) → Pg cN %d BS TS g :=' % (Q, Q))
        L.append('  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun')
        return L

    def emit(self, ns='AMW.Cert.PC9XA'):
        L = list(PRE_HEAD)
        L.append('namespace %s' % ns)
        L.append('open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell')
        L += self.head() + self.split() + self.tmatc() + self.mult() + self.leaf() + self.walk()
        L.append('end %s' % ns)
        L.append('end')
        return '\n'.join(L) + '\n'


def wmask_payload(bits):
    """zfNat64 payload of 2^bits - 1 (radix 64, alphabet A-Z a-z 0-9 + _, big-endian)"""
    alpha = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+_'
    v = (1 << bits) - 1
    n = -(-bits // 6)
    s = []
    for _ in range(n):
        s.append(alpha[v & 63])
        v >>= 6
    return ''.join(reversed(s))


LAMDEFS = """def lamV (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (a L U k x y p r : ℕ) : ℕ :=
  Nat.mul a (Nat.add (Nat.add (Nat.mul 32768 (mvKF top bk f L (uc L U) k x p r)) (Nat.mul 10 (mcK f true L k x p r))) (Nat.mul 10 (mcK f false L k y p r)))
def lamI (f : ℕ → ℕ) (a k x y p r : ℕ) : ℕ := Nat.mul a (Nat.add (Nat.mul 2000000000 (mwT k x)) (mslK f k y p r))
def lamF (Ip In dp dn W x : ℕ) : ℕ := Nat.mul W (Nat.sub (Nat.add (Nat.mul 1024 Ip) (Nat.mul x dp)) (Nat.add (Nat.mul 1024 In) (Nat.mul x dn)))
def lamB (Ip In bp bn dp dn W b x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) b (Bool.rec (motive := fun _ => ℕ) b x (Nat.blt (Nat.add (Nat.mul b bp) (Nat.add (Nat.mul x bn) (lamF Ip In dp dn W x)))
    (Nat.add (Nat.mul x bp) (Nat.add (Nat.mul b bn) (lamF Ip In dp dn W b))))) (Nat.ble x 1024)
def lamT (Ip In dp dn : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2000 (Bool.rec (motive := fun _ => ℕ) 2000 (Nat.div (Nat.mul 1024 (Nat.sub In Ip)) (Nat.sub dp dn)) (Nat.ble Ip In)) (Nat.blt dn dp))
    (Bool.rec (motive := fun _ => ℕ) 2000 (Nat.div (Nat.mul 1024 (Nat.sub Ip In)) (Nat.sub dn dp)) (Nat.ble In Ip)) (Nat.blt dp dn)
def lamR (Ip In bp bn dp dn W : ℕ) : ℕ :=
  forceR (lamT Ip In dp dn) fun t => lamB Ip In bp bn dp dn W (lamB Ip In bp bn dp dn W (lamB Ip In bp bn dp dn W 0 t) (Nat.add t 1)) 1024"""

PRE_HEAD = """-- SWAP BEGIN certificate: instance + data + full cert + RiemannFail (W8, W8_adm, W8_B, cert_AM)
/- Mechanical extraction of attempt016 at commit 296f7bb9c4e01b0c97554cf76af91ed99a410e8d,
   original physical lines 22795-23023; mathematical body retained byte-for-byte.
   Full original attribution retained above. Imports/global options and, where
   necessary, balanced closing ends are the only added commands. Source-only;
   no new compilation or acceptance claim. Original SHA256 5000dfb504e4cba831b3a7976974849f7574e2d7384a14f974b4a8bb02de2945.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section""".split('\n')

KEQ_TAIL = """theorem kEqE_ok {t : St} {e : ℕ} (h : Covered (toCl t)) : CovK (kEqE t e) := fun s hs => by
  have e' : U (kEqE t e) s = Bool.rec (motive := fun _ => ℕ) 0 e (stEq s t) := rfl
  rw [e'] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
def cutAt (cuts : List (ℕ × St × ℕ)) (pos : ℕ) (k : ST) : ST :=
  List.rec (motive := fun _ => ST) k (fun c _ ih => Bool.rec (motive := fun _ => ST) ih (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos)) cuts
def CutsOk (cuts : List (ℕ × St × ℕ)) : Prop := ∀ c ∈ cuts, Covered (toCl c.2.1)
theorem cutsOk_nil : CutsOk [] := fun _ h => absurd h (by simp)
theorem cutsOk_cons {p e : ℕ} {t : St} {cs : List (ℕ × St × ℕ)} (h : Covered (toCl t)) (hs : CutsOk cs) :
    CutsOk ((p, t, e) :: cs) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h
  · exact hs c hc
theorem cutAt_ok {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (pos : ℕ) {k : ST} (hk : CovK k) : CovK (cutAt cuts pos k) := by
  induction cuts with
  | nil => exact hk
  | cons c cs ih =>
    show CovK (Bool.rec (motive := fun _ => ST) (cutAt cs pos k) (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos))
    cases Nat.beq c.1 pos
    · exact ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))
    · exact kEqE_ok (hc c (List.mem_cons.mpr (Or.inl rfl)))
def walkCut (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => cutAt cuts pos (node top bk tD bD pb R bits ih pos)) fuel
def walkCutR (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  fun pos => tm (walkCut top bk tD bD pb R bits cuts fuel pos)
theorem walkCut_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) : ∀ fuel, WalkOK (walkCut top bk tD bD pb R bits cuts fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => cutAt_ok hc pos
      (show CovK (node top bk tD bD pb R bits (walkCut top bk tD bD pb R bits cuts n) pos) from
        brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
        (splitAx_ok (walkCut_ok hlb hD hpt hR bits hc n) _ _ _))
theorem covered_of_walkCutR {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (fuel pos e : ℕ) (s : St)
    (h : U (walkCutR top bk tD bD pb R bits cuts fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  tm_ok (walkCut_ok hlb hD hpt hR bits hc fuel pos) s (h ▸ he)"""
