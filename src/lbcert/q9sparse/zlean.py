"""Lean text of the sparse leaf check "Z" for the Q-gap instance module (namespace AMW.Cert.PC9XA).

Leaf payload (after the leaf's leading 0 bit), see FORMAT.md in this directory:
  bits 0 .. NT-1: presence mask (bit n set: term n is listed);
  then, for each listed term in increasing n: 3-bit kind z, then
    z = 1: 7-bit anchor code                      1024 tangent(p)
    z = 2: 7-bit anchor code, 10-bit lam          (1024 - lam) lb + lam tangent(p)
    z = 3: two 7-bit anchor codes, 10-bit lam     (1024 - lam) tangent(p) + lam tangent(r)
    z = 0: nothing                                1024 lb
    z >= 4: 7-bit anchor code, 10-bit lam         lam tangent(p)   (no constant part)
  then the multiplier list as in the K-format (ydecH).
Unlisted terms contribute nothing.  The check folds the listed terms into one record (TZ: ok flag, CV, CP,
CN and the per-gap sums X_r, Y_r), then evaluates mcheckGX's final inequality on the accumulators.

Soundness (all here, no sorry): tzv_cov (one listed term satisfies the per-term bound of mtermTI; kind >= 4
by dropping the nonnegative constant part), ZInv_add / ZInv_skip (the fold invariant: the listed terms
among the first N bound by sum_{n<N} a_n wfun; an unlisted term adds a_n wfun >= 0), zfin_ok (the final
aggregation of mcheckGX_soundH on the accumulators), mleafZ_ok (the chain), leafStep_ok.

    text(Q, TS, BS) -> str     (TS: list of (i, j, a, k) in TS order; BS: the Q bs weights)
"""


def nest_add0(xs):
    e = '0'
    for x in xs:
        e = '(Nat.add %s %s)' % (e, x)
    return e


def text(Q, TS, BS, pt='f'):
    NT = len(TS)
    X = ['X%d' % r for r in range(Q)]
    Y = ['Y%d' % r for r in range(Q)]
    FLD = ['ok', 'CV', 'CP', 'CN'] + X + Y
    B = 'Bool.rec (motive := fun _ => ℕ)'
    BB = 'Bool.rec (motive := fun _ => Bool)'
    L = []
    L.append('/-! ###### sparse leaf check Z: the leaf lists only its nonzero terms (presence mask), folded into accumulators ###### -/')
    L.append('structure TZ where\n  (%s : ℕ)' % ' '.join(FLD))
    # ------------------------------------------------------------ one listed term
    tan1 = ('forceT (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127)) fun p => forceT (%s p) fun g => forceT (trip g) fun v =>' % pt)
    tan2 = ('forceT (gptQG 3 eL eU (Nat.land (Nat.shiftRight w (Nat.add o 7)) 127)) fun r => forceT (%s r) fun gr => forceT (trip gr) fun vr =>' % pt)
    cpx = lambda l, v, p: '(Nat.mul (Nat.mul %s (Nat.sub (hi32 (hi32 %s)) 2000000000)) (Nat.sub %s e0))' % (l, v, p)
    cnx = lambda l, v, p: '(Nat.mul (Nat.mul %s (Nat.sub 2000000000 (hi32 (hi32 %s)))) (Nat.sub %s e0))' % (l, v, p)
    lbv = '(lbF top bk eL (uc eL eU))'
    k1 = ('(%s\n       k (Nat.mul 1024 (lo32 v)) %s %s (Nat.mul 1024 (lo32 (hi32 v))) 1024 (%s 0 1 (ivIn2 g eL eU p)) (Nat.add o 7))'
          % (tan1, cpx('1024', 'v', 'p'), cnx('1024', 'v', 'p'), B))
    lam7 = 'forceT (Nat.land (Nat.shiftRight w (Nat.add o 7)) 1023) fun lam =>'
    okl = '(%s 0 (%s 0 1 (ivIn2 g eL eU p)) (Nat.ble lam 1024))' % (B, B)
    k2 = ('(%s %s\n       k (Nat.add (Nat.mul (Nat.sub 1024 lam) %s) (Nat.mul lam (lo32 v))) %s %s (Nat.mul lam (lo32 (hi32 v))) lam %s (Nat.add o 17))'
          % (tan1, lam7, lbv, cpx('lam', 'v', 'p'), cnx('lam', 'v', 'p'), okl))
    k4 = ('(%s %s\n       k (Nat.mul lam (lo32 v)) %s %s (Nat.mul lam (lo32 (hi32 v))) lam %s (Nat.add o 17))'
          % (tan1, lam7, cpx('lam', 'v', 'p'), cnx('lam', 'v', 'p'), okl))
    ok3 = '(%s 0 (%s 0 (%s 0 1 (ivIn2 gr eL eU r)) (ivIn2 g eL eU p)) (Nat.ble lam 1024))' % (B, B, B)
    k3 = ('(%s\n       %s\n       forceT (Nat.land (Nat.shiftRight w (Nat.add o 14)) 1023) fun lam => forceT (Nat.sub 1024 lam) fun l1 =>\n'
          '       k (Nat.add (Nat.mul l1 (lo32 v)) (Nat.mul lam (lo32 vr))) (Nat.add %s %s) (Nat.add %s %s)\n'
          '         (Nat.add (Nat.mul l1 (lo32 (hi32 v))) (Nat.mul lam (lo32 (hi32 vr)))) (Nat.add l1 lam) %s (Nat.add o 24))'
          % (tan1, tan2, cpx('l1', 'v', 'p'), cpx('lam', 'vr', 'r'), cnx('l1', 'v', 'p'), cnx('lam', 'vr', 'r'), ok3))
    k0 = '(k (Nat.mul 1024 %s) 0 0 0 0 1 o)' % lbv
    L.append('/-- the values of one listed term of kind `z` (anchor codes and lam read from `w` at `o`), passed to `k` as\n'
             'value, charge +, charge −, slope claim, slope weight, side condition (0: failed), next offset -/')
    L.append('def tzv (top : ℕ) (bk : ℕ → ℕ) (%s : ℕ → ℕ) (z w o eL eU e0 : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=' % pt)
    L.append('  %s\n    (%s\n      (%s\n        (%s\n          %s\n          %s\n          (Nat.beq z 2))\n        %s\n        (Nat.beq z 0))\n'
             '      %s\n      (Nat.beq z 3))\n    %s\n    (Nat.beq z 1)' % (B, B, B, B, k4, k2, k0, k3, k1))
    L.append(SOUND_TERM)
    # ------------------------------------------------------------ the accumulators
    L.append('/-- the per-gap sums of a record, as functions of the gap -/')
    L.append('def zx (t : TZ) (r : ℕ) : ℕ := [%s].getD r 0' % ', '.join('t.' + x for x in X))
    L.append('def zy (t : TZ) (r : ℕ) : ℕ := [%s].getD r 0' % ', '.join('t.' + y for y in Y))
    L.append(SOUND_INV.replace('@Q@', str(Q)).replace('@QQ@', str(Q - 1)))
    # ------------------------------------------------------------ one term step
    upd = lambda f, v: ', '.join('%s t.%s%d (Nat.add t.%s%d (Nat.mul a %s)) (inr %d i j)' % (B, f, r, f, r, v, r) for r in range(Q))
    L.append('/-- term `n` of the chain: listed (mask bit `n`) -> decode, check and accumulate; unlisted -> nothing -/')
    L.append('def tzG (top : ℕ) (bk : ℕ → ℕ) (%s : ℕ → ℕ) (i j a eL eU e0 n m w o : ℕ) (t : TZ) (k : ℕ → TZ → ℕ) : ℕ :=' % pt)
    L.append('  %s (k o t)\n    (forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>\n'
             '     tzv top bk %s (Nat.land (Nat.shiftRight w o) 7) w (Nat.add o 3) eL eU e0 fun mv cp cn sl mw ok o\' =>\n'
             '     k o\' ⟨Nat.mul t.ok ok, Nat.add t.CV (Nat.mul a mv), Nat.add t.CP (Nat.mul a cp), Nat.add t.CN (Nat.mul a cn),\n'
             '       %s,\n       %s⟩)\n    (Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1)'
             % (B, pt, upd('X', 'mw'), upd('Y', 'sl')))
    L.append(SOUND_STEP.replace('@QQ@', str(Q - 1)).replace('@Q@', str(Q)))
    # ------------------------------------------------------------ final inequality
    ng = nest_add0(['(Nat.mul (Nat.sub s.u%d s.l%d) (Nat.sub (Nat.add (Nat.mul 2000000000 t.X%d) y.P%d) (Nat.add (Nat.add (Nat.mul 1024000000000 %d) t.Y%d) y.S%d)))'
                    % (r, r, r, r, BS[r], r, r) for r in range(Q)])
    bl = nest_add0(['(Nat.mul %d s.l%d)' % (BS[r], r) for r in range(Q)])
    box = 'true'
    for r in range(Q):
        box = '(%s false (Nat.ble s.l%d s.u%d) %s)' % (BB, r, r, box)
    chk = ('%s false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add t.CN y.Cp) %s)))\n'
           '      (Nat.add (Nat.add (Nat.mul 10240000000000 %s) (Nat.mul 32768 t.CV)) (Nat.mul 10 (Nat.add t.CP y.Cm))))\n'
           '    (%s false %s (Nat.ble 1 t.ok))' % (BB, ng, bl, BB, box))
    L.append('/-- the final inequality of `mcheckGX` on the accumulators (and the box, and the side conditions) -/')
    L.append('def zchk (s : St) (t : TZ) (y : YA) : Bool :=\n  ' + chk)
    L.append('def zfin (s : St) (t : TZ) (y : YA) : ℕ := %s 0 y.o (zchk s t y)' % B)
    L.append(SOUND_FIN.replace('@Q@', str(Q)).replace('@QQ@', str(Q - 1)).replace('@NT@', str(NT)))
    # ------------------------------------------------------------ the chain
    hdr = '(top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (%s : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ' % pt
    L.append('/-- the sparse leaf check: the mask, the chain over the %d terms, the multipliers, the final inequality -/' % NT)
    L.append('def mleafZ %s :=' % hdr)
    L.append('  forceR (Nat.land w %d) fun m =>' % ((1 << NT) - 1))
    t0 = '⟨1, %s⟩' % ', '.join(['0'] * (3 + 2 * Q))
    for n, (i, j, a, k) in enumerate(TS):
        if j - i == 1:
            rg = 's.l%d s.u%d s.l%d' % (i, i, i)
        else:
            rg = '(e%d%d s) (f%d%d s) (x%d%d s)' % (i, j, i, j, i, j)
        tin = t0 if n == 0 else 't%d' % n
        oin = str(NT) if n == 0 else 'o%d' % n
        L.append('  tzG top bk %s %d %d a%d%d %s %d m w %s %s fun o%d t%d =>' % (pt, i, j, i, j, rg, n, oin, tin, n + 1, n + 1))
    L.append('  zfin s t%d (ydecH s 14 w 42 ⟨o%d, %s⟩)' % (NT, NT, ', '.join(['0'] * (2 * Q + 2))))
    imp = '{top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}'
    L.append('theorem mleafZ_ok %s' % imp)
    L.append('    (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x)) (w : ℕ) (s : St)')
    L.append('    (h : mleafZ top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by')
    L.append('  intro g hg')
    L.append('  rcases lt_or_ge (g %d) (g 0) with hlt | hle' % (Q - 1))
    L.append('  · exact Or.inr hlt')
    L.append('  left')
    L.append('  unfold mleafZ at h')
    L.append('  rw [forceR_eq] at h')
    for n in range(NT):
        hin = '(ZInv_zero s g)' if n == 0 else 'hi'
        L.append('  refine tzG_cov hlb hpt hg h (n := %d) (by decide) rfl rfl rfl rfl rfl rfl %s fun _ _ hi h => ?_' % (n, hin))
    L.append('  exact zfin_ok hg hle hi (ydecH_ok s 14 w 42 _ (MulOK_zeroH s _)) h')
    return '\n'.join(L) + '\n'


SOUND_TERM = r'''/-- the per-term bound that `mcheckGX_soundH` consumes, for one term's values -/
def TBnd (top : ℕ) (bk : ℕ → ℕ) (L U e0 mv cp cn sl mw : ℕ) : Prop :=
  ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
    ∃ D : ℝ, (sl : ℝ) - 2000000000 * (mw : ℝ) ≤ 1000000000 * D ∧
      32768 * (mv : ℝ) + 327680000000000 * (D * (s - (e0 : ℝ) / 32768)) + 10 * (cp : ℝ) - 10 * (cn : ℝ)
        ≤ 327680000000000 * 1024 * wfun s
/-- `mtermTI` for values equal to a kernel term's (the value may be smaller: a dropped constant part) -/
theorem tbnd_of {top : ℕ} {bk : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x))
    {L U e0 k m p r mv cp cn sl mw : ℕ} (he : e0 ≤ L) (hok : mokI pb L U k m p r = true)
    (hmv : mv ≤ mvT top bk (tf pb) L (uc L U) k m p r) (hcp : cp = mcpT (tf pb) e0 k m p r)
    (hcn : cn = mcnT (tf pb) e0 k m p r) (hsl : sl = mslT (tf pb) k m p r) (hmw : mw = mwT k m) :
    TBnd top bk L U e0 mv cp cn sl mw := by
  intro s hs1 hs2
  obtain ⟨D, h1, h2⟩ := mtermTI hlb hpt e0 L U k m p r he hok s hs1 hs2
  refine ⟨D, by rw [hsl, hmw]; exact h1, ?_⟩
  have hmv' : (mv : ℝ) ≤ (mvT top bk (tf pb) L (uc L U) k m p r : ℝ) := by exact_mod_cast hmv
  rw [hcp, hcn]
  linarith
theorem ivIn_of2 {v L U p : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 1 (ivIn2 v L U p) ≠ 0) : ivIn v L U p = true := by
  rw [← ivIn2_eq]; cases hb : ivIn2 v L U p
  · rw [hb] at h; exact absurd rfl h
  · rfl
theorem brec_ok {b : Bool} {x : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 x b ≠ 0) : b = true ∧ x ≠ 0 := by
  cases b
  · exact absurd rfl h
  · exact ⟨rfl, h⟩
theorem mokI_0 (pb : ℕ → ℕ) (L U : ℕ) : mokI pb L U 0 0 0 0 = true := rfl
theorem mokI_1 {pb : ℕ → ℕ} {L U p : ℕ} (r : ℕ) (h : ivIn (pb p) L U p = true) : mokI pb L U 1 1024 p r = true := by
  unfold mokI; rw [h]; rfl
theorem mokI_2 {pb : ℕ → ℕ} {L U lam p : ℕ} (r : ℕ) (hl : Nat.ble lam 1024 = true) (h : ivIn (pb p) L U p = true) :
    mokI pb L U 2 lam p r = true := by
  unfold mokI; rw [hl, h]; cases Nat.beq (mw1 2 lam) 0 <;> rfl
theorem mokI_3 {pb : ℕ → ℕ} {L U lam p r : ℕ} (hl : Nat.ble lam 1024 = true) (hp : ivIn (pb p) L U p = true)
    (hr : ivIn (pb r) L U r = true) : mokI pb L U 3 lam p r = true := by
  unfold mokI; rw [hl, hp, hr]; cases Nat.beq (mw1 3 lam) 0 <;> cases Nat.beq (mw2 3 lam) 0 <;> rfl
theorem z0_vals (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U e0 : ℕ) :
    mvT top bk f L U 0 0 0 0 = Nat.mul 1024 (lb top bk L U) ∧ (0 : ℕ) = mcpT f e0 0 0 0 0 ∧ (0 : ℕ) = mcnT f e0 0 0 0 0 ∧
      (0 : ℕ) = mslT f 0 0 0 0 ∧ (0 : ℕ) = mwT 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;>
  simp only [mvT, mval, mcpT, mcp, mcnT, mcn, mslT, msl, show mwc 0 0 = 1024 from rfl, show mw1 0 0 = 0 from rfl,
    show mw2 0 0 = 0 from rfl, Nat.mul_eq, Nat.add_eq, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
theorem z1_vals (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U e0 p r : ℕ) :
    mvT top bk f L U 1 1024 p r = Nat.mul 1024 (lo32 (f p)) ∧
    Nat.mul (Nat.mul 1024 (Nat.sub (hi32 (hi32 (f p))) 2000000000)) (Nat.sub p e0) = mcpT f e0 1 1024 p r ∧
    Nat.mul (Nat.mul 1024 (Nat.sub 2000000000 (hi32 (hi32 (f p))))) (Nat.sub p e0) = mcnT f e0 1 1024 p r ∧
    Nat.mul 1024 (lo32 (hi32 (f p))) = mslT f 1 1024 p r ∧ (1024 : ℕ) = mwT 1 1024 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩ <;>
  simp only [mvT, mval, mcpT, mcp, mcnT, mcn, mslT, msl, show mwc 1 1024 = 0 from rfl, show mw1 1 1024 = 1024 from rfl,
    show mw2 1 1024 = 0 from rfl, Nat.mul_eq, Nat.add_eq, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
theorem z2_vals (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U e0 lam p r : ℕ) :
    mvT top bk f L U 2 lam p r = Nat.add (Nat.mul (Nat.sub 1024 lam) (lb top bk L U)) (Nat.mul lam (lo32 (f p))) ∧
    Nat.mul (Nat.mul lam (Nat.sub (hi32 (hi32 (f p))) 2000000000)) (Nat.sub p e0) = mcpT f e0 2 lam p r ∧
    Nat.mul (Nat.mul lam (Nat.sub 2000000000 (hi32 (hi32 (f p))))) (Nat.sub p e0) = mcnT f e0 2 lam p r ∧
    Nat.mul lam (lo32 (hi32 (f p))) = mslT f 2 lam p r ∧ lam = mwT 2 lam := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [mvT, mval, mcpT, mcp, mcnT, mcn, mslT, msl, mwT, show mwc 2 lam = Nat.sub 1024 lam from rfl, show mw1 2 lam = lam from rfl,
    show mw2 2 lam = 0 from rfl, Nat.mul_eq, Nat.add_eq, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
/-- one listed term: every kind's values satisfy the per-term bound when its side condition holds -/
theorem tzv_cov {top : ℕ} {bk : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x))
    {z w o eL eU e0 : ℕ} (he : e0 ≤ eL) {k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {Pr : Prop}
    (hk : ∀ mv cp cn sl mw ok o', (ok ≠ 0 → TBnd top bk eL eU e0 mv cp cn sl mw) → k mv cp cn sl mw ok o' ≠ 0 → Pr)
    (h : tzv top bk pb z w o eL eU e0 k ≠ 0) : Pr := by
  unfold tzv at h
  cases h1 : Nat.beq z 1
  · rw [h1] at h
    cases h3 : Nat.beq z 3
    · rw [h3] at h
      cases h0 : Nat.beq z 0
      · rw [h0] at h
        cases h2 : Nat.beq z 2
        · -- z ≥ 4: lam × tangent, the kind-2 term without its constant part
          rw [h2] at h
          simp only [forceT_eq] at h
          refine hk _ _ _ _ _ _ _ (fun hok => ?_) h
          obtain ⟨hl, hv⟩ := brec_ok hok
          have hz := z2_vals top bk (tf pb) eL (uc eL eU) e0 (Nat.land (Nat.shiftRight w (Nat.add o 7)) 1023)
            (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127)) 0
          exact tbnd_of hlb hpt he (mokI_2 0 hl (ivIn_of2 hv)) (by rw [hz.1]; exact Nat.le_add_left _ _)
            hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
        · -- z = 2: (1024 − lam) lb + lam tangent
          rw [h2] at h
          simp only [forceT_eq] at h
          refine hk _ _ _ _ _ _ _ (fun hok => ?_) h
          obtain ⟨hl, hv⟩ := brec_ok hok
          have hz := z2_vals top bk (tf pb) eL (uc eL eU) e0 (Nat.land (Nat.shiftRight w (Nat.add o 7)) 1023)
            (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127)) 0
          exact tbnd_of hlb hpt he (mokI_2 0 hl (ivIn_of2 hv)) (by rw [hz.1, lbF_eq]; try exact le_refl _)
            hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
      · -- z = 0: 1024 lb
        rw [h0] at h
        dsimp only at h
        refine hk _ _ _ _ _ _ _ (fun _ => ?_) h
        have hz := z0_vals top bk (tf pb) eL (uc eL eU) e0
        exact tbnd_of hlb hpt he (mokI_0 pb eL eU) (by rw [hz.1, lbF_eq]; try exact le_refl _) hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2
    · -- z = 3: (1024 − lam) tangent(p) + lam tangent(r)
      rw [h3] at h
      simp only [forceT_eq] at h
      refine hk _ _ _ _ _ _ _ (fun hok => ?_) h
      obtain ⟨hl, hv⟩ := brec_ok hok
      obtain ⟨hvp, hv⟩ := brec_ok hv
      have hvp' : ivIn (pb (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127))) eL eU (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127)) = true := by
        rw [← ivIn2_eq]; exact hvp
      refine tbnd_of hlb hpt he (mokI_3 hl hvp' (ivIn_of2 hv)) ?_ rfl rfl rfl rfl
      simp only [mvT, mval, show mwc 3 (Nat.land (Nat.shiftRight w (Nat.add o 14)) 1023) = 0 from rfl, Nat.mul_eq, Nat.add_eq, Nat.zero_mul,
        Nat.zero_add, mw1, mw2, Nat.sub_eq, tf]
      exact le_refl _
  · -- z = 1: 1024 tangent
    rw [h1] at h
    simp only [forceT_eq] at h
    refine hk _ _ _ _ _ _ _ (fun hok => ?_) h
    have hz := z1_vals top bk (tf pb) eL (uc eL eU) e0 (gptQG 3 eL eU (Nat.land (Nat.shiftRight w o) 127)) 0
    exact tbnd_of hlb hpt he (mokI_1 0 (ivIn_of2 hok)) (by rw [hz.1]; try exact le_refl _) hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2'''

SOUND_INV = r'''/-- the fold invariant after the first `N` terms: the listed ones among them are bounded by `Σ_{n<N} a_n wfun` -/
def ZInv (s : St) (g : ℕ → ℝ) (N : ℕ) (t : TZ) : Prop :=
  t.ok ≠ 0 → ∃ D : ℕ → ℝ, (∀ r < @Q@, ((zy t r : ℕ) : ℝ) - 2000000000 * ((zx t r : ℕ) : ℝ) ≤ 1000000000 * D r) ∧
    32768 * (t.CV : ℝ) + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
      + 10 * (t.CP : ℝ) - 10 * (t.CN : ℝ)
      ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range N, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
theorem ZInv_zero (s : St) (g : ℕ → ℝ) : ZInv s g 0 ⟨1, @ZEROS@⟩ := by
  intro _
  refine ⟨fun _ => 0, fun r hr => ?_, ?_⟩
  · interval_cases r <;> simp [zx, zy]
  · simp
/-- an unlisted term: its `a_n wfun ≥ 0` only loosens the bound -/
theorem ZInv_skip {s : St} {g : ℕ → ℝ} {n : ℕ} {t : TZ} (h : ZInv s g n t) : ZInv s g (n + 1) t := by
  intro hne
  obtain ⟨D, h1, h2⟩ := h hne
  refine ⟨D, h1, ?_⟩
  rw [Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n]
  have : (0 : ℝ) ≤ ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)) := mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _)
  linarith
theorem brec_inr_cast (x y r i j : ℕ) :
    ((Bool.rec (motive := fun _ => ℕ) x (Nat.add x y) (inr r i j) : ℕ) : ℝ) = (x : ℝ) + if i ≤ r ∧ r < j then (y : ℝ) else 0 := by
  by_cases h : i ≤ r ∧ r < j
  · rw [show inr r i j = true from (inr_true r i j).mpr h, if_pos h]; simp [Nat.add_eq]
  · rw [show inr r i j = false from Bool.eq_false_iff.mpr fun e => h ((inr_true r i j).mp e), if_neg h]; simp
/-- a listed term: the per-term bound added to the invariant, its slope weight to the gaps it spans -/
theorem ZInv_add {s : St} {g : ℕ → ℝ} {n i j a e0 : ℕ} {t t' : TZ} {ok mv cp cn sl mw : ℕ} (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a) (h0 : eL0 TS (toCl s) n = e0)
    (hinv : ZInv s g n t)
    (htb : ok ≠ 0 → ∃ D : ℝ, (sl : ℝ) - 2000000000 * (mw : ℝ) ≤ 1000000000 * D ∧
       32768 * (mv : ℝ) + 327680000000000 * (D * (gsum g i j - (e0 : ℝ) / 32768)) + 10 * (cp : ℝ) - 10 * (cn : ℝ)
         ≤ 327680000000000 * 1024 * wfun (gsum g i j))
    (hok : t'.ok = Nat.mul t.ok ok) (hcv : t'.CV = Nat.add t.CV (Nat.mul a mv)) (hcp : t'.CP = Nat.add t.CP (Nat.mul a cp))
    (hcn : t'.CN = Nat.add t.CN (Nat.mul a cn))
    (hx : ∀ r < @Q@, zx t' r = Bool.rec (motive := fun _ => ℕ) (zx t r) (Nat.add (zx t r) (Nat.mul a mw)) (inr r i j))
    (hy : ∀ r < @Q@, zy t' r = Bool.rec (motive := fun _ => ℕ) (zy t r) (Nat.add (zy t r) (Nat.mul a sl)) (inr r i j)) :
    ZInv s g (n + 1) t' := by
  intro hne
  rw [hok] at hne
  have h1 : t.ok ≠ 0 := fun e => hne (by rw [e]; exact Nat.zero_mul _)
  have h2 : ok ≠ 0 := fun e => hne (by rw [e]; exact Nat.mul_zero _)
  obtain ⟨D, hD1, hD2⟩ := hinv h1
  obtain ⟨Dn, hn1, hn2⟩ := htb h2
  obtain ⟨hij, hjQ, -⟩ := hTS n hn
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  refine ⟨fun r => D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0, fun r hr => ?_, ?_⟩
  · rw [hx r hr, hy r hr, brec_inr_cast, brec_inr_cast]
    have := hD1 r hr
    dsimp only
    split_ifs with hrr
    · simp only [Nat.mul_eq]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hn1 ha0]
    · simpa using this
  · have hsp : ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = (a : ℝ) * (Dn * (gsum g i j - (e0 : ℝ) / 32768)) := by
      rw [← h0, ← hi, ← hj, span_eq (Q := @Q@) g hij.le hjQ, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      split_ifs <;> ring
    have e : ∑ r ∈ Finset.range @Q@, (D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
          + ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; ring
    rw [e, hsp, Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n, ha, hi, hj, hcv, hcp, hcn]
    simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hn2 ha0]'''

SOUND_STEP = r'''theorem tzG_cov {top : ℕ} {bk : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x))
    {s : St} {g : ℕ → ℝ} (hg : InCell @Q@ PR (toCl s) g) {i j a eLx eUx e0x n m w o : ℕ} {t : TZ} {k : ℕ → TZ → ℕ} {Pr : Prop}
    (h : tzG top bk pb i j a eLx eUx e0x n m w o t k ≠ 0) (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a)
    (hL : eL TS (toCl s) n = eLx) (hU : eU TS (toCl s) n = eUx) (h0 : eL0 TS (toCl s) n = e0x)
    (hinv : ZInv s g n t) (hk : ∀ o' t', ZInv s g (n + 1) t' → k o' t' ≠ 0 → Pr) : Pr := by
  obtain ⟨hr0, hr1, hr2⟩ := term_range hPR hTS hg hn
  rw [hL, h0] at hr0
  rw [hL, hi, hj] at hr1
  rw [hU, hi, hj] at hr2
  unfold tzG at h
  cases hb : Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1
  · rw [hb] at h
    exact hk _ _ (ZInv_skip hinv) h
  · rw [hb] at h
    simp only [forceR_eq] at h
    refine tzv_cov hlb hpt hr0 (fun mv cp cn sl mw ok o' htb hk' => hk _ _ ?_ hk') h
    refine ZInv_add hn hi hj ha h0 hinv (fun hok => htb hok _ hr1 hr2) rfl rfl rfl rfl ?_ ?_
    · intro r hr; interval_cases r <;> rfl
    · intro r hr; interval_cases r <;> rfl'''

SOUND_FIN = r'''def zu (s : St) (r : ℕ) : ℕ := (toCl s).U.getD r 0
def zl (s : St) (r : ℕ) : ℕ := (toCl s).L.getD r 0
def zp (y : YA) (r : ℕ) : ℕ := [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.P8].getD r 0
def zs (y : YA) (r : ℕ) : ℕ := [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.S8].getD r 0
/-- `zchk` with its sums as `isum` over the gaps (the same term up to unfolding) -/
def zchkG (s : St) (t : TZ) (y : YA) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add t.CN y.Cp)
      (isum (fun r => Nat.mul (Nat.sub (zu s r) (zl s r)) (Nat.sub (Nat.add (Nat.mul 2000000000 (zx t r)) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zy t r)) (zs y r)))) @Q@))))
      (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (BS.getD r 0) (zl s r)) @Q@)) (Nat.mul 32768 t.CV))
        (Nat.mul 10 (Nat.add t.CP y.Cm))))
    (Bool.rec (motive := fun _ => Bool) false (iall (fun r => Nat.ble (zl s r) (zu s r)) @Q@) (Nat.ble 1 t.ok))
theorem zchk_eq (s : St) (t : TZ) (y : YA) : zchk s t y = zchkG s t y := rfl
theorem zfin_ok {s : St} {g : ℕ → ℝ} (hg : InCell @Q@ PR (toCl s) g) (hle : g 0 ≤ g (@Q@ - 1)) {t : TZ} {y : YA}
    (hinv : ZInv s g @NT@ t) (hY : MulOKH s y) (h : zfin s t y ≠ 0) : (cN : ℝ) ≤ Fg @Q@ BS TS g := by
  have hc : zchkG s t y = true := by rw [← zchk_eq]; exact brec_ne h
  unfold zchkG at hc
  obtain ⟨hpre, hmain⟩ := brec_and hc
  obtain ⟨hok, hbox⟩ := brec_and hpre
  have hbox' := iall_true hbox
  have hok' : t.ok ≠ 0 := by have := Nat.le_of_ble_eq_true hok; omega
  obtain ⟨D, hD1, hD2⟩ := hinv hok'
  rw [Nat.ble_eq] at hmain
  set e : ℕ → ℝ := fun r => g r - ((zl s r : ℕ) : ℝ) / 32768 with he
  -- per gap: the slope charge bounds the slope from below
  have S3 : ∀ r ∈ Finset.range @Q@, -(10 * (((Nat.sub (Nat.add (Nat.mul 2000000000 (zx t r)) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zy t r)) (zs y r)) : ℕ) : ℝ) * ((zu s r - zl s r : ℕ) : ℝ)))
      ≤ 327680000000000 * ((1024 * ((BS.getD r 0 : ℕ) : ℝ) + D r - (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) / 1000000000) * e r) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hlu : zl s r ≤ zu s r := Nat.le_of_ble_eq_true (hbox' r hr')
    have hgr := hg.1 r hr'
    have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
    rw [hSCe] at hgr
    refine gap_lo (natsub_nonneg _ _) ?_ (by simp only [he, zl]; linarith [hgr.1]) ?_
    · refine neg_natsub_le ?_
      simp only [Nat.add_eq, Nat.mul_eq]
      push_cast
      have := hD1 r hr'
      linarith
    · rw [Nat.cast_sub hlu, sub_div]; simp only [he, zl, zu] at hgr ⊢; linarith [hgr.2]
  have S4 := hY g hg hle
  have S4' : ∑ r ∈ Finset.range @Q@, (((([y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.P8] : List ℕ).getD r 0 : ℕ) : ℝ)
        - (([y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.S8] : List ℕ).getD r 0 : ℕ)) * (32768 * g r - ((toCl s).L.getD r 0 : ℕ))
      = 32768 * ∑ r ∈ Finset.range @Q@, (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) * e r := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; simp only [he, zp, zs, zl]; ring
  have S5 := (Nat.cast_le (α := ℝ)).mpr hmain
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at S5
  push_cast at S5
  rw [isum_cast, isum_cast] at S5
  push_cast at S5
  have S3s := Finset.sum_le_sum S3
  have e1 : ∑ r ∈ Finset.range @Q@, 327680000000000 * ((1024 * ((BS.getD r 0 : ℕ) : ℝ) + D r
        - (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) / 1000000000) * e r)
      = 327680000000000 * 1024 * ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * e r
        + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * e r
        - 327680 * ∑ r ∈ Finset.range @Q@, (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) * e r := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have e2 : ∑ r ∈ Finset.range @Q@, -(10 * (((Nat.sub (Nat.add (Nat.mul 2000000000 (zx t r)) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zy t r)) (zs y r)) : ℕ) : ℝ) * ((zu s r - zl s r : ℕ) : ℝ)))
      = -(10 * ∑ r ∈ Finset.range @Q@, ((zu s r - zl s r : ℕ) : ℝ) * ((Nat.sub (Nat.add (Nat.mul 2000000000 (zx t r)) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zy t r)) (zs y r)) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _; ring
  have e3 : ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * g r
      = (∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * ((zl s r : ℕ) : ℝ)) / 32768
        + ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * e r := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
  have e4 : ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) = ∑ r ∈ Finset.range @Q@, D r * e r := rfl
  rw [e1, e2] at S3s
  rw [S4'] at S4
  rw [e4] at hD2
  unfold Fg
  rw [e3, show TS.length = @NT@ from rfl]
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at S3s
  push_cast at S3s
  linarith [S3s, S4, S5, hD2]'''


def zeros(Q):
    return ', '.join(['0'] * (3 + 2 * Q))


def full_text(Q, TS, BS, pt='f', proofs=True, spec=False):
    t = text(Q, TS, BS, pt).replace('@ZEROS@', zeros(Q))
    if spec:
        t = specialise(t, Q, TS)
    if not proofs:
        t = strip_proofs(t)
    return t


def strip_proofs(t):
    '''BENCH ONLY: drop theorems and Prop definitions (kernel code only)'''
    out = []
    skip = False
    for l in t.split('\n'):
        if l.startswith('/--') and l.rstrip().endswith('-/'):
            continue
        if l.startswith(('theorem ', 'def TBnd', 'def ZInv', 'def zu ', 'def zl ', 'def zp ', 'def zs ', 'def zchkG')):
            skip = True
            continue
        if skip and (l.startswith((' ', '\t')) or l == ''):
            continue
        skip = False
        out.append(l)
    return '\n'.join(out) + '\n'


def specialise(t, Q, TS):
    '''BENCH VARIANT: one tzG copy per term with its gap updates written out (no inr tests)'''
    import re
    i0 = t.index('def tzG ')
    i1 = min(x for x in (t.find('\ntheorem', i0), t.find('\ndef zchk', i0)) if x > 0)
    body = t[i0:i1]
    defs = []
    for n, (i, j, a, k) in enumerate(TS):
        b = body.replace('def tzG ', 'def tzG%d ' % n)
        for r in range(Q):
            if 't.V0' in b:
                old = 'Bool.rec (motive := fun _ => ℕ) t.V%d (Nat.sub (Nat.add t.V%d (Nat.mul a (Nat.mul 2000000000 mw))) (Nat.mul a sl)) (inr %d i j)' % (r, r, r)
                new = ('Nat.sub (Nat.add t.V%d (Nat.mul a (Nat.mul 2000000000 mw))) (Nat.mul a sl)' % r) if i <= r < j else 't.V%d' % r
                assert old in b
                b = b.replace(old, new)
                continue
            for f, v in (('X', 'mw'), ('Y', 'sl')):
                old = 'Bool.rec (motive := fun _ => ℕ) t.%s%d (Nat.add t.%s%d (Nat.mul a %s)) (inr %d i j)' % (f, r, f, r, v, r)
                new = ('Nat.add t.%s%d (Nat.mul a %s)' % (f, r, v)) if i <= r < j else 't.%s%d' % (f, r)
                assert old in b
                b = b.replace(old, new)
        defs.append(b)
    t = t[:i1] + '\n' + '\n'.join(defs) + t[i1:]
    for n in range(len(TS)):
        t = re.sub(r'(\n  tzG) (top bk \S+ \d+ \d+ a\d+ .*? %d m w )' % n, lambda mo: mo.group(1) + '%d ' % n + mo.group(2), t, count=1)
    return t


KV = 1 << 160          # offset of the merged per-gap slope sums V_r (exactness only; soundness holds for any value)


def kernel_m(Q, TS, BS, pt='f'):
    """Kernel code of the merged-accumulator Z check: record (CVP, CN, V_0 .. V_{Q-1}),
    CVP = sum a (32768 mv + 10 cp), CN = sum a cn, V_r = KV + sum (a 2e9 mw) - (a sl) (truncated per step);
    a failed side condition ends the leaf (0)."""
    NT = len(TS)
    B = 'Bool.rec (motive := fun _ => ℕ)'
    BB = 'Bool.rec (motive := fun _ => Bool)'
    t = text(Q, TS, BS, pt)
    i0 = t.index('/-- the values of one listed term')
    i1 = t.index('/-- the per-term bound')
    tzv = t[i0:i1]
    L = ['/-! ###### sparse leaf check Z: the leaf lists only its nonzero terms (presence mask), folded into accumulators ###### -/']
    L.append('structure TZ where\n  (CVP CN %s : ℕ)' % ' '.join('V%d' % r for r in range(Q)))
    L.append('/-- the offset of the merged per-gap slope sums (it keeps them from truncating; soundness does not need it) -/')
    L.append('def KVz : ℕ := %d' % KV)
    L.append(tzv.rstrip('\n'))
    upd = ', '.join('%s t.V%d (Nat.sub (Nat.add t.V%d (Nat.mul a (Nat.mul 2000000000 mw))) (Nat.mul a sl)) (inr %d i j)' % (B, r, r, r) for r in range(Q))
    L.append('/-- term `n` of the chain: listed (mask bit `n`) -> decode, check and accumulate; unlisted -> nothing -/')
    L.append('def tzG (top : ℕ) (bk : ℕ → ℕ) (%s : ℕ → ℕ) (i j a eL eU e0 n m w o : ℕ) (t : TZ) (k : ℕ → TZ → ℕ) : ℕ :=' % pt)
    L.append('  %s (k o t)\n    (forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>\n'
             '     tzv top bk %s (Nat.land (Nat.shiftRight w o) 7) w (Nat.add o 3) eL eU e0 fun mv cp cn sl mw ok o\' =>\n'
             '     %s (k o\' ⟨Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))), Nat.add t.CN (Nat.mul a cn),\n'
             '       %s⟩) 0 (Nat.beq ok 0))\n    (Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1)' % (B, pt, B, upd))
    ng = nest_add0(['(Nat.mul (Nat.sub s.u%d s.l%d) (Nat.sub (Nat.add t.V%d y.P%d) (Nat.add (Nat.add (Nat.mul 1024000000000 %d) y.S%d) %s)))'
                    % (r, r, r, r, BS[r], r, 'KVz') for r in range(Q)])
    bl = nest_add0(['(Nat.mul %d s.l%d)' % (BS[r], r) for r in range(Q)])
    box = 'true'
    for r in range(Q):
        box = '(%s false (Nat.ble s.l%d s.u%d) %s)' % (BB, r, r, box)
    chk = ('%s false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add t.CN y.Cp) %s)))\n'
           '      (Nat.add (Nat.add (Nat.mul 10240000000000 %s) t.CVP) (Nat.mul 10 y.Cm)))\n    %s' % (BB, ng, bl, box))
    L.append('def zchk (s : St) (t : TZ) (y : YA) : Bool :=\n  ' + chk)
    L.append('def zfin (s : St) (t : TZ) (y : YA) : ℕ := %s 0 y.o (zchk s t y)' % B)
    j0 = t.index('def mleafZ')
    j1 = t.index('theorem mleafZ_ok')
    ml = t[j0:j1]
    ml = ml.replace('⟨1, %s⟩' % ', '.join(['0'] * (3 + 2 * Q)), '⟨0, 0, %s⟩' % ', '.join(['KVz'] * Q))
    L.append(ml.rstrip('\n'))
    return '\n'.join(L) + '\n'


SOUND_INV_M = r'''/-- the per-gap merged slope sums of a record, as a function of the gap -/
def zv (t : TZ) (r : ℕ) : ℕ := [@VS@].getD r 0
/-- the fold invariant after the first `N` terms: the listed ones among them are bounded by `Σ_{n<N} a_n wfun`;
`KV − V_r` is at most the gap's summed slope claims minus `2·10⁹` times its summed slope weights -/
def ZInv (s : St) (g : ℕ → ℝ) (N : ℕ) (t : TZ) : Prop :=
  ∃ D : ℕ → ℝ, (∀ r < @Q@, (@KV@ : ℝ) - ((zv t r : ℕ) : ℝ) ≤ 1000000000 * D r) ∧
    (t.CVP : ℝ) + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) - 10 * (t.CN : ℝ)
      ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range N, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
theorem ZInv_zero (s : St) (g : ℕ → ℝ) : ZInv s g 0 ⟨0, 0, @VS0@⟩ := by
  refine ⟨fun _ => 0, fun r hr => ?_, ?_⟩
  · interval_cases r <;> simp [zv]
  · simp
/-- an unlisted term: its `a_n wfun ≥ 0` only loosens the bound -/
theorem ZInv_skip {s : St} {g : ℕ → ℝ} {n : ℕ} {t : TZ} (h : ZInv s g n t) : ZInv s g (n + 1) t := by
  obtain ⟨D, h1, h2⟩ := h
  refine ⟨D, h1, ?_⟩
  rw [Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n]
  have : (0 : ℝ) ≤ ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)) := mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _)
  linarith
theorem brec_inr_sub (x y z r i j : ℕ) :
    (x : ℝ) + (if i ≤ r ∧ r < j then (y : ℝ) - z else 0) ≤ ((Bool.rec (motive := fun _ => ℕ) x (Nat.sub (Nat.add x y) z) (inr r i j) : ℕ) : ℝ) := by
  by_cases h : i ≤ r ∧ r < j
  · rw [show inr r i j = true from (inr_true r i j).mpr h, if_pos h]
    have := natsub_ge (x + y) z
    simp only [Nat.sub_eq, Nat.add_eq]; push_cast at this ⊢; linarith
  · rw [show inr r i j = false from Bool.eq_false_iff.mpr fun e => h ((inr_true r i j).mp e), if_neg h]; simp
/-- a listed term: the per-term bound added to the invariant, its slope weight to the gaps it spans -/
theorem ZInv_add {s : St} {g : ℕ → ℝ} {n i j a e0 : ℕ} {t t' : TZ} {mv cp cn sl mw : ℕ} (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a) (h0 : eL0 TS (toCl s) n = e0)
    (hinv : ZInv s g n t)
    (htb : ∃ D : ℝ, (sl : ℝ) - 2000000000 * (mw : ℝ) ≤ 1000000000 * D ∧
       32768 * (mv : ℝ) + 327680000000000 * (D * (gsum g i j - (e0 : ℝ) / 32768)) + 10 * (cp : ℝ) - 10 * (cn : ℝ)
         ≤ 327680000000000 * 1024 * wfun (gsum g i j))
    (hcv : t'.CVP = Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))))
    (hcn : t'.CN = Nat.add t.CN (Nat.mul a cn))
    (hx : ∀ r < @Q@, zv t' r = Bool.rec (motive := fun _ => ℕ) (zv t r) (Nat.sub (Nat.add (zv t r) (Nat.mul a (Nat.mul 2000000000 mw))) (Nat.mul a sl)) (inr r i j)) :
    ZInv s g (n + 1) t' := by
  obtain ⟨D, hD1, hD2⟩ := hinv
  obtain ⟨Dn, hn1, hn2⟩ := htb
  obtain ⟨hij, hjQ, -⟩ := hTS n hn
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  refine ⟨fun r => D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0, fun r hr => ?_, ?_⟩
  · have hv := brec_inr_sub (zv t r) (Nat.mul a (Nat.mul 2000000000 mw)) (Nat.mul a sl) r i j
    rw [← hx r hr] at hv
    have := hD1 r hr
    dsimp only
    split_ifs at hv ⊢ with hrr
    · simp only [Nat.mul_eq] at hv
      push_cast at hv
      nlinarith [mul_le_mul_of_nonneg_left hn1 ha0]
    · linarith
  · have hsp : ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = (a : ℝ) * (Dn * (gsum g i j - (e0 : ℝ) / 32768)) := by
      rw [← h0, ← hi, ← hj, span_eq (Q := @Q@) g hij.le hjQ, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      split_ifs <;> ring
    have e : ∑ r ∈ Finset.range @Q@, (D r + if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
        = ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768)
          + ∑ r ∈ Finset.range @Q@, (if i ≤ r ∧ r < j then (a : ℝ) * Dn else 0) * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; ring
    rw [e, hsp, Finset.sum_range_succ (fun k => ((tA TS k : ℕ) : ℝ) * wfun (gsum g (tI TS k) (tJ TS k))) n, ha, hi, hj, hcv, hcn]
    simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hn2 ha0]'''

SOUND_STEP_M = r'''theorem tzG_cov {top : ℕ} {bk : ℕ → ℕ} {pb : ℕ → ℕ} (hlb : LBSound top bk) (hpt : ∀ x, PVI x (pb x))
    {s : St} {g : ℕ → ℝ} (hg : InCell @Q@ PR (toCl s) g) {i j a eLx eUx e0x n m w o : ℕ} {t : TZ} {k : ℕ → TZ → ℕ} {Pr : Prop}
    (h : tzG top bk pb i j a eLx eUx e0x n m w o t k ≠ 0) (hn : n < TS.length)
    (hi : tI TS n = i) (hj : tJ TS n = j) (ha : tA TS n = a)
    (hL : eL TS (toCl s) n = eLx) (hU : eU TS (toCl s) n = eUx) (h0 : eL0 TS (toCl s) n = e0x)
    (hinv : ZInv s g n t) (hk : ∀ o' t', ZInv s g (n + 1) t' → k o' t' ≠ 0 → Pr) : Pr := by
  obtain ⟨hr0, hr1, hr2⟩ := term_range hPR hTS hg hn
  rw [hL, h0] at hr0
  rw [hL, hi, hj] at hr1
  rw [hU, hi, hj] at hr2
  unfold tzG at h
  cases hb : Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1
  · rw [hb] at h
    exact hk _ _ (ZInv_skip hinv) h
  · rw [hb] at h
    simp only [forceR_eq] at h
    refine tzv_cov hlb hpt hr0 (fun mv cp cn sl mw ok o' htb hk' => ?_) h
    cases hz : Nat.beq ok 0
    · rw [hz] at hk'
      have hok : ok ≠ 0 := fun e => by rw [e] at hz; exact absurd hz (by decide)
      refine hk _ _ ?_ hk'
      refine ZInv_add hn hi hj ha h0 hinv (htb hok _ hr1 hr2) rfl rfl ?_
      intro r hr; interval_cases r <;> rfl
    · rw [hz] at hk'; exact absurd rfl hk'
'''

SOUND_FIN_M = r'''def zu (s : St) (r : ℕ) : ℕ := (toCl s).U.getD r 0
def zl (s : St) (r : ℕ) : ℕ := (toCl s).L.getD r 0
def zp (y : YA) (r : ℕ) : ℕ := [@PS@].getD r 0
def zs (y : YA) (r : ℕ) : ℕ := [@SS@].getD r 0
/-- `zchk` with its sums as `isum` / `iall` over the gaps (the same term up to unfolding) -/
def zchkG (s : St) (t : TZ) (y : YA) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add t.CN y.Cp)
      (isum (fun r => Nat.mul (Nat.sub (zu s r) (zl s r)) (Nat.sub (Nat.add (zv t r) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zs y r)) @KV@))) @Q@))))
      (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (BS.getD r 0) (zl s r)) @Q@)) t.CVP)
        (Nat.mul 10 y.Cm)))
    (iall (fun r => Nat.ble (zl s r) (zu s r)) @Q@)
theorem zchk_eq (s : St) (t : TZ) (y : YA) : zchk s t y = zchkG s t y := rfl
theorem zfin_ok {s : St} {g : ℕ → ℝ} (hg : InCell @Q@ PR (toCl s) g) (hle : g 0 ≤ g (@Q@ - 1)) {t : TZ} {y : YA}
    (hinv : ZInv s g @NT@ t) (hY : MulOKH s y) (h : zfin s t y ≠ 0) : (cN : ℝ) ≤ Fg @Q@ BS TS g := by
  have hc : zchkG s t y = true := by rw [← zchk_eq]; exact brec_ne h
  unfold zchkG at hc
  obtain ⟨hbox, hmain⟩ := brec_and hc
  have hbox' := iall_true hbox
  obtain ⟨D, hD1, hD2⟩ := hinv
  rw [Nat.ble_eq] at hmain
  set e : ℕ → ℝ := fun r => g r - ((zl s r : ℕ) : ℝ) / 32768 with he
  have S3 : ∀ r ∈ Finset.range @Q@, -(10 * (((Nat.sub (Nat.add (zv t r) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zs y r)) @KV@) : ℕ) : ℝ) * ((zu s r - zl s r : ℕ) : ℝ)))
      ≤ 327680000000000 * ((1024 * ((BS.getD r 0 : ℕ) : ℝ) + D r - (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) / 1000000000) * e r) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hlu : zl s r ≤ zu s r := Nat.le_of_ble_eq_true (hbox' r hr')
    have hgr := hg.1 r hr'
    have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
    rw [hSCe] at hgr
    refine gap_lo (natsub_nonneg _ _) ?_ (by simp only [he, zl]; linarith [hgr.1]) ?_
    · refine neg_natsub_le ?_
      simp only [Nat.add_eq, Nat.mul_eq]
      push_cast
      have := hD1 r hr'
      linarith
    · rw [Nat.cast_sub hlu, sub_div]; simp only [he, zl, zu] at hgr ⊢; linarith [hgr.2]
  have S4 := hY g hg hle
  have S4' : ∑ r ∈ Finset.range @Q@, (((([@PS@] : List ℕ).getD r 0 : ℕ) : ℝ)
        - (([@SS@] : List ℕ).getD r 0 : ℕ)) * (32768 * g r - ((toCl s).L.getD r 0 : ℕ))
      = 32768 * ∑ r ∈ Finset.range @Q@, (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) * e r := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; simp only [he, zp, zs, zl]; ring
  have S5 := (Nat.cast_le (α := ℝ)).mpr hmain
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at S5
  push_cast at S5
  rw [isum_cast, isum_cast] at S5
  push_cast at S5
  have S3s := Finset.sum_le_sum S3
  have e1 : ∑ r ∈ Finset.range @Q@, 327680000000000 * ((1024 * ((BS.getD r 0 : ℕ) : ℝ) + D r
        - (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) / 1000000000) * e r)
      = 327680000000000 * 1024 * ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * e r
        + 327680000000000 * ∑ r ∈ Finset.range @Q@, D r * e r
        - 327680 * ∑ r ∈ Finset.range @Q@, (((zp y r : ℕ) : ℝ) - (zs y r : ℕ)) * e r := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have e2 : ∑ r ∈ Finset.range @Q@, -(10 * (((Nat.sub (Nat.add (zv t r) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zs y r)) @KV@) : ℕ) : ℝ) * ((zu s r - zl s r : ℕ) : ℝ)))
      = -(10 * ∑ r ∈ Finset.range @Q@, ((zu s r - zl s r : ℕ) : ℝ) * ((Nat.sub (Nat.add (zv t r) (zp y r))
        (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (zs y r)) @KV@) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _; ring
  have e3 : ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * g r
      = (∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * ((zl s r : ℕ) : ℝ)) / 32768
        + ∑ r ∈ Finset.range @Q@, ((BS.getD r 0 : ℕ) : ℝ) * e r := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
  have e4 : ∑ r ∈ Finset.range @Q@, D r * (g r - (((toCl s).L.getD r 0 : ℕ) : ℝ) / 32768) = ∑ r ∈ Finset.range @Q@, D r * e r := rfl
  rw [e1, e2] at S3s
  rw [S4'] at S4
  rw [e4] at hD2
  unfold Fg
  rw [e3, show TS.length = @NT@ from rfl]
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq] at S3s
  push_cast at S3s
  linarith [S3s, S4, S5, hD2]'''


def text_m(Q, TS, BS, pt='f', proofs=True):
    """the merged-accumulator Z check with its soundness proofs"""
    NT = len(TS)
    k = kernel_m(Q, TS, BS, pt)
    t = text(Q, TS, BS, pt)
    st0 = t.index('/-- the per-term bound')
    st1 = t.index('/-- the per-gap sums of a record')
    term = t[st0:st1].rstrip('\n')
    rep = {'@Q@': str(Q), '@NT@': str(NT), '@KV@': 'KVz', '@VS@': ', '.join('t.V%d' % r for r in range(Q)),
           '@VS0@': ', '.join(['KVz'] * Q), '@PS@': ', '.join('y.P%d' % r for r in range(Q)),
           '@SS@': ', '.join('y.S%d' % r for r in range(Q))}

    def R(x):
        for a, b in rep.items():
            x = x.replace(a, b)
        return x
    # order: TZ, tzv | term proofs | invariant | tzG | step proof | zchk, zfin | final proof | mleafZ | mleafZ_ok
    a0 = k.index('/-- term `n` of the chain')
    a1 = k.index('def zchk')
    a2 = k.index('def mleafZ')
    j1 = t.index('theorem mleafZ_ok')
    out = k[:a0] + term + '\n' + R(SOUND_INV_M) + '\n' + k[a0:a1] + R(SOUND_STEP_M) + '\n' + k[a1:a2] + R(SOUND_FIN_M) + '\n' + k[a2:] + t[j1:]
    if not proofs:
        out = strip_proofs(out)
    return out
