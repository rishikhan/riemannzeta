# Nine-point certificate checker of attempt-031: data model and soundness logic

This file describes the finite certificate checker in the riemannzeta.fun attempt-031 proof
(Samuel Lavery's team, Apache-2.0), file `Solution.lean`, sha256
`0adbf8e04b4bc3db5dae886dfe003dc4fb9b9acd6d998a43f2a5603cba515f32`, 17161 lines. Line numbers
refer to that file. `replay.py` in this directory re-implements every `decide +kernel` check
in exact arithmetic; `python -I replay.py Solution.lean` runs all of them.

## Contents

1. [Attribution](#1-attribution)
2. [The statement the certificate proves](#2-the-statement-the-certificate-proves)
3. [Scalings and global constants](#3-scalings-and-global-constants)
4. [Packed numerals and dispatch tables](#4-packed-numerals-and-dispatch-tables)
5. [The cell evaluator CellA](#5-the-cell-evaluator-cella)
6. [The `decide +kernel` checks, in dependency order](#6-the-decide-kernel-checks-in-dependency-order)
7. [Polytope cells and the walk](#7-polytope-cells-and-the-walk)
8. [The leaf inequality](#8-the-leaf-inequality)
9. [Covering the orthant](#9-covering-the-orthant)
10. [Window, weight and structural dependence](#10-window-weight-and-structural-dependence)
11. [Report on attempt-031's certificate](#11-report-on-attempt-031s-certificate)
12. [Generator requirements](#12-generator-requirements)

## 1. Attribution

The Lean header (lines 1 to 280) and the module notices name these authors for the checker's
components. The file as a whole is Copyright (c) 2026 Samuel Lavery (github: samlavery),
Apache-2.0, built on his attempt-012 to attempt-016 submissions and on R. Arun Chandru's
"master-of-puppets" files. "bridge-port", "am-cert", "mvt-engine", "window-scope" and "the lead"
are members of Samuel Lavery's agent team.

| Component | Lean location | Authors named in the header |
|---|---|---|
| `zfNat64` radix-64 numeral packing | `ZeroForgePackedNat`, lines 107 to 179 | Zero Forge / @zkvoxels (GitHub cafeai), critical-strip-exclusion-attempt-1, Apache-2.0 |
| Cell evaluator `AMW.G.CellA`, interval arithmetic `SZ`/`IV` | lines 5536 to 7761 | mechanical extraction of Samuel Lavery's attempt016; engine speed-ups in CEngine, GFar, GCell from seven-point-optimised-window by typh (Apache-2.0) |
| Window family (ω₀ = √2, ω_j = 2πj, 13 terms) | `AMW.cAMn`, line 288 | AMTOPA, zeta-exact-pressure (MIT); window WL1 from the lead's window search, started from ajp88's W9A2 window (ajp88-w9a2-window-nine-point) |
| Window-dependent declarations (vAM bounds, positive-variation check, profile constants, CE/CJ/FA, matching constants) | lines 288 to 3183, 5860 to 5946 | ajp88's W9A2 declarations, literals regenerated for WL1 by bridge-port |
| Pyramid lower-bound table (`Pyr`) | lines 7862 to 8326 | adapted from five-point-pyramid-2 by typh (Apache-2.0) |
| Derivative pyramid, fast reads (`PyrD`, `lbDrF`, `lbF`, `tcheckZC`, `mcheckGX`) | lines 8329 to 10392 | bridge-port (PCDF, PCDZ) |
| Polytope-cell layer (pair-distance splits, multiplier leaves, minorant leaf, root cover) | `AMW.Cert.PCell`, lines 9196 to 9716 | bridge-port, on the lead's polytope-cell design (PCellCore, PCellGen, PCellLeaf, PCellRoot, PCellT1) |
| Slot lemmas, `mat_gen`, tangent extension | lines 9656 to 10392 | bridge-port, to mvt-engine's specification TZ.md / tz.py |
| Closure splits (`cuB`, `colB`, `rowB`, `cov_splitB`), arbitrary-cut and boundary cuts (`bcutL`) | lines 10395 to 10560, 10011 to 10020 | bridge-port (closure through one point) and mvt-engine (PCellClose, PCellCloseB); boundary-split candidates designed by the lead |
| Precertified tangent intervals (`ivOk`, `ivIn`, `mokI`) | lines 10563 to 10723 | am-cert |
| Fast leaf checker (`dec4QG`, `gptQG`, multiplier tree `ydecS`, fixed-width walk fields) | lines 11527 to 11607, 11949 to 12132 | am-cert (module PCellFast); range-end anchor code 34 by am-cert (PCellDKH) |
| Anchor-variance term, curvature table (`curvatureOk`, `tbOk`, `vbW`, `mcheckW`) | lines 10773 to 11504 | Yuhang Shi, shi-anchor-variance-refinement-2026 (Apache-2.0), adapting Samuel Lavery's `w2_nonneg`; ported to nine points by am-cert (PCellVarW) |
| Instance module `PC9XA` and data module `PC9XAData` | lines 11610 to 14067 | bridge-port's instance layer (amg/genpcell4.py) with mvt-engine's closure walk; data by mvt-engine; certificate thinning and exact floor closure by am-cert |
| Weighted n-point chain, `WCert`, `Fw` | lines 5217 to 5300 | Ainta's weighted n-point refinement, generalised by Samuel Lavery's team (OpethN); Kristian Muri Knausgard's `card_near_le` |
| H_W enclosure (`HW_ge`, line 1982) | lines 1805 to 2034 | R. Arun Chandru (master-of-puppets2/3/4), Yuhang Shi (terminal HW floor), the lead's order-34 closure |

The header also lists edge-window certificates (`PCE5KP`, `PCE6UPC`) and `ready*_cursor`
theorems. Neither occurs in attempt-031: the final chain (`Opeth.AMFinal.actual_dyadic`,
line 16780) uses only `PC9XA`, and long walks are split with cut states (section 7.4).

## 2. The statement the certificate proves

`RiemannFail.cert_AM` (line 14362) states

    ∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W9 g,
    c = cN / SA = 74590093983395854023056456154 / 8388608000000000000000000000000 ≈ 0.0088918321,

with `Fw W g = Σ_r b_r g_r + Σ_{i<j} a_ij w(y_j − y_i)` (line 5223), `y` the prefix sums of `g`,
`w = wfunAM = kfunAM²` (line 531), `kfunAM x = K(x)/K(0)`, `K(x) = ∫_{-1/2}^{1/2} v(t) cos(2πxt) dt`
(`KfunAM`, line 529), `v = vAM = Σ_{j<13} c_j cos(ω_j t)` (line 305). `Fw_W9` (line 14355)
rewrites `Fw W9` as `PC9XA.G` (line 11635), and `Fg_G` (line 11638) identifies `SA · G` with the
checker's `Fg 8 BS TS` (line 9470). The chain then uses `κ = (H_W⁻ − B)/(1 − c)` (`Opeth.AMFinal`, lines 16779 to 16798) with
`B = Σ b_r = 37629197974786539520000000000/SA` (`W9_B`, line 14239).

The chain of theorems from the finite checks to `cert_AM`:

1. `PC9XAData.cert` (line 14065): `∀ g ≥ 0, Pg cN 8 BS TS g`, where `Pg` (line 9473) is
   `cN ≤ Fg g ∨ g 7 < g 0`. It is `cert_of` (line 12239) applied to the root cover data and `run`.
2. `PC9XA_half` (line 14073) and `PC9XA_G_rev` (line 14071, `G` is invariant under reversing the
   gaps, proved by `ring_nf`) remove the `g 7 < g 0` alternative: `PC9XA_cert_full` (line 14083).
3. `cert_AM` rewrites with `Fw_W9`.

The weights must therefore be palindromic (`b_r = b_{7−r}`, `a_ij = a_{8−j,8−i}`); `ring_nf`
fails otherwise. `W9_adm` (line 14350) also needs `a ≥ 0`, `b_r ≥ min_r b_r` (`W9_bmin`, line 14327)
and the span capacity `Σ_{j−i=s} a_ij ≤ 2` for every span `s` (`W9_capacity`, line 14339; the
definition `WCert.Adm` is at line 5231).

## 3. Scalings and global constants

All checks run on natural numbers. The real quantities they bound:

| Name | Value | Meaning | Line |
|---|---|---|---|
| `SC` | 32768 | gap and distance grid: an integer `x` stands for `x/SC` | 5828, 7765 |
| `KB` | 2^20 | key radix (`CellN.key = LN·KB + UN`); all positions are `< KB` (x < 32) | 7766 |
| `SW` | 10^13 | `CellN.WZ / SW ≤ w` | 7767 |
| `U1` | 10^9 | derivative scale: `W1LO/U1 ≤ w′ ≤ W1HI/U1` | 7768 |
| `KU1` | 2·10^9 | offset that keeps `1e9·(w′ + 2)` and `1e9·(2 − w′)` nonnegative | 7769 |
| value fields | `v/10^10 ≤ w` | pyramid entries, point values, `lb` | 7974 (`CS`) |
| `DZ` | 10^15 | fixed-point unit of CellA intervals | 5537 |
| `SA` | 2^23·10^24 | weight scale: real weight = integer/SA | 11634 |
| `cN` | 74590093983395854023056456154 | floor numerator: `c = cN/SA` | 11622 |
| `SIG` | 2^17·10^33 | multiplier quantum: a multiplier is `SIG · (14-bit integer)` | 11623 |
| `BB`, `TB` | 2^42, 2^43 | bias of the closure column and row vectors | 10419, 10421 |
| `VD` | 10^9 | curvature denominator; a table field `f` means `w″ ≥ f·2^19/VD` | 11031 |

Index conventions: the 9 points are `y_0 = 0, y_{i+1} = y_i + g_i`; a cell stores bounds for the 8
gaps `g_r` (`L r`, `U r`) and the 28 non-adjacent pairs `(i, j)`, `j ≥ i + 2` (`A k`, `B k`, bounds
of `y_j − y_i`, in the order of `PR`, line 11624). The 34 weighted terms are `TS` (line 11627):
`(i, j, a_ij·SA, k)` with `k` the index into `PR` (or 0 when `j = i + 1`); pairs (0,2) and (6,8)
have weight 0 and are absent. `BS` (line 11626) holds `b_r·SA`. `SL` (line 11629) maps a slot
`(a, b)`, `a < b ≤ 8`, to a gap index (`< 8`) or `8 + k` (pair k). `ADJ` (line 12237) lists the
`TS` index of each adjacent term.

## 4. Packed numerals and dispatch tables

* `zfNat64 bits "payload"` (macro, line 175; decoder `ZeroForgePackedNat.decode64`, line 146):
  big-endian radix 64 over `A–Z a–z 0–9 + _`, exact bit length checked, at most 65536 bits. The
  macro produces an ordinary numeral, so the kernel sees plain `Nat` literals. attempt-031 has 231
  such literals (`TOP`, `TOPD`, every `BK_j`, `BKD_j`, `WL*_*`, `WMASK`). `replay.py:decode64`
  repeats every check of the macro.
* Dispatch functions: `dsel j m a b = if m ≤ j then b else a`, `dpk j k v = if j = k then v else 0`
  (lines 8927, 8928). `BK j` (line 13320), `BKD j` (line 13591) and `WL r j` (for example line
  13649) are balanced binary trees of `dsel` over the literals `BK_j`, `BKD_j`, `WL r_j`. Missing
  indices return 0.

## 5. The cell evaluator CellA

`AMW.G.CellA` (structure at line 5899) evaluates, for a cell `[LN/SC, UN/SC]`, interval enclosures
of `k`, `k′`, `k″` in units of `1/DZ`. All window literals of the certificate's analytic side enter
here.

* Formula. `kfunAM_eq` (line 6234): for `1 − 2(πx)² ≠ 0`,
  `k(x) = mN/mD + ρ Σ_{j=1}^{12} c_j T_j(x)`, with `mN = cos πx − 2γ πx sin πx`, `mD = 1 − 2(πx)²`,
  `γ = (√2/2) cot(√2/2)` (line 6147), `ρ = (√2/2)/sin(√2/2)`, and
  `T_j(x) = (sinc π(x − j) + sinc π(x + j))/2` (line 6230). The ω₀ = √2 term gives `mN/mD`; it
  depends on the window only through ω₀ (and `c_0 = 1`).
* Arithmetic. `SZ` (line 5556) is a signed integer as a pair of naturals; `IV` (line 5644) is an
  interval of `SZ`; `IV.mul`, `IV.mulc`, `IV.divp` round outward to `1/DZ`.
* Reduction. `k = round(2x)` over the cell (`CellA.k`, line 5902); `side` says whether the cell
  lies right of `k/2`. `T = π|x − k/2|` is enclosed in `[TLZ, TUZ]` (lines 5909, 5910) and must be
  `≤ 1` (`ok`, line 5936); `cos`, `sin`, `sinc`, `sc1`, `sc2` of `T` use degree 10 to 11 Taylor
  polynomials (`cosP` to `s2N`, lines 5841 to 5850) with error `ERRD = 2262000/DZ ≥ 13/5748019200`.
  `CX`, `SX` (lines 5916, 5922) are `cos πx`, `sin πx` from `T` and `k mod 4`.
* Far sum. `FA c n` (line 5940) encloses `Σ_j c_j (−1)^j d^n/dx^n [x/(x² − j²)]`-type sums
  (`farJ`, line 5883) for `n = 0, 1, 2`, using monotonicity of each term on the cell. The list
  `(j, |c_j|·10^9, sign flag)` is `CE` (line 5860) and is unrolled in `FA` (line 5946). The flag is
  the sign of `−(−1)^j c_j`.
* Near term. When `k` is even and `2 ≤ k ≤ 24` (`nearOn`, line 5948), `j0 = k/2` is the
  correction index whose `sinc π(x − j0)` is singular-looking at `x = j0`; it is enclosed through
  the Taylor polynomials of `sinc`, `sc1`, `sc2` at `T` (`S0`, `G1`, `G2`, `B0`, `B1`, `B2`, lines
  5949 to 5963) with `CJ j0 = (|c_j0|·10^9, sign c_j0)` (line 5864).
* Outputs (readers used by the checker):
  * `ok` (line 5936): `LN ≤ UN`, `TUZ ≤ DZ`, the cell lies on one side of `k/2`, `E0 > 0`
    (that is `2(πx)² > 1`, so `x > 0.225`).
  * `K0` encloses `k` (`K0_enc`, line 7575), `K1` encloses `k′` (line 7642, needs `E2L > 0`), `K2`
    encloses `k″` (line 7667, needs `E3L > 0`).
  * `KAn = max(0, min|K0|)` (line 7715): `(KAn/DZ)² ≤ w` (`w_lower`, line 7721).
  * `W1 = 2·K0·K1` encloses `w′ = 2kk′` (`w1_enc`, line 7730).
  * `W2L = (min|K1|)² + DZ·lo(K0·K2)` (line 5984): `W2L ≥ 0 ⇒ w″ ≥ 0` (`w2_nonneg`, line 7735),
    and `2·W2L/DZ² ≤ w″` (`w2_lower`, line 10794).
* `CellN` (line 7778) wraps a cell as `key = LN·KB + UN`. Readers: `okC`, `WZ = ⌊KAn²·SW/DZ²⌋`
  (line 7787, sound by `cellN_soundWZ`, line 7810), `okD = ok ∧ E2L > 0`,
  `W1LO = ⌊lo(W1)/10^6⌋`, `W1HI = ⌈hi(W1)/10^6⌉` (lines 7790, 7791, sound by `cellD_sound`,
  line 7826), `convOk = okD ∧ E3L > 0 ∧ W2L ≥ 0` (line 7792, `cellConv_sound`, line 7853).

`replay.py:CellEval` mirrors every definition above. An independent numerical check (quadrature
of `K`) confirms that the replayed `K0` intervals contain `k(x)`.

## 6. The `decide +kernel` checks, in dependency order

`grep -n "decide +kernel"` gives 79 lines: one in the header comment (line 273) and 78 checks. The
table lists each family, the data it reads and the theorem that turns it into a real statement.

| # | Lean (line) | Checks | Data | Consumer |
|---|---|---|---|---|
| 1 | `pvCheck_AM` (3145) | positive variation of `v/MAM` on `[0, 1/2]` is `≤ 9/200` | `cAMn`, `sinTabZ` (2972), Lipschitz constant 114 in `cellU` (2990) | `posVar_of_check` (3090) → `profile_AM` (3151) |
| 2 | `winOk_all` (9159) | `|k| ≥ 1/2` on the 16 cells of `[1/4, 1/2]` | CellA | `wfun_quarter_high` (9160) → `wfun_window` (9189): `w ≥ 1/4` on `[0, 1/2]` |
| 3 | `TB_ok` (12087) | every nonzero 12-bit curvature field `f` of cell `[256i, 256(i+1)]` satisfies `w″ ≥ f·2^19/VD` there | `PC9XA.TB` (12086) | `tfld_sound`, `cmin_sound` (11096, 11133) → `mtermTIW` (11325) |
| 4 | `top_ok` (13321), `blk_0..4` (13322 to 13326) | value pyramid: leaves certified by CellA, each parent `≤ min` of its children | `TOP` (12328), `BK_j` | `lbS : LBSound TOP BK` (13330) |
| 5 | `topD_ok` (13592), `dblk_0..3` (13593 to 13596) | derivative pyramid, same structure, two 32-bit lanes | `TOPD` (13331), `BKD_j` | `lbD : LBSoundD TOPD BKD` (13600) |
| 6 | `hR` (13602) | 16 convexity regions: `w″ ≥ 0` on each, by a chain of CellA cells | `REG` (13601) | `rg_conv` (9072) |
| 7 | `PTT_0_ok .. PTT_7_ok` (13604 to 13618) | every tangent point word: value, slope bounds, and its interval's tangent claim | `PTT_*` (13603 to 13617) | `ptS : ∀ x, PVI x (PT x)` (13622) |
| 8 | `cert` hcov (14066) | root cover segments: certified segments carry `a_adj·w ≥ c` | `COV` (13623), `SMAX` (13632) | `cert_of` (12239) → `root_cover` (9590) |
| 9 | `rc0 .. rc47` (13645 to 13993) | each root box walk returns its stated end position | `WL r_*`, root index tuple, end `e` | `rcOf` (13634), `rcOfC` (13638) → `run8` (13994) |
| 10 | `wcs9_1, wcs10_1, wcs34_1, wcs36_1, wcs37_1, wcs42_1` (13720 to 13962) | a subtree walk from a stated cut position and state returns its stated end | `CS*_1` states | `ccs*_1` → `CUTS*` → `rcOfC` |

Plain `decide` checks (cheap, also replayed): `hPR` (11625), `hTS` (11628), `hSL` (11630), `hADJ`
(12238), `CE_pos` (7116), and the `cert_of` side conditions `hS`, `hwin`, `hW` (14066).

### 6.1 pvCheck (lines 2951 to 3145)

On 128 cells of width `1/256` in `[0, 1/2]`, `termU i j` bounds `−c_j ω_j sin(ω_j s)` at the
cell midpoint above (j = 0 with `√2` enclosed by `s2LoQ`, `s2HiQ`; j ≥ 1 with the table `sinTabZ`
of `sin(πq/256)`, itself checked by `tabOk` against degree-11 Taylor bounds `sinPiI`).
`cellU i = Σ_j termU i j + 114/512` adds the Lipschitz error over half a cell (`vAMd_lipschitz`,
line 3081, a window-dependent real-analysis lemma). The check is
`Σ_i max(cellU i, 0)/320 ≤ 9/200` (`1/320 = (1/256)/MAM`). attempt-031's value is 0.041132.

### 6.2 Value pyramid `Pyr` (lines 7862 to 8326)

Geometry: level `l` index `i` is the cell `[i·2^l, (i+1)·2^l]/SC`; levels 0 to 19, so the
pyramid spans `[0, 16]`. Statement `CS l i v` (line 7974): `v/10^10 ≤ w` on that cell.

* `TOP`: 32-bit fields `fld TOP (2^{19−l} + i)` for levels 11 to 19 (heap order).
* `BK j`, `j < 512`, covers level 10 index `j`, that is `[j/32, (j+1)/32]`. Bits 0 to 4 hold the
  finest stored level `r ≤ 10`; the rest is a heap of 32-bit fields `fld (X/32) (2^d − 1 + t)`,
  depth `d ≤ 10 − r`, for level `10 − d`, index `j·2^d + t`. `BK j = 0` means "no information"
  (every value 0).
* `blockOkX` (line 7907): every leaf field (depth `10 − r`) passes `cellOk r i v` (line 7903):
  `v = 0`, or `cellOkCore` (line 7901): `CellA.ok ∧ 1000·v·DZ² ≤ KAn²·SW`, that is
  `v/10^10 ≤ (KAn/DZ)²`. Every inner field is `≤ min` of its two children.
* `topOk` (line 7920): every `TOP` field is `≤ min` of its children; level 10 reads the block
  roots.
* `lb top bk lo hi` (line 7889): 0 if `hi ≤ lo` or `hi ≥ 524289`; otherwise
  `k = blen((hi − lo)/32)` (bit length, table `BL8`, line 7885) and `dcov` (line 7882): up to 14
  `dstep`s (line 7876) cover `[lo, hi]` by aligned dyadic cells at levels `≥ k` (the 3-bit table
  inside `dstep` picks the alignment) and return the minimum of their entries. `entry` (line 7870)
  reads `TOP` for levels 11 to 19 and the block heap otherwise (a level finer than the block's `r`
  reads its ancestor, `CS_anc`, line 7993). `lb_sound` (line 8292):
  `lo/SC ≤ x ≤ hi/SC ⇒ lb/10^10 ≤ w(x)`.

attempt-031: 496 nonzero blocks, all with `r = 8` (cells of width 1/128), 1984 CellA leaves.

### 6.3 Derivative pyramid `PyrD` (lines 8329 to 8797)

Same geometry with 64-bit fields `fld2`; each field packs two 32-bit lanes,
`lo32` is a lower bound of `10^9(w′ + 2)` and `hi32` a lower bound of `10^9(2 − w′)` on the
cell. `pmin`, `ple` act per lane. Leaves: `cellOk2` (line 8373) = `cellOkD true` on `lo32` and
`cellOkD false` on `hi32` (line 8332): `okD` and `v ≤ KU1 + W1LO` (resp. `v ≤ KU1 − W1HI`). A lane
value 0 carries no claim. `lbDr` (line 8820) is `lb` with `blen((hi − lo)/64)`; `lbDr_sound`
(line 8834). attempt-031: 130 nonzero blocks (121 with `r = 8`, 9 with `r = 7`).

### 6.4 Convexity regions `REG` (lines 8921 to 8935)

`REG = (Apack, Bpack, chains)`. Region `k < 16` is `[rgA k, rgB k]` (20-bit fields of `Apack`,
`Bpack`). `rgOk`: either `rgB < rgA` (empty) or the chain `a = rgA, b_1, ..., b_m = rgB` has
`b_i ≤ b_{i+1}`, `b + 1 ≤ KB` and `convOk [b_i, b_{i+1}]` for each link, so `w″ ≥ 0` on the region
(`chainOk_sound`, line 8949; `rg_conv`, line 9072). A tangent point `p` belongs to region
`(p + 16384) >> 15`, the integer nearest to `p/SC`. attempt-031: region 0 empty, regions 1 to 15
around `x = 1, ..., 15`, region 1 = `[0.5, 1.2324]`.

### 6.5 Tangent point table `PTT` (lines 12255 to 12321, data 13603 to 13622)

`PTrD` (line 12290) is a binary search tree over `x/1024`: `.nd k l r` goes left when
`x/1024 < k`; `.lf j L` holds pairs `(x mod 1024, word)`. `PT x = ptGetD PTT x` (line 12293)
returns `pwD x word` (line 12255) for the first matching entry, else 0. The expanded word:

| bits | field | claim (`PVI x v`, line 10605) |
|---|---|---|
| 0 to 31 | `V = lo32` | `V/10^10 ≤ w(x/SC)` (`ptOk`, line 8339, CellA on the degenerate cell `[x, x]`) |
| 32 to 63 | `P = lo32(hi32)` | `P/U1 ≤ w′(x/SC) + 2` (`ptdOk`, line 8815) |
| 64 to 95 | `M = hi32(hi32)` | `M/U1 ≤ 2 − w′(x/SC)` |
| 96 to 119 | `ivA` | interval start, stored in the source as `x − offset` (20-bit offset) |
| 120 and up | `ivB` | interval end, stored as `x + offset`; `ivB = 0`: no interval |

`ptlOkD` (line 12261) checks `pt3e` (the three pointwise claims) and `ivOk` (line 10624), which is
`tcheckPZC` (line 10118) on `[ivA, ivB]`: the tangent line `V/10^10 + w′(p)(s − p/SC)` stays below
`w` on `[ivA, ivB]`. `tcheckZC` (line 10099) proves this by:

* inside the convexity region of `p`, convexity (`ext_tangent`, line 9016);
* right of the region up to `U`: either the derivative pyramid shows `w′ ≥ 2 − M/10^9 ≥ w′(p)`
  (`lo32(lbDr) + M ≥ 4·10^9`), possibly on the dyadically rounded range `rup U jj`, or `zsideF`
  (line 9733) shows `V + w′(p)·(s − p) ≤ lb` piecewise on 1, 2 or `n = 32` pieces (`zpt`, line
  9721, with `w′(p) ≤ (2·10^9 − M)/10^9`);
* left of the region down to `L`: the mirror statements with `P`.

`csh = 4` sets the rounding granularity. Soundness: `tangent_valZC` (line 10122), `ivOk_sound`
(line 10628). attempt-031: 6145 points, `x ∈ [0.8125, 15.047]`, every point carries an interval
(mean width 1.53, max 55.8).

### 6.6 Curvature table `TB` (lines 11027 to 11160)

`TB` is a list of clusters `(B0, N, T)` in decreasing `B0`; cell `i` (width `256/SC = 1/128`) reads
the 12-bit field `i − B0` of `T` in the first cluster with `B0 ≤ i` (`tfld`, line 11051). `tbOk`
(line 11068): `T < 2^{12N}` and each nonzero field `f` passes `curvatureOk` (line 10825):
`f·2^19·DZ² ≤ 2·VD·W2L` on the cell, that is `w″ ≥ f·2^19/VD`. attempt-031: 12 clusters,
73 nonzero fields, in `x ∈ [1.0, 11.08]`.

### 6.7 Window bound `winOk` (line 9158)

16 cells `[8192 + 512i, 8704 + 512i]` (`x ∈ [1/4, 1/2]`): `CellA.ok ∧ DZ² ≤ 4·KAn²`. With
`kfunAM_ge_cos` (`k ≥ cos πx` on `[0, 1/2]`, line 9124) it gives `w ≥ 1/4` on `[0, 1/2]`.
attempt-031: `min 4KAn²/DZ² = 1.1707`.

## 7. Polytope cells and the walk

### 7.1 Cells

`Cl = (L, U, A, B)` (line 9230). `InCell` (line 9235): `L_r/SC ≤ g_r ≤ U_r/SC` and
`A_k/SC ≤ y_j − y_i ≤ B_k/SC`. `Covered c` (line 11641) = `CovBy 8 PR (Pg cN 8 BS TS) c`: every
`g` in the cell satisfies `Pg`. The instance flattens a cell into the 73-field structure `St`
(line 11642: `l0 u0 ... l7 u7 A02 B02 ... A68 B68 M`; `M` is unused and 0). The kernel-facing
code (`cuH`, `colK*`, `rowK*`, `splG`, `qs_*`, `tm`, `yupdS`, `mcheckP`) is the unrolled form of the
generic definitions; `cuL_eq` (line 11742), `spH_ok` (line 11749), `tm_ok` (line 11945),
`yupdS_ok` (line 11968) and `mcheckP_ok` (line 12037) identify them. `replay.py` implements the
generic forms.

### 7.2 Walk words

Root `r` reads its tree from `WD r = rdw (WL r)` (line 12159):
`bits pos = (WL r (pos / 32768) >> (pos mod 32768)) & WMASK`, `WMASK = 2^600 − 1`. A block holds
32768 + up to 600 bits so that a word starting near a block end is complete. Positions are bit
offsets; the root is at position 1.

`node` (line 12160) at position `pos`, word `w = bits pos`:

* split (`w` bit 0 = 1): axis `ax = (w >> 1) & 63` (0 to 7: gap `ax`; 8 to 35: pair `PR[ax − 8]`),
  mode `md = (w >> 7) & 7`; the children start at `pos + 10`.
* leaf (bit 0 = 0): `leafStep` (line 12133).

`walkC` (line 12164) recurses with fuel 128 (maximum depth). `splitAx` (line 11911) dispatches on
`ax` (`ax ≥ 36` fails). The left child runs at `pos + 10` and returns its end `pp`; the right child
runs at `pp`; the node returns the right child's end. 0 means failure and propagates.
`walk` (line 12166) applies `tm` (`matC`, line 9692: `A_k ← max(A_k, Σ_{i≤r<j} L_r)`,
`B_k ← min(B_k, Σ U_r)`) once at the root.

### 7.3 Splits (closure through one edge)

The cut `q` for slot bounds `(lo, hi)` (the gap's `(L, U)` or the pair's `(A, B)` before the
split): `md = 0`: `(lo + hi)/2`; `md = 1`: `bcutL BND 64 lo hi` (line 10014), the entry of `BND`
(line 11631) nearest the midpoint among those at least 64 inside `[lo, hi]` (midpoint if none);
`md ≥ 2`: `fracQ` (line 11632), `lo + ⌊(hi − lo)·k/8⌋`, `k = md − 1` for `md ≤ 4`, `k = md` for
`md ≥ 5` (k ∈ {1, 2, 3, 5, 6, 7}).

Children for a split on `(i, j)` at `q`: left is `y_j − y_i ≤ q`, right is `y_j − y_i ≥ q`. Each
child is `cuB c (colB c s) (rowB c E t)` (lines 10432 to 10501): with
`D(a, b)` = the cell's bound of `y_b − y_a` (`hi` slot if `a < b`, 0 if equal, `−lo` of `(b, a)` if
`a > b`, via `SL`), `dE E a b = E + D(a, b)` truncated at 0, `X_x = BB + D(x, s)`,
`Y_x = E + D(t, x)`, and every slot `(a, b)` tightened by the path through the new edge:
`hi(a, b) ← min(hi, X_a + Y_b − TB)`, `lo(a, b) ← max(lo, TB − X_b − Y_a)`. Left uses
`(s, t, E) = (i, j, BB + q)`, right uses `(j, i, BB − q)`. Soundness: `cov_splitB` (line 10542).

### 7.4 Cuts

`walkCut` (line 12218) is `walkC` that, at a position listed in `cuts`, returns the stated end
`e` if the current state equals the stated state (`stEq`, line 12183) and 0 otherwise.
`walkCutR = tm ∘ walkCut` (line 12221). A cut `(pos, CS, e)` is justified by a separate theorem
`wcs*` that `walkC ... 128 pos CS = e` (for example line 13720) and `ccs*` (line 13722). Six roots
(9, 10, 34, 36, 37, 42) use one cut each; the cut splits the kernel work of one large root into
two `decide +kernel` evaluations.

### 7.5 Leaf word

`leafStep pos w s`: if `U_7 < L_0` the leaf is a reflection leaf (all `g` in it satisfy
`g_7 < g_0`, the second disjunct of `Pg`) and the walk continues at `pos + 1`. Otherwise bit 1
selects `mleafV` (variance leaf) or `mleafP`; both read `w >> 2` and return the payload length
`n`; the walk continues at `pos + 2 + n`.

Payload (`mleafP`, line 12042), offsets in bits from 0:

1. 34 term records, in `TS` order, decoded by `dec4QG 3 10 w o L U` (line 11588) with `[L, U]` the
   term's range (`eL`, `eU`, lines 9458, 9461: the gap's `[L_i, U_i]` for adjacent terms, else
   `[max(A_k, Σ L), min(B_k, Σ U)]`):
   * 2 bits kind `κ`.
   * `κ = 0` (constant, 2 bits): minorant `lb(eL, uc)`.
   * `κ = 1` (tangent, 9 bits): 7-bit anchor code at bit 2.
   * `κ = 2` (constant/tangent mix, 19 bits): anchor at bit 2, 10-bit `λ` at bit 9.
   * `κ = 3` (two tangents, 26 bits): anchors at bits 2 and 9, 10-bit `λ` at bit 16.
   * Anchor code `jj` (`gptQG 3 L U jj`, line 11581): 33 is `L`, 34 is `U`; otherwise the point
     `L + ⌊(U − L)(jj & 63)/32⌋` rounded down to a multiple of `2^gs` (`gs = 3` if bit 6 of `jj`
     is set, else 8) and clamped into `[⌈L⌉_gs, ⌊U⌋_gs]` (`gq`, line 11570). The anchor must be a
     point of `PTT` whose interval contains `[eL, eU]`.
   * Weights (lines 8983 to 8991): constant weight `mwc`, tangent weights `mw1` (anchor p),
     `mw2` (anchor r); `κ=0`: (1024, 0, 0); `κ=1`: (0, 1024, 0); `κ=2`: (1024 − λ, λ, 0);
     `κ=3`: (0, 1024 − λ, λ).
2. Multiplier list (`ydecS s 14 w 42`, line 11966), at most 42 entries: a 1 bit, a 5-bit pair
   index `c < 28`, a side bit `sd`, a 14-bit magnitude `Y/SIG`. A 0 bit (1 bit) or `c ≥ 28`
   (21 bits) ends the list. Each entry adds `Y` times the pair constraint `y_j − y_i ≥ A_c`
   (`sd = 0`) or `≤ B_c` (`sd = 1`) to the slope certificate (`mul_step`, line 9293).
3. The payload length `n` is the offset after the list.

## 8. The leaf inequality

`mcheckGX` (line 10260; `mcheckP`, line 12034, is its unrolled instance) returns true when all
`L_r ≤ U_r`, every term passes `mokI` (line 10658: `λ ≤ 1024` and each used anchor `p` has
`ivA ≤ eL ≤ p ≤ eU ≤ ivB`) and

    335544320000000000·cN + 10·(Σ_n a_n·mcn_n + Cp + Σ_r (U_r − L_r)·Ng_r)
      ≤ 10240000000000·Σ_r b_r·L_r + 32768·Σ_n a_n·mv_n + 10·(Σ_n a_n·mcp_n + Cm)

with integer weights `a_n = tA`, `b_r = BS[r]` and, for term `n` with anchors `p`, `r`, point words
`(V, P, M)` and `L0 = eL0 = Σ_{i≤r<j} L_r`:

* `mv_n = mwc·lb(eL, max(eU, eL+1)) + mw1·V_p + mw2·V_r` (`mvT`, line 9374), plus the variance
  bonus `vbW` in `mleafV`;
* `mcp_n = Σ_t mw_t·(M_t − 2·10^9)⁺·(p_t − L0)`, `mcn_n = Σ_t mw_t·(2·10^9 − M_t)⁺·(p_t − L0)`
  (`mcp`, `mcn`, lines 8994, 8997);
* `Ng_r = (2·10^9·Σ_{n∋r} a_n·(mw1 + mw2) + P_r − 1024·10^9·b_r − Σ_{n∋r} a_n·msl_n − S_r)⁺`,
  `msl_n = mw1·P_p + mw2·P_r` (`Ng`, line 9465); `P_r`, `S_r`, `Cp`, `Cm` come from the multipliers.

Meaning (divide by `3.3554432·10^17·SA`; `3.3554432·10^17 = 1024·10^10·32768`). For `g` in the
cell, each term is bounded below on `s ∈ [eL/SC, eU/SC]` by the convex combination
`λ_c·lb + Σ_t λ_t·(V_t/10^10 + w′(p_t)(s − p_t/SC))` of a constant and up to two tangents
(`mterm_minV`, line 9887; tangent validity from `PVI` and `mokI`, `mtermTI`, line 10708). Writing
`s − p_t/SC = (s − L0/SC) − (p_t − L0)/SC` moves the anchors to the range start; the bounds
`(P − 2·10^9)/10^9 ≤ w′(p) ≤ (2·10^9 − M)/10^9` turn the anchor shift into the `mcp − mcn` charge
and give each term a slope `D_n ≥ (msl_n − 2·10^9(mw1 + mw2))/(1024·10^9)`. Then `F(g)` is at
least a linear function of `g − L/SC` whose coefficients are bounded below; the multiplier
inequality `MulOKg` (line 9290) shifts weight between gap coefficients using the pair bounds; the
remaining negative coefficient parts cost at most `(U_r − L_r)·Ng_r`. The result
`cN ≤ Fg g` for every `g` in the cell is `mcheckGX_sound` (line 10275).

Variance leaves (`mleafV`, line 12088; `mcheckW`, line 11357): for a `κ = 3` term whose range lies
in at most five curvature cells (`U/256 − L/256 ≤ 4`) that contain both anchors, the bonus
`vbon(μ, λ, p, r) = ⌊10^10·μ·λ(1024 − λ)(p − r)²/(2048·SC²·VD)⌋` with `μ = 2^19·min field` is added
to `mv_n`. It is the anchors' variance under `w″ ≥ μ/VD` (`variance_lower`, line 11155;
`mterm_okIV`, line 11238).

The margin of a leaf is `RHS − LHS`; in units of `F` it is `margin/(3.3554432·10^17·SA)`.

## 9. Covering the orthant

`root_cover` (line 9590) with the arguments of `cert_of` (line 14066):

* Small gaps: `hwin`: `4·cN ≤ a_adj(r)` for every `r`. If some `g_r ≤ 1/2` then `w(g_r) ≥ 1/4`
  (section 6.7) and the adjacent term alone gives `F ≥ c`.
* Large gaps: `hS`: `cN·SC ≤ b_r·SMAX r`. If `g_r ≥ SMAX r/SC` then `b_r g_r ≥ c`.
* Middle gaps: `hcov` = `coverChk cN a_adj(r) (SC/2) (SMAX r) (COV r)` (line 9515). `COV r` is a
  list of contiguous segments `(a, b, flag)` from `16384` (x = 1/2) to at least `SMAX r`, each with
  `b < KB`. A segment with flag `true` must satisfy `cN·SW ≤ a_adj(r)·WZ [a, b]`, so the adjacent
  term alone gives `F ≥ c` there. Segments with flag `false` are "bad" (`badOf`, line 9521).
* Remaining region: every `g_r` lies in a bad segment of `COV r`. For each choice `idx` of one bad
  segment per gap, `rootCl` (line 9568) is the box with `L_r, U_r` = that segment, `A_k = 0`,
  `B_k = W = 2^40` (any `W ≥ 8·KB` is valid). `run` (line 14053) and `run8` (line 13994) reduce the
  48 combinations (bad-segment counts 1, 3, 2, 2, 2, 2, 1, 1) to the theorems `rc0 .. rc47`.
* Reflection: leaves with `U_7 < L_0` and the `g 7 < g 0` disjunct of `Pg` mean the trees need only
  certify the half `g_7 ≥ g_0`; `PC9XA_half` and the palindromic weights supply the other half.
* Far region and tails: there is no separate far-region certificate. `lb` returns 0 for distances
  `≥ 16` (`hi ≥ 524289`), so a far term contributes only through a constant 0 or tangents of
  `PTT`; the bad segment of gap 0 and 7 runs to `x ≈ 32` and the leaves cover it with the gap
  pressures `b_r`.

## 10. Window, weight and structural dependence

### 10.1 Window-dependent (regenerate for a new window)

| Item | Lean | Kind |
|---|---|---|
| `cAMn`, `ωAM`, `vAM` with `Finset.range 13` | 288 to 305 | literals and term count |
| vAM bounds, `vAMd_lipschitz` (constant 114), `profile_AM` (δ = 1/10, A₁ = 78/25, A₂ = 456/5, ρ = 9/200, `vAM 0/MAM ≤ 81/100`) | 305 to 3183 | real-analysis proofs with window literals |
| `pvCheck` cell count (128), `termU`'s ω_j = 2πj | 2984 to 2992 | code; finer cells may be needed |
| `kfunAM_eq`, `k1AM_eq`, `k2AM_eq`, `sum_T0..2`, `fsum_CE`, `CJ_val`, `sep` (all over `Finset.range 12` or `j ≤ 12`) | 6234 to 6284, 7139, 7372 to 7436 | proofs fixed to 12 corrections |
| `CE`, `CJ`, `FA`'s unrolled `farJ` list, `nearOn` bound 24 (= 2·12) | 5860 to 5948 | literals and code |
| `GAM0`, `GAM1`, `G1C`, `G2C`, `RHOC`, `SIGC`, `TAUC`, `PIC`, `PI2C` | 5851 to 5859 | depend only on ω₀ = √2 and π: unchanged if ω₀ = √2, c₀ = 1 |
| `TOP`, `BK_*`, `TOPD`, `BKD_*` | 12328 to 13591 | data (w and w′ lower bounds) |
| `REG` | 13601 | data (convexity regions near integers) |
| `PTT_*` | 13603 to 13619 | data (tangent points, intervals) |
| `TB` | 12086 | data (curvature table) |
| `COV` good segments | 13623 | data (depend on `w`, and on `a_adj`, `c`) |
| `winOk` | 9157 | passes iff `|k| ≥ 1/2` on `[1/4, 1/2]` |
| `HW_ge` and the H_W enclosure | 1805 to 2034 | real-analysis proof with window literals |

### 10.2 Weight-dependent

`cN`, `SA`, `SIG` (11622 to 11634), `BS`, `TS` weights, `G` (11635) and `Fg_G`, `aW9`, `bW9`, `W9`,
`W9_B`, `W9_a_nonneg`, `W9_bmin`, `W9_capacity`, `Fw_W9`, `cert_AM` (14102 to 14368), the final
constants in `Opeth.AMFinal` (16780 to 16800), `COV` segmentation and `SMAX`, the root theorems
`rc*` and their `run8` arms, the bad-segment lengths in `run`, every walk word `WL*_*`, the cut
states `CS*` and `wcs*` theorems, and `BND` (split candidates, a generator choice).

### 10.3 Structural (fixed by the checker code)

`Q = 8`, `PR` (28 pairs), `SL`, `ADJ`, the `TS` index layout (34 terms in order, zero-weight pairs
(0,2) and (6,8) absent; a nonzero weight there needs new `mleafP`/`mcheckP` code), `SC`, `KB`,
`SW`, `U1`, `KU1`, `DZ`, `BB`, `TB`, `VD`, the pyramid geometry (512 blocks × 1024, levels 0 to 19,
32-bit and 64-bit fields, range `[0, 16]`), `BL8`, the `dstep` alignment table, 16 regions indexed
by the nearest integer, tangent parameters `n = 32`, `csh = 4`, curvature cells of width `256/SC`,
the leaf decoder (`fs = 3`, `lb = 10`, `qb = 14`, 42 multipliers), `WMASK` (600 bits), block size
32768, fuel 128, split word width 10.

## 11. Report on attempt-031's certificate

All values come from `python -I replay.py Solution.lean --workers 4 --stats stats.json` and
`--mutation-suite`.

* Replay: all 78 `decide +kernel` checks and the plain `decide` side conditions return true
  (about 3 s on 4 cores). Every root and cut walk ends at exactly the stated position.
* Mutation suite: one changed data value per family makes the replayed check false in every case
  (sine table entry, window literal c₁ in `FA`, curvature field, `TOP` field, block root field in
  `BK` and `BKD`, `TOPD` field, region chain end, tangent value, a bad segment flagged good, one walk
  bit, a stated end position (root and cut), a cut state coordinate, `b_0`, the floor `c`).
* Leaves: 9932 (9545 inequality leaves, 387 reflection leaves), 9884 splits, 48 roots, 6 cuts.
  16 leaves use the variance bonus. Depth: mean 31.2, max 122 (fuel 128). Roots 16 to 31 have 1
  to 4 leaves each. Counting their cut subtrees, roots 10, 37, 9 and 34 are the largest (627, 616,
  603 and 595 inequality leaves); among uncut roots, roots 5, 33 and 13 (414, 409, 406).
* Terms per leaf (324530 records): kind 0 constant 47.7 %, kind 1 tangent 40.7 %, kind 3 two
  tangents 8.2 %, kind 2 mix 3.3 %. Multipliers: mean 0.68 per leaf, max 3, none in 3648 leaves.
* Splits: modes `md = 0` 1860, `md = 1` (boundary list) 1650, `fracQ` 6374. The pair (0, 8) is
  split most often (973), then pairs (1, 7) (602) and (0, 7) (601), then (1, 8), (0, 6) and gaps 0
  and 7 (527, 436, 428, 424); pair (0, 2) is never split.
* Margins in units of F (c = 0.0088918): min 0 (exactly tight, root 37 position 89902, a variance
  leaf), 1st percentile 3.3e-8, 10th 2.3e-6, median 3.5e-5, 90th 2.8e-4, max 0.0106. 9 leaves have
  margins below 1e-9. The floor is the largest c that every leaf certifies (header: "exact floor
  closure").
* Other constraints:
  * `hS` is exact for gaps 0 and 7 (`b_r·SMAX = cN·SC`, `SMAX = 1048575`, x ≈ 32); other gaps
    have 0.03 % to 1.9 % slack.
  * `coverChk` has 0.002 % slack on gaps 0 and 7 (segment `[0.80859, 0.8125]`), 0.06 % to 1 %
    elsewhere.
  * `hwin`: `a_adj/(4c)` is 3.4 to 9.4 (loose).
  * `pvCheck`: 0.041132 against 0.045. `winOk`: `min 4KAn²/DZ²` = 1.1707.
  * Capacity: `a_08 = 2` and `a_07 + a_18 = 2` sit at the span-capacity bound 2.

## 12. Generator requirements

To emit a certificate for a new window and weights that this checker accepts, a generator must
produce the following, in this order, and validate each piece with `replay.py`.

1. Lean code for the window (not only data) when the term count changes. The cell evaluator and its
   proofs are written for 12 corrections: `CE`, `CJ`, `FA`'s unrolled `farJ`, `nearOn` (bound 24),
   `CJ_val`, `fsum_CE`, `sum_T0..2`, `kfunAM_eq`, `k1AM_eq`, `k2AM_eq` and `vAM`'s `Finset.range 13`
   all change for 17 terms. The real-analysis window lemmas (`vAMd_lipschitz`, `profile_AM` bounds,
   `pAM_le_edge` (line 15183), `Tj_abs_le_sep`, `HW_ge` (line 1982)) must be re-proved; the Lipschitz constant grows with
   `Σ|c_j|ω_j²`, so `pvCheck` may need more than 128 cells. `replay.py` reads `CE`, `CJ`, the `FA`
   list and the `nearOn` bound from the source, so it follows a regenerated evaluator.
2. Pyramid tables `TOP`/`BK` and `TOPD`/`BKD`: evaluate CellA on dyadic cells, store certified
   leaves (`v ≤ 10^10·(KAn/DZ)²`, lanes `≤ KU1 ± W1`), propagate minima upward, pack 32-bit and
   64-bit heaps with the level byte, and emit the `dsel` dispatch tree.
3. `REG`: one convex interval per integer `1..15` (nearest-integer indexing), each covered by a
   chain of CellA cells with `convOk`.
4. `PTT`: tangent points on the anchor grid that leaves will use, with value and slope lower
   bounds certified by CellA on `[x, x]`, and an interval `[ivA, ivB]` that passes `tcheckZC`
   (convexity inside the region, derivative pyramid or piecewise `lb` checks outside).
5. `TB`: curvature fields for the cells where variance leaves are wanted.
6. Root cover: `COV` segments per gap (good segments certified by `WZ`), `SMAX` from `hS`, and the
   product of bad segments as roots (the Lean text of `run`, `run8` and `rc*` depends on the counts).
7. Trees: split decisions that the checker's closure (`cuB`) reproduces bit for bit, with modes and
   cut positions chosen from the parent state; leaves whose term records and multipliers make the
   integer inequality of section 8 hold with the decoder's exact anchor rounding (`gptQG`) and the
   exact `lb`/`PT` values; reflection leaves where `U_7 < L_0`; depth at most 128.
8. Encoding: the bit stream (10-bit split words, leaf payloads with exact lengths, multiplier
   terminators), the 32768-bit blocks with 600-bit overlap, `zfNat64` literals, and the root and
   cut theorems with their exact end positions (computed by running the walk).
9. Kernel cost: split large roots with cut states so each `decide +kernel` stays within the
   verifier's budget.

Hardest parts, in order:

* Re-proving the window lemmas for 17 terms (item 1). It is Lean proof work, not data, and the
  `pvCheck` cell count and the near-term range interact with ω_16 = 32π.
* The leaf optimisation (item 7): per leaf, choose kinds, anchors on the clamped grid, `λ`, and up
  to 42 quantised multipliers so that an exact integer inequality holds; attempt-031 runs with a
  median margin of 3.5e-5 in F and a zero minimum, so floating-point sizing must be followed by
  exact integer verification and repair.
* Tangent intervals (item 4): a leaf may use an anchor only if its precertified interval covers
  the term's whole range, so interval lengths trade off against `tcheckZC` success.
* Emulating the walk exactly (items 7 and 8): the closure update, the split rules and the payload
  lengths determine every later position; `replay.py` is the reference implementation to check a
  generated tree before writing Lean.
