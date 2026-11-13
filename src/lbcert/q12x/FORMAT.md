# q12x data format: exact certified trees for the q = 12 Lean checker

Status 2026-10-25. Producer: src/lbcert/q12x (cpp_race/xgen, run_root.py, finalize.py). Consumer: the Lean
generator for q = 12 (q12lean/gen12.py). The format is the q = 9 sparse format Z (q9sparse/zfmt.py, as used by
the q = 9 entry with levers y, p, b, S, ptb) with the q = 12 field widths. Nothing in the leaf semantics
changes; only Q, the term count and two field widths do.

## Model

q12x/m12w/run_m12.sh builds the model from a refit JSON: q9win/build9.py at c = eps - 6e-7 and KB = 2^22, then
extend_model.py. The model directory holds model.pkl (the checker tables and weights), pts.pkl (the tangent
points), spec.json (the window, the weights, the root cover and the exact κ the model certifies), and the
xio.setup outputs model.pkl.eng, exact.txt and root_<k>.box that xgen reads. Constants the stream depends on:

| name | value | meaning |
|---|---|---|
| Q | 12 | gaps |
| NP | 66 | pairs PR (lexicographic (i, j), j >= i + 2) |
| NT | 72 | terms TS (adjacent terms plus the nonzero-weight pairs, q9 qgen.layout order) |
| AXB | 7 | split axis bits ((Q + NP - 1).bit_length()); axes 0..Q-1 gaps, Q.. pairs |
| PB | 7 | multiplier pair-index bits (NP.bit_length()) |
| QB | 14 | multiplier magnitude bits (Y = SIG * q) |
| YFUEL | 42 | multiplier fuel: at most 41 records per leaf |
| WMASK | 1024 bits | leaf window: a leaf (leading 0 bit included) is at most 1024 bits |
| FS | 3 | fine anchor grid of gptQG (anchor codes use gptQG(3, eL, eU, jj)) |
| KV | 2^160 | accumulator offset of the Z fold (zfmt.ZChecker.KV) |

## Root stream

One bit stream per root, bit 0 unused (0), the first node at position 1 (q9 convention). Nodes in preorder:

* split: `1 | ax << 1 | md << 8` (11 bits), then the left subtree, then the right subtree. Children are the
  checker's splitAx / cuB / colB / rowB with cut point md (0 midpoint, 1 bcutL, >= 2 fracQ).
* reflection leaf: one `0` bit, exactly when U_{Q-1} < L_0 for the node's box.
* checked leaf: one `0` bit, then the payload:
  * 72-bit presence mask, bit n for term n of TS;
  * for each listed term in increasing n: 3-bit kind z, then the anchor code(s) (7 bits; one for z = 1, 2, 4,
    two for z = 3, none for z = 0), then a 10-bit λ for z = 2, 3, 4;
  * the multiplier list: per record `1`, 7-bit c, 1-bit side, 14-bit q (c < 66 pair PR[c], c = 66 the
    half-space row g_0 <= g_{Q-1}; the side bit is read and ignored for c = 66), then a single `0` terminator.
  * next position = position of the leading 0 bit + 1 + payload length.

Kinds (value per 1024 units of the term's weight; an unlisted term contributes nothing):
z = 0: 1024 lb(eL, max(eU, eL + 1)); z = 1: 1024 tangent(p); z = 2: (1024 - λ) lb + λ tangent(p);
z = 3: (1024 - λ) tangent(p) + λ tangent(r); z = 4: λ tangent(p) (no constant part). Kinds 5..7 never occur.
The check is zfmt.ZChecker.zleaf with hs.ydec_half for the multipliers: side condition ivIn(PT(p), eL, eU, p)
for every tangent used, the merged accumulators CVP, CN, V_r (V_r truncated at 0 after each term), then
`335544320000000000 cN + 10 (CN + Cp + Σ_r (U_r - L_r) (V_r + P_r ∸ (1024e9 BS_r + S_r + KV)))
<= 10240000000000 Σ BS_r L_r + CVP + 10 Cm` and L_r <= U_r. Every emitted leaf also satisfies lever P's
per-term bounds (mw < 2049, sl <= 2^43).

Producer-side guarantees: every leaf passes the exact C++ check (the function `zcheck` in cpp_race/xgen.cpp,
GMP) and the Python mirror (pycheck.py, q9sparse zfmt.ZChecker with the 7-bit split word) against the final
table below; the two agree on mutated leaves. Anchor codes are the first code in q9enc kformat.CODES order
(0..32, 64..96, 33, 34) with gptQG(3, eL, eU, jj) = p.

## Tangent-point table

`table.lean.txt`, rows `x stored_word n`, the q9 `hull_final.txt` format (q9ptt PTN / q9leaf2 PTB input):
stored_word = V | P << 32 | M << 64 | (x - A) << 96 | (B - x) << 116, i.e. the pts.pkl word with its interval
cut to the hull [A, B] of the term ranges that use x; n = the piece count for ivOk(n, 4, x, pwD(x, word)),
the cheapest in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64) by pyramid lookups. A point whose hull fails for
every n keeps its maximal pts.pkl interval. Every row passes pt3e and ivOk (ptable.py). Only points that
some leaf uses are in the table; x < 2^19 for all of them on m12r; on an extended model (m12r_xf, PLV 21) points reach 2^20 (the final m12r_p table has points from x = 524288).
`table.xgen.txt` has the same table as `x V P M A B` for `xgen check --table`.

## Files per run (`work/<run>/`)

| file | content |
|---|---|
| `trees.pkl` | {root k: dict(idx, bits, nbits)}: idx = root index tuple (gen_treeshs.roots_of order), bits = the stream as a Python int, nbits = end position (the q9 `z_F_trees.pkl` shape, gen9 `--trees`) |
| `table.lean.txt`, `table.xgen.txt` | the point table (above) |
| `r<k>/final.nodes` | the final tree (after the point selection) as text; it matches trees.pkl and table.lean.txt |
| `r<k>/tree.nodes` | the generated tree before the selection: valid against pts.pkl's maximal-interval words only, NOT against table.lean.txt (some of its points are not in the table). Text format: one node per line (preorder): `S ax md`, `R`, `L nt (n z jp p jr r λ)×nt nm (c sd q)×nm` (p, r are the decoded points, -1 when unused) |
| `r<k>/top.nodes`, `job_<id>.nodes`, `job_<id>.jobs` | frontier and job files (a resplit job is itself a frontier; its J k records refer to job_<id>.k; a tree job with donated boxes has J p<hex> records, see below) |
| `r<k>/queue/<id>.job` | a box donated by a running job and not yet finished (work stealing, below) |
| `r<k>/stats.json` | leaves, splits, failures, CPU seconds, checks |
| `summary.json` | per root: leaves, bits, listed terms per leaf, check results; table size |

The root box of root k is `root_state(C, idx)` (gen/core.py: matC of rootState), also stored flattened
(L, U, A, B) in `root_<k>.box`.

## Job files and work stealing (xgen_st `--steal-dir`)

Generator-side only: the assembled tree (`tree.nodes`, `final.nodes`, `trees.pkl`) never contains a `J`
record, and nothing above changes for the checker.

* Placeholder `J id` in a node file stands for the whole subtree of job `P.id`, where `P` is the id of the
  file's own job (`job_P.nodes`; top level `top.nodes`: no prefix). Assembly (xio.assemble) substitutes
  `job_<P.id>.nodes` recursively. Frontier jobs have numeric ids, donated boxes `p<hex>`: the hex digits
  of the bit string `1 b_1 ... b_d` (left-padded with 0 to a multiple of 4), where b_i is the path from the
  job's root box to the donated box (0 left, 1 right child). The id therefore depends only on the box's
  place in the tree, so a job that is rerun after a crash gives a box the same id again.
* `job_P.jobs` lists the jobs a finished job refers to, one per line: `rel-id box`. xgen_st writes it
  before it renames `job_P.nodes` into place, and removes a stale one when it donated nothing.
* Box (a `.box` file, a `.jobs` line after the id, or a `queue/<id>.job` file): the NS integers
  L, U, A, B, optionally followed by the trailer `M have_m m depth` for a donated box: `m` is the margin the
  parent's split scan gave the box (C99 hex float, exact), `have_m` whether that margin is used (0 after a
  midpoint fallback split), `depth` the box's depth from the root. The job starts from exactly the state
  the donor would have used, so a box's subtree does not depend on whether it was donated (measured:
  byte-identical assembled trees). An older xgen ignores the trailer and recomputes the
  margin (cold LP), which can change near-tied choices: run donated jobs with cpp_race/xgen.
* `queue/<P.id>.job` holds the box of a donated job from the moment of donation until that job finishes
  (the worker removes it); the same box is also listed in `job_P.jobs` once job P finishes.
