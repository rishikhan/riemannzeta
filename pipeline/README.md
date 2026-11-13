# pipeline: the Python library of the window search

The generator in `src/lbcert/` and `make hfloor` import these modules. They run as a package from the repository root
(`PYTHONPATH=.`, which the Makefile sets).

| module | contents |
|---|---|
| `hfloor.py` | the closed-form H = 2 − W(v) of a cosine-sum window, in Arb, with exact rational endpoints (Proposition 5.1) |
| `freqspec.py` | frequency spec strings (`sqrt(2)`, `2*pi`, …) and their rigorous values |
| `kernel.py` | the window kernel, in float64 |
| `geometry.py` | index bookkeeping for the (q+1)-point, q-gap local geometry |
| `objective.py` | the local functional F_q and the projected Newton that minimizes it |
| `wtable.py` | cubic-spline tables of w, w′ and w″ on a uniform grid |
| `lp.py` | the cutting-plane model of the certified energy over the weights, and its level step |
| `score.py` | scores a window: solves its weights cold and assembles its bound |
| `cppgmin.py`, `cpp/gmin.cpp`, `cpp/knots.cpp` | the threaded C++ minimizer of F_q, compiled on first use |
| `assembly.py` | assembly formulas the scoring code imports |
| `certref.py` | locates a certificate file under `results/`; `src/lbcert/q12/cert12.py` imports it for its command line, which needs such a file and is not a documented step |

These modules only select windows and weights. Nothing here enters a proof: the Lean kernel
checks the certificate, and `src/sep_conditions_cert.py` and `hfloor.py` compute the other
inputs of Proposition 5.1 in ball arithmetic.
