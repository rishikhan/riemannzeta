# Third-party Lean sources read by the generator

The Lean generator in `src/lbcert` copies checker and window code verbatim out of two published
entries of the riemannzeta.fun challenge (github.com/josusanmartin/riemann). Both files are
unmodified copies of the submitted `Solution.lean`.

| file | entry | sha256 | read by |
|---|---|---|---|
| `attempt-031/Solution.lean` | attempt-031, Samuel Lavery | `0adbf8e04b4bc3db5dae886dfe003dc4fb9b9acd6d998a43f2a5603cba515f32` | `src/lbcert/gen/core.py` (env `A031` overrides) |
| `attempt-032/Solution.lean` | attempt-032, Samuel Lavery | `9f4af56ebc9014fdf938da887cf7d2c51eb08a20203ac7d5524a62740b65bfa2` | `src/lbcert/q9lean/gen9.py` (env `A032` overrides; the hash is checked) |

Both files are released under the Apache License, Version 2.0 (`LICENSE-Apache-2.0`). Each
carries its own copyright, attribution and NOTICE lines at the top, which apply to the file
and to every part of it that the generator copies into a generated proof. The generated
proofs reproduce those notices unchanged.
