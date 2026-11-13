# Trusted statement templates of the riemannzeta.fun challenge

These three files are copied unchanged from `challenge/templates/` of github.com/josusanmartin/riemann
at commit `0adc86db286879c9a706a3d2bc8ea729bf09d5c1`. The challenge's verifier generates the trusted
statement layer of every candidate from them. `proofs/verify.sh` does the same before it builds a
proof, so the statements a proof is checked against come from this directory, not from the archive.

| file | use |
|---|---|
| `CandidateSpec.lean.tmpl` | defines `currentRecordKappa` and `candidateKappa`; filled with the record at the time and the proof's κ from `proofs/archives.tsv` |
| `Challenge.Candidate.lean` | the three statements, with `sorry`, that the comparator checks a solution's theorems against |
| `PrintAxioms.Candidate.lean` | `#print axioms` for those three theorems |
