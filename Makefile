# A formally verified lower bound for the proportion of simple critical-line zeros of zeta.
#
#   make            what each target does and what it costs
#
# THREADS sets the threads of the Lean build, nanoda and the kernel replay.

# Use the repository's own virtualenv when it exists, so `make venv` is enough.
PYTHON     ?= $(shell [ -x .venv/bin/python ] && echo .venv/bin/python || echo python3)
THREADS    ?= 8
Q          ?= 12
PROOF_OPTS ?=
RUN        ?= results/rerun
export PYTHONPATH := .

.DEFAULT_GOAL := help
.PHONY: help venv proofs proof conditions hfloor paper clean

help:
	@echo "Lean proofs (proofs/; the sources are on Zenodo, doi:10.5281/zenodo.24166562)"
	@echo "    make proofs                       download and unpack q = 9..12        315 MB"
	@echo "    make proof Q=12                   build; check axioms; print statements ~30 min, ~15 GB"
	@echo "    make proof Q=12 PROOF_OPTS=--deep also nanoda and the Lean kernel replay ~11 h, ~15 GB"
	@echo "    make proof Q=10 PROOF_OPTS=--compare  the challenge's comparator       ~2 h"
	@echo "    (Q = 9, 10, 11, 12; THREADS=$(THREADS))"
	@echo ""
	@echo "Window inputs of Proposition 5.1"
	@echo "    make conditions                   (W1), (W2) in Arb, against the record  <1 min"
	@echo "    make hfloor                       the H floor H_W^- in Arb, 60 digits    <1 min"
	@echo ""
	@echo "Setup and paper"
	@echo "    make venv                         .venv with requirements.txt"
	@echo "    make paper                        paper/simple-zeros-lower-bound.pdf      ~1 min, needs pdflatex"
	@echo ""
	@echo "The generator of the Lean proofs: src/lbcert/README.md"

venv:
	python3 -m venv .venv
	.venv/bin/pip install -q -r requirements.txt

# proofs/fetch.sh downloads each archive and checks its SHA-256; proofs/verify.sh builds the proof.
proofs:
	bash proofs/fetch.sh

proof:
	@[ -d proofs/q$(Q) ] || bash proofs/fetch.sh q$(Q)
	THREADS=$(THREADS) bash proofs/verify.sh q$(Q) $(PROOF_OPTS)

# The window conditions (W1), (W2) of the main theorem's window, recomputed in Arb and compared
# with the shipped record. The conclusions must agree exactly. The ball values agree to about
# 1e-18, not bit for bit: FLINT builds on different platforms round the lower end of a ball
# differently, and every such lower end is a rigorous bound.
define CONDITIONS_COMPARE
import json, sys
f = 'sep_conditions_final2_q12.json'
a, b = (json.load(open(d + '/' + f)) for d in (sys.argv[1], 'results'))
mid = lambda x: float(str(x).strip('[]').split('+/-')[0])
same = all(a[k] == b[k] for k in ('cert', 'sep', 'gamma', 'segments', 'c_le_1_64', 'ok')) and a['ok']
close = all(abs(mid(a[k]) - mid(b[k])) < 1e-15 for k in
            ('majorant_margin_lower', 'eigencap_L_upper', 'close_pair_margin_lower', 'rho_upper'))
print('  ', f, 'MATCH' if same and close else 'DIFFERS')
sys.exit(not (same and close))
endef
export CONDITIONS_COMPARE
conditions:
	mkdir -p $(RUN)
	$(PYTHON) src/sep_conditions_cert.py --out $(RUN)/sep_conditions_final2_q12.json
	$(PYTHON) -c "$$CONDITIONS_COMPARE" $(RUN)

# The H floor of Proposition 5.1: the Arb enclosure of H = 2 - W(v) for the window of Table 1,
# against H_W^- = 6720761997177286221959388707769754155716 / 10^40 of the Lean theorem HW_ge.
define HFLOOR_CHECK
import json, sys
from fractions import Fraction
from pipeline.hfloor import H_interval
from pipeline.freqspec import harm_specs
w = json.load(open('src/lbcert/q12win/work/final2_q12.json'))['window']
H, _, _ = H_interval(w['numerators'], w['denominator'], harm_specs(16, 'sqrt(2)'), dps=60)
HW = Fraction(6720761997177286221959388707769754155716, 10**40)
print('   H in [%.17f, %.17f]' % (H.a, H.b))
print('   lower end - H_W^- = %.3e' % float(H.a - HW), 'PASS' if H.a >= HW else 'FAIL')
sys.exit(H.a < HW)
endef
export HFLOOR_CHECK
hfloor:
	$(PYTHON) -c "$$HFLOOR_CHECK"

paper:
	bash paper/build.sh

clean:
	rm -rf $(RUN) paper/*.aux paper/*.log paper/*.out
