#!/usr/bin/env python3
"""val96.py Q LOG OUTDIR WORKERS SPEC...: cold 96-round refits (winobj.evaluate, x0 None, 1 thread each) of
CMA log entries; SPEC is gen:i, or gen:best for the best of that generation.  Writes OUTDIR/g<gen>i<i>.json."""
import json, os, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import winobj

q, log, out, nw = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4])
E = [json.loads(l) for l in open(log)]
E = [e for e in E if 'i' in e and 'xfree' in e]
jobs = []
for s in sys.argv[5:]:
    g, i = s.split(':')
    G = [e for e in E if e['gen'] == int(g)]
    e = max(G, key=lambda e: e['achieved']) if i == 'best' else next(e for e in G if e['i'] == int(i))
    jobs.append(e)

def run(e):
    r = winobj.evaluate(e['xfree'], q, rounds=96, threads=1, x0=None)
    r.update(xfree=e['xfree'], q=q, gen=e['gen'], i=e['i'], achieved40=e['achieved'], rounds=96, warm='none (cold)')
    p = os.path.join(out, 'g%di%d.json' % (e['gen'], e['i']))
    open(p, 'w').write(json.dumps(r, indent=1))
    return '%s achieved40 %.10f achieved96 %.10f ceiling %.10f kappa_lb %.10f secs %s' % (
        p, e['achieved'], r['achieved'], r.get('ceiling', -1), r.get('kappa_lb', -1), r['secs'])

os.makedirs(out, exist_ok=True)
with Pool(nw) as P:
    for s in P.imap_unordered(run, jobs):
        print(s, flush=True)
