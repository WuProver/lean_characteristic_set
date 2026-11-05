"""Optional SymPy backend. Install bench/cas/requirements.txt in your Python environment."""
import json
from pathlib import Path
import sys
import time

import sympy
from sympy import Poly, QQ, Rational, symbols
from sympy.external.gmpy import GROUND_TYPES

x, y = symbols("x y")
fixture = json.loads(Path(sys.argv[1]).read_text())


def polynomial(ts):
    return Poly.from_dict({tuple(t["powers"]): Rational(t["num"], t["den"]) for t in ts},
                          (x, y), domain=QQ)


def encode(p):
    return [{"powers": list(m), "num": str(c.p), "den": str(c.q)} for m, c in p.terms()]


p, q = polynomial(fixture["lhs"]), polynomial(fixture["rhs"])
r = p*q  # warmup, outside the timed batches
samples = []
batch = fixture["batch_size"]
for trial in range(fixture["trials"]):
    inputs = [q + (trial*batch + i + 1) for i in range(batch)]
    outputs = []
    start = time.perf_counter()
    outputs = [p * operand for operand in inputs]
    seconds = time.perf_counter() - start
    samples.append({"seconds": seconds, "outputs": [encode(o) for o in outputs]})
print("CSBENCH_VERSION:" + sympy.__version__ + "; Python=" + sys.version.split()[0]
      + "; ground_types=" + GROUND_TYPES)
print("CSBENCH_RESULT:" + json.dumps({"terms": encode(r), "samples": samples}, separators=(",", ":")))
