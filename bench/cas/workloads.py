"""Deterministic QQ[x,y] fixtures; expected products use independent convolution."""
from fractions import Fraction


def terms(coefficients):
    return [{"powers": list(p), "num": str(c.numerator), "den": str(c.denominator)}
            for p, c in sorted(coefficients.items()) if c]


def dense(size):
    left = {(i, j): Fraction((3*i + j) % 7 + 1, 2) for i in range(size) for j in range(size)}
    right = {(i, j): Fraction((i + 2*j) % 5 + 1, 3) for i in range(size) for j in range(size)}
    product = {}
    for (i, j), a in left.items():
        for (k, l), b in right.items():
            p = (i+k, j+l)
            product[p] = product.get(p, Fraction()) + a*b
    return {"id": f"dense-{size}", "variables": ["x", "y"],
            "lhs": terms(left), "rhs": terms(right), "expected": terms(product)}
