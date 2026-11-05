# Characteristic Set

The goal of this project is to formalize the Characteristic Set Method (also known as Wu's Method) in the Lean 4 theorem prover. This project establishes the mathematical infrastructure for algebraic geometry based on triangular decomposition, bridging the gap between Lean and algorithmic methods for solving systems of multivariate polynomial equations.

This project is a work in progress; feedback, fixes, and suggestions are highly welcome.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/lean_characteristic_set)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/lean_characteristic_set)

## Introduction

### Definitions

- [`MvPolynomial.mainDegree`](./packages/theory/CharacteristicSetTheory/MainDegree.lean): The degree in the largest variable, represented as a multiset.
- [`MvPolynomial.rank` and `TriangularSet.rank`](./packages/theory/CharacteristicSetTheory/Rank.lean): The ranks used to order polynomials and triangular sets.
- [`TriangularSet`](./packages/theory/CharacteristicSetTheory/TriangularSet.lean): A finite ordered sequence of nonzero polynomials with strictly increasing classes.
- [`TriangularSet.IsAscendingSet` and `TriangularSet.IsWeakAscendingSet`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): Ritt's strong ascending sets and Wu's weak ascending sets.
- [`PseudoDivisionSpec`](./packages/theory/CharacteristicSetTheory/PseudoDivision.lean): The specification for pseudo-division and its remainder.
- [`BasicSetSpec`](./packages/theory/CharacteristicSetTheory/BasicSet.lean): The basic-set interface used by characteristic sets and zero decomposition.

### Main Statements

For polynomial systems over a field, the project establishes:

- [Basic-set minimality](./packages/bridge/CharacteristicSetBridge/BasicSetCorrectness.lean): Standard and weak basic sets are minimal among the corresponding ascending sets contained in the input.
- [Characteristic-set correctness](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The computed characteristic set $CS$ has zero pseudo-remainders for the input polynomials and satisfies $Zero(PS) \subseteq Zero(CS)$.
- [Zero decomposition](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The zero set is a finite union of quasi-varieties:
  $Zero(PS) = \bigcup_{CS \in \mathcal{ZD}} Zero(CS / \text{InitialProd}(CS))$.

### Example

[Wallace–Simson theorem](./packages/bridge/CharacteristicSetBridge/Examples/Simson.lean): Collinearity of the three perpendicular feet, proved using the verified characteristic-set algorithm. Concrete computations use `native_decide`.

## Packages

The executable algorithms use [Hex](https://github.com/kim-em/hex-dev) for sparse multivariate polynomial arithmetic.

| Package | Import | Contents |
| --- | --- | --- |
| `packages/computable` | `CharacteristicSet` | Executable algorithms and examples, without Mathlib |
| `packages/theory` | `CharacteristicSetTheory` | Mathematical definitions, algorithms, and proofs |
| `packages/bridge` | `CharacteristicSetBridge` | Correspondence, termination, and correctness of the executable algorithms |

Computable and theory are independent; bridge depends on both. Standard and weak algorithms provide basic sets, characteristic sets, and zero decomposition. The repository root builds all three packages.

## Project Resources

- [Project Homepage](https://wuprover.github.io/lean_characteristic_set/)
- [Formalization Blueprint](https://wuprover.github.io/lean_characteristic_set/blueprint/)
- [Dependency Graph](https://wuprover.github.io/lean_characteristic_set/blueprint/dep_graph_document.html)
- [Performance Benchmarks](bench/README.md)

## Build

Install [Lean 4 and Lake](https://leanprover-community.github.io/get_started.html), then run:

```bash
git clone https://github.com/WuProver/lean_characteristic_set.git
cd lean_characteristic_set
lake exe cache get
lake build
```

To build only the executable algorithms:

```bash
lake -d packages/computable build
```

## References

Wen-Tsun, W. Mathematics Mechanization: Mechanical Geometry Theorem-Proving, Mechanical Geometry Problem-Solving and Polynomial Equations-Solving. Springer, 2001. https://link.springer.com/book/9780792358350

Wen-Tsun, W. Basic principles of mechanical theorem proving in elementary geometries. Journal of Automated  Reasoning 2, 221–252 (1986). https://doi.org/10.1007/BF02328447
