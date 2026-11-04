# Characteristic Set

The goal of this project is to formalize the Characteristic Set Method (also known as Wu's Method) in the Lean 4 theorem prover. This project establishes the mathematical infrastructure for algebraic geometry based on triangular decomposition, bridging the gap between Lean and algorithmic methods for solving systems of multivariate polynomial equations.

This project is a work in progress; feedback, fixes, and suggestions are highly welcome.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/lean_characteristic_set)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/lean_characteristic_set)

## Introduction

### Definitions

- [`MvPolynomial.mainDegree`](./packages/theory/CharacteristicSetTheory/MainDegree.lean): The multiset of occurrences of the largest variable in a polynomial. Its cardinality is the degree in that variable; it is empty for constants and zero.
- [`MvPolynomial.rank` and `TriangularSet.rank`](./packages/theory/CharacteristicSetTheory/Rank.lean): The ranks used to order polynomials and triangular sets.
- [`MvPolynomial.pseudo` and `MvPolynomial.setPseudo`](./packages/theory/CharacteristicSetTheory/PseudoDivision.lean): Pseudo-division by a polynomial or a triangular set.
- [`TriangularSet`](./packages/theory/CharacteristicSetTheory/TriangularSet.lean): A finite ordered sequence of nonzero polynomials with strictly increasing classes.
- [`TriangularSet.IsAscendingSet` and `TriangularSet.IsWeakAscendingSet`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): Ritt's strong ascending sets and Wu's weak ascending sets, respectively.
- [`BasicSetSpec`](./packages/theory/CharacteristicSetTheory/BasicSet.lean): The interface required by the characteristic-set and zero-decomposition algorithms.
- [`Computable.Standard.basicSet` and `Computable.Weak.basicSet`](./CharacteristicSet/Computable/AscendingSet.lean): Executable standard and weak basic sets on Hex polynomial lists, with matching `isAscendingSet` checks.
- [`Bridge.Standard.basicSetSpec` and `Bridge.Weak.basicSetSpec`](./packages/bridge/CharacteristicSetBridge/BasicSet.lean): Specifications built from the executable algorithms for `Fin n` variables. The theory package provides the abstract interface; the bridge proves structure and rank minimality directly for the executable loops and supplies both implementations. Both preserve the complete ordered output, including stable equal-rank selection. The existing `Computable.basicSet` name remains a standard-algorithm compatibility entry point.
- [`Computable.Standard.characteristicSet` and `Computable.Weak.characteristicSet`](./CharacteristicSet/Computable/CharacteristicSet.lean): Executable characteristic sets returning Hex polynomial lists without an iteration limit. Import `CharacteristicSet.Computable` to run either algorithm independently. Computation stays in Hex; the bridge separately proves termination by rank descent and mathematical correctness.
- [`Bridge.Standard.characteristicSet_toMvPolynomial` and `Bridge.Weak.characteristicSet_toMvPolynomial`](./packages/bridge/CharacteristicSetBridge/CharacteristicSet.lean): Exact ordered correspondence with the theory algorithms. The `characteristicSet_terminates` theorem proves termination over fields; `characteristicSet_check` and `characteristicSet_correct` establish the corresponding ascending property and characteristic-set correctness for the actual output.
- [`MvPolynomial.List.characteristicSet`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The characteristic set of a list of polynomials.
- [`MvPolynomial.List.zeroDecomposition`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): A list of triangular sets that decompose the zero set of a polynomial system.

### Main Statements

Given a field $K$, an ordered finite index set $\sigma$, and a list of polynomials $PS \subseteq K[x_\sigma]$, we establish the following core results:

- [`Bridge.Standard.basicSet_minimal` and `Bridge.Weak.basicSet_minimal`](./packages/bridge/CharacteristicSetBridge/BasicSetCorrectness.lean): The computed basic set is minimal among ascending sets contained in the input list, for either ascending-set predicate.
- [`MvPolynomial.List.characteristicSet_isCharacteristicSet`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The computed characteristic set $CS$ has zero pseudo-remainders for the input polynomials and satisfies $Zero(PS) \subseteq Zero(CS)$.
- [`MvPolynomial.List.vanishingSet_eq_zeroDecomposition_union`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The zero set of a polynomial system is a finite union of quasi-varieties:
  $Zero(PS) = \bigcup_{CS \in \mathcal{ZD}} Zero(CS / \text{InitialProd}(CS))$.

### Packages and executable foundations

| Package location | Import | Contents |
| --- | --- | --- |
| Repository root | `CharacteristicSet` | Executable polynomial foundations |
| `packages/theory` | `CharacteristicSetTheory` | Mathematical definitions, algorithms, and proofs |
| `packages/bridge` | `CharacteristicSetBridge` | Computation, theory, and correspondence proofs |

[Performance benchmarks](bench/README.md)

## Project Resources

We maintain a set of web-based resources to track and explore the formalization effort:

- 📘 **[Project Homepage](https://wuprover.github.io/lean_characteristic_set/)**

- 📐 **[Formalization Blueprint](https://wuprover.github.io/lean_characteristic_set/blueprint/)**
  A detailed list of definitions, lemmas, and theorems, including their proof status and logical dependencies.

- 🔗 **[Dependency Graph](https://wuprover.github.io/lean_characteristic_set/blueprint/dep_graph_document.html)**
  A visual representation of the dependency structure of the formalized components.

These tools help us manage development, track progress toward formalization, and guide future contributors.

## Build

To use this project, you'll need to have Lean 4 and its package manager lake installed. If you don’t already have Lean 4 set up, follow the [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the executable foundations:

``` bash
git clone https://github.com/WuProver/lean_characteristic_set.git
cd lean_characteristic_set
lake build
# For the full theory and correctness bridges:
lake -d packages/bridge exe cache get
lake -d packages/bridge build
```

Executable examples live in `CharacteristicSet/Computable/Examples/` and run without
Mathlib or bridge imports. They are checked by the root package’s `lake build`:

```bash
lake env lean CharacteristicSet/Computable/Examples/Basic.lean
lake env lean CharacteristicSet/Computable/Examples/CharacteristicSet.lean
```

## References

Wen-Tsun, W. Mathematics Mechanization: Mechanical Geometry Theorem-Proving, Mechanical Geometry Problem-Solving and Polynomial Equations-Solving. Springer, 2001. https://link.springer.com/book/9780792358350

Wen-Tsun, W. Basic principles of mechanical theorem proving in elementary geometries. Journal of Automated  Reasoning 2, 221–252 (1986). https://doi.org/10.1007/BF02328447
