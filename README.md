# Characteristic Set

The goal of this project is to formalize the Characteristic Set Method (also known as Wu's Method) in the Lean 4 theorem prover. This project establishes the mathematical infrastructure for algebraic geometry based on triangular decomposition, bridging the gap between Lean and algorithmic methods for solving systems of multivariate polynomial equations.

This project is a work in progress; feedback, fixes, and suggestions are highly welcome.

The project uses **Lean 4.35.0** and official **mathlib v4.35.0**. Its characteristic-set
implementation is ported from [SnkXyx/mathlib4, `full-pr-draft` at `b7f37486`](https://github.com/SnkXyx/mathlib4/tree/b7f37486b1c723b65299b4fd7ad635131674d9e8),
with local module paths and compatibility changes for Lean 4.35.0.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/lean_characteristic_set)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/lean_characteristic_set)

## Introduction

### Definitions

- [`MvPolynomial.mainDegree`](./CharacteristicSet/MainDegree.lean): The multiset of occurrences of the largest variable in a polynomial. Its cardinality is the degree in that variable; it is empty for constants and zero.
- [`MvPolynomial.rank` and `TriangularSet.rank`](./CharacteristicSet/Rank.lean): The ranks used to order polynomials and triangular sets.
- [`MvPolynomial.pseudo` and `MvPolynomial.setPseudo`](./CharacteristicSet/PseudoDivision.lean): Pseudo-division by a polynomial or a triangular set.
- [`TriangularSet`](./CharacteristicSet/TriangularSet.lean): A finite ordered sequence of nonzero polynomials with strictly increasing classes.
- [`TriangularSet.IsAscendingSet` and `TriangularSet.IsWeakAscendingSet`](./CharacteristicSet/AscendingSet.lean): Ritt's strong ascending sets and Wu's weak ascending sets, respectively.
- [`AscendingSetTheory`](./CharacteristicSet/AscendingSet.lean): An interface parameterized by the ascending-set predicate, providing the basic-set algorithm and its properties.
- [`MvPolynomial.List.basicSet`](./CharacteristicSet/AscendingSet.lean): The minimal ascending set contained in a list of polynomials.
- [`MvPolynomial.List.characteristicSet`](./CharacteristicSet/CharacteristicSet.lean): The characteristic set of a list of polynomials.
- [`MvPolynomial.List.zeroDecomposition`](./CharacteristicSet/CharacteristicSet.lean): A list of triangular sets that decompose the zero set of a polynomial system.

### Main Statements

Given a field $K$, an ordered finite index set $\sigma$, and a list of polynomials $PS \subseteq K[x_\sigma]$, we establish the following core results:

- [`MvPolynomial.List.basicSet_minimal`](./CharacteristicSet/AscendingSet.lean): The computed basic set is minimal among ascending sets contained in the input list, for either ascending-set predicate.
- [`MvPolynomial.List.characteristicSet_isCharacteristicSet`](./CharacteristicSet/CharacteristicSet.lean): The computed characteristic set $CS$ has zero pseudo-remainders for the input polynomials and satisfies $Zero(PS) \subseteq Zero(CS)$.
- [`MvPolynomial.List.vanishingSet_eq_zeroDecomposition_union`](./CharacteristicSet/CharacteristicSet.lean): The zero set of a polynomial system is a finite union of quasi-varieties:
  $Zero(PS) = \bigcup_{CS \in \mathcal{ZD}} Zero(CS / \text{InitialProd}(CS))$.

The algorithms take the ascending-set predicate explicitly, so both theories can be used together:

```lean
import CharacteristicSet

open MvPolynomial

noncomputable section

example (l : List (MvPolynomial (Fin 2) ℚ)) :
    (l.characteristicSet TriangularSet.IsAscendingSet).IsCharacteristicSet ℚ l :=
  List.characteristicSet_isCharacteristicSet ℚ l

example (l : List (MvPolynomial (Fin 2) ℚ)) :
    (l.characteristicSet TriangularSet.IsWeakAscendingSet).IsCharacteristicSet ℚ l :=
  List.characteristicSet_isCharacteristicSet ℚ l
```

### Executable foundations

`import CharacteristicSet.Computable` provides `mainVar`, numerical `mainDegree`,
`initialOf`, `initial`, `rank`, and `compareRank` in `CharacteristicSet.Computable`.
They run directly on `Hex.MvPoly n R cmp`; the computation layer imports no Mathlib.
The main variable uses the natural order on `Fin n`, independently of the storage
comparator `cmp`. `compareRank` compares the variable and then the degree;
its `.eq` result means equal ranks, and polynomial equality remains Hex equality.

`import CharacteristicSet.Bridge` adds general correctness theorems relating these
operations to the existing `MvPolynomial` definitions, using
`HexMvPolyTheory.toMvPolynomial`. The original `CharacteristicSet` entry point
continues to provide the reference theory and algorithms.

Build both entry points and run the rational-coefficient examples with:

```bash
lake build CharacteristicSet.Computable CharacteristicSet.Bridge CharacteristicSet.Computable.Examples
lake env lean CharacteristicSet/Computable/Examples.lean
```

See [the examples](./CharacteristicSet/Computable/Examples.lean) for construction,
arithmetic, zero and constant cases, and different storage orders. Executable
pseudo-division and characteristic-set algorithms are not included in this layer yet.

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

Once Lean is installed, you can clone this repository and build the project:

``` bash
git clone https://github.com/WuProver/lean_characteristic_set.git
cd lean_characteristic_set
lake exe cache get
lake build
```

## References

Wen-Tsun, W. Mathematics Mechanization: Mechanical Geometry Theorem-Proving, Mechanical Geometry Problem-Solving and Polynomial Equations-Solving. Springer, 2001. https://link.springer.com/book/9780792358350

Wen-Tsun, W. Basic principles of mechanical theorem proving in elementary geometries. Journal of Automated  Reasoning 2, 221–252 (1986). https://doi.org/10.1007/BF02328447
