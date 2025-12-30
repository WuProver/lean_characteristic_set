# Characteristic Set

The goal of this project is the formalization of the Characteristic Set Method (also known as Wu's Method) in  Lean 4 theorem prover. This project establishes the mathematical infrastructure for algebraic geometry based on triangular decomposition, bridging the gap between Lean and algorithmic methods for solving systems of multivariate polynomial equations.

This project is still work in process. Any fix and suggestions will be welcomed.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/lean_characteristic_set)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/lean_characteristic_set)

## Introduction

### Definitions

- [`MvPolynomial.cls`](./CharacteristicSet/Basic.lean): The **class** of a polynomial (the largest variable index in its support).
- [`MvPolynomial.pseudo`](./CharacteristicSet/PseudoDivision.lean): **Pseudo-division** of a polynomial $g$ by a polynomial $f$ (or a triangulated set).
- [`TriangulatedSet`](./CharacteristicSet/TriangulatedSet.lean): A finite ordered sequence of polynomials with strictly increasing classes.
- [`AscendingSet`](./CharacteristicSet/AscendingSet.lean): An abstract **Ascending Set**. This is a `TriangulatedSet` where every element is reduced with respect to its predecessors.
- [`StandardAscendingSet`](./CharacteristicSet/StandardAscendingSet.lean) and [`WeakAscendingSet`](./CharacteristicSet/WeakAscendingSet.lean): Concrete instances of ascending sets using **strong reduction** (Ritt) and **initial reduction** (Wu), respectively.
- [`MvPolynomial.List.basicSet`](./CharacteristicSet/AscendingSet.lean): The **Basic Set** of a polynomial set, defined as the minimal ascending set contained within the set.
- [`MvPolynomial.List.characteristicSet`](./CharacteristicSet/CharacteristicSet.lean): The **Characteristic Set** of a polynomial set.
- [`MvPolynomial.List.zeroDecomposition`](./CharacteristicSet/CharacteristicSet.lean): A list of characteristic sets that decompose the zero set of a polynomial set.

### Main Statements

Given a field $K$, an ordered finite index set $\sigma$, and a list of polynomials $PS \subseteq K[x_\sigma]$, we establish the following core results:

- [`MvPolynomial.Classical.hasBasicSet`](./CharacteristicSet/AscendingSet.lean): For any set of polynomials, there exists a Basic Set (a minimal ascending set) contained within it.
- [`StandardAscendingSet.basicSet_minimal`](./CharacteristicSet/StandardAscendingSet.lean) and [`WeakAscendingSet.basicSet_minimal`](./WeakAscendingSet.lean): The provided algorithms correctly compute the Basic Set according to Ritt's and Wu's definitions respectively.
- [`MvPolynomial.List.characteristicSet_isCharacteristicSet`](./CharacteristicSet/CharacteristicSet.lean): The computed Characteristic Set $CS$ satisfies the key algebraic property (pseudo-remainder of input polynomials is 0) and the geometric property ( $Zero(PS) \subseteq Zero(CS)$ ).
- [`MvPolynomial.List.vanishingSet_eq_zeroDecomposition_union`](./CharacteristicSet/CharacteristicSet.lean): **Zero Decomposition Theorem**. The zero set of a polynomial system $PS$ can be decomposed into a finite union of "quasi-varieties" defined by triangular sets:
  $Zero(PS) = \bigcup_{CS \in \mathcal{D}} Zero(CS / \text{InitialProd}(CS))$

## Project Resources
We maintain a set of web-based resources to track and explore the formalization effort:

- 📘 **[Project Homepage](https://wuprover.github.io/lean_characteristic_set/)**

- 📐 **[Formalization Blueprint](https://wuprover.github.io/lean_characteristic_set/blueprint/)**
  A detailed list of definitions, lemmas, and theorems, including their proof status and logical dependencies.

- 🔗 **[Dependency Graph](https://wuprover.github.io/lean_characteristic_set/blueprint/dep_graph_document.html)**
  A visual representation of the dependency structure of the formalized components.

These tools help us manage development, track formalization progress, and guide future contributors.

## Build

To use this project, you'll need to have Lean 4 and its package manager lake installed. If you don’t already have Lean 4 set up, follow the [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:

``` bash
git clone https://github.com/WuProver/lean_characteristic_set.git
cd lean_characteristic_set
lake exe cache get
lake build
```

## Reference

Wen-Tsun, W. Mathematics Mechanization: Mechanical Geometry Theorem-Proving, Mechanical Geometry Problem-Solving and Polynomial Equations-Solving. Springer, 2001. https://link.springer.com/book/9780792358350

Wen-Tsun, W. Basic principles of mechanical theorem proving in elementary geometries. Journal of Automated  Reasoning 2, 221–252 (1986). https://doi.org/10.1007/BF02328447
