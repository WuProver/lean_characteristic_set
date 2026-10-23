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

- [`MvPolynomial.mainDegree`](./packages/theory/CharacteristicSetTheory/MainDegree.lean): The multiset of occurrences of the largest variable in a polynomial. Its cardinality is the degree in that variable; it is empty for constants and zero.
- [`MvPolynomial.rank` and `TriangularSet.rank`](./packages/theory/CharacteristicSetTheory/Rank.lean): The ranks used to order polynomials and triangular sets.
- [`MvPolynomial.pseudo` and `MvPolynomial.setPseudo`](./packages/theory/CharacteristicSetTheory/PseudoDivision.lean): Pseudo-division by a polynomial or a triangular set.
- [`TriangularSet`](./packages/theory/CharacteristicSetTheory/TriangularSet.lean): A finite ordered sequence of nonzero polynomials with strictly increasing classes.
- [`TriangularSet.IsAscendingSet` and `TriangularSet.IsWeakAscendingSet`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): Ritt's strong ascending sets and Wu's weak ascending sets, respectively.
- [`AscendingSetTheory`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): An interface parameterized by the ascending-set predicate, providing the basic-set algorithm and its properties.
- [`MvPolynomial.List.basicSet`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): The minimal ascending set contained in a list of polynomials.
- [`MvPolynomial.List.characteristicSet`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The characteristic set of a list of polynomials.
- [`MvPolynomial.List.zeroDecomposition`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): A list of triangular sets that decompose the zero set of a polynomial system.

### Main Statements

Given a field $K$, an ordered finite index set $\sigma$, and a list of polynomials $PS \subseteq K[x_\sigma]$, we establish the following core results:

- [`MvPolynomial.List.basicSet_minimal`](./packages/theory/CharacteristicSetTheory/AscendingSet.lean): The computed basic set is minimal among ascending sets contained in the input list, for either ascending-set predicate.
- [`MvPolynomial.List.characteristicSet_isCharacteristicSet`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The computed characteristic set $CS$ has zero pseudo-remainders for the input polynomials and satisfies $Zero(PS) \subseteq Zero(CS)$.
- [`MvPolynomial.List.vanishingSet_eq_zeroDecomposition_union`](./packages/theory/CharacteristicSetTheory/CharacteristicSet.lean): The zero set of a polynomial system is a finite union of quasi-varieties:
  $Zero(PS) = \bigcup_{CS \in \mathcal{ZD}} Zero(CS / \text{InitialProd}(CS))$.

The algorithms take the ascending-set predicate explicitly, so both theories can be used together:

```lean
import CharacteristicSetTheory

open MvPolynomial

noncomputable section

example (l : List (MvPolynomial (Fin 2) ℚ)) :
    (l.characteristicSet TriangularSet.IsAscendingSet).IsCharacteristicSet ℚ l :=
  List.characteristicSet_isCharacteristicSet ℚ l

example (l : List (MvPolynomial (Fin 2) ℚ)) :
    (l.characteristicSet TriangularSet.IsWeakAscendingSet).IsCharacteristicSet ℚ l :=
  List.characteristicSet_isCharacteristicSet ℚ l
```

### Packages and executable foundations

The repository contains three Lake packages with independent module roots:

| Package location | Package/library and entry point | Dependencies |
| --- | --- | --- |
| Repository root | `CharacteristicSet` | Hex computation libraries only |
| `packages/theory` | `CharacteristicSetTheory` | Mathlib and its normal dependencies only |
| `packages/bridge` | `CharacteristicSetBridge` | Both local packages, fixed Hex theory, Mathlib, doc-gen4 and checkdecls |

All packages use Lean 4.35.0. Mathlib remains at v4.35.0 and Hex and tooling
revisions are fixed by their manifests. The Bridge workspace directly pins Mathlib
to this release because the fixed Hex theory release originally pinned an older revision.

`import CharacteristicSet` (or `CharacteristicSet.Computable`) provides `mainVar`,
numerical `mainDegree`, `initialOf`, `initial`, `rank`, and `compareRank` in
`CharacteristicSet.Computable`. They run directly on `Hex.MvPoly n R cmp`.
The main variable uses the natural order on `Fin n`, independently of the storage
comparator `cmp`. `compareRank` compares the variable and then the degree;
its `.eq` result means equal ranks, and polynomial equality remains Hex equality.

`import CharacteristicSetTheory` provides the full reference theory, including
ascending sets, pseudo-division and characteristic sets.
`import CharacteristicSetBridge` provides both full entries and all general
correctness bridges through `HexMvPolyTheory.toMvPolynomial`.
Theoretical modules formerly named `CharacteristicSet.Initial`, etc. are now
`CharacteristicSetTheory.Initial`, etc.; `CharacteristicSet.Bridge.*` modules
are now `CharacteristicSetBridge.*`. Public declaration namespaces and names,
including `MvPolynomial`, `TriangularSet`, `CharacteristicSet.Computable` and
`CharacteristicSet.Bridge`, are preserved. The root `CharacteristicSet` import
now selects the executable computation entry point.

Build the computation package and run its 19 rational-coefficient assertions:

```bash
lake build
lake env lean CharacteristicSet/Computable/Examples.lean
```

See [the examples](./CharacteristicSet/Computable/Examples.lean) for construction,
arithmetic, zero and constant cases, and different storage orders. Executable
pseudo-division and characteristic-set algorithms are not included in this layer yet.

Build only the complete Mathlib theory:

```bash
cd packages/theory
lake exe cache get
lake build
```

Build the full Bridge workspace, API documentation and blueprint declaration checks:

```bash
cd packages/bridge
lake exe cache get
lake build
LEAN_NUM_THREADS=2 lake build CharacteristicSetBridge:docs
lake exe checkdecls ../../blueprint/lean_decls
```

The declaration list is generated by the existing repository-level blueprint build.
API documentation reads [`packages/bridge/docs/references.bib`](./packages/bridge/docs/references.bib)
and writes `packages/bridge/.lake/build/doc`; CI copies that directory to
`home_page/docs`. Native `lake env lean`, doc-gen4 and checkdecls resolve the three
module roots directly. Each library uses Lake's conventional root and submodule glob.

Codespaces/devcontainers and Gitpod Classic prepare the pinned Lean toolchain in
their images. After checkout, workspace initialization fetches Mathlib's cache and
builds the complete project through `packages/bridge`, using each package's own
Lake build directory. Both initialization commands can be run again from the
repository root.

Other projects can select any one of the packages via Lake's Git dependency support.
Pin `rev` to a commit containing this layout. For computation:

```toml
[[require]]
name = "CharacteristicSet"
git = "https://github.com/WuProver/lean_characteristic_set.git"
rev = "<commit-containing-the-three-packages>"
```

For pure theory, use `name = "CharacteristicSetTheory"` and add
`subDir = "packages/theory"`. For the complete Bridge workspace, use
`name = "CharacteristicSetBridge"` and `subDir = "packages/bridge"`.
Git subdirectory dependencies retain the whole repository checkout, so the Bridge
package's `../..` and `../theory` path dependencies resolve within that checkout.
For local checkouts, replace `git`, `rev`, and `subDir` with respectively
`path = "../lean_characteristic_set"`,
`path = "../lean_characteristic_set/packages/theory"`, or
`path = "../lean_characteristic_set/packages/bridge"`.

Run the reproducible computation isolation check from the repository root:

```bash
python3 scripts/verify_computable.py
# Optional: reuse clean dependency Git sources, without their build artifacts.
python3 scripts/verify_computable.py --dependency-cache .lake/packages
```

The script copies only the computation sources and configuration to a fresh directory
outside the repository, clears `LEAN_PATH` and `LEAN_SRC_PATH`, builds the package
and examples, and builds a minimal consumer. It checks the pinned dependency manifest,
source import closure and consumer search paths, and requires Mathlib, Hex theory,
project theory and Bridge imports to fail because their modules are unavailable.
It prints the retained temporary directory containing command logs and evidence.

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
lake build
# For the full theory and correctness bridges:
cd packages/bridge
lake exe cache get
lake build
```

## References

Wen-Tsun, W. Mathematics Mechanization: Mechanical Geometry Theorem-Proving, Mechanical Geometry Problem-Solving and Polynomial Equations-Solving. Springer, 2001. https://link.springer.com/book/9780792358350

Wen-Tsun, W. Basic principles of mechanical theorem proving in elementary geometries. Journal of Automated  Reasoning 2, 221–252 (1986). https://doi.org/10.1007/BF02328447
