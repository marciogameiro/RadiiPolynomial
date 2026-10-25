# RadiiPolynomial

A Lean 4 library for the radii polynomial approach to computer-assisted proofs in dynamics:
weighted sequence spaces and their convolution algebras, the radii polynomial theorems, problem
classes of differential equations (operators, bounds, exact checkers, interpretation of zeros as
solutions), and exact rational certificates.

Lean `v4.35.0`, Mathlib `v4.35.0`. No `sorry`; the axioms are `propext`, `Classical.choice` and
`Quot.sound`.

```bash
lake exe cache get   # Mathlib build cache
lake build
python3 scripts/check_layers.py
```

## Layers

Each folder of `RadiiPolynomial/` is a layer. A file may import Mathlib and, from this library,
only the layers listed for it; `scripts/check_layers.py` checks this.

| Layer | Contents | May import |
|---|---|---|
| `WeightedLp` | weights, weighted ℓ^p spaces `WeightedLp 𝕜 ω p` (by transport from Mathlib's `lp`), `WeightedL1`, column-norm bounds for operators | — |
| `Convolution` | the Banach algebra ℓ¹_{ω,I} under convolution (commutative monoid `I`, submultiplicative `ω`), Young's inequality, evaluation at bounded characters, power series, Taylor, Chebyshev, cosine and Fourier sequence spaces, Chebyshev and Fourier series as functions | `WeightedLp` |
| `Calculus` | derivatives and Lipschitz bounds of polynomial maps on Banach algebras, uniqueness for ODEs (Grönwall) | `WeightedLp`, `Convolution` |
| `Abstract` | the radii polynomial theorems (`radii_poly`, `radii_poly_two_radii`, `HasIsolatedZero`), injectivity, nondegenerate zeros | — |
| `BlockTail` | operators made of a finite block and a diagonal tail (approximate inverses and derivatives), with an extra scalar unknown | `WeightedLp`, `Abstract` |
| `Certificate` | exact rational data: matrices, polynomials, finite sequences (Taylor, Chebyshev, cosine, Fourier), complex rationals, with soundness theorems | `WeightedLp`, `Convolution`, `Calculus`, `Abstract` |
| `Problems` | problem classes: `FiniteDimZeros`, `TaylorIVP`, `ChebBVP` (Chebyshev BVPs and IVPs), `CubicCosine`, `QuadraticFourier`, `FourierPeriodic`; for each, the operator `F`, the bound theorem (`*Radii`), the checker (`*Check`) and the interpretation (`*Solution`) | all of the above |

The general part, `WeightedLp`, `Convolution` and `Calculus`, depends on Mathlib only.

## Conventions

* Every file is a Lean module: `module`, `public import …`, and `@[expose] public section` after
  the module docstring (all declarations and definition bodies are visible to importers).
  A downstream file that runs a checker with `native_decide` needs `public meta import` of the
  checker module (`RadiiPolynomial.Problems.*Check`).
* The layer rule is checked by `scripts/check_layers.py`, which the pre-commit hook
  `scripts/hooks/pre-commit` runs; enable it once per clone with
  `git config core.hooksPath scripts/hooks`.
* No references to any book in the comments; mathematical statements are documented in the module
  docstrings.
* Problem theorems take bounds as real inequalities; checkers compute them exactly from data and
  are proved to be sound, so certification backends can be exchanged.

## Users

The computer-assisted proofs of the book *Ordinary Differential Equations: A Constructive Approach*
are checked with this library in the project `lean/` of the repository `LeanearizedODEs`.

## License

Released under the MIT License; see [`LICENSE`](LICENSE).
