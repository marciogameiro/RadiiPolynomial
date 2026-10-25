module

public import RadiiPolynomial.Convolution.Chebyshev
public import RadiiPolynomial.Calculus.Polynomial

/-!
# Boundary value problems via Chebyshev series

A boundary value problem

  `u' = L f(u)` on `[-1, 1]`,   `B₋ u(-1) + B₊ u(1) = q`,

with a polynomial vector field `f : ℝⁿ → ℝⁿ` (`ChebBVP`), is written as a zero finding problem
`F(a) = 0` for the Chebyshev coefficients `a = (a_1, …, a_n) ∈ X = X_ν^n` (max norm), with values
in `Y = Y_ν^n`:

  `F_j(a)_0 = q_j - ∑ᵢ (B₋)_{ji} uᵢ(-1) - ∑ᵢ (B₊)_{ji} uᵢ(1)`,
  `F_j(a)_k = 2k (a_j)_k + L ((c_j)_{k+1} - (c_j)_{k-1})`   (`k ≥ 1`),

where `c_j = φ_j(a)` is `f_j` evaluated with the Chebyshev product and
`uᵢ(±1) = (aᵢ)_0 + 2 ∑_{k ≥ 1} (±1)^k (aᵢ)_k`. In operator form
`F_j(a) = (q_j - ℓ_j(a)) e₀ + D a_j + L S φ_j(a)` (`ChebBVP.F`), with the bounded operators `D`, `S`
and the boundary functional `ℓ_j` (`ChebBVP.bcLin`).

`ChebBVP.hasFDerivAt_F`: `F` is Fréchet differentiable, with
`DF(a) h = (-ℓ_j(h)) e₀ + D h_j + L S (∑ᵢ ∂ᵢφ_j(a) * hᵢ)` (`ChebBVP.DF`).

The initial value problem `u(-1) = x₀` is the case `B₋ = I`, `B₊ = 0`, `q = x₀` (`ChebBVP.ivp`).
-/

@[expose] public section

namespace RadiiPolynomial

open Chebyshev MvPolynomial

/-- A boundary value problem `u' = L f(u)` on `[-1, 1]`, `B₋ u(-1) + B₊ u(1) = q`, with a polynomial
vector field `f = (f_1, …, f_n)`. -/
structure ChebBVP (n : ℕ) where
  /-- the vector field, a polynomial in each component -/
  f : Fin n → MvPolynomial (Fin n) ℝ
  /-- the time scaling -/
  L : ℝ
  /-- the boundary matrix at `t = -1` -/
  Bm : Matrix (Fin n) (Fin n) ℝ
  /-- the boundary matrix at `t = 1` -/
  Bp : Matrix (Fin n) (Fin n) ℝ
  /-- the right-hand side of the boundary condition -/
  q : Fin n → ℝ

namespace ChebBVP

/-- The initial value problem `u' = L f(u)`, `u(-1) = x₀`. -/
def ivp {n : ℕ} (f : Fin n → MvPolynomial (Fin n) ℝ) (L : ℝ) (x₀ : Fin n → ℝ) : ChebBVP n :=
  ⟨f, L, 1, 0, x₀⟩

variable {n : ℕ} (P : ChebBVP n) (ν : ℝ) (hν : 1 ≤ ν)

/-- `u(-1) = a_0 + 2 ∑_{k ≥ 1} (-1)^k a_k`. -/
noncomputable abbrev evalMinus : X ν hν →L[ℝ] ℝ := boundaryEval ν hν (-1) (by simp)

/-- `u(1) = a_0 + 2 ∑_{k ≥ 1} a_k`. -/
noncomputable abbrev evalPlus : X ν hν →L[ℝ] ℝ := boundaryEval ν hν 1 (by simp)

/-- The linear part of the boundary condition, row `j`:
`ℓ_j(a) = ∑ᵢ (B₋)_{ji} uᵢ(-1) + ∑ᵢ (B₊)_{ji} uᵢ(1)`. -/
noncomputable def bcLin (j : Fin n) : (Fin n → X ν hν) →L[ℝ] ℝ :=
  ∑ i, (P.Bm j i • (evalMinus ν hν).comp (ContinuousLinearMap.proj i) +
    P.Bp j i • (evalPlus ν hν).comp (ContinuousLinearMap.proj i))

/-- The zero finding map `F : X_ν^n → Y_ν^n`. -/
noncomputable def F (a : Fin n → X ν hν) : Fin n → Y ν hν := fun j =>
  (P.q j - P.bcLin ν hν j a) • e0 ν hν + diffOp ν hν (a j) +
    P.L • shiftOp ν hν (aeval a (P.f j))

/-- The derivative of `F`. -/
noncomputable def DF (a : Fin n → X ν hν) : (Fin n → X ν hν) →L[ℝ] (Fin n → Y ν hν) :=
  ContinuousLinearMap.pi fun j =>
    -(P.bcLin ν hν j).smulRight (e0 ν hν) + (diffOp ν hν).comp (ContinuousLinearMap.proj j) +
      P.L • (shiftOp ν hν).comp (polyDeriv (P.f j) a)

/-- `F` is Fréchet differentiable with derivative `DF`. -/
theorem hasFDerivAt_F (a : Fin n → X ν hν) : HasFDerivAt (P.F ν hν) (P.DF ν hν a) a := by
  refine hasFDerivAt_pi.2 fun j => ?_
  have h1 : HasFDerivAt (fun x : Fin n → X ν hν => (P.q j - P.bcLin ν hν j x) • e0 ν hν)
      (-(P.bcLin ν hν j).smulRight (e0 ν hν)) a := by
    have := ((hasFDerivAt_const (P.q j) a).sub (P.bcLin ν hν j).hasFDerivAt).smul_const (e0 ν hν)
    convert this using 1
    ext h; simp
  have h2 : HasFDerivAt (fun x : Fin n → X ν hν => diffOp ν hν (x j))
      ((diffOp ν hν).comp (ContinuousLinearMap.proj j)) a :=
    ((diffOp ν hν).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => X ν hν) j)).hasFDerivAt
  have h3 : HasFDerivAt (fun x : Fin n → X ν hν => P.L • shiftOp ν hν (aeval x (P.f j)))
      (P.L • (shiftOp ν hν).comp (polyDeriv (P.f j) a)) a :=
    ((shiftOp ν hν).hasFDerivAt.comp a (hasFDerivAt_aeval (P.f j) a)).const_smul P.L
  exact (h1.add h2).add h3

theorem F_apply_zero (a : Fin n → X ν hν) (j : Fin n) :
    P.F ν hν a j 0 = P.q j - P.bcLin ν hν j a := by
  simp [F, diffOp_apply, shiftOp_apply]

theorem F_apply_of_ne_zero (a : Fin n → X ν hν) (j : Fin n) {k : ℕ} (hk : k ≠ 0) :
    P.F ν hν a j k =
      2 * k * a j k + P.L * ((aeval a (P.f j)) (k + 1) - (aeval a (P.f j)) (k - 1)) := by
  simp [F, diffOp_apply, shiftOp_apply, hk]

end ChebBVP

end RadiiPolynomial
