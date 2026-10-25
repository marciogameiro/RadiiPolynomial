module

public import RadiiPolynomial.Convolution.Cosine

/-!
# Cubic equilibrium problems in cosine series

For eigenvalues `μ = (μ_k)_{k ≥ 0}` (`CubicCosine`), the problem is `F(a) = 0` for the one-sided
cosine coefficients `a ∈ X = ℓ¹_ν` (`ν ≥ 1`, `Cosine.X`), where

  `F_k(a) = μ_k a_k - (a³)_k`,   `k ≥ 0`,

and `a³ = a * a * a` is the symmetric product (`Cosine.cube`). For instance, equilibria
`u(y) = a_0 + 2 ∑_{k ≥ 1} a_k cos(k L y)` of `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³` (even and
`2π/L`-periodic) are the zeros of `F` with `μ_k = λ - (1 - k² L²)²`.

In operator form `F(a) = Λ a - ι(a³)` (`CubicCosine.F`), with values in `Y = ℓ¹_ω`,
`ω_k = ν^k / (1 + |μ_k|)` (`CubicCosine.Y`), where `Λ` is the diagonal operator `(Λ a)_k = μ_k a_k`
and `ι : X → Y` the inclusion, both of norm at most `1`. Only `F : X → Y` and the boundedness of the
operators between `X` and `Y` depend on `Y`; all bounds of the radii polynomial theorem are in `X`.

`CubicCosine.hasFDerivAt_F`: `F` is Fréchet differentiable, with `DF(a) h = Λ h - 3 ι(a * a * h)`
(`CubicCosine.DF`).
-/

@[expose] public section

namespace RadiiPolynomial

open Cosine

/-- The eigenvalues `μ_k` of the linear part of a cubic equilibrium problem in cosine series. -/
structure CubicCosine where
  /-- the eigenvalue of the mode `cos(k L y)` -/
  μ : ℕ → ℝ

namespace CubicCosine

variable (P : CubicCosine) (ν : ℝ) (hν : 1 ≤ ν)

/-- The weights `ω_k = ν^k / (1 + |μ_k|)`. -/
noncomputable def weightsY : Weights ℕ :=
  ⟨fun k => ν ^ k / (1 + |P.μ k|), fun k => div_pos (pow_pos (Chebyshev.nu_pos hν) k)
    (by positivity)⟩

theorem weightsY_apply (k : ℕ) : P.weightsY ν hν k = ν ^ k / (1 + |P.μ k|) := rfl

/-- The codomain `Y = ℓ¹_ω`, `ω_k = ν^k / (1 + |μ_k|)`. -/
abbrev Y := WeightedL1 ℝ (P.weightsY ν hν)

variable {ν hν}

theorem diag_bound (k : ℕ) : ‖P.μ k‖ * P.weightsY ν hν k ≤ 1 * Cosine.weights ν hν k := by
  rw [weightsY_apply, Cosine.weights_apply, one_mul, Real.norm_eq_abs, mul_div_assoc', div_le_iff₀
    (by positivity)]
  nlinarith [pow_pos (Chebyshev.nu_pos hν) k, abs_nonneg (P.μ k)]

theorem incl_bound (k : ℕ) : ‖(1 : ℝ)‖ * P.weightsY ν hν k ≤ 1 * Cosine.weights ν hν k := by
  rw [weightsY_apply, Cosine.weights_apply, norm_one, one_mul, one_mul]
  exact div_le_self (pow_pos (Chebyshev.nu_pos hν) k).le (by linarith [abs_nonneg (P.μ k)])

variable (ν hν)

/-- The diagonal operator `(Λ a)_k = μ_k a_k`, `X → Y`, of norm at most `1`. -/
noncomputable def diag : X ν hν →L[ℝ] P.Y ν hν :=
  (ColNormBound.single (ω := P.weightsY ν hν) (ω' := Cosine.weights ν hν) (fun k => k) P.μ
    zero_le_one P.diag_bound).toCLM

/-- The inclusion `ι : X → Y`, of norm at most `1`. -/
noncomputable def incl : X ν hν →L[ℝ] P.Y ν hν :=
  (ColNormBound.single (ω := P.weightsY ν hν) (ω' := Cosine.weights ν hν) (fun k => k)
    (fun _ => (1 : ℝ)) zero_le_one P.incl_bound).toCLM

/-- The zero finding map `F(a) = Λ a - ι(a³)`. -/
noncomputable def F (a : X ν hν) : P.Y ν hν := P.diag ν hν a - P.incl ν hν (cube ν hν a)

/-- The derivative `DF(a) = Λ - ι ∘ D(a³)`. -/
noncomputable def DF (a : X ν hν) : X ν hν →L[ℝ] P.Y ν hν :=
  P.diag ν hν - (P.incl ν hν).comp (cubeDeriv ν hν a)

variable {ν hν}

@[simp] theorem diag_apply (a : X ν hν) (k : ℕ) : P.diag ν hν a k = P.μ k * a k := by
  rw [diag, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

@[simp] theorem incl_apply (a : X ν hν) (k : ℕ) : P.incl ν hν a k = a k := by
  rw [incl, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

/-- `F` is Fréchet differentiable with derivative `DF`. -/
theorem hasFDerivAt_F (a : X ν hν) : HasFDerivAt (P.F ν hν) (P.DF ν hν a) a :=
  (P.diag ν hν).hasFDerivAt.sub ((P.incl ν hν).hasFDerivAt.comp a (hasFDerivAt_cube a))

theorem F_apply (a : X ν hν) (k : ℕ) : P.F ν hν a k = P.μ k * a k - cube ν hν a k := by
  simp [F]

theorem DF_apply (a h : X ν hν) :
    P.DF ν hν a h = P.diag ν hν h - P.incl ν hν ((3 : ℝ) • mul3 ν hν a a h) := by
  simp [DF, cubeDeriv_apply]

end CubicCosine

end RadiiPolynomial
