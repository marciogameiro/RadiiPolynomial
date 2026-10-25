module

public import RadiiPolynomial.Convolution.Fourier
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Forced quadratic problems in Fourier series

For eigenvalues `λ = (λ_n)_{n ∈ ℤ}` and a finitely supported forcing `g` (`QuadraticFourier`), the
problem is `F(a) = 0` for the Fourier coefficients `a ∈ X = ℓ¹_ν` (`ν ≥ 1`, `Fourier.X`), where

  `F_n(a) = λ_n a_n - (a * a)_n - g_n`,   `n ∈ ℤ`,

and `*` is the discrete convolution. For instance, the `2π`-periodic solutions
`u(t) = ∑_n a_n e^{int}` of `u'' + c₁ u' + c₂ u - u² = c₃ cos t` are the zeros of `F` with
`λ_n = -n² + i c₁ n + c₂` and `g = (c₃/2) (e₁ + e₋₁)`.

In operator form `F(a) = Λ a - ι(a * a + g)` (`QuadraticFourier.F`), with values in `Y = ℓ¹_ω`,
`ω_n = ν^{|n|} / (1 + |λ_n|)` (`QuadraticFourier.Y`), where `Λ` is the diagonal operator
`(Λ a)_n = λ_n a_n` and `ι : X → Y` the inclusion, both of norm at most `1`. Only `F : X → Y` and the
boundedness of the operators between `X` and `Y` depend on `Y`; all bounds of the radii polynomial
theorem are in `X`.

`QuadraticFourier.hasFDerivAt_F`: `F` is Fréchet differentiable, with `DF(a) h = Λ h - ι(2 a * h)`
(`QuadraticFourier.DF`).
-/

@[expose] public section

namespace RadiiPolynomial

open Fourier

/-- The data of a forced quadratic problem in Fourier series. -/
structure QuadraticFourier where
  /-- the eigenvalue `λ_n` of the mode `e^{int}` -/
  lam : ℤ → ℂ
  /-- the Fourier coefficients of the forcing -/
  g : ℤ →₀ ℂ

namespace QuadraticFourier

variable (P : QuadraticFourier) (ν : ℝ) (hν : 1 ≤ ν)

/-- The weights `ω_n = ν^{|n|} / (1 + |λ_n|)`. -/
noncomputable def weightsY : Weights ℤ :=
  ⟨fun n => ν ^ n.natAbs / (1 + ‖P.lam n‖), fun n => div_pos (pow_pos (nu_pos hν) _)
    (by positivity)⟩

theorem weightsY_apply (n : ℤ) : P.weightsY ν hν n = ν ^ n.natAbs / (1 + ‖P.lam n‖) := rfl

/-- The codomain `Y = ℓ¹_ω`, `ω_n = ν^{|n|} / (1 + |λ_n|)`. -/
abbrev Y := WeightedL1 ℂ (P.weightsY ν hν)

/-- The forcing as an element of `ℓ¹_ν`. -/
noncomputable def forcing : X ν hν :=
  WeightedL1.ofSummable (fun n => P.g n) (summable_of_ne_finset_zero (s := P.g.support)
    fun n hn => by simp [Finsupp.notMem_support_iff.1 hn])

variable {ν hν}

@[simp] theorem forcing_apply (n : ℤ) : P.forcing ν hν n = P.g n := rfl

theorem diag_bound (n : ℤ) : ‖P.lam n‖ * P.weightsY ν hν n ≤ 1 * Weights.geomInt ν hν n := by
  rw [weightsY_apply, Weights.geomInt_apply, one_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [pow_pos (nu_pos hν) n.natAbs, norm_nonneg (P.lam n)]

theorem incl_bound (n : ℤ) : ‖(1 : ℂ)‖ * P.weightsY ν hν n ≤ 1 * Weights.geomInt ν hν n := by
  rw [weightsY_apply, Weights.geomInt_apply, norm_one, one_mul, one_mul]
  exact div_le_self (pow_pos (nu_pos hν) _).le (by linarith [norm_nonneg (P.lam n)])

variable (ν hν)

/-- The diagonal operator `(Λ a)_n = λ_n a_n`, `X → Y`, of norm at most `1`. -/
noncomputable def diag : X ν hν →L[ℂ] P.Y ν hν :=
  (ColNormBound.single (ω := P.weightsY ν hν) (ω' := Weights.geomInt ν hν) (fun n => n) P.lam
    zero_le_one P.diag_bound).toCLM

/-- The inclusion `ι : X → Y`, of norm at most `1`. -/
noncomputable def incl : X ν hν →L[ℂ] P.Y ν hν :=
  (ColNormBound.single (ω := P.weightsY ν hν) (ω' := Weights.geomInt ν hν) (fun n => n)
    (fun _ => (1 : ℂ)) zero_le_one P.incl_bound).toCLM

/-- The zero finding map `F(a) = Λ a - ι(a * a + g)`. -/
noncomputable def F (a : X ν hν) : P.Y ν hν := P.diag ν hν a - P.incl ν hν (a * a + P.forcing ν hν)

/-- The derivative `DF(a) h = Λ h - ι(2 a * h)`. -/
noncomputable def DF (a : X ν hν) : X ν hν →L[ℂ] P.Y ν hν :=
  P.diag ν hν - (P.incl ν hν).comp ((2 : ℂ) • ContinuousLinearMap.mul ℂ (X ν hν) a)

variable {ν hν}

@[simp] theorem diag_apply (a : X ν hν) (n : ℤ) : P.diag ν hν a n = P.lam n * a n := by
  rw [diag, ColNormBound.toCLM_apply, tsum_eq_single n fun m hm => by simp [Ne.symm hm]]
  simp

@[simp] theorem incl_apply (a : X ν hν) (n : ℤ) : P.incl ν hν a n = a n := by
  rw [incl, ColNormBound.toCLM_apply, tsum_eq_single n fun m hm => by simp [Ne.symm hm]]
  simp

/-- `F` is Fréchet differentiable with derivative `DF`. -/
theorem hasFDerivAt_F (a : X ν hν) : HasFDerivAt (P.F ν hν) (P.DF ν hν a) a := by
  have hsq : HasFDerivAt (fun x : X ν hν => x * x + P.forcing ν hν)
      ((2 : ℂ) • ContinuousLinearMap.mul ℂ (X ν hν) a) a := by
    refine (((hasFDerivAt_id a).mul (hasFDerivAt_id a)).add_const _).congr_fderiv ?_
    ext1 h
    simp only [add_apply, smul_apply, id_eq,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
    rw [two_smul]
  exact (P.diag ν hν).hasFDerivAt.sub ((P.incl ν hν).hasFDerivAt.comp a hsq)

theorem F_apply (a : X ν hν) (n : ℤ) : P.F ν hν a n = P.lam n * a n - (a * a) n - P.g n := by
  simp [F]
  ring

theorem DF_apply (a h : X ν hν) :
    P.DF ν hν a h = P.diag ν hν h - P.incl ν hν ((2 : ℂ) • (a * h)) := by
  simp [DF]

theorem DF_apply_coeff (a h : X ν hν) (n : ℤ) :
    P.DF ν hν a h n = P.lam n * h n - 2 * (a * h) n := by
  rw [DF_apply, WeightedLp.sub_apply, diag_apply, incl_apply, WeightedLp.smul_apply]

end QuadraticFourier

end RadiiPolynomial
