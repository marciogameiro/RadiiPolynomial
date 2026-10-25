module

public import RadiiPolynomial.Convolution.Fourier
public import RadiiPolynomial.Calculus.Polynomial

/-!
# Periodic orbits of polynomial vector fields via Fourier series

A `2π τ₀`-periodic solution of `x' = f(x)`, `f : ℂⁿ → ℂⁿ` polynomial, is after rescaling time a
`2π`-periodic solution of `x' = τ₀ f(x)`, written as a Fourier series
`x_j(t) = ∑_k a_{j,k} e^{ikt}`. The unknowns are `x = (τ₀, a) ∈ X = ℂ × (ℓ¹_ν)^n` (max norm,
`Fourier.X`), and the zero finding map `F : X → Y = ℂ × (ℓ¹_ω)^n` (`ω_k = ν^{|k|} / (1 + |k|)`,
`Fourier.Y`) is (`FourierPeriodic.F`)

  `F₀(τ₀, a) = ∑_j ξ̂_j (∑_{|k| ≤ N₀} a_{j,k} - ξ_j)`          (phase condition),
  `F_j(τ₀, a)_k = i k a_{j,k} - τ₀ φ_j(a)_k`,                 `k ∈ ℤ`,

where `φ_j(a)` is `f_j` evaluated with the discrete convolution (`MvPolynomial.aeval`), and
`ξ, ξ̂ ∈ ℂⁿ` and `N₀` fix the phase. In operator form `F_j(τ₀, a) = D a_j - τ₀ ι φ_j(a)`, with
`D = Fourier.diffOp` and the inclusion `ι = Fourier.incl`.

`FourierPeriodic.hasFDerivAt_F`: `F` is Fréchet differentiable, with (`FourierPeriodic.DF`)

  `DF(τ₀, a) h = (∑_j ξ̂_j ∑_{|k| ≤ N₀} h_{j,k}, j ↦ D h_j - h₀ ι φ_j(a) - τ₀ ι ∑ᵢ ∂ᵢφ_j(a) * hᵢ)`.
-/

@[expose] public section

namespace RadiiPolynomial

open MvPolynomial

/-- A periodic orbit problem for `x' = f(x)` with a polynomial vector field `f` and the phase
condition `∑_j ξ̂_j (∑_{|k| ≤ N₀} a_{j,k} - ξ_j) = 0`. -/
structure FourierPeriodic (n : ℕ) where
  /-- the vector field, a polynomial in each component -/
  f : Fin n → MvPolynomial (Fin n) ℂ
  /-- the anchor point of the phase condition -/
  ξ : Fin n → ℂ
  /-- the normal vector of the phase condition -/
  ξhat : Fin n → ℂ
  /-- the truncation of the phase condition -/
  N₀ : ℕ

namespace FourierPeriodic

variable {n : ℕ} (P : FourierPeriodic n) (ν : ℝ) (hν : 1 ≤ ν)

variable (n) in
/-- The space of unknowns `X = ℂ × (ℓ¹_ν)^n`. -/
abbrev X := ℂ × (Fin n → Fourier.X ν hν)

variable (n) in
/-- The codomain `Y = ℂ × (ℓ¹_ω)^n`. -/
abbrev Y := ℂ × (Fin n → Fourier.Y ν hν)

/-- The linear part of the phase condition, `a ↦ ∑_j ξ̂_j ∑_{|k| ≤ N₀} a_{j,k}`. -/
noncomputable def phaseCLM : (Fin n → Fourier.X ν hν) →L[ℂ] ℂ :=
  ∑ j, ∑ k ∈ Fourier.center P.N₀,
    P.ξhat j • (WeightedLp.evalCLM k).comp (ContinuousLinearMap.proj j)

/-- The zero finding map. -/
noncomputable def F (x : X n ν hν) : Y n ν hν :=
  (P.phaseCLM ν hν x.2 - ∑ j, P.ξhat j * P.ξ j,
    fun j => Fourier.diffOp ν hν (x.2 j) - x.1 • Fourier.incl ν hν (aeval x.2 (P.f j)))

/-- The derivative of `F`. -/
noncomputable def DF (x : X n ν hν) : X n ν hν →L[ℂ] Y n ν hν :=
  ((P.phaseCLM ν hν).comp (ContinuousLinearMap.snd ℂ _ _)).prod
    (ContinuousLinearMap.pi fun j =>
      (Fourier.diffOp ν hν).comp
          ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _)) -
        (ContinuousLinearMap.fst ℂ _ _).smulRight (Fourier.incl ν hν (aeval x.2 (P.f j))) -
        x.1 • (Fourier.incl ν hν).comp ((polyDeriv (P.f j) x.2).comp (ContinuousLinearMap.snd ℂ _ _)))

variable {ν hν}

theorem phaseCLM_apply (a : Fin n → Fourier.X ν hν) :
    P.phaseCLM ν hν a = ∑ j, P.ξhat j * ∑ k ∈ Fourier.center P.N₀, a j k := by
  simp [phaseCLM, sum_apply, Finset.mul_sum]

/-- `F` is Fréchet differentiable with derivative `DF`. -/
theorem hasFDerivAt_F (x : X n ν hν) : HasFDerivAt (P.F ν hν) (P.DF ν hν x) x := by
  have h0 : HasFDerivAt (fun y : X n ν hν => P.phaseCLM ν hν y.2)
      ((P.phaseCLM ν hν).comp (ContinuousLinearMap.snd ℂ _ _)) x :=
    (P.phaseCLM ν hν).hasFDerivAt.comp x hasFDerivAt_snd
  refine HasFDerivAt.prodMk (HasFDerivAt.sub_const (∑ j, P.ξhat j * P.ξ j) h0) ?_
  refine hasFDerivAt_pi.2 fun j => ?_
  have hD : HasFDerivAt (fun y : X n ν hν => Fourier.diffOp ν hν (y.2 j))
      ((Fourier.diffOp ν hν).comp
        ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ _ _))) x :=
    (Fourier.diffOp ν hν).hasFDerivAt.comp x ((hasFDerivAt_apply (𝕜 := ℂ) j x.2).comp x
      hasFDerivAt_snd)
  have hφ : HasFDerivAt (fun y : X n ν hν => Fourier.incl ν hν (aeval y.2 (P.f j)))
      ((Fourier.incl ν hν).comp ((polyDeriv (P.f j) x.2).comp (ContinuousLinearMap.snd ℂ _ _))) x :=
    (Fourier.incl ν hν).hasFDerivAt.comp x
      ((hasFDerivAt_aeval (P.f j) x.2).comp x hasFDerivAt_snd)
  have hprod := hasFDerivAt_fst.smul hφ
  refine (hD.sub hprod).congr_fderiv ?_
  abel

theorem F_fst (x : X n ν hν) :
    (P.F ν hν x).1 = ∑ j, P.ξhat j * ∑ k ∈ Fourier.center P.N₀, x.2 j k - ∑ j, P.ξhat j * P.ξ j := by
  simp [F, phaseCLM_apply]

theorem F_snd_apply (x : X n ν hν) (j : Fin n) (k : ℤ) :
    (P.F ν hν x).2 j k = Complex.I * k * x.2 j k - x.1 * (aeval x.2 (P.f j)) k := by
  simp [F]

theorem DF_fst (x h : X n ν hν) :
    (P.DF ν hν x h).1 = ∑ j, P.ξhat j * ∑ k ∈ Fourier.center P.N₀, h.2 j k := by
  simp [DF, phaseCLM_apply]

theorem DF_snd_apply (x h : X n ν hν) (j : Fin n) (k : ℤ) :
    (P.DF ν hν x h).2 j k = Complex.I * k * h.2 j k - h.1 * (aeval x.2 (P.f j)) k -
      x.1 * (polyDeriv (P.f j) x.2 h.2) k := by
  simp [DF]

end FourierPeriodic

end RadiiPolynomial
