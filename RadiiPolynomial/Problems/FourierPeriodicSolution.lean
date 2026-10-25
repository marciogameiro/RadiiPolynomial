module

public import RadiiPolynomial.Problems.FourierPeriodic
public import RadiiPolynomial.Convolution.FourierSeries
public import RadiiPolynomial.Abstract.RadiiPoly
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Periodic solutions from zeros of the periodic orbit map

Symmetry: for `x = (τ₀, a)` let `x^* = (τ₀^*, a^*)` (`conjXP`), an isometric involution of `X`. If the
vector field has real coefficients and `ξ, ξ̂` are real (`IsReal`), then `F(x) = 0` implies
`F(x^*) = 0` (`F_conjXP_eq_zero`), and the zero of `F` near a symmetric `x̄` is symmetric
(`conjXP_eq_of_isolatedZero`).

Solutions: if `F(x) = 0` with `τ₀ ∈ ℝ`, `τ₀ > 0` and `a^* = a`, then
`γ(t) = (∑_k a_{j,k} e^{ikt/τ₀})_j` (`orbit`) is real, solves `γ' = f(γ)` and is `2π τ₀`-periodic
(`hasDerivAt_orbit`, `orbit_add_period`). `exists_solution` collects these facts: an isolated zero
of `F` near a symmetric `x̄ = (τ̄₀, ā)` with `r₀ < τ̄₀` gives a periodic solution of `x' = f(x)` with
period `T`, `|T - 2π τ̄₀| < 2π r₀`, within `r₀` of `∑_k ā_k e^{2πikt/T}`; its coefficients `(T/2π, a)`
form the unique zero of `F` within `r₁` of `x̄`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace FourierPeriodic

open Fourier Metric MvPolynomial

variable {n : ℕ} (P : FourierPeriodic n) {ν : ℝ} {hν : 1 ≤ ν}

/-- `x^* = (τ₀^*, a^*)`. -/
noncomputable def conjXP (x : X n ν hν) : X n ν hν := (star x.1, fun j => conjX (x.2 j))

theorem conjXP_sub (x y : X n ν hν) : conjXP (x - y) = conjXP x - conjXP y := by
  refine Prod.ext ?_ ?_
  · simp [conjXP]
  · funext j; simp [conjXP, conjX_sub]

theorem norm_conjXP (x : X n ν hν) : ‖conjXP x‖ = ‖x‖ := by
  have h2 : ‖(fun j => conjX (x.2 j) : Fin n → Fourier.X ν hν)‖ = ‖x.2‖ := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
      ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
    · rw [norm_conjX]; exact norm_le_pi_norm x.2 j
    · rw [← norm_conjX]; exact norm_le_pi_norm (fun j => conjX (x.2 j)) j
  rw [Prod.norm_def, Prod.norm_def, conjXP, h2, norm_star]

/-- The data are real: real coefficients and a real phase condition. -/
structure IsReal : Prop where
  coeff : ∀ j d, star ((P.f j).coeff d) = (P.f j).coeff d
  ξ : ∀ j, star (P.ξ j) = P.ξ j
  ξhat : ∀ j, star (P.ξhat j) = P.ξhat j

theorem sum_center_neg (N : ℕ) (g : ℤ → ℂ) :
    ∑ k ∈ center N, g (-k) = ∑ k ∈ center N, g k :=
  Finset.sum_nbij' (fun k => -k) (fun k => -k)
    (fun k hk => by rw [mem_center] at hk ⊢; simpa using hk)
    (fun k hk => by rw [mem_center] at hk ⊢; simpa using hk)
    (fun k _ => neg_neg k) (fun k _ => neg_neg k) (fun k _ => rfl)

variable {P}

/-- If the data are real, `F(x) = 0` implies `F(x^*) = 0`. -/
theorem F_conjXP_eq_zero (hP : P.IsReal) {x : X n ν hν} (hF : P.F ν hν x = 0) :
    P.F ν hν (conjXP x) = 0 := by
  have h1 : (P.F ν hν x).1 = 0 := by rw [hF]; rfl
  have h2 : ∀ j k, (P.F ν hν x).2 j k = 0 := fun j k => by rw [hF]; rfl
  refine Prod.ext ?_ ?_
  · have : (P.F ν hν (conjXP x)).1 = star (P.F ν hν x).1 := by
      rw [F_fst, F_fst, star_sub, star_sum, star_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_mul', hP.ξhat, star_sum]
        congr 1
        simp only [conjXP, conjX_apply]
        exact sum_center_neg _ (fun k => star (x.2 j k))
      · exact Finset.sum_congr rfl fun j _ => by rw [star_mul', hP.ξhat, hP.ξ]
    rw [this, h1, star_zero]; rfl
  · funext j
    ext k
    have hk := congrArg star (h2 j (-k))
    rw [F_snd_apply] at hk
    rw [F_snd_apply]
    have hφ : (aeval (conjXP x).2 (P.f j)) k = star ((aeval x.2 (P.f j)) (-k)) := by
      have := conjX_aeval (P.f j) (hP.coeff j) x.2
      rw [← conjX_apply, this]; rfl
    rw [hφ]
    simp only [conjXP, conjX_apply, star_sub, star_mul', star_zero, Complex.star_def,
      Complex.conj_I, Int.cast_neg, map_neg, map_intCast, Prod.snd_zero, Pi.zero_apply,
      WeightedLp.zero_apply] at hk ⊢
    linear_combination hk

/-- The zero of `F` near a symmetric `x̄` is symmetric. -/
theorem conjXP_eq_of_isolatedZero (hP : P.IsReal) {xbar : X n ν hν} (hxbar : conjXP xbar = xbar)
    {r₀ r₁ : ℝ} (hr : r₀ ≤ r₁) {x : X n ν hν} (hx : x ∈ ball xbar r₀) (hF : P.F ν hν x = 0)
    (huniq : ∀ y ∈ closedBall xbar r₁, P.F ν hν y = 0 → y = x) : conjXP x = x := by
  refine huniq _ ?_ (F_conjXP_eq_zero hP hF)
  rw [mem_closedBall, dist_eq_norm, ← hxbar, ← conjXP_sub, norm_conjXP, ← dist_eq_norm]
  exact (mem_ball.1 hx).le.trans hr

variable (ν hν) in
/-- The periodic orbit `γ(t) = (∑_k a_{j,k} e^{ikt/τ})_j` (real part). -/
noncomputable def orbit (x : X n ν hν) (τ : ℝ) (t : ℝ) : Fin n → ℝ :=
  fun j => (fourierEval ν hν (t / τ) (x.2 j)).re

theorem orbit_add_period (x : X n ν hν) {τ : ℝ} (hτ : τ ≠ 0) (t : ℝ) :
    orbit ν hν x τ (t + 2 * Real.pi * τ) = orbit ν hν x τ t := by
  funext j
  simp only [orbit]
  rw [show (t + 2 * Real.pi * τ) / τ = t / τ + 2 * Real.pi by field_simp, fourierEval_add_two_pi]

theorem aeval_eq_eval (z : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) : aeval z p = eval z p := by
  simp only [aeval_def, Algebra.algebraMap_self, eval]; rfl

/-- If `F(x) = 0`, `τ₀ = τ > 0` and `a^* = a`, then `γ' = f(γ)`. -/
theorem hasDerivAt_orbit (hν1 : 1 < ν) {x : X n ν hν} (hF : P.F ν hν x = 0) {τ : ℝ}
    (hτ : x.1 = τ) (hτ0 : 0 < τ) (hsym : ∀ j, conjX (x.2 j) = x.2 j) (t : ℝ) :
    HasDerivAt (orbit ν hν x τ)
      (fun j => (eval (fun i => (orbit ν hν x τ t i : ℂ)) (P.f j)).re) t := by
  refine hasDerivAt_pi.2 fun j => ?_
  set s := t / τ
  have hΓ := hasDerivAt_fourierEval hν1 (x.2 j) s
  have hser : ∑' k, Complex.I * k * x.2 j k * expI s k =
      τ * eval (fun i => fourierEval ν hν s (x.2 i)) (P.f j) := by
    have hk : ∀ k : ℤ, Complex.I * k * x.2 j k = x.1 * (aeval x.2 (P.f j)) k := fun k => by
      have := congrArg (fun y : Y n ν hν => y.2 j k) hF
      simp only [F_snd_apply] at this
      exact sub_eq_zero.1 this
    rw [← aeval_eq_eval, ← comp_aeval_apply, fourierEval_apply, ← tsum_mul_left]
    exact tsum_congr fun k => by rw [hk, hτ]; ring
  have hcomp := hΓ.scomp t ((hasDerivAt_id t).div_const τ)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  convert hre using 1
  · funext s; rfl
  rw [hser]
  have hreal : ∀ i, (orbit ν hν x τ t i : ℂ) = fourierEval ν hν s (x.2 i) := fun i =>
    ofReal_re_fourierEval (hsym i) s
  simp only [hreal, Complex.reCLM_apply, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, show 1 / τ * τ = 1 by field_simp, Complex.ofReal_one,
    one_mul]

/-- An isolated zero of `F` near a symmetric `x̄ = (τ̄₀, ā)` (real data, `ν > 1`, `r₀ < τ̄₀`) gives
a periodic solution `γ` of `x' = f(x)` with period `T`, `|T - 2π τ̄₀| < 2π r₀`, within `r₀` (in each
component) of `∑_k ā_k e^{2πikt/T}`; its coefficients form the unique zero of `F` within `r₁`. -/
theorem exists_solution (hν1 : 1 < ν) (hP : P.IsReal) {xbar : X n ν hν} {τbar : ℝ}
    (hτbar : xbar.1 = τbar) (habar : ∀ j, conjX (xbar.2 j) = xbar.2 j) {r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁) (hr₀ : r₀ < τbar) (h : HasIsolatedZero (P.F ν hν) xbar r₀ r₁) :
    ∃ x : X n ν hν, P.F ν hν x = 0 ∧ (∀ y ∈ closedBall xbar r₁, P.F ν hν y = 0 → y = x) ∧
      ∃ T : ℝ, 0 < T ∧ |T - 2 * Real.pi * τbar| < 2 * Real.pi * r₀ ∧
        ∃ γ : ℝ → Fin n → ℝ,
          (∀ t, HasDerivAt γ (fun j => (eval (fun i => (γ t i : ℂ)) (P.f j)).re) t) ∧
          (∀ t, γ (t + T) = γ t) ∧
          ∀ t j, (γ t j : ℂ) = ∑' k, x.2 j k * expI (2 * Real.pi * t / T) k ∧
            ‖(γ t j : ℂ) - fourierEval ν hν (2 * Real.pi * t / T) (xbar.2 j)‖ < r₀ := by
  obtain ⟨x, hx, hFx, huniq⟩ := h
  have hxbar : conjXP xbar = xbar := by
    refine Prod.ext ?_ ?_
    · simp only [conjXP, hτbar, Complex.star_def, Complex.conj_ofReal]
    · funext j; exact habar j
  have hsym := conjXP_eq_of_isolatedZero hP hxbar hr hx hFx huniq
  have hx1 : star x.1 = x.1 := congrArg Prod.fst hsym
  have hx2 : ∀ j, conjX (x.2 j) = x.2 j := fun j => congrFun (congrArg Prod.snd hsym) j
  set τ := x.1.re with hτdef
  have hτ : x.1 = τ := by
    rw [hτdef]; exact (Complex.conj_eq_iff_re.1 (by rwa [Complex.star_def] at hx1)).symm
  have hdist : ‖x - xbar‖ < r₀ := by rwa [mem_ball, dist_eq_norm] at hx
  have hτclose : |τ - τbar| < r₀ := by
    have h1 : ‖(x - xbar).1‖ ≤ ‖x - xbar‖ := norm_fst_le _
    rw [Prod.fst_sub, hτ, hτbar, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
    exact lt_of_le_of_lt h1 hdist
  have hτ0 : 0 < τ := by have := (abs_lt.1 hτclose).1; linarith
  have hpi := Real.pi_pos
  refine ⟨x, hFx, huniq, 2 * Real.pi * τ, by positivity, ?_, orbit ν hν x τ,
    fun t => hasDerivAt_orbit hν1 hFx hτ hτ0 hx2 t, fun t => orbit_add_period x hτ0.ne' t,
    fun t j => ?_⟩
  · rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact mul_lt_mul_of_pos_left hτclose (by positivity)
  · have hs : 2 * Real.pi * t / (2 * Real.pi * τ) = t / τ := by field_simp
    have hreal := ofReal_re_fourierEval (hx2 j) (t / τ)
    refine ⟨by rw [hs]; exact hreal, ?_⟩
    rw [hs]
    change ‖((fourierEval ν hν (t / τ) (x.2 j)).re : ℂ) - _‖ < r₀
    rw [hreal, ← map_sub]
    refine lt_of_le_of_lt (norm_fourierEval_le _ _) (lt_of_le_of_lt ?_ hdist)
    exact (norm_le_pi_norm (x - xbar).2 j).trans (norm_snd_le _)

end FourierPeriodic

end RadiiPolynomial
