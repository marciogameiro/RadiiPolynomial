module

public import RadiiPolynomial.Convolution.Taylor
public import RadiiPolynomial.Calculus.Polynomial
public import RadiiPolynomial.Convolution.PowerSeries
public import RadiiPolynomial.Abstract.RadiiPoly
public import RadiiPolynomial.Calculus.ODE
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Initial value problems via Taylor series

An initial value problem

  `x' = τ f(x)`,   `x(0) = x₀`,

with a polynomial vector field `f : ℝⁿ → ℝⁿ` and a time scale `τ` (`TaylorIVP`), is written as a
zero finding problem `F(a) = 0` for the Taylor coefficients `a = (a_1, …, a_n) ∈ X = (ℓ¹_ν)^n`
(max norm), `x_j(t) = ∑_k (a_j)_k t^k`, with values in `Y = (ℓ¹_ω)^n`:

  `F_j(a)_0 = (a_j)_0 - (x₀)_j`,
  `F_j(a)_k = k (a_j)_k - τ φ_j(a)_{k-1}`   (`k ≥ 1`),

where `φ_j(a)` is `f_j` evaluated with the Cauchy product. In operator form
`F_j(a) = D a_j - (x₀)_j e₀ - τ ι S φ_j(a)` (`TaylorIVP.F`), with the bounded operators `D`, `S` and
the inclusion `ι : ℓ¹_ν → ℓ¹_ω`.

`TaylorIVP.hasFDerivAt_F`: `F` is Fréchet differentiable, with
`DF(a) h = D h_j - τ ι S (∑ᵢ ∂ᵢφ_j(a) * hᵢ)` (`TaylorIVP.DF`).

Solutions: for `a ∈ (ℓ¹_ν)^n` let `x(t) = (∑_k a_{j,k} t^k)_j` (`TaylorIVP.sol`), `|t| ≤ ν`. Then
`f_j(x(t)) = ∑_k φ_j(a)_k t^k` (`eval_sol`), `|x_j(t) - y_j(t)| ≤ ‖a - b‖` for the series `y` of `b`
(`abs_sol_sub_le`), and if `F(a) = 0`, then `x(0) = x₀` (`sol_zero`) and `x' = τ f(x)` on
`(-ν, ν)` (`hasDerivAt_sol`); `x` is continuous on `[-ν, ν]` (`continuousOn_sol`).
`exists_solution`: an isolated zero of `F` near `ā` gives a solution of `x' = f(x)`, `x(0) = x₀` on
`|t| < τ ν` (for `τ > 0`), continuous on `|t| ≤ τ ν`, within `r₀` of `∑_k ā_{j,k} (t/τ)^k`;
`exists_unique_solution`: moreover every solution of this IVP on `|t| < τ ν` coincides with it
(the polynomial field is Lipschitz on bounded sets, `eqOn_Ioo_of_lipschitzOnWith_closedBall`).
-/

@[expose] public section

namespace RadiiPolynomial

open Taylor MvPolynomial

/-- An initial value problem `x' = τ f(x)`, `x(0) = x₀`, with a polynomial vector field
`f = (f_1, …, f_n)`. -/
structure TaylorIVP (n : ℕ) where
  /-- the vector field, a polynomial in each component -/
  f : Fin n → MvPolynomial (Fin n) ℝ
  /-- the time scale -/
  τ : ℝ
  /-- the initial value -/
  x₀ : Fin n → ℝ

namespace TaylorIVP

variable {n : ℕ} (P : TaylorIVP n) (ν : ℝ) (hν : 0 < ν)

/-- The zero finding map `F : (ℓ¹_ν)^n → (ℓ¹_ω)^n`. -/
noncomputable def F (a : Fin n → X ν hν) : Fin n → Y ν hν := fun j =>
  diffOp ν hν (a j) - P.x₀ j • e0 ν hν - P.τ • incl ν hν (shift ν hν (aeval a (P.f j)))

/-- The derivative of `F`. -/
noncomputable def DF (a : Fin n → X ν hν) : (Fin n → X ν hν) →L[ℝ] (Fin n → Y ν hν) :=
  ContinuousLinearMap.pi fun j =>
    (diffOp ν hν).comp (ContinuousLinearMap.proj j) -
      P.τ • ((incl ν hν).comp (shift ν hν)).comp (polyDeriv (P.f j) a)

/-- `F` is Fréchet differentiable with derivative `DF`. -/
theorem hasFDerivAt_F (a : Fin n → X ν hν) : HasFDerivAt (P.F ν hν) (P.DF ν hν a) a := by
  refine hasFDerivAt_pi.2 fun j => ?_
  have h1 : HasFDerivAt (fun x : Fin n → X ν hν => diffOp ν hν (x j))
      ((diffOp ν hν).comp (ContinuousLinearMap.proj j)) a :=
    ((diffOp ν hν).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => X ν hν) j)).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Fin n → X ν hν => P.τ • incl ν hν (shift ν hν (aeval x (P.f j))))
      (P.τ • ((incl ν hν).comp (shift ν hν)).comp (polyDeriv (P.f j) a)) a :=
    (((incl ν hν).comp (shift ν hν)).hasFDerivAt.comp a (hasFDerivAt_aeval (P.f j) a)).const_smul
      P.τ
  have := (h1.sub_const (P.x₀ j • e0 ν hν)).sub h2
  convert this using 1
  funext x
  rfl

theorem F_apply_zero (a : Fin n → X ν hν) (j : Fin n) : P.F ν hν a j 0 = a j 0 - P.x₀ j := by
  simp [F, diffOp_apply, shift_apply]

theorem F_apply_of_ne_zero (a : Fin n → X ν hν) (j : Fin n) {k : ℕ} (hk : k ≠ 0) :
    P.F ν hν a j k = k * a j k - P.τ * (aeval a (P.f j)) (k - 1) := by
  simp [F, diffOp_apply, shift_apply, hk]

/-! ### Solutions -/

section Solution

variable {P ν hν}

/-- The function `x(t) = (∑_k a_{j,k} t^k)_j`. -/
noncomputable def sol (a : Fin n → X ν hν) (t : ℝ) : Fin n → ℝ := fun j => ∑' k, a j k * t ^ k

theorem norm_le_nu {t : ℝ} (ht : |t| ≤ ν) : ‖t‖ ≤ ν := by rwa [Real.norm_eq_abs]

/-- `f(x(t)) = ∑_k φ(a)_k t^k` for `|t| ≤ ν`. -/
theorem eval_sol (a : Fin n → X ν hν) {t : ℝ} (ht : |t| ≤ ν) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval (sol a t) p = ∑' k, (aeval a p) k * t ^ k := by
  have h := MvPolynomial.comp_aeval_apply (WeightedL1.powerSeriesEval hν (norm_le_nu ht)) (f := a) p
  rw [WeightedL1.powerSeriesEval_apply] at h
  rw [h]
  simp only [WeightedL1.powerSeriesEval_apply, MvPolynomial.aeval_def, Algebra.algebraMap_self,
    MvPolynomial.eval]
  rfl

theorem sol_zero (a : Fin n → X ν hν) (hF : P.F ν hν a = 0) : sol a 0 = P.x₀ := by
  funext j
  have hk := congrArg (fun y => y j 0) hF
  simp only [Pi.zero_apply, WeightedLp.zero_apply, F_apply_zero, sub_eq_zero] at hk
  rw [sol, tsum_eq_single 0 fun k hk => by simp [hk], pow_zero, mul_one, hk]

/-- If `F(a) = 0`, then `x' = τ f(x)` on `(-ν, ν)`. -/
theorem hasDerivAt_sol (a : Fin n → X ν hν) (hF : P.F ν hν a = 0) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (sol a) (fun j => P.τ * MvPolynomial.eval (sol a t) (P.f j)) t := by
  refine hasDerivAt_pi.2 fun j => ?_
  have h := WeightedL1.hasDerivAt_powerSeries (a j) ht
  refine h.congr_deriv ?_
  rw [eval_sol a ht.le, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hk := congrArg (fun y => y j (m + 1)) hF
  simp only [Pi.zero_apply, WeightedLp.zero_apply] at hk
  rw [P.F_apply_of_ne_zero ν hν a j (Nat.succ_ne_zero m), Nat.succ_sub_one, sub_eq_zero,
    Nat.succ_eq_add_one] at hk
  push_cast at hk
  rw [← mul_assoc, ← hk]

/-- `x` is continuous on `[-ν, ν]` (the series converge uniformly there). -/
theorem continuousOn_sol (a : Fin n → X ν hν) : ContinuousOn (sol a) (Set.Icc (-ν) ν) := by
  refine continuousOn_pi.2 fun j => ?_
  refine continuousOn_tsum (u := fun k => ν ^ k * ‖a j k‖)
    (fun k => (continuous_const.mul (continuous_pow k)).continuousOn) ?_ (fun k t ht => ?_)
  · simpa [Weights.geom_apply] using (a j).summable
  · have htν : |t| ≤ ν := abs_le.2 ht
    rw [norm_mul, norm_pow, mul_comm]
    gcongr
    exact (Real.norm_eq_abs t).trans_le htν

/-- `|x_j(t) - y_j(t)| ≤ ‖a - b‖` for `|t| ≤ ν`. -/
theorem abs_sol_sub_le (a b : Fin n → X ν hν) {t : ℝ} (ht : |t| ≤ ν) (j : Fin n) :
    |sol a t j - sol b t j| ≤ ‖a - b‖ := by
  have hsa := (WeightedL1.summable_powerSeries (a j) (norm_le_nu ht)).of_norm
  have hsb := (WeightedL1.summable_powerSeries (b j) (norm_le_nu ht)).of_norm
  have hsd := WeightedL1.summable_powerSeries ((a - b) j) (norm_le_nu ht)
  rw [sol, sol, ← hsa.tsum_sub hsb, ← Real.norm_eq_abs]
  have heq : (fun k => a j k * t ^ k - b j k * t ^ k) = fun k => (a - b) j k * t ^ k := by
    funext k; simp [sub_mul]
  rw [heq]
  refine (norm_tsum_le_tsum_norm hsd).trans ?_
  refine le_trans ?_ ((norm_le_pi_norm (a - b) j).trans le_rfl)
  rw [WeightedL1.norm_eq_tsum]
  refine Summable.tsum_le_tsum (fun k => ?_) hsd (WeightedL1.summable _)
  rw [norm_mul, norm_pow, Weights.geom_apply, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg t) (norm_le_nu ht) k)
    (norm_nonneg _)

/-- From an isolated zero of `F` near `ā` to a solution of `x' = f(x)`, `x(0) = x₀` on `|t| < τ ν`
within `r₀` of `x̄(t) = ∑_k ā_{j,k} (t/τ)^k`. -/
theorem exists_solution {abar : Fin n → X ν hν} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) (hτ : 0 < P.τ) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = P.x₀ ∧
      (∀ t, |t| < P.τ * ν → HasDerivAt x (fun j => MvPolynomial.eval (x t) (P.f j)) t) ∧
      (∀ t, |t| ≤ P.τ * ν → ∀ j, |x t j - ∑' k, abar j k * (t / P.τ) ^ k| < r₀) ∧
      ContinuousOn x (Set.Icc (-(P.τ * ν)) (P.τ * ν)) := by
  obtain ⟨a, ha, hFa, -⟩ := h
  have hs : ∀ t, |t| ≤ P.τ * ν ↔ |t / P.τ| ≤ ν := fun t => by
    rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ, mul_comm]
  have hs' : ∀ t, |t| < P.τ * ν ↔ |t / P.τ| < ν := fun t => by
    rw [abs_div, abs_of_pos hτ, div_lt_iff₀ hτ, mul_comm]
  refine ⟨fun t => sol a (t / P.τ), by simpa using sol_zero a hFa, fun t ht => ?_, fun t ht j => ?_,
    (continuousOn_sol a).comp (continuousOn_id.div_const P.τ) fun t ht => ?_⟩
  · have hd := (hasDerivAt_sol a hFa ((hs' t).1 ht)).scomp t ((hasDerivAt_id t).div_const P.τ)
    have hfun : (fun t => sol a (t / P.τ)) = sol a ∘ fun x => id x / P.τ := rfl
    rw [hfun]
    convert hd using 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, id]
    field_simp
  · rw [Metric.mem_ball, dist_eq_norm] at ha
    exact lt_of_le_of_lt (abs_sol_sub_le a abar ((hs t).1 ht) j) ha
  · exact abs_le.1 ((hs t).1 (abs_le.2 ht))

/-- `exists_solution` with uniqueness: every solution of `x' = f(x)`, `x(0) = x₀` on `|t| < τ ν`
coincides with the solution obtained from the zero of `F`. -/
theorem exists_unique_solution {abar : Fin n → X ν hν} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) (hτ : 0 < P.τ) :
    ∃ x : ℝ → Fin n → ℝ, x 0 = P.x₀ ∧
      (∀ t, |t| < P.τ * ν → HasDerivAt x (fun j => MvPolynomial.eval (x t) (P.f j)) t) ∧
      (∀ t, |t| ≤ P.τ * ν → ∀ j, |x t j - ∑' k, abar j k * (t / P.τ) ^ k| < r₀) ∧
      ContinuousOn x (Set.Icc (-(P.τ * ν)) (P.τ * ν)) ∧
      ∀ y : ℝ → Fin n → ℝ, y 0 = P.x₀ →
        (∀ t, |t| < P.τ * ν → HasDerivAt y (fun j => MvPolynomial.eval (y t) (P.f j)) t) →
        ∀ t, |t| < P.τ * ν → y t = x t := by
  obtain ⟨x, hx0, hxd, hxe, hxc⟩ := exists_solution h hτ
  refine ⟨x, hx0, hxd, hxe, hxc, fun y hy0 hyd t ht => ?_⟩
  have hv : ∀ R, ∃ K, LipschitzOnWith K
      (fun z : Fin n → ℝ => fun j => MvPolynomial.eval z (P.f j)) (Metric.closedBall 0 R) :=
    lipschitzOnWith_eval_pi P.f
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(P.τ * ν)) (P.τ * ν) := by
    have := mul_pos hτ hν; constructor <;> linarith
  exact eqOn_Ioo_of_lipschitzOnWith_closedBall hv h0 (fun s hs => hyd s (abs_lt.2 hs))
    (fun s hs => hxd s (abs_lt.2 hs)) (hy0.trans hx0.symm) (abs_lt.1 ht)

end Solution

end TaylorIVP

end RadiiPolynomial
