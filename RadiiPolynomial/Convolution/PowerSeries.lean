module

public import RadiiPolynomial.Convolution.Instances
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Products of power series

Let `ν > 0` and `|t| ≤ ν`. For `a ∈ ℓ¹_{ν,ℕ}` the power series `∑ₙ aₙ tⁿ` converges absolutely
(`summable_powerSeries`), and evaluation at `t` is an algebra homomorphism
`ℓ¹_{ν,ℕ} → 𝕜` (`powerSeriesEval`). In particular

* `(∑ aₙ tⁿ)(∑ bₙ tⁿ) = ∑ (a * b)ₙ tⁿ` (`powerSeriesEval_mul`), and
* `∑ₙ (a^α)ₙ tⁿ = ∏ⱼ (∑ₙ aⱼ,ₙ tⁿ)^{αⱼ}` for `a^α = a₁^{α₁} * ⋯ * a_L^{α_L}` computed in
  `ℓ¹_{ν,ℕ}` (`powerSeriesEval_prod_pow`).

For real `t` with `|t| < ν` the power series can be differentiated term by term:
`d/dt ∑ₙ aₙ tⁿ = ∑ₘ (m + 1) a_{m+1} tᵐ` (`hasDerivAt_powerSeries`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace WeightedL1

open Convolution

variable {𝕜 : Type*} [RCLike 𝕜] {ν : ℝ} {hν : 0 < ν} {t : 𝕜}

/-- For `|t| ≤ ν` the power series `∑ₙ aₙ tⁿ` converges absolutely. -/
theorem summable_powerSeries (a : WeightedL1 𝕜 (Weights.geom ν hν)) (ht : ‖t‖ ≤ ν) :
    Summable fun n => ‖a n * t ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by
      rw [norm_mul, norm_pow, mul_comm, Weights.geom_apply]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg t) ht n) (norm_nonneg _))
    a.summable

variable (hν) in
/-- Evaluation of the power series at `t`, `|t| ≤ ν`: an algebra homomorphism
`ℓ¹_{ν,ℕ} → 𝕜`. -/
noncomputable def powerSeriesEval (ht : ‖t‖ ≤ ν) : WeightedL1 𝕜 (Weights.geom ν hν) →ₐ[𝕜] 𝕜 :=
  AlgHom.ofLinearMap
    { toFun := fun a => ∑' n, a n * t ^ n
      map_add' := fun a b => by
        simp only [WeightedLp.add_apply, add_mul]
        exact (summable_powerSeries a ht).of_norm.tsum_add (summable_powerSeries b ht).of_norm
      map_smul' := fun c a => by
        simp only [WeightedLp.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc]
        exact tsum_mul_left }
    (by
      change ∑' n, (single 0 1 : WeightedL1 𝕜 (Weights.geom ν hν)) n * t ^ n = 1
      rw [tsum_eq_single 0 fun n hn => by simp [single_apply, hn]]
      simp)
    (fun a b => by
      change ∑' n, conv a b n * t ^ n = (∑' n, a n * t ^ n) * ∑' n, b n * t ^ n
      rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_powerSeries a ht)
        (summable_powerSeries b ht)]
      refine tsum_congr fun n => ?_
      rw [conv_nat, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [← hp, pow_add]
      ring)

theorem powerSeriesEval_apply (ht : ‖t‖ ≤ ν) (a : WeightedL1 𝕜 (Weights.geom ν hν)) :
    powerSeriesEval hν ht a = ∑' n, a n * t ^ n := rfl

/-- `(∑ aₙ tⁿ)(∑ bₙ tⁿ) = ∑ (a * b)ₙ tⁿ`. -/
theorem powerSeriesEval_mul (ht : ‖t‖ ≤ ν) (a b : WeightedL1 𝕜 (Weights.geom ν hν)) :
    ∑' n, (a * b) n * t ^ n = (∑' n, a n * t ^ n) * ∑' n, b n * t ^ n :=
  map_mul (powerSeriesEval hν ht) a b

/-- `∑ₙ (a^α)ₙ tⁿ = ∏ⱼ (∑ₙ aⱼ,ₙ tⁿ)^{αⱼ}`. -/
theorem powerSeriesEval_prod_pow (ht : ‖t‖ ≤ ν) {L : Type*} [Fintype L]
    (a : L → WeightedL1 𝕜 (Weights.geom ν hν)) (α : L → ℕ) :
    ∑' n, (∏ j, a j ^ α j) n * t ^ n = ∏ j, (∑' n, a j n * t ^ n) ^ α j := by
  have := map_prod (powerSeriesEval hν ht) (fun j => a j ^ α j) Finset.univ
  simpa only [map_pow, powerSeriesEval_apply] using this

section Deriv

variable {ν : ℝ} {hν : 0 < ν}

/-- Term by term differentiation inside the disc of convergence, in the form
`d/dt ∑ₙ aₙ tⁿ = ∑ₙ aₙ n t^{n-1}`. -/
theorem hasDerivAt_powerSeries' (a : WeightedL1 ℝ (Weights.geom ν hν)) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (fun s => ∑' n, a n * s ^ n) (∑' n, a n * (n * t ^ (n - 1))) t ∧
      Summable fun n => a n * (n * t ^ (n - 1)) := by
  set ρ := (|t| + ν) / 2 with hρdef
  have hρ : |t| < ρ := by rw [hρdef]; linarith
  have hρν : ρ < ν := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt (abs_nonneg t) hρ
  set q := ρ / ν with hqdef
  have hq0 : 0 ≤ q := div_nonneg hρ0.le hν.le
  have hq1 : q < 1 := by rw [hqdef, div_lt_one hν]; exact hρν
  have hsum : Summable fun n : ℕ => (n : ℝ) * q ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0] : ‖q‖ < 1)
  set B := ∑' n : ℕ, (n : ℝ) * q ^ n
  have hB : ∀ n : ℕ, (n : ℝ) * q ^ n ≤ B := fun n =>
    hsum.le_tsum n fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hq0 m)
  set u : ℕ → ℝ := fun n => ν ^ n * ‖a n‖ * (B / ρ) with hu
  have hus : Summable u := by
    have := a.summable.mul_right (B / ρ)
    simpa only [Weights.geom_apply] using this
  have hbound : ∀ n (y : ℝ), y ∈ Metric.ball (0 : ℝ) ρ → ‖a n * (n * y ^ (n - 1))‖ ≤ u n := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs y, Real.norm_natCast, hu]
    have h1 : (n : ℝ) * |y| ^ (n - 1) ≤ (n : ℝ) * ρ ^ (n - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy.le _) (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * ρ ^ (n - 1) ≤ ν ^ n * (B / ρ) := by
      rcases n with _ | n
      · simp only [Nat.cast_zero, zero_mul]; positivity
      · rw [Nat.add_sub_cancel]
        have hqn := hB (n + 1)
        rw [hqdef, div_pow, mul_div_assoc', div_le_iff₀ (pow_pos hν _)] at hqn
        rw [mul_div_assoc', le_div_iff₀ hρ0]
        calc ((n + 1 : ℕ) : ℝ) * ρ ^ n * ρ = ((n + 1 : ℕ) : ℝ) * ρ ^ (n + 1) := by ring
          _ ≤ B * ν ^ (n + 1) := hqn
          _ = ν ^ (n + 1) * B := by ring
    calc ‖a n‖ * ((n : ℝ) * |y| ^ (n - 1)) ≤ ‖a n‖ * (ν ^ n * (B / ρ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = ν ^ n * ‖a n‖ * (B / ρ) := by ring
  have ht' : t ∈ Metric.ball (0 : ℝ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hρ
  refine ⟨hasDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball
    (convex_ball (0 : ℝ) ρ).isPreconnected (fun n y _ => ?_) hbound
    (Metric.mem_ball_self hρ0) ?_ ht', Summable.of_norm_bounded hus fun n => hbound n t ht'⟩
  · simpa using (hasDerivAt_pow n y).const_mul (a n)
  · exact (summable_powerSeries a (by simpa using hν.le : ‖(0 : ℝ)‖ ≤ ν)).of_norm

/-- Term by term differentiation: `d/dt ∑ₙ aₙ tⁿ = ∑ₘ (m + 1) a_{m+1} tᵐ` for `|t| < ν`. -/
theorem hasDerivAt_powerSeries (a : WeightedL1 ℝ (Weights.geom ν hν)) {t : ℝ} (ht : |t| < ν) :
    HasDerivAt (fun s => ∑' n, a n * s ^ n) (∑' m : ℕ, ((m : ℝ) + 1) * a (m + 1) * t ^ m) t := by
  obtain ⟨h, hs⟩ := hasDerivAt_powerSeries' a ht
  convert h using 1
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel]
  exact tsum_congr fun m => by ring

end Deriv

end WeightedL1

end RadiiPolynomial
