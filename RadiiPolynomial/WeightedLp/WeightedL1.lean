module

public import RadiiPolynomial.WeightedLp.WeightedLp

/-!
# The weighted ℓ¹ space

`WeightedL1 𝕜 ω := WeightedLp 𝕜 ω 1`, the space `ℓ¹_{ω,I}` of sequences with
`‖a‖ = ∑ₖ ω k |a k| < ∞`.

* `norm_eq_tsum`, `hasSum_norm`: the norm formula;
* `ofSummable`: the element with given coefficients, when `∑ₖ ω k |a k| < ∞`;
* `single`: the unit sequences, `‖single k c‖ = ω k |c|`;
* `summable_mul`, `norm_tsum_mul_le`: the duality bound: if `|c k| ≤ κ ω k` for all `k`, then
  `∑ₖ c k a k` converges absolutely and `|∑ₖ c k a k| ≤ κ ‖a‖`.
-/

@[expose] public section

open scoped ENNReal

namespace RadiiPolynomial

variable (𝕜 : Type*) [RCLike 𝕜] {I : Type*}

/-- The weighted space `ℓ¹_{ω,I}`. -/
abbrev WeightedL1 (ω : Weights I) := WeightedLp 𝕜 ω 1

namespace WeightedL1

variable {𝕜} {ω : Weights I}

theorem summable (a : WeightedL1 𝕜 ω) : Summable fun k => ω k * ‖a k‖ := by
  have := a.memℓp.summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  simpa [norm_weigh_apply] using this

theorem norm_eq_tsum (a : WeightedL1 𝕜 ω) : ‖a‖ = ∑' k, ω k * ‖a k‖ := by
  rw [WeightedLp.norm_def, lp.norm_eq_tsum_rpow (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
  exact tsum_congr fun k => by
    rw [WeightedLp.toLp_apply, norm_mul, RCLike.norm_ofReal, abs_of_pos (ω.pos k)]

theorem hasSum_norm (a : WeightedL1 𝕜 ω) : HasSum (fun k => ω k * ‖a k‖) ‖a‖ := by
  rw [norm_eq_tsum]; exact a.summable.hasSum

/-- The element of `ℓ¹_{ω,I}` with coefficients `a`, when `∑ₖ ω k |a k| < ∞`. -/
def ofSummable (a : I → 𝕜) (ha : Summable fun k => ω k * ‖a k‖) : WeightedL1 𝕜 ω :=
  WeightedLp.mk a (memℓp_gen (by simpa [norm_weigh_apply] using ha))

@[simp] theorem ofSummable_apply (a : I → 𝕜) (ha : Summable fun k => ω k * ‖a k‖) (k : I) :
    ofSummable a ha k = a k := rfl

theorem norm_ofSummable (a : I → 𝕜) (ha : Summable fun k => ω k * ‖a k‖) :
    ‖ofSummable a ha‖ = ∑' k, ω k * ‖a k‖ := norm_eq_tsum _

/-- To bound the norm it suffices to bound the weighted sums. -/
theorem norm_le_of_tsum_le (a : WeightedL1 𝕜 ω) {C : ℝ} (h : ∑' k, ω k * ‖a k‖ ≤ C) : ‖a‖ ≤ C := by
  rwa [norm_eq_tsum]

section single

variable [DecidableEq I]

/-- The sequence with coefficient `c` at `k` and `0` elsewhere. -/
def single (k : I) (c : 𝕜) : WeightedL1 𝕜 ω :=
  ofSummable (Pi.single k c) (by
    refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
    rw [Finset.mem_singleton] at hj
    simp [hj])

theorem single_apply (k : I) (c : 𝕜) (j : I) :
    (single k c : WeightedL1 𝕜 ω) j = if j = k then c else 0 := by
  simp [single, Pi.single_apply]

@[simp] theorem single_apply_self (k : I) (c : 𝕜) : (single k c : WeightedL1 𝕜 ω) k = c := by
  simp [single_apply]

theorem norm_single (k : I) (c : 𝕜) : ‖(single k c : WeightedL1 𝕜 ω)‖ = ω k * ‖c‖ := by
  rw [norm_eq_tsum, tsum_eq_single k fun j hj => by simp [single_apply, hj]]
  simp

theorem single_eq_smul (k : I) (c : 𝕜) :
    (single k c : WeightedL1 𝕜 ω) = c • single k 1 := by
  ext j; simp [single_apply]

/-- Every `a ∈ ℓ¹_{ω,I}` is the sum of its coefficients times the unit sequences:
`a = ∑ₖ a_k e_k`. -/
theorem hasSum_single (a : WeightedL1 𝕜 ω) : HasSum (fun k => (single k (a k) : WeightedL1 𝕜 ω)) a := by
  let e := WeightedLp.toLpEquiv 𝕜 ω 1
  have h := (lp.hasSum_single (E := fun _ : I => 𝕜) ENNReal.one_ne_top (e a)).mapL
    (e.symm.toContinuousLinearEquiv : lp (fun _ : I => 𝕜) 1 →L[𝕜] WeightedL1 𝕜 ω)
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] at h
  convert h using 1
  funext k
  apply e.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  refine lp.ext (funext fun m => ?_)
  rw [lp.single_apply]
  change (ω m : 𝕜) * (single k (a k) : WeightedL1 𝕜 ω) m =
    (Pi.single k ((ω k : 𝕜) * a k) : I → 𝕜) m
  rw [single_apply]
  by_cases hm : m = k
  · subst hm; simp
  · simp [hm]

end single

/-- Duality: if `|c k| ≤ κ ω k` for all `k`, then `∑ₖ c k a k` converges absolutely. -/
theorem summable_mul (a : WeightedL1 𝕜 ω) {c : I → 𝕜} {κ : ℝ} (hc : ∀ k, ‖c k‖ ≤ κ * ω k) :
    Summable fun k => ‖c k * a k‖ :=
  Summable.of_nonneg_of_le (f := fun k => κ * (ω k * ‖a k‖)) (fun _ => norm_nonneg _)
    (fun k => by
      rw [norm_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc k) (norm_nonneg _))
    (a.summable.mul_left κ)

/-- Duality bound: if `|c k| ≤ κ ω k` for all `k`, then `|∑ₖ c k a k| ≤ κ ‖a‖`. -/
theorem norm_tsum_mul_le (a : WeightedL1 𝕜 ω) {c : I → 𝕜} {κ : ℝ} (hc : ∀ k, ‖c k‖ ≤ κ * ω k) :
    ‖∑' k, c k * a k‖ ≤ κ * ‖a‖ := by
  refine (norm_tsum_le_tsum_norm (a.summable_mul hc)).trans ?_
  rw [norm_eq_tsum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) (a.summable_mul hc) (a.summable.mul_left κ)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hc k) (norm_nonneg _)

end WeightedL1

end RadiiPolynomial
