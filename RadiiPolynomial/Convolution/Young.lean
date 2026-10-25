module

public import RadiiPolynomial.Convolution.Basic
public import Mathlib.Analysis.MeanInequalities

/-!
# Young's inequality

Let `I` be a cancellative commutative monoid, `ω` submultiplicative weights and `1 ≤ p < ∞`. For
`a ∈ ℓ^p_{ω,I}` and `b ∈ ℓ¹_{ω,I}` the sums `(a * b)_k = ∑_{i + j = k} a_i b_j` over the fibers converge
absolutely (`summable_fiber_Lp`), `a * b ∈ ℓ^p_{ω,I}` (`convLp`, `convLp_apply`) and

  `‖a * b‖_p ≤ ‖a‖_p ‖b‖₁`   (`norm_convLp_le`).

Proof. With `αᵢ = ωᵢ |aᵢ|`, `βⱼ = ωⱼ |bⱼ|`, `B = ∑ⱼ βⱼ = ‖b‖₁` and `q` the conjugate exponent of `p`,
submultiplicativity and Hölder's inequality on the fiber of `k` give
`ω_k ∑ |aᵢ| |bⱼ| ≤ ∑ (αᵢ βⱼ^{1/p}) βⱼ^{1/q} ≤ (∑_{fiber} αᵢ^p βⱼ)^{1/p} B^{1/q}`
(`fiber_bound`; on a fiber `(i, j) ↦ j` is injective since `I` is cancellative, so the second sum is at
most `B`). Raising to the power `p` and summing over `k`, the fibers regroup to
`∑_{(i, j)} αᵢ^p βⱼ = ‖a‖_p^p B`, hence `‖a * b‖_p^p ≤ ‖a‖_p^p B^{p/q + 1} = ‖a‖_p^p B^p`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace Convolution

open WeightedLp
open scoped ENNReal

variable {I : Type*} [AddCommMonoid I] {𝕜 : Type*} [RCLike 𝕜] {ω : Weights I}

/-! ### The norm of `ℓ^p_{ω,I}` -/

omit [AddCommMonoid I] in
theorem norm_eq_tsum_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (a : WeightedLp 𝕜 ω p) :
    ‖a‖ = (∑' k, (ω k * ‖a k‖) ^ p.toReal) ^ (1 / p.toReal) := by
  rw [WeightedLp.norm_def, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact tsum_congr fun k => by
    rw [WeightedLp.toLp_apply, norm_mul, RCLike.norm_ofReal, abs_of_pos (ω.pos k)]

omit [AddCommMonoid I] in
theorem summable_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (a : WeightedLp 𝕜 ω p) :
    Summable fun k => (ω k * ‖a k‖) ^ p.toReal := by
  simpa [norm_weigh_apply] using a.memℓp.summable hp

/-! ### Hölder's inequality on a fiber -/

section Fiber

variable [IsCancelAdd I]

omit [AddCommMonoid I] [IsCancelAdd I] in
theorem nonneg_weighted (a : I → 𝕜) (k : I) : 0 ≤ ω k * ‖a k‖ :=
  mul_nonneg (ω.pos k).le (norm_nonneg _)

/-- On a fiber, `(i, j) ↦ j` is injective. -/
theorem fiber_snd_injective (k : I) : Function.Injective fun q : fiber k => q.1.2 := by
  intro q q' h
  simp only at h
  have h1 : q.1.1 + q.1.2 = q'.1.1 + q.1.2 := by rw [q.2, h, q'.2]
  exact Subtype.ext (Prod.ext (add_right_cancel h1) h)

/-- Hölder's inequality on the fiber of `k`, for `α, β ≥ 0` with `∑ αᵢ^P < ∞`, `∑ βⱼ < ∞`, `P ≥ 1`:
`∑_{fiber} αᵢ βⱼ` converges and is at most `(∑_{fiber} αᵢ^P βⱼ)^{1/P} (∑ⱼ βⱼ)^{1 - 1/P}`. -/
theorem fiber_bound {α β : I → ℝ} (hα0 : ∀ i, 0 ≤ α i) (hβ0 : ∀ j, 0 ≤ β j) {P : ℝ} (hP : 1 ≤ P)
    (hα : Summable fun i => α i ^ P) (hβ : Summable β) (k : I) :
    Summable (fun q : fiber k => α q.1.1 * β q.1.2) ∧
      ∑' q : fiber k, α q.1.1 * β q.1.2 ≤
        (∑' q : fiber k, α q.1.1 ^ P * β q.1.2) ^ (1 / P) * (∑' j, β j) ^ (1 - 1 / P) := by
  have hG : Summable fun q : I × I => α q.1 ^ P * β q.2 :=
    hα.mul_of_nonneg hβ (fun i => Real.rpow_nonneg (hα0 i) P) hβ0
  have hGf : Summable fun q : fiber k => α q.1.1 ^ P * β q.1.2 :=
    ((sigmaFiberEquiv.summable_iff (f := fun q : I × I => α q.1 ^ P * β q.2)).2 hG).sigma_factor k
  have hβf : Summable fun q : fiber k => β q.1.2 := hβ.comp_injective (fiber_snd_injective k)
  have hβle : ∑' q : fiber k, β q.1.2 ≤ ∑' j, β j :=
    tsum_comp_le_tsum_of_inj hβ hβ0 (fiber_snd_injective k)
  rcases eq_or_lt_of_le hP with h1 | h1
  · subst h1
    simp only [Real.rpow_one, div_one, sub_self, Real.rpow_zero, mul_one] at hGf ⊢
    exact ⟨hGf, le_rfl⟩
  -- `P > 1`: Hölder with the conjugate exponent `Q`
  set Q := P.conjExponent with hQ
  have hPQ : P.HolderConjugate Q := Real.HolderConjugate.conjExponent h1
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hinv : 1 / Q = 1 - 1 / P := by
    have := hPQ.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  set f : fiber k → ℝ := fun q => α q.1.1 * β q.1.2 ^ (1 / P) with hf
  set g : fiber k → ℝ := fun q => β q.1.2 ^ (1 / Q) with hg
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (hα0 _) (Real.rpow_nonneg (hβ0 _) _)
  have hg0 : ∀ q, 0 ≤ g q := fun q => Real.rpow_nonneg (hβ0 _) _
  have hfP : ∀ q, f q ^ P = α q.1.1 ^ P * β q.1.2 := fun q => by
    rw [hf, Real.mul_rpow (hα0 _) (Real.rpow_nonneg (hβ0 _) _), ← Real.rpow_mul (hβ0 _),
      one_div_mul_cancel hP0.ne', Real.rpow_one]
  have hgQ : ∀ q, g q ^ Q = β q.1.2 := fun q => by
    rw [hg, ← Real.rpow_mul (hβ0 _), one_div_mul_cancel hQ0.ne', Real.rpow_one]
  have hfg : ∀ q, f q * g q = α q.1.1 * β q.1.2 := fun q => by
    rw [hf, hg, mul_assoc, ← Real.rpow_add' (hβ0 _) (by rw [hinv]; norm_num), hinv]
    norm_num
  have hsP : Summable fun q => f q ^ P := by simpa only [hfP] using hGf
  have hsQ : Summable fun q => g q ^ Q := by simpa only [hgQ] using hβf
  refine ⟨?_, ?_⟩
  · simpa only [hfg] using Real.summable_mul_of_Lp_Lq_of_nonneg hPQ hf0 hg0 hsP hsQ
  · have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hPQ hf0 hg0 hsP hsQ
    simp only [hfg, hfP, hgQ] at hH
    refine hH.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg
      (tsum_nonneg fun q => mul_nonneg (Real.rpow_nonneg (hα0 _) P) (hβ0 _)) _))
    rw [hinv]
    exact Real.rpow_le_rpow (tsum_nonneg fun q => hβ0 _) hβle (by
      have : 1 / P ≤ 1 := by rw [div_le_one hP0]; exact hP
      linarith)

end Fiber

/-! ### Young's inequality -/

section Young

variable [IsCancelAdd I] [hω : ω.IsSubmultiplicative] {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

theorem one_le_toReal (hp : p ≠ ⊤) : 1 ≤ p.toReal := by
  have := ENNReal.toReal_mono hp hp1.out
  rwa [ENNReal.toReal_one] at this

omit [IsCancelAdd I] hp1 in
/-- On the fiber of `k`: `ω k |a_i b_j| ≤ (ω i |a_i|) (ω j |b_j|)`. -/
theorem term_le' (a b : I → 𝕜) (k : I) (q : fiber k) :
    ω k * ‖a q.1.1 * b q.1.2‖ ≤ (ω q.1.1 * ‖a q.1.1‖) * (ω q.1.2 * ‖b q.1.2‖) := by
  have hk : ω k ≤ ω q.1.1 * ω q.1.2 := by
    have := hω.le_mul q.1.1 q.1.2
    rwa [q.2] at this
  rw [norm_mul]
  calc ω k * (‖a q.1.1‖ * ‖b q.1.2‖) ≤ (ω q.1.1 * ω q.1.2) * (‖a q.1.1‖ * ‖b q.1.2‖) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ω q.1.1 * ‖a q.1.1‖ * (ω q.1.2 * ‖b q.1.2‖) := by ring

/-- The fiber bound for `a ∈ ℓ^p`, `b ∈ ℓ¹`. -/
theorem fiber_bound_Lp (hp : p ≠ ⊤) (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) (k : I) :
    Summable (fun q : fiber k => ‖a q.1.1 * b q.1.2‖) ∧
      ω k * ‖conv a b k‖ ≤
        (∑' q : fiber k, (ω q.1.1 * ‖a q.1.1‖) ^ p.toReal * (ω q.1.2 * ‖b q.1.2‖)) ^
          (1 / p.toReal) * ‖b‖ ^ (1 - 1 / p.toReal) := by
  have hP := one_le_toReal hp
  obtain ⟨hs, hle⟩ := fiber_bound (nonneg_weighted a) (nonneg_weighted b) hP
    (summable_rpow (by linarith) a) b.summable k
  rw [← WeightedL1.norm_eq_tsum] at hle
  have hsum : Summable fun q : fiber k => ‖a q.1.1 * b q.1.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by
      rw [le_inv_mul_iff₀ (ω.pos k)]
      exact term_le' a b k q)
      (hs.mul_left (ω k)⁻¹)
  refine ⟨hsum, ?_⟩
  calc ω k * ‖conv a b k‖ ≤ ω k * ∑' q : fiber k, ‖a q.1.1 * b q.1.2‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) (ω.pos k).le
    _ = ∑' q : fiber k, ω k * ‖a q.1.1 * b q.1.2‖ := tsum_mul_left.symm
    _ ≤ ∑' q : fiber k, (ω q.1.1 * ‖a q.1.1‖) * (ω q.1.2 * ‖b q.1.2‖) :=
        (hsum.mul_left _).tsum_le_tsum (term_le' a b k) hs
    _ ≤ _ := hle

/-- The sums defining `(a * b)_k` converge absolutely for `a ∈ ℓ^p`, `b ∈ ℓ¹`. -/
theorem summable_fiber_Lp (hp : p ≠ ⊤) (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) (k : I) :
    Summable fun q : fiber k => ‖a q.1.1 * b q.1.2‖ :=
  (fiber_bound_Lp hp a b k).1

/-- `(ω_k |(a * b)_k|)^p ≤ (∑_{fiber} αᵢ^p βⱼ) ‖b‖^{p - 1}`, and the regrouped sum. -/
theorem rpow_le (hp : p ≠ ⊤) (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) (k : I) :
    (ω k * ‖conv a b k‖) ^ p.toReal ≤
      (∑' q : fiber k, (ω q.1.1 * ‖a q.1.1‖) ^ p.toReal * (ω q.1.2 * ‖b q.1.2‖)) *
        ‖b‖ ^ (p.toReal - 1) := by
  have hP := one_le_toReal hp
  have hP0 : 0 < p.toReal := by linarith
  have hS0 : 0 ≤ ∑' q : fiber k, (ω q.1.1 * ‖a q.1.1‖) ^ p.toReal * (ω q.1.2 * ‖b q.1.2‖) :=
    tsum_nonneg fun q => mul_nonneg (Real.rpow_nonneg (nonneg_weighted a _) _) (nonneg_weighted b _)
  refine (Real.rpow_le_rpow (nonneg_weighted (conv a b) k) (fiber_bound_Lp hp a b k).2
    hP0.le).trans_eq ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hS0 _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul hS0, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hP0.ne',
    Real.rpow_one, sub_mul, one_mul, one_div_mul_cancel hP0.ne']

theorem summable_conv_rpow (hp : p ≠ ⊤) (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) :
    Summable (fun k => (ω k * ‖conv a b k‖) ^ p.toReal) ∧
      ∑' k, (ω k * ‖conv a b k‖) ^ p.toReal ≤
        (∑' i, (ω i * ‖a i‖) ^ p.toReal) * ‖b‖ * ‖b‖ ^ (p.toReal - 1) := by
  have hP0 : 0 < p.toReal := by linarith [one_le_toReal hp]
  set G : I × I → ℝ := fun q => (ω q.1 * ‖a q.1‖) ^ p.toReal * (ω q.2 * ‖b q.2‖) with hGdef
  have hG : Summable G := (summable_rpow hP0 a).mul_of_nonneg b.summable
    (fun i => Real.rpow_nonneg (nonneg_weighted a i) _) (nonneg_weighted b)
  have hGs : Summable fun σ : Σ k : I, fiber k => G σ.2.1 :=
    (sigmaFiberEquiv.summable_iff (f := G)).2 hG
  have hsumG : ∑' k, ∑' q : fiber k, G q.1 = (∑' i, (ω i * ‖a i‖) ^ p.toReal) * ‖b‖ := by
    rw [← hGs.tsum_sigma, WeightedL1.norm_eq_tsum,
      (summable_rpow hP0 a).tsum_mul_tsum b.summable hG]
    exact sigmaFiberEquiv.tsum_eq G
  have hdom : Summable fun k => (∑' q : fiber k, G q.1) * ‖b‖ ^ (p.toReal - 1) :=
    hGs.sigma.mul_right _
  have hs : Summable fun k => (ω k * ‖conv a b k‖) ^ p.toReal :=
    Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (nonneg_weighted _ k) _) (rpow_le hp a b) hdom
  refine ⟨hs, ?_⟩
  calc ∑' k, (ω k * ‖conv a b k‖) ^ p.toReal
      ≤ ∑' k, (∑' q : fiber k, G q.1) * ‖b‖ ^ (p.toReal - 1) :=
        hs.tsum_le_tsum (rpow_le hp a b) hdom
    _ = _ := by rw [tsum_mul_right, hsumG]

variable (hp : p ≠ ⊤)

/-- The convolution `a * b ∈ ℓ^p_{ω,I}` of `a ∈ ℓ^p_{ω,I}` and `b ∈ ℓ¹_{ω,I}`. -/
noncomputable def convLp (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) : WeightedLp 𝕜 ω p :=
  WeightedLp.mk (conv a b) (memℓp_gen (by
    simpa [norm_weigh_apply] using (summable_conv_rpow hp a b).1))

@[simp] theorem convLp_apply (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) (k : I) :
    convLp hp a b k = conv a b k := rfl

/-- Young's inequality: `‖a * b‖_p ≤ ‖a‖_p ‖b‖₁`. -/
theorem norm_convLp_le (a : WeightedLp 𝕜 ω p) (b : WeightedL1 𝕜 ω) :
    ‖convLp hp a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hP0 : 0 < p.toReal := by linarith [one_le_toReal hp]
  set A := ∑' i, (ω i * ‖a i‖) ^ p.toReal
  have hA0 : 0 ≤ A := tsum_nonneg fun i => Real.rpow_nonneg (nonneg_weighted a i) _
  have hb0 := norm_nonneg b
  rw [norm_eq_tsum_rpow hP0, norm_eq_tsum_rpow hP0 a]
  simp only [convLp_apply]
  have hbound : (A * ‖b‖ * ‖b‖ ^ (p.toReal - 1)) = A * ‖b‖ ^ p.toReal := by
    rw [mul_assoc, ← Real.rpow_one_add' hb0 (by linarith), add_sub_cancel]
  calc (∑' k, (ω k * ‖conv a b k‖) ^ p.toReal) ^ (1 / p.toReal)
      ≤ (A * ‖b‖ ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_le_rpow (tsum_nonneg fun k => Real.rpow_nonneg (nonneg_weighted _ k) _)
          ((summable_conv_rpow hp a b).2.trans_eq hbound) (by positivity)
    _ = A ^ (1 / p.toReal) * ‖b‖ := by
        rw [Real.mul_rpow hA0 (Real.rpow_nonneg hb0 _), ← Real.rpow_mul hb0,
          mul_one_div_cancel hP0.ne', Real.rpow_one]

end Young

end Convolution

end RadiiPolynomial
