module

public import RadiiPolynomial.Convolution.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Evaluation at a bounded character

Let `χ : I → 𝕜` be a character of the monoid `I` (`χ 0 = 1`, `χ (i + j) = χ i χ j`) bounded by the
weights, `|χ i| ≤ ω i`. Then `a ↦ ∑ᵢ aᵢ χ(i)` converges absolutely on `ℓ¹_{ω,I}`
(`summable_charEval`) and is an algebra homomorphism `ℓ¹_{ω,I} → 𝕜` (`charEval`): the convolution
becomes the product, `∑ (a * b)_k χ(k) = (∑ aᵢ χ(i)) (∑ bⱼ χ(j))`. For `I = ℕ`, `χ(n) = tⁿ` this is
the evaluation of power series; for `I = ℤ`, `χ(k) = e^{ikt}` the evaluation of Fourier series.
-/

@[expose] public section

namespace RadiiPolynomial

namespace WeightedL1

open Convolution

variable {I : Type*} [AddCommMonoid I] {𝕜 : Type*} [RCLike 𝕜] {ω : Weights I}
  [ω.IsSubmultiplicative] {χ : I → 𝕜}

omit [AddCommMonoid I] [ω.IsSubmultiplicative] in
theorem summable_charEval (hle : ∀ i, ‖χ i‖ ≤ ω i) (a : WeightedL1 𝕜 ω) :
    Summable fun i => ‖a i * χ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hle i) (norm_nonneg _))
    a.summable

omit [ω.IsSubmultiplicative] in
/-- `∑ (a * b)_k χ(k) = (∑ aᵢ χ(i)) (∑ bⱼ χ(j))`. -/
theorem tsum_conv_mul_char (hadd : ∀ i j, χ (i + j) = χ i * χ j) (hle : ∀ i, ‖χ i‖ ≤ ω i)
    (a b : WeightedL1 𝕜 ω) :
    ∑' k, conv a b k * χ k = (∑' i, a i * χ i) * ∑' j, b j * χ j := by
  rw [tsum_mul_tsum_of_summable_norm (summable_charEval hle a) (summable_charEval hle b)]
  set h : I × I → 𝕜 := fun z => a z.1 * χ z.1 * (b z.2 * χ z.2) with hh
  have hsum : Summable fun z => ‖h z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => by
      rw [hh, norm_mul, norm_mul, norm_mul, prodFamily]
      calc ‖a z.1‖ * ‖χ z.1‖ * (‖b z.2‖ * ‖χ z.2‖)
          ≤ ‖a z.1‖ * ω z.1 * (‖b z.2‖ * ω z.2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hle _) (norm_nonneg _)) (by positivity)
              (mul_nonneg (norm_nonneg _) (ω.pos _).le)
        _ = ω z.1 * ‖a z.1‖ * (ω z.2 * ‖b z.2‖) := by ring) (summable_prodFamily a b)
  have hsig : Summable fun σ : Σ k : I, fiber k => h σ.2.1 :=
    (sigmaFiberEquiv.summable_iff (f := h)).2 hsum.of_norm
  rw [← sigmaFiberEquiv.tsum_eq h]
  change _ = ∑' c : Σ k : I, fiber k, h c.2.1
  rw [hsig.tsum_sigma]
  refine tsum_congr fun k => ?_
  rw [conv, ← tsum_mul_right]
  refine tsum_congr fun q => ?_
  change a q.1.1 * b q.1.2 * χ k = a q.1.1 * χ q.1.1 * (b q.1.2 * χ q.1.2)
  have hk : χ k = χ q.1.1 * χ q.1.2 := by rw [← hadd, q.2]
  rw [hk]
  ring

variable [DecidableEq I]

variable (χ) in
/-- Evaluation at the bounded character `χ`: an algebra homomorphism `ℓ¹_{ω,I} → 𝕜`. -/
noncomputable def charEval (h0 : χ 0 = 1) (hadd : ∀ i j, χ (i + j) = χ i * χ j)
    (hle : ∀ i, ‖χ i‖ ≤ ω i) : WeightedL1 𝕜 ω →ₐ[𝕜] 𝕜 :=
  AlgHom.ofLinearMap
    { toFun := fun a => ∑' i, a i * χ i
      map_add' := fun a b => by
        simp only [WeightedLp.add_apply, add_mul]
        exact (summable_charEval hle a).of_norm.tsum_add (summable_charEval hle b).of_norm
      map_smul' := fun c a => by
        simp only [WeightedLp.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc]
        exact tsum_mul_left }
    (by
      change ∑' i, (single 0 1 : WeightedL1 𝕜 ω) i * χ i = 1
      rw [tsum_eq_single 0 fun i hi => by simp [single_apply, hi]]
      simp [h0])
    (fun a b => tsum_conv_mul_char hadd hle a b)

theorem charEval_apply (h0 : χ 0 = 1) (hadd : ∀ i j, χ (i + j) = χ i * χ j)
    (hle : ∀ i, ‖χ i‖ ≤ ω i) (a : WeightedL1 𝕜 ω) :
    charEval χ h0 hadd hle a = ∑' i, a i * χ i := rfl

/-- `|∑ aᵢ χ(i)| ≤ ‖a‖`. -/
theorem norm_charEval_le (h0 : χ 0 = 1) (hadd : ∀ i j, χ (i + j) = χ i * χ j)
    (hle : ∀ i, ‖χ i‖ ≤ ω i) (a : WeightedL1 𝕜 ω) : ‖charEval χ h0 hadd hle a‖ ≤ ‖a‖ := by
  rw [charEval_apply, norm_eq_tsum]
  refine (norm_tsum_le_tsum_norm (summable_charEval hle a)).trans
    (Summable.tsum_le_tsum (fun i => ?_) (summable_charEval hle a) a.summable)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hle i) (norm_nonneg _)

end WeightedL1

end RadiiPolynomial
