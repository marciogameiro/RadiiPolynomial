module

public import RadiiPolynomial.WeightedLp.WeightedL1
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Convolution on weighted ℓ¹

Let `I` be a commutative (additive) monoid. The convolution of `a, b : I → 𝕜` is

  `(a * b)_k = ∑_{i + j = k} a_i b_j`,

a sum over the fiber `fiber k = {(i, j) : i + j = k}` (finite for `I = ℕ`, infinite for `I = ℤ`).
A sequence of weights is submultiplicative if `ω (i + j) ≤ ω i ω j`.

For submultiplicative `ω`:
* `summable_fiber`, `summable_conv`, `norm_conv_le`: if `a, b ∈ ℓ¹_{ω,I}`, the sums defining
  `a * b` converge absolutely, `a * b ∈ ℓ¹_{ω,I}`, and `‖a * b‖ ≤ ‖a‖ ‖b‖`;
* the convolution is bilinear, commutative and associative, and `single 0 1` is a unit, so
  `ℓ¹_{ω,I}` is a commutative Banach algebra with unit (`instNormedCommRing`,
  `instNormedAlgebra`).

Associativity is proved by writing both `((a * b) * c)_k` and `(a * (b * c))_k` as the sum of
`a_i b_j c_l` over the triple fiber `{(i, j, l) : i + j + l = k}` (`tsum_conv_conv_left`,
`tsum_conv_conv_right`); regrouping is justified by absolute summability.
-/

@[expose] public section

open scoped ENNReal

namespace RadiiPolynomial

/-- A sequence of weights is submultiplicative if `ω (i + j) ≤ ω i ω j`. -/
class Weights.IsSubmultiplicative {I : Type*} [AddCommMonoid I] (ω : Weights I) : Prop where
  le_mul : ∀ i j, ω (i + j) ≤ ω i * ω j

namespace Convolution

variable {I : Type*} [AddCommMonoid I]

/-- The fiber `{(i, j) : i + j = k}`. -/
abbrev fiber (k : I) := {q : I × I // q.1 + q.2 = k}

/-- The triple fiber `{(i, j, l) : i + j + l = k}`. -/
abbrev fiber3 (k : I) := {t : I × I × I // t.1 + t.2.1 + t.2.2 = k}

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The convolution `(a * b)_k = ∑_{i + j = k} a_i b_j` of sequences `a, b : I → 𝕜`. -/
noncomputable def conv (a b : I → 𝕜) (k : I) : 𝕜 := ∑' q : fiber k, a q.1.1 * b q.1.2

/-- `(Σ k, fiber k) ≃ I × I`. -/
def sigmaFiberEquiv : (Σ k : I, fiber k) ≃ I × I := Equiv.sigmaFiberEquiv fun q : I × I => q.1 + q.2

/-- Regrouping `((a * b) * c)_k`: `(Σ (q : fiber k), fiber q.1) ≃ fiber3 k`. -/
def sigmaLeftEquiv (k : I) : (Σ q : fiber k, fiber q.1.1) ≃ fiber3 k where
  toFun σ := ⟨(σ.2.1.1, σ.2.1.2, σ.1.1.2), by rw [σ.2.2]; exact σ.1.2⟩
  invFun t := ⟨⟨(t.1.1 + t.1.2.1, t.1.2.2), t.2⟩, ⟨(t.1.1, t.1.2.1), rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨q₁, q₂⟩, hq⟩, ⟨⟨r₁, r₂⟩, hr⟩⟩
    simp only at hr
    subst hr
    rfl
  right_inv t := rfl

/-- Regrouping `(a * (b * c))_k`: `(Σ (q : fiber k), fiber q.2) ≃ fiber3 k`. -/
def sigmaRightEquiv (k : I) : (Σ q : fiber k, fiber q.1.2) ≃ fiber3 k where
  toFun σ := ⟨(σ.1.1.1, σ.2.1.1, σ.2.1.2), by rw [add_assoc, σ.2.2]; exact σ.1.2⟩
  invFun t := ⟨⟨(t.1.1, t.1.2.1 + t.1.2.2), by rw [← add_assoc]; exact t.2⟩,
    ⟨(t.1.2.1, t.1.2.2), rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨q₁, q₂⟩, hq⟩, ⟨⟨r₁, r₂⟩, hr⟩⟩
    simp only at hr
    subst hr
    rfl
  right_inv t := rfl

/-- `fiber k ≃ fiber k`, `(i, j) ↦ (j, i)`. -/
def fiberSwap (k : I) : fiber k ≃ fiber k where
  toFun q := ⟨q.1.swap, by rw [Prod.fst_swap, Prod.snd_swap, add_comm]; exact q.2⟩
  invFun q := ⟨q.1.swap, by rw [Prod.fst_swap, Prod.snd_swap, add_comm]; exact q.2⟩
  left_inv q := rfl
  right_inv q := rfl

section Analytic

variable {ω : Weights I} [hω : ω.IsSubmultiplicative]

/-- The product family `(ω i |a i|) (ω j |b j|)` on `I × I`; its sum is `‖a‖ ‖b‖`. -/
def prodFamily (a b : WeightedL1 𝕜 ω) (q : I × I) : ℝ := (ω q.1 * ‖a q.1‖) * (ω q.2 * ‖b q.2‖)

omit [AddCommMonoid I] hω in
theorem prodFamily_nonneg (a b : WeightedL1 𝕜 ω) (q : I × I) : 0 ≤ prodFamily a b q :=
  mul_nonneg (mul_nonneg (ω.pos _).le (norm_nonneg _)) (mul_nonneg (ω.pos _).le (norm_nonneg _))

omit [AddCommMonoid I] hω in
theorem summable_prodFamily (a b : WeightedL1 𝕜 ω) : Summable (prodFamily a b) :=
  a.summable.mul_of_nonneg b.summable (fun i => mul_nonneg (ω.pos i).le (norm_nonneg _))
    (fun j => mul_nonneg (ω.pos j).le (norm_nonneg _))

omit [AddCommMonoid I] hω in
theorem tsum_prodFamily (a b : WeightedL1 𝕜 ω) : ∑' q, prodFamily a b q = ‖a‖ * ‖b‖ := by
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum,
    a.summable.tsum_mul_tsum b.summable (summable_prodFamily a b)]
  rfl

omit hω in
/-- The product family, regrouped over the fibers. -/
theorem summable_sigma_prodFamily (a b : WeightedL1 𝕜 ω) :
    Summable fun σ : Σ k : I, fiber k => prodFamily a b σ.2.1 :=
  (sigmaFiberEquiv.summable_iff (f := prodFamily a b)).2 (summable_prodFamily a b)

omit hω in
theorem tsum_sigma_prodFamily (a b : WeightedL1 𝕜 ω) :
    ∑' k, ∑' q : fiber k, prodFamily a b q.1 = ‖a‖ * ‖b‖ := by
  rw [← (summable_sigma_prodFamily a b).tsum_sigma, ← tsum_prodFamily]
  exact sigmaFiberEquiv.tsum_eq (prodFamily a b)

/-- On the fiber of `k`: `ω k |a_i b_j| ≤ (ω i |a_i|) (ω j |b_j|)`. -/
theorem term_le (a b : WeightedL1 𝕜 ω) (k : I) (q : fiber k) :
    ω k * ‖a q.1.1 * b q.1.2‖ ≤ prodFamily a b q.1 := by
  have hk : ω k ≤ ω q.1.1 * ω q.1.2 := by
    have := hω.le_mul q.1.1 q.1.2
    rwa [q.2] at this
  rw [norm_mul, prodFamily]
  calc ω k * (‖a q.1.1‖ * ‖b q.1.2‖) ≤ (ω q.1.1 * ω q.1.2) * (‖a q.1.1‖ * ‖b q.1.2‖) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ω q.1.1 * ‖a q.1.1‖ * (ω q.1.2 * ‖b q.1.2‖) := by ring

/-- The sum defining `(a * b)_k` converges absolutely. -/
theorem summable_fiber (a b : WeightedL1 𝕜 ω) (k : I) :
    Summable fun q : fiber k => ‖a q.1.1 * b q.1.2‖ := by
  refine Summable.of_nonneg_of_le (f := fun q : fiber k => (ω k)⁻¹ * prodFamily a b q.1)
    (fun _ => norm_nonneg _) (fun q => ?_) (((summable_sigma_prodFamily a b).sigma_factor k).mul_left _)
  rw [le_inv_mul_iff₀ (ω.pos k)]
  exact term_le a b k q

theorem weighted_conv_le (a b : WeightedL1 𝕜 ω) (k : I) :
    ω k * ‖conv a b k‖ ≤ ∑' q : fiber k, prodFamily a b q.1 := by
  calc ω k * ‖conv a b k‖ ≤ ω k * ∑' q : fiber k, ‖a q.1.1 * b q.1.2‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (summable_fiber a b k)) (ω.pos k).le
    _ = ∑' q : fiber k, ω k * ‖a q.1.1 * b q.1.2‖ := (tsum_mul_left).symm
    _ ≤ ∑' q : fiber k, prodFamily a b q.1 :=
        ((summable_fiber a b k).mul_left _).tsum_le_tsum (term_le a b k)
          ((summable_sigma_prodFamily a b).sigma_factor k)

/-- `a * b ∈ ℓ¹_{ω,I}`. -/
theorem summable_conv (a b : WeightedL1 𝕜 ω) : Summable fun k => ω k * ‖conv a b k‖ :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (ω.pos k).le (norm_nonneg _))
    (weighted_conv_le a b) (summable_sigma_prodFamily a b).sigma

/-- `‖a * b‖ ≤ ‖a‖ ‖b‖`, in terms of the weighted sum. -/
theorem tsum_conv_le (a b : WeightedL1 𝕜 ω) : ∑' k, ω k * ‖conv a b k‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← tsum_sigma_prodFamily]
  exact (summable_conv a b).tsum_le_tsum (weighted_conv_le a b)
    (summable_sigma_prodFamily a b).sigma

/-- The triple family `(ω i |a_i|) (ω j |b_j|) (ω l |c_l|)` on `I × I × I`. -/
def tripleFamily (a b c : WeightedL1 𝕜 ω) (t : I × I × I) : ℝ :=
  (ω t.1 * ‖a t.1‖) * prodFamily b c t.2

omit [AddCommMonoid I] hω in
theorem summable_tripleFamily (a b c : WeightedL1 𝕜 ω) : Summable (tripleFamily a b c) :=
  a.summable.mul_of_nonneg (summable_prodFamily b c)
    (fun i => mul_nonneg (ω.pos i).le (norm_nonneg _)) (prodFamily_nonneg b c)

/-- The sum of `a_i b_j c_l` over the triple fiber of `k` converges absolutely. -/
theorem summable_fiber3 (a b c : WeightedL1 𝕜 ω) (k : I) :
    Summable fun t : fiber3 k => ‖a t.1.1 * b t.1.2.1 * c t.1.2.2‖ := by
  refine Summable.of_nonneg_of_le (f := fun t : fiber3 k => (ω k)⁻¹ * tripleFamily a b c t.1)
    (fun _ => norm_nonneg _) (fun t => ?_)
    (((summable_tripleFamily a b c).subtype fun t => t.1 + t.2.1 + t.2.2 = k).mul_left _)
  rw [le_inv_mul_iff₀ (ω.pos k)]
  have hk : ω k ≤ ω t.1.1 * ω t.1.2.1 * ω t.1.2.2 := by
    have h1 := hω.le_mul (t.1.1 + t.1.2.1) t.1.2.2
    rw [t.2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hω.le_mul _ _) (ω.pos _).le)
  rw [norm_mul, norm_mul, tripleFamily, prodFamily]
  calc ω k * (‖a t.1.1‖ * ‖b t.1.2.1‖ * ‖c t.1.2.2‖)
      ≤ (ω t.1.1 * ω t.1.2.1 * ω t.1.2.2) * (‖a t.1.1‖ * ‖b t.1.2.1‖ * ‖c t.1.2.2‖) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
    _ = ω t.1.1 * ‖a t.1.1‖ * (ω t.1.2.1 * ‖b t.1.2.1‖ * (ω t.1.2.2 * ‖c t.1.2.2‖)) := by ring

/-- `((a * b) * c)_k = ∑_{i + j + l = k} a_i b_j c_l`. -/
theorem conv_conv_left (a b c : WeightedL1 𝕜 ω) (k : I) :
    conv (conv a b) c k = ∑' t : fiber3 k, a t.1.1 * b t.1.2.1 * c t.1.2.2 := by
  have hs : Summable fun σ : Σ q : fiber k, fiber q.1.1 =>
      a σ.2.1.1 * b σ.2.1.2 * c σ.1.1.2 :=
    ((sigmaLeftEquiv k).summable_iff (f := fun t : fiber3 k => a t.1.1 * b t.1.2.1 * c t.1.2.2)).2
      (summable_fiber3 a b c k).of_norm
  calc conv (conv a b) c k
      = ∑' q : fiber k, ∑' r : fiber q.1.1, a r.1.1 * b r.1.2 * c q.1.2 :=
        tsum_congr fun q => tsum_mul_right.symm
    _ = ∑' σ : Σ q : fiber k, fiber q.1.1, a σ.2.1.1 * b σ.2.1.2 * c σ.1.1.2 := hs.tsum_sigma.symm
    _ = ∑' t : fiber3 k, a t.1.1 * b t.1.2.1 * c t.1.2.2 :=
        (sigmaLeftEquiv k).tsum_eq fun t : fiber3 k => a t.1.1 * b t.1.2.1 * c t.1.2.2

/-- `(a * (b * c))_k = ∑_{i + j + l = k} a_i b_j c_l`. -/
theorem conv_conv_right (a b c : WeightedL1 𝕜 ω) (k : I) :
    conv a (conv b c) k = ∑' t : fiber3 k, a t.1.1 * b t.1.2.1 * c t.1.2.2 := by
  have hs : Summable fun σ : Σ q : fiber k, fiber q.1.2 =>
      a σ.1.1.1 * b σ.2.1.1 * c σ.2.1.2 :=
    ((sigmaRightEquiv k).summable_iff (f := fun t : fiber3 k => a t.1.1 * b t.1.2.1 * c t.1.2.2)).2
      (summable_fiber3 a b c k).of_norm
  calc conv a (conv b c) k
      = ∑' q : fiber k, ∑' r : fiber q.1.2, a q.1.1 * b r.1.1 * c r.1.2 :=
        tsum_congr fun q => by
          rw [conv, ← tsum_mul_left]
          exact tsum_congr fun r => (mul_assoc _ _ _).symm
    _ = ∑' σ : Σ q : fiber k, fiber q.1.2, a σ.1.1.1 * b σ.2.1.1 * c σ.2.1.2 := hs.tsum_sigma.symm
    _ = ∑' t : fiber3 k, a t.1.1 * b t.1.2.1 * c t.1.2.2 :=
        (sigmaRightEquiv k).tsum_eq fun t : fiber3 k => a t.1.1 * b t.1.2.1 * c t.1.2.2

end Analytic

end Convolution

namespace WeightedL1

open Convolution

variable {I : Type*} [AddCommMonoid I] {𝕜 : Type*} [RCLike 𝕜] {ω : Weights I}
  [ω.IsSubmultiplicative]

/-- The convolution product on `ℓ¹_{ω,I}`. -/
noncomputable instance : Mul (WeightedL1 𝕜 ω) :=
  ⟨fun a b => ofSummable (conv a b) (summable_conv a b)⟩

theorem mul_apply (a b : WeightedL1 𝕜 ω) (k : I) : (a * b) k = conv a b k := rfl

/-- `‖a * b‖ ≤ ‖a‖ ‖b‖`. -/
theorem norm_mul_le' (a b : WeightedL1 𝕜 ω) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [norm_eq_tsum]; exact tsum_conv_le a b

protected theorem mul_assoc (a b c : WeightedL1 𝕜 ω) : a * b * c = a * (b * c) := by
  ext k
  change conv (conv a b) c k = conv a (conv b c) k
  rw [conv_conv_left, conv_conv_right]

protected theorem mul_comm (a b : WeightedL1 𝕜 ω) : a * b = b * a := by
  ext k
  change conv a b k = conv b a k
  calc conv a b k = ∑' q : fiber k, a (fiberSwap k q).1.1 * b (fiberSwap k q).1.2 :=
        ((fiberSwap k).tsum_eq fun q : fiber k => a q.1.1 * b q.1.2).symm
    _ = conv b a k := tsum_congr fun q => mul_comm _ _

protected theorem left_distrib (a b c : WeightedL1 𝕜 ω) : a * (b + c) = a * b + a * c := by
  ext k
  change conv a (b + c) k = conv a b k + conv a c k
  simp only [conv, Pi.add_apply, mul_add]
  exact (summable_fiber a b k).of_norm.tsum_add (summable_fiber a c k).of_norm

protected theorem right_distrib (a b c : WeightedL1 𝕜 ω) : (a + b) * c = a * c + b * c := by
  rw [WeightedL1.mul_comm, WeightedL1.left_distrib, WeightedL1.mul_comm c, WeightedL1.mul_comm c]

protected theorem zero_mul (a : WeightedL1 𝕜 ω) : 0 * a = 0 := by
  ext k
  change conv 0 a k = 0
  simp [conv]

protected theorem mul_zero (a : WeightedL1 𝕜 ω) : a * 0 = 0 := by
  rw [WeightedL1.mul_comm, WeightedL1.zero_mul]

protected theorem smul_mul_assoc (r : 𝕜) (a b : WeightedL1 𝕜 ω) : r • a * b = r • (a * b) := by
  ext k
  change conv (r • a) b k = r * conv a b k
  simp only [conv, WeightedLp.smul_apply, mul_assoc]
  exact tsum_mul_left

protected theorem mul_smul_comm (r : 𝕜) (a b : WeightedL1 𝕜 ω) : a * r • b = r • (a * b) := by
  rw [WeightedL1.mul_comm, WeightedL1.smul_mul_assoc, WeightedL1.mul_comm]

variable [DecidableEq I]

/-- The unit `e = single 0 1` (`e_0 = 1`, `e_k = 0` otherwise). -/
instance : One (WeightedL1 𝕜 ω) := ⟨single 0 1⟩

omit [ω.IsSubmultiplicative] in
theorem one_def : (1 : WeightedL1 𝕜 ω) = single 0 1 := rfl

protected theorem one_mul (a : WeightedL1 𝕜 ω) : 1 * a = a := by
  ext k
  change conv (single 0 1 : WeightedL1 𝕜 ω) a k = a k
  rw [conv, tsum_eq_single (⟨(0, k), zero_add k⟩ : fiber k) fun q hq => ?_]
  · simp
  · by_cases h0 : q.1.1 = 0
    · exfalso
      apply hq
      have h2 : q.1.2 = k := by have := q.2; rwa [h0, zero_add] at this
      exact Subtype.ext (Prod.ext h0 h2)
    · simp [single_apply, h0]

protected theorem mul_one (a : WeightedL1 𝕜 ω) : a * 1 = a := by
  rw [WeightedL1.mul_comm, WeightedL1.one_mul]

/-- `(ℓ¹_{ω,I}, *)` is a commutative ring. -/
noncomputable instance instCommRing : CommRing (WeightedL1 𝕜 ω) where
  __ := (inferInstance : AddCommGroup (WeightedL1 𝕜 ω))
  mul_assoc := WeightedL1.mul_assoc
  one_mul := WeightedL1.one_mul
  mul_one := WeightedL1.mul_one
  left_distrib := WeightedL1.left_distrib
  right_distrib := WeightedL1.right_distrib
  zero_mul := WeightedL1.zero_mul
  mul_zero := WeightedL1.mul_zero
  mul_comm := WeightedL1.mul_comm

/-- `(ℓ¹_{ω,I}, *)` is a commutative Banach algebra with unit: `‖a * b‖ ≤ ‖a‖ ‖b‖`. -/
noncomputable instance instNormedCommRing : NormedCommRing (WeightedL1 𝕜 ω) where
  __ := (inferInstance : NormedAddCommGroup (WeightedL1 𝕜 ω))
  __ := instCommRing
  norm_mul_le := norm_mul_le'

noncomputable instance instAlgebra : Algebra 𝕜 (WeightedL1 𝕜 ω) :=
  Algebra.ofModule WeightedL1.smul_mul_assoc WeightedL1.mul_smul_comm

noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (WeightedL1 𝕜 ω) where
  norm_smul_le := norm_smul_le

end WeightedL1

end RadiiPolynomial
