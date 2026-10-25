module

public import RadiiPolynomial.Convolution.Instances

/-!
# Symmetric sequences

A sequence `a : ℤ → 𝕜` is symmetric if `a_{-n} = a_n` for all `n`. The convolution of symmetric
sequences is symmetric (`Convolution.isSymmetric_conv`), so the symmetric sequences form a
subalgebra of `ℓ¹_{ν,ℤ}` (`ν ≥ 1`), which is closed (`isClosed_symmetricSubalgebra`) and hence a
commutative Banach algebra with unit. It is the natural space for Chebyshev series: a symmetric
`a` is determined by `(a_n)_{n ≥ 0}`, and the convolution of symmetric sequences corresponds to
the product of Chebyshev series.
-/

@[expose] public section

namespace RadiiPolynomial

variable {𝕜 : Type*} [RCLike 𝕜]

/-- `a` is symmetric: `a_{-n} = a_n` for all `n`. -/
def IsSymmetric (a : ℤ → 𝕜) : Prop := ∀ n, a (-n) = a n

namespace Convolution

/-- The convolution of symmetric sequences is symmetric. -/
theorem isSymmetric_conv {a b : ℤ → 𝕜} (ha : IsSymmetric a) (hb : IsSymmetric b) :
    IsSymmetric (conv a b) := fun n => by
  rw [conv_int, conv_int, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply]
  rw [ha j, show -n - -j = -(n - j) by ring, hb]

end Convolution

namespace WeightedL1

variable (𝕜) (ν : ℝ) (hν : 1 ≤ ν)

/-- The symmetric sequences, a subalgebra of `ℓ¹_{ν,ℤ}`. -/
def symmetricSubalgebra : Subalgebra 𝕜 (WeightedL1 𝕜 (Weights.geomInt ν hν)) where
  carrier := {a | IsSymmetric a}
  mul_mem' {a b} ha hb := Convolution.isSymmetric_conv ha hb
  add_mem' {a b} ha hb n := by
    change a (-n) + b (-n) = a n + b n
    rw [ha n, hb n]
  algebraMap_mem' c n := by
    rw [Algebra.algebraMap_eq_smul_one, WeightedLp.smul_apply, WeightedLp.smul_apply, one_def,
      single_apply, single_apply]
    simp only [neg_eq_zero]

/-- The symmetric sequences form a closed subalgebra. -/
theorem isClosed_symmetricSubalgebra :
    IsClosed (symmetricSubalgebra 𝕜 ν hν : Set (WeightedL1 𝕜 (Weights.geomInt ν hν))) := by
  have : (symmetricSubalgebra 𝕜 ν hν : Set (WeightedL1 𝕜 (Weights.geomInt ν hν))) =
      ⋂ n : ℤ, {a | a (-n) = a n} := by
    ext a; simp [symmetricSubalgebra, IsSymmetric]
  rw [this]
  exact isClosed_iInter fun n =>
    isClosed_eq (WeightedLp.continuous_apply (-n)) (WeightedLp.continuous_apply n)

end WeightedL1

end RadiiPolynomial
