module

public import RadiiPolynomial.WeightedLp.WeightedL1
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Linear operators on weighted ℓ¹ and on finite products

* Column-norm bound. An infinite matrix `M : I → J → 𝕜` whose weighted columns satisfy
  `∑ₘ |M m n| ω m ≤ K ω' n` for all `n` (`ColNormBound M ω ω' K`) defines an operator
  `ℓ¹_{ω',J} → ℓ¹_{ω,I}`, `(M b)_m = ∑ₙ M m n b n`, of norm at most `K`
  (`ColNormBound.toCLM`, `ColNormBound.norm_toCLM_le`). The sums defining `M b` converge
  absolutely. Operators made of a finite matrix block and a diagonal tail are special cases.
* Block operators on finite products. Bounded operators `A i j : V j → W i` define
  `(A v)_i = ∑ⱼ A i j v j` on `∏ⱼ V j → ∏ᵢ W i` (sup norms), with
  `‖A‖ ≤ maxᵢ ∑ⱼ ‖A i j‖` (`blockCLM`, `norm_blockCLM_le`).
-/

@[expose] public section

namespace RadiiPolynomial

section ColNorm

variable {𝕜 : Type*} [RCLike 𝕜] {I J : Type*} {ω : Weights I} {ω' : Weights J}

/-- The weighted columns of `M` are summable and `∑ₘ |M m n| ω m ≤ K ω' n` for every `n`. -/
structure ColNormBound (M : I → J → 𝕜) (ω : Weights I) (ω' : Weights J) (K : ℝ) : Prop where
  nonneg : 0 ≤ K
  summable : ∀ n, Summable fun m => ‖M m n‖ * ω m
  le : ∀ n, ∑' m, ‖M m n‖ * ω m ≤ K * ω' n

namespace ColNormBound

variable {M : I → J → 𝕜} {K : ℝ} (h : ColNormBound M ω ω' K)
include h

omit h in
theorem nonneg_double (b : WeightedL1 𝕜 ω') (m : I) (n : J) : 0 ≤ ‖M m n‖ * ω m * ‖b n‖ :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (ω.pos m).le) (norm_nonneg _)

/-- Summing the double family `‖M m n‖ ω m ‖b n‖` over `m` first gives at most
`K ω' n ‖b n‖`, which is summable over `n`. -/
theorem summable_double_swap (b : WeightedL1 𝕜 ω') :
    Summable fun q : J × I => ‖M q.2 q.1‖ * ω q.2 * ‖b q.1‖ := by
  have hf : (0 : J × I → ℝ) ≤ fun q => ‖M q.2 q.1‖ * ω q.2 * ‖b q.1‖ := by
    intro q
    exact nonneg_double b q.2 q.1
  refine (summable_prod_of_nonneg hf).2 ⟨fun n => ?_, ?_⟩
  · exact (h.summable n).mul_right ‖b n‖
  · refine Summable.of_nonneg_of_le (f := fun n => K * (ω' n * ‖b n‖)) (fun n => ?_)
      (fun n => ?_) (b.summable.mul_left K)
    · exact tsum_nonneg fun m => hf (n, m)
    · show ∑' m, ‖M m n‖ * ω m * ‖b n‖ ≤ K * (ω' n * ‖b n‖)
      rw [tsum_mul_right, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (h.le n) (norm_nonneg _)

/-- The nonnegative double family `‖M m n‖ ω m ‖b n‖` is summable over `I × J`. -/
theorem summable_double (b : WeightedL1 𝕜 ω') :
    Summable (Function.uncurry fun m n => ‖M m n‖ * ω m * ‖b n‖) :=
  (h.summable_double_swap b).prod_symm

/-- Each row `n ↦ M m n b n` is absolutely summable. -/
theorem summable_row (b : WeightedL1 𝕜 ω') (m : I) : Summable fun n => ‖M m n * b n‖ := by
  have := ((h.summable_double b).prod_factor m).mul_left (ω m)⁻¹
  refine this.congr fun n => ?_
  simp only [Function.uncurry_apply_pair, norm_mul]
  field_simp [ω.ne_zero m]

/-- The weighted terms of the image are dominated by the row sums of the double family. -/
theorem weighted_image_le (b : WeightedL1 𝕜 ω') (m : I) :
    ω m * ‖∑' n, M m n * b n‖ ≤ ∑' n, ‖M m n‖ * ω m * ‖b n‖ := by
  calc ω m * ‖∑' n, M m n * b n‖ ≤ ω m * ∑' n, ‖M m n * b n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (h.summable_row b m)) (ω.pos m).le
    _ = ∑' n, ‖M m n‖ * ω m * ‖b n‖ := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by rw [norm_mul]; ring

/-- The image `(M b)_m = ∑ₙ M m n b n` is in `ℓ¹_{ω,I}`. -/
theorem summable_image (b : WeightedL1 𝕜 ω') :
    Summable fun m => ω m * ‖∑' n, M m n * b n‖ :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (ω.pos m).le (norm_nonneg _))
    (h.weighted_image_le b) ((h.summable_double b).prod)

/-- `∑ₘ ω m |(M b)_m| ≤ K ‖b‖`. -/
theorem tsum_image_le (b : WeightedL1 𝕜 ω') :
    ∑' m, ω m * ‖∑' n, M m n * b n‖ ≤ K * ‖b‖ := by
  calc ∑' m, ω m * ‖∑' n, M m n * b n‖ ≤ ∑' m, ∑' n, ‖M m n‖ * ω m * ‖b n‖ :=
        (h.summable_image b).tsum_le_tsum (h.weighted_image_le b) (h.summable_double b).prod
    _ = ∑' n, ∑' m, ‖M m n‖ * ω m * ‖b n‖ := (h.summable_double b).tsum_comm.symm
    _ ≤ ∑' n, K * (ω' n * ‖b n‖) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (h.summable_double_swap b).prod
          (b.summable.mul_left K)
        rw [tsum_mul_right, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (h.le n) (norm_nonneg _)
    _ = K * ‖b‖ := by rw [tsum_mul_left, WeightedL1.norm_eq_tsum]

/-- The operator `b ↦ M b` as a linear map `ℓ¹_{ω',J} → ℓ¹_{ω,I}`. -/
noncomputable def toLinearMap : WeightedL1 𝕜 ω' →ₗ[𝕜] WeightedL1 𝕜 ω where
  toFun b := WeightedL1.ofSummable (fun m => ∑' n, M m n * b n) (h.summable_image b)
  map_add' b c := by
    ext m
    simp only [WeightedL1.ofSummable_apply, WeightedLp.add_apply, mul_add]
    exact ((h.summable_row b m).of_norm).tsum_add (h.summable_row c m).of_norm
  map_smul' c b := by
    ext m
    simp only [WeightedL1.ofSummable_apply, WeightedLp.smul_apply, RingHom.id_apply]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring

/-- The bounded operator `b ↦ M b`, `ℓ¹_{ω',J} → ℓ¹_{ω,I}`. -/
noncomputable def toCLM : WeightedL1 𝕜 ω' →L[𝕜] WeightedL1 𝕜 ω :=
  h.toLinearMap.mkContinuous K fun b => by
    rw [WeightedL1.norm_eq_tsum]
    exact h.tsum_image_le b

theorem toCLM_apply (b : WeightedL1 𝕜 ω') (m : I) : h.toCLM b m = ∑' n, M m n * b n := rfl

/-- Column-norm bound: `‖M‖ ≤ K`. -/
theorem norm_toCLM_le : ‖h.toCLM‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ h.nonneg _

omit h in
/-- A matrix with at most one nonzero entry `c n` per column, in row `σ n`: the column-norm
condition reads `|c n| ω (σ n) ≤ K ω' n`. -/
theorem single [DecidableEq I] (σ : J → I) (c : J → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ n, ‖c n‖ * ω (σ n) ≤ K * ω' n) :
    ColNormBound (fun m n => if m = σ n then c n else 0) ω ω' K where
  nonneg := hK
  summable n := summable_of_ne_finset_zero (s := {σ n}) fun m hm => by
    rw [Finset.mem_singleton] at hm
    simp [hm]
  le n := by
    rw [tsum_eq_single (σ n) fun m hm => by simp [hm]]
    simpa using hc n

end ColNormBound

end ColNorm

section Block

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
  {V : κ → Type*} {W : ι → Type*} [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace 𝕜 (V j)]
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace 𝕜 (W i)]

/-- The block operator `(A v)_i = ∑ⱼ A i j v j`. -/
def blockCLM (A : ∀ i j, V j →L[𝕜] W i) : (∀ j, V j) →L[𝕜] (∀ i, W i) :=
  ContinuousLinearMap.pi fun i => ∑ j, (A i j).comp (ContinuousLinearMap.proj j)

omit [Fintype ι] in
@[simp] theorem blockCLM_apply (A : ∀ i j, V j →L[𝕜] W i) (v : ∀ j, V j) (i : ι) :
    blockCLM A v i = ∑ j, A i j (v j) := by
  simp [blockCLM]

/-- `‖A‖ ≤ maxᵢ ∑ⱼ ‖A i j‖` for the block operator, with sup norms on the products. -/
theorem norm_blockCLM_le (A : ∀ i j, V j →L[𝕜] W i) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ∑ j, ‖A i j‖ ≤ C) : ‖blockCLM A‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).2 fun i => ?_
  rw [blockCLM_apply]
  calc ‖∑ j, A i j (v j)‖ ≤ ∑ j, ‖A i j (v j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖v‖ :=
        Finset.sum_le_sum fun j _ => (A i j).le_opNorm_of_le (norm_le_pi_norm v j)
    _ = (∑ j, ‖A i j‖) * ‖v‖ := (Finset.sum_mul ..).symm
    _ ≤ C * ‖v‖ := by gcongr; exact h i

end Block

end RadiiPolynomial
