module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.RCLike.Basic

/-!
# Weighted ℓ^p spaces

A sequence of weights over an index type `I` is a family of positive reals `ω k` (`Weights I`).
For `𝕜 ∈ {ℝ, ℂ}` and `p ∈ [1, ∞]`, the weighted space `WeightedLp 𝕜 ω p = ℓ^p_{ω,I}` consists of
the sequences `a : I → 𝕜` with `(ω k a k)_k ∈ ℓ^p`, normed by `‖a‖ = ‖(ω k a k)_k‖_p`; for
`p < ∞` this is `(∑ₖ (ω k |a k|)^p)^{1/p}`.

The space is defined by transport from Mathlib's `lp`: the map `a ↦ (ω k a k)_k` (`toLp`) is a
bijective linear isometry onto `lp`, which gives the normed space structure and completeness
(`WeightedLp.toLpEquiv`, `WeightedLp.instCompleteSpace`).

`WeightedLp` is a type of its own (built on the submodule `WeightedLp.submodule` of `I → 𝕜`), so
that it carries no other norm, even when `I` is finite. Elements coerce to functions `I → 𝕜`.
-/

@[expose] public section

open scoped ENNReal

namespace RadiiPolynomial

/-- A sequence of weights over `I`: positive real numbers `ω k`. -/
structure Weights (I : Type*) where
  /-- the weights -/
  toFun : I → ℝ
  /-- the weights are positive -/
  pos' : ∀ k, 0 < toFun k

namespace Weights

variable {I : Type*}

instance : CoeFun (Weights I) fun _ => I → ℝ := ⟨Weights.toFun⟩

theorem pos (ω : Weights I) (k : I) : 0 < ω k := ω.pos' k

theorem ne_zero (ω : Weights I) (k : I) : ω k ≠ 0 := (ω.pos k).ne'

@[simp] theorem abs_apply (ω : Weights I) (k : I) : |ω k| = ω k := abs_of_pos (ω.pos k)

end Weights

variable (𝕜 : Type*) [RCLike 𝕜] {I : Type*}

/-- The weighted sequence `k ↦ ω k a k`. -/
def weigh (ω : Weights I) (a : I → 𝕜) : I → 𝕜 := fun k => (ω k : 𝕜) * a k

variable {𝕜}

@[simp] theorem weigh_apply (ω : Weights I) (a : I → 𝕜) (k : I) :
    weigh 𝕜 ω a k = (ω k : 𝕜) * a k := rfl

theorem norm_weigh_apply (ω : Weights I) (a : I → 𝕜) (k : I) :
    ‖weigh 𝕜 ω a k‖ = ω k * ‖a k‖ := by
  rw [weigh_apply, norm_mul, RCLike.norm_ofReal, abs_of_pos (ω.pos k)]

namespace WeightedLp

variable (𝕜) in
/-- The sequences `a` with `(ω k a k)_k ∈ ℓ^p`, as a submodule of `I → 𝕜`. -/
def submodule (ω : Weights I) (p : ℝ≥0∞) : Submodule 𝕜 (I → 𝕜) where
  carrier := {a | Memℓp (weigh 𝕜 ω a) p}
  add_mem' {a b} ha hb := by
    have : weigh 𝕜 ω (a + b) = weigh 𝕜 ω a + weigh 𝕜 ω b := by
      funext k; simp [mul_add]
    show Memℓp (weigh 𝕜 ω (a + b)) p
    rw [this]; exact ha.add hb
  zero_mem' := by
    have : weigh 𝕜 ω (0 : I → 𝕜) = 0 := by funext k; simp
    show Memℓp (weigh 𝕜 ω 0) p
    rw [this]; exact zero_memℓp
  smul_mem' c a ha := by
    have : weigh 𝕜 ω (c • a) = fun k => c * weigh 𝕜 ω a k := by
      funext k; simp only [weigh_apply, Pi.smul_apply, smul_eq_mul]; ring
    show Memℓp (weigh 𝕜 ω (c • a)) p
    rw [this]; exact Memℓp.const_mul ha c

end WeightedLp

variable (𝕜) in
/-- The weighted space `ℓ^p_{ω,I}` of sequences `a : I → 𝕜` with `(ω k a k)_k ∈ ℓ^p`. -/
def WeightedLp (ω : Weights I) (p : ℝ≥0∞) : Type _ := WeightedLp.submodule 𝕜 ω p

namespace WeightedLp

variable {ω : Weights I} {p : ℝ≥0∞}

instance : AddCommGroup (WeightedLp 𝕜 ω p) := inferInstanceAs (AddCommGroup (submodule 𝕜 ω p))

instance : Module 𝕜 (WeightedLp 𝕜 ω p) := inferInstanceAs (Module 𝕜 (submodule 𝕜 ω p))

/-- The coefficients `(a k)_k` of `a`. -/
@[coe] def coeff (a : WeightedLp 𝕜 ω p) : I → 𝕜 := (show submodule 𝕜 ω p from a).1

instance : CoeFun (WeightedLp 𝕜 ω p) fun _ => I → 𝕜 := ⟨coeff⟩

theorem memℓp (a : WeightedLp 𝕜 ω p) : Memℓp (weigh 𝕜 ω a) p := (show submodule 𝕜 ω p from a).2

/-- The element of `WeightedLp` with coefficients `a`. -/
def mk (a : I → 𝕜) (ha : Memℓp (weigh 𝕜 ω a) p) : WeightedLp 𝕜 ω p :=
  (⟨a, ha⟩ : submodule 𝕜 ω p)

@[simp] theorem mk_apply (a : I → 𝕜) (ha : Memℓp (weigh 𝕜 ω a) p) (k : I) :
    mk a ha k = a k := rfl

@[ext] theorem ext {a b : WeightedLp 𝕜 ω p} (h : ∀ k, a k = b k) : a = b :=
  show (show submodule 𝕜 ω p from a) = (show submodule 𝕜 ω p from b) from Subtype.ext (funext h)

@[simp] theorem zero_apply (k : I) : (0 : WeightedLp 𝕜 ω p) k = 0 := rfl

@[simp] theorem add_apply (a b : WeightedLp 𝕜 ω p) (k : I) : (a + b) k = a k + b k := rfl

@[simp] theorem neg_apply (a : WeightedLp 𝕜 ω p) (k : I) : (-a) k = -a k := rfl

@[simp] theorem sub_apply (a b : WeightedLp 𝕜 ω p) (k : I) : (a - b) k = a k - b k := rfl

@[simp] theorem smul_apply (c : 𝕜) (a : WeightedLp 𝕜 ω p) (k : I) : (c • a) k = c * a k := rfl

/-- The weighted sequence `(ω k a k)_k` as an element of `lp`. -/
def toLp : WeightedLp 𝕜 ω p →ₗ[𝕜] lp (fun _ : I => 𝕜) p where
  toFun a := ⟨weigh 𝕜 ω a, a.memℓp⟩
  map_add' a b := lp.ext (by rw [lp.coeFn_add]; funext k; simp [mul_add])
  map_smul' c a := lp.ext (by rw [lp.coeFn_smul]; funext k; simp; ring)

@[simp] theorem toLp_apply (a : WeightedLp 𝕜 ω p) (k : I) : toLp a k = (ω k : 𝕜) * a k := rfl

theorem toLp_injective : Function.Injective (toLp : WeightedLp 𝕜 ω p → lp (fun _ : I => 𝕜) p) := by
  intro a b h
  ext k
  have := congrArg (fun x : lp (fun _ : I => 𝕜) p => x k) h
  simp only [toLp_apply] at this
  exact mul_left_cancel₀ (by exact_mod_cast ω.ne_zero k) this

/-- The inverse of `toLp`: `x ↦ (x k / ω k)_k`. -/
def ofLp (x : lp (fun _ : I => 𝕜) p) : WeightedLp 𝕜 ω p :=
  mk (fun k => (ω k : 𝕜)⁻¹ * x k) (by
    have : weigh 𝕜 ω (fun k => (ω k : 𝕜)⁻¹ * x k) = (x : I → 𝕜) := by
      funext k
      simp only [weigh_apply]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ω.ne_zero k), one_mul]
    rw [this]; exact x.2)

theorem toLp_ofLp (x : lp (fun _ : I => 𝕜) p) : toLp (ofLp (ω := ω) x) = x := by
  refine lp.ext (funext fun k => ?_)
  change (ω k : 𝕜) * ((ω k : 𝕜)⁻¹ * x k) = x k
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ω.ne_zero k), one_mul]

theorem sum_apply {ι : Type*} (S : Finset ι) (a : ι → WeightedLp 𝕜 ω p) (k : I) :
    (∑ i ∈ S, a i) k = ∑ i ∈ S, a i k := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, add_apply, ih]

section Normed

variable [Fact (1 ≤ p)]

/-- The norm of `WeightedLp`: `‖a‖ = ‖(ω k a k)_k‖_p`. -/
noncomputable instance : NormedAddCommGroup (WeightedLp 𝕜 ω p) :=
  NormedAddCommGroup.induced _ _ (toLp : WeightedLp 𝕜 ω p →ₗ[𝕜] _).toAddMonoidHom toLp_injective

noncomputable instance : NormedSpace 𝕜 (WeightedLp 𝕜 ω p) :=
  NormedSpace.induced 𝕜 _ _ (toLp : WeightedLp 𝕜 ω p →ₗ[𝕜] _)

theorem norm_def (a : WeightedLp 𝕜 ω p) : ‖a‖ = ‖toLp a‖ := rfl

variable (𝕜 ω p) in
/-- `a ↦ (ω k a k)_k` is a linear isometric equivalence `ℓ^p_{ω,I} ≃ ℓ^p`. -/
noncomputable def toLpEquiv : WeightedLp 𝕜 ω p ≃ₗᵢ[𝕜] lp (fun _ : I => 𝕜) p :=
  { LinearEquiv.ofBijective (toLp : WeightedLp 𝕜 ω p →ₗ[𝕜] _)
      ⟨toLp_injective, fun x => ⟨ofLp x, toLp_ofLp x⟩⟩ with
    norm_map' := fun _ => rfl }

/-- `ℓ^p_{ω,I}` is a Banach space. -/
instance instCompleteSpace : CompleteSpace (WeightedLp 𝕜 ω p) :=
  (toLpEquiv 𝕜 ω p).toIsometryEquiv.completeSpace

/-- `‖a‖ = 0 ↔ a = 0` and the other norm axioms hold by construction; for reference, each
coefficient satisfies `ω k |a k| ≤ ‖a‖`. -/
theorem norm_apply_le (a : WeightedLp 𝕜 ω p) (k : I) : ω k * ‖a k‖ ≤ ‖a‖ := by
  have hp : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have := lp.norm_apply_le_norm hp (toLp a) k
  rwa [toLp_apply, norm_mul, RCLike.norm_ofReal, abs_of_pos (ω.pos k)] at this

/-- Evaluation of the coefficient `k` is a bounded linear functional: `|a k| ≤ ‖a‖ / ω k`. -/
noncomputable def evalCLM (k : I) : WeightedLp 𝕜 ω p →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun a => a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    (ω k)⁻¹ fun a => by
      change ‖a k‖ ≤ (ω k)⁻¹ * ‖a‖
      rw [le_inv_mul_iff₀ (ω.pos k)]
      exact norm_apply_le a k

@[simp] theorem evalCLM_apply (k : I) (a : WeightedLp 𝕜 ω p) : evalCLM k a = a k := rfl

theorem continuous_apply (k : I) : Continuous fun a : WeightedLp 𝕜 ω p => a k :=
  (evalCLM k).continuous

end Normed

end WeightedLp

end RadiiPolynomial
