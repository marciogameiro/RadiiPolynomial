module

public import RadiiPolynomial.Abstract.Injectivity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Finite dimensions: invertibility and nondegenerate zeros

In finite dimension, `‖I - A B‖ < 1` implies that both `A` and `B` are invertible
(`isInvertible_of_norm_id_sub_comp_lt_one`). Combined with `radii_poly` (applied with `X = Y = E`,
`A† = Df(x̄)`, `Z₁ = 0`), this gives the finite-dimensional radii polynomial theorem: `Z₀ < 1` makes
`A` invertible, and the conclusion `‖I - A Df(x̃)‖ < 1` makes the zero `x̃` nondegenerate.

`ℝⁿ` with an arbitrary norm is modelled by an arbitrary finite-dimensional normed space `E` (in Lean
the norm is part of the type; `Fin n → ℝ` carries the sup norm).
-/

@[expose] public section

namespace RadiiPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- `x` is a nondegenerate zero of `f` (with derivative `Df`) if `f(x) = 0` and `Df(x)` is
invertible. -/
def IsNondegenerateZero (f : E → E) (Df : E → E →L[𝕜] E) (x : E) : Prop :=
  f x = 0 ∧ (Df x).IsInvertible

/-- In finite dimension, a bijective continuous linear map is invertible. -/
theorem isInvertible_of_bijective (A : E →L[𝕜] E) (hA : Function.Bijective A) : A.IsInvertible :=
  ⟨(LinearEquiv.ofBijective (A : E →ₗ[𝕜] E) hA).toContinuousLinearEquiv, by ext; rfl⟩

/-- In finite dimension, `‖I - A B‖ < 1` implies that `A` and `B` are invertible. -/
theorem isInvertible_of_norm_id_sub_comp_lt_one (A B : E →L[𝕜] E)
    (h : ‖ContinuousLinearMap.id 𝕜 E - A.comp B‖ < 1) : A.IsInvertible ∧ B.IsInvertible := by
  have hinj : Function.Injective (A.comp B) := injective_of_norm_id_sub_lt_one _ h
  have hsurj : Function.Surjective (A.comp B) :=
    (LinearMap.injective_iff_surjective (f := ((A.comp B : E →L[𝕜] E) : E →ₗ[𝕜] E))).1 hinj
  have hAs : Function.Surjective A := fun x =>
    let ⟨z, hz⟩ := hsurj x
    ⟨B z, hz⟩
  have hBi : Function.Injective B := fun x y hxy => hinj (by simp [hxy])
  exact ⟨isInvertible_of_bijective A
      ⟨(LinearMap.injective_iff_surjective (f := (A : E →ₗ[𝕜] E))).2 hAs, hAs⟩,
    isInvertible_of_bijective B
      ⟨hBi, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[𝕜] E))).1 hBi⟩⟩

end RadiiPolynomial
