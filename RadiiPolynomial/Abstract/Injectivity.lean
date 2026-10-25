module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Injectivity of the approximate inverse

The radii polynomial theorem needs the approximate inverse `A` to be injective. Two criteria:

* `injective_of_norm_id_sub_lt_one`: a bounded operator `M` with `‖I - M‖ < 1` is injective;
* `injective_of_decomposition`: if `A` and `A†` split into a finite part and a tail compatible with
  idempotent projections, the finite parts have equal finite dimension, the tail part of `A` is
  injective and `‖I - A A†‖ < 1`, then `A` is injective. This is the typical situation for
  operators on sequence spaces: a finite matrix block plus an injective diagonal tail.
-/

@[expose] public section

namespace RadiiPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- If `‖I - M‖ < 1`, then `M` is injective. -/
theorem injective_of_norm_id_sub_lt_one (M : V →L[𝕜] V)
    (h : ‖ContinuousLinearMap.id 𝕜 V - M‖ < 1) : Function.Injective M := by
  refine (injective_iff_map_eq_zero M).2 fun v hv => ?_
  by_contra hne
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hne
  have h1 : (ContinuousLinearMap.id 𝕜 V - M) v = v := by simp [hv]
  have h2 := (ContinuousLinearMap.id 𝕜 V - M).le_opNorm v
  rw [h1] at h2
  nlinarith

end

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Injectivity of `A` from a finite/tail decomposition.

The idempotent linear maps `πX`, `πY` (not assumed bounded) split `X` and `Y` into finite parts
`range πX`, `range πY` and tails `ker πX`, `ker πY`. The hypotheses `hA`, `hAdag` say that `A` and
`A†` map finite parts to finite parts and tails to tails, i.e. `A = A^F π_Y + A^∞ (1 - π_Y)` and
similarly for `A†`. The finite parts have the same finite dimension, the tail part of `A` is
injective (`htail`), and `‖I - A A†‖ < 1`. Then `A` is injective. -/
theorem injective_of_decomposition (A : Y →L[𝕜] X) (Adag : X →L[𝕜] Y)
    (πX : X →ₗ[𝕜] X) (πY : Y →ₗ[𝕜] Y) (hπX : IsIdempotentElem πX) (hπY : IsIdempotentElem πY)
    (hA : (A : Y →ₗ[𝕜] X) ∘ₗ πY = πX ∘ₗ (A : Y →ₗ[𝕜] X))
    (hAdag : (Adag : X →ₗ[𝕜] Y) ∘ₗ πX = πY ∘ₗ (Adag : X →ₗ[𝕜] Y))
    [FiniteDimensional 𝕜 (LinearMap.range πX)] [FiniteDimensional 𝕜 (LinearMap.range πY)]
    (hdim : Module.finrank 𝕜 (LinearMap.range πX) = Module.finrank 𝕜 (LinearMap.range πY))
    (htail : ∀ y, πY y = 0 → A y = 0 → y = 0)
    (hnorm : ‖ContinuousLinearMap.id 𝕜 X - A.comp Adag‖ < 1) :
    Function.Injective A := by
  have hAA : Function.Injective (A.comp Adag) := injective_of_norm_id_sub_lt_one _ hnorm
  -- `A` and `A†` commute with the projections, pointwise
  have hA' : ∀ y, A (πY y) = πX (A y) := fun y => LinearMap.congr_fun hA y
  have hAdag' : ∀ x, Adag (πX x) = πY (Adag x) := fun x => LinearMap.congr_fun hAdag x
  -- an idempotent fixes its range
  have fixY : ∀ y ∈ LinearMap.range πY, πY y = y := by
    rintro _ ⟨z, rfl⟩; exact LinearMap.congr_fun hπY.eq z
  have fixX : ∀ x ∈ LinearMap.range πX, πX x = x := by
    rintro _ ⟨z, rfl⟩; exact LinearMap.congr_fun hπX.eq z
  -- `A` maps the finite part of `Y` to the finite part of `X`, and `A†` conversely
  have hAmaps : ∀ y ∈ LinearMap.range πY, A y ∈ LinearMap.range πX := fun y hy =>
    ⟨A y, by rw [← hA', fixY y hy]⟩
  have hAdmaps : ∀ x ∈ LinearMap.range πX, Adag x ∈ LinearMap.range πY := fun x hx =>
    ⟨Adag x, by rw [← hAdag', fixX x hx]⟩
  -- the finite parts `A^F` and `A^{†,F}`
  let fA : LinearMap.range πY →ₗ[𝕜] LinearMap.range πX :=
    ((A : Y →ₗ[𝕜] X).domRestrict (LinearMap.range πY)).codRestrict (LinearMap.range πX)
      fun y => hAmaps y y.2
  let fD : LinearMap.range πX →ₗ[𝕜] LinearMap.range πY :=
    ((Adag : X →ₗ[𝕜] Y).domRestrict (LinearMap.range πX)).codRestrict (LinearMap.range πY)
      fun x => hAdmaps x x.2
  -- `A^F A^{†,F}` is injective, hence (finite dimension) surjective; so `A^F` is surjective,
  -- and therefore injective since the finite parts have equal dimension
  have hinj : Function.Injective (fA ∘ₗ fD) := by
    intro x x' hxx'
    exact Subtype.ext (hAA (congrArg Subtype.val hxx'))
  have hsurj : Function.Surjective (fA ∘ₗ fD) := LinearMap.injective_iff_surjective.1 hinj
  have hfAsurj : Function.Surjective fA := fun x =>
    let ⟨z, hz⟩ := hsurj x
    ⟨fD z, hz⟩
  have hfAinj : Function.Injective fA :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).2 hfAsurj
  -- conclusion: `A y = 0` forces `πY y = 0` (finite part) and then `y = 0` (tail)
  refine (injective_iff_map_eq_zero A).2 fun y hy => ?_
  have hπ : A (πY y) = 0 := by rw [hA', hy, map_zero]
  have hπ0 : πY y = 0 := by
    have h0 : fA ⟨πY y, LinearMap.mem_range_self πY y⟩ = 0 := Subtype.ext hπ
    exact congrArg Subtype.val (hfAinj (h0.trans (map_zero fA).symm))
  exact htail y hπ0 hy

end RadiiPolynomial
