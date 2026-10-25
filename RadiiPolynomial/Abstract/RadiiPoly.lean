module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The radii polynomial theorem

Let `X` be a Banach space and `Y` a normed space over `𝕜 ∈ {ℝ, ℂ}`, `F : X → Y`, `x̄ ∈ X` an
approximate zero, `A† : X → Y` an approximate derivative and `A : Y → X` an injective approximate
inverse. At a radius `r₀ > 0` the bounds are

* `‖A F(x̄)‖ ≤ Y₀`,
* `‖I - A A†‖ ≤ Z₀`,
* `‖A [DF(x̄) - A†]‖ ≤ Z₁`,
* `‖A [DF(c) - DF(x̄)]‖ ≤ Z₂ r₀` for all `c` in the closed ball of radius `r₀` about `x̄`,

and the radii polynomial is `p(r) = Z₂ r² - (1 - Z₀ - Z₁) r + Y₀` (`radiiPoly`). If `p(r₀) < 0`,
then `F` has a unique zero in the closed ball (`radii_poly`); with two radii `r₀ ≤ r₁` one obtains
a zero in the small ball that is unique in the large ball (`radii_poly_two_radii`; for maps
whose derivative need not be recorded, this conclusion is `HasIsolatedZero F xbar r₀ r₁`).

In applications `Z₂` usually comes from a function `Z₂(r)` valid for `0 < r ≤ r_*`; the theorems are
then applied with `Z₂ = Z₂(r₀)` (and `Z₂(r₁)`).

The derivative of `F` is only required within the closed ball, which covers maps that are
differentiable on all of `X`.
-/

@[expose] public section

namespace RadiiPolynomial

open Metric

/-- The radii polynomial `Z₂ r² - (1 - Z₀ - Z₁) r + Y₀`. It is defined over any commutative ring so
that it can be evaluated exactly (e.g. over `ℚ`) and then cast to `ℝ` (`Rat.cast_radiiPoly`). -/
def radiiPoly {R : Type*} [CommRing R] (Y₀ Z₀ Z₁ Z₂ r : R) : R := Z₂ * r ^ 2 - (1 - Z₀ - Z₁) * r + Y₀

/-- `F` has a zero in the open ball of radius `r₀` about `xbar`, and it is the only zero of `F` in the
closed ball of radius `r₁` about `xbar`. -/
def HasIsolatedZero {X Y : Type*} [PseudoMetricSpace X] [Zero Y] (F : X → Y) (xbar : X)
    (r₀ r₁ : ℝ) : Prop :=
  ∃ x ∈ ball xbar r₀, F x = 0 ∧ ∀ y ∈ closedBall xbar r₁, F y = 0 → y = x

/-- If `A` is injective, then `x` is a fixed point of `T(x) = x - A f(x)` if and only if
`f(x) = 0`. -/
theorem sub_apply_eq_self_iff {R X Y : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (A : Y →ₗ[R] X) (hA : Function.Injective A) (f : X → Y)
    (x : X) : x - A (f x) = x ↔ f x = 0 := by
  rw [sub_eq_self]
  exact A.map_eq_zero_iff hA

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Radii polynomial theorem.**

Under the four bounds at the radius `r₀ > 0` and `p(r₀) < 0`, the map `F` has a unique zero `x̃` in
the closed ball of radius `r₀` about `x̄`; moreover `x̃` lies in the open ball and
`‖I - A DF(x̃)‖ < 1`. -/
theorem radii_poly (F : X → Y) (DF : X → X →L[𝕜] Y) (A : Y →L[𝕜] X) (Adag : X →L[𝕜] Y)
    (xbar : X) {r₀ Y₀ Z₀ Z₁ Z₂ : ℝ} (hA : Function.Injective A) (hr₀ : 0 < r₀)
    (hF : ∀ x ∈ closedBall xbar r₀, HasFDerivWithinAt F (DF x) (closedBall xbar r₀) x)
    (hY₀ : ‖A (F xbar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 X - A.comp Adag‖ ≤ Z₀)
    (hZ₁ : ‖A.comp (DF xbar - Adag)‖ ≤ Z₁)
    (hZ₂ : ∀ c ∈ closedBall xbar r₀, ‖A.comp (DF c - DF xbar)‖ ≤ Z₂ * r₀)
    (hp : radiiPoly Y₀ Z₀ Z₁ Z₂ r₀ < 0) :
    ∃ x ∈ ball xbar r₀, F x = 0 ∧ (∀ y ∈ closedBall xbar r₀, F y = 0 → y = x) ∧
      ‖ContinuousLinearMap.id 𝕜 X - A.comp (DF x)‖ < 1 := by
  let _ : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  set K := closedBall xbar r₀ with hK
  -- the Newton-like operator `T(x) = x - A F(x)` and its derivative `I - A DF(x)`
  set T : X → X := fun x => x - A (F x) with hT
  set κ : ℝ := Z₀ + Z₁ + Z₂ * r₀ with hκ
  have hDT : ∀ x ∈ K, HasFDerivWithinAt T (ContinuousLinearMap.id 𝕜 X - A.comp (DF x)) K x :=
    fun x hx => (hasFDerivWithinAt_id x K).sub (A.hasFDerivAt.comp_hasFDerivWithinAt x (hF x hx))
  -- `‖I - A DF(c)‖ ≤ κ` on the closed ball
  have hbound : ∀ c ∈ K, ‖ContinuousLinearMap.id 𝕜 X - A.comp (DF c)‖ ≤ κ := by
    intro c hc
    have hsplit : ContinuousLinearMap.id 𝕜 X - A.comp (DF c) =
        (ContinuousLinearMap.id 𝕜 X - A.comp Adag) - A.comp (DF xbar - Adag) -
          A.comp (DF c - DF xbar) := by
      simp only [ContinuousLinearMap.comp_sub]; abel
    rw [hsplit]
    calc _ ≤ ‖ContinuousLinearMap.id 𝕜 X - A.comp Adag - A.comp (DF xbar - Adag)‖ +
          ‖A.comp (DF c - DF xbar)‖ := norm_sub_le _ _
      _ ≤ ‖ContinuousLinearMap.id 𝕜 X - A.comp Adag‖ + ‖A.comp (DF xbar - Adag)‖ +
          ‖A.comp (DF c - DF xbar)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ κ := by have := hZ₂ c hc; linarith
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
  have hκnn : 0 ≤ κ := (norm_nonneg _).trans (hbound xbar (mem_closedBall_self hr₀.le))
  -- `p(r₀) < 0` means `κ r₀ - r₀ + Y₀ < 0`, hence `κ < 1`
  have hp' : κ * r₀ - r₀ + Y₀ < 0 := by
    simp only [radiiPoly] at hp; rw [hκ]; nlinarith
  have hκ1 : κ < 1 := by
    by_contra h; nlinarith [not_lt.mp h]
  -- `T` is `κ`-Lipschitz on the closed ball (mean value inequality)
  have hLip : ∀ x ∈ K, ∀ y ∈ K, ‖T x - T y‖ ≤ κ * ‖x - y‖ := fun x hx y hy =>
    (convex_closedBall xbar r₀).norm_image_sub_le_of_norm_hasFDerivWithin_le hDT hbound hy hx
  -- `T` maps the closed ball into the open ball
  have hmaps : ∀ x ∈ K, T x ∈ ball xbar r₀ := by
    intro x hx
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖T x - T xbar‖ ≤ κ * r₀ := by
      calc _ ≤ κ * ‖x - xbar‖ := hLip x hx xbar (mem_closedBall_self hr₀.le)
        _ ≤ κ * r₀ := by gcongr; rwa [← dist_eq_norm, ← mem_closedBall]
    have h2 : ‖T xbar - xbar‖ ≤ Y₀ := by simpa [hT] using hY₀
    calc ‖T x - xbar‖ = ‖(T x - T xbar) + (T xbar - xbar)‖ := by congr 1; abel
      _ ≤ ‖T x - T xbar‖ + ‖T xbar - xbar‖ := norm_add_le _ _
      _ < r₀ := by linarith
  -- contraction on the complete metric space `K`
  have : CompleteSpace K := completeSpace_coe_iff_isComplete.mpr isClosed_closedBall.isComplete
  have : Nonempty K := ⟨⟨xbar, mem_closedBall_self hr₀.le⟩⟩
  let TK : K → K := fun x => ⟨T x, ball_subset_closedBall (hmaps x x.2)⟩
  have hcontr : ContractingWith ⟨κ, hκnn⟩ TK := by
    refine ⟨by exact_mod_cast hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, TK]
    exact hLip x x.2 y y.2
  set xt := ContractingWith.fixedPoint TK hcontr with hxt
  have hfix : T xt = xt := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hcontr)
  have hzero : ∀ y, T y = y ↔ F y = 0 := fun y =>
    sub_apply_eq_self_iff (A : Y →ₗ[𝕜] X) hA F y
  refine ⟨xt, hfix ▸ hmaps xt xt.2, (hzero xt).1 hfix, fun y hy hFy => ?_,
    lt_of_le_of_lt (hbound xt xt.2) hκ1⟩
  have hyfix : Function.IsFixedPt TK ⟨y, hy⟩ := Subtype.ext ((hzero y).2 hFy)
  exact congrArg Subtype.val (ContractingWith.fixedPoint_unique hcontr hyfix)

/-- **Radii polynomial theorem with two radii.**

If the hypotheses of `radii_poly` hold at `r₀` (with `Z₂ = Z₂₀`) and at `r₁ ≥ r₀` (with `Z₂ = Z₂₁`),
then `F` has a zero in the open ball of radius `r₀`, it is the unique zero in the closed ball of
radius `r₁`, and `‖I - A DF(x̃)‖ < 1`. -/
theorem radii_poly_two_radii (F : X → Y) (DF : X → X →L[𝕜] Y) (A : Y →L[𝕜] X)
    (Adag : X →L[𝕜] Y) (xbar : X) {r₀ r₁ Y₀ Z₀ Z₁ Z₂₀ Z₂₁ : ℝ}
    (hA : Function.Injective A) (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hF : ∀ x ∈ closedBall xbar r₁, HasFDerivWithinAt F (DF x) (closedBall xbar r₁) x)
    (hY₀ : ‖A (F xbar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 X - A.comp Adag‖ ≤ Z₀)
    (hZ₁ : ‖A.comp (DF xbar - Adag)‖ ≤ Z₁)
    (hZ₂₀ : ∀ c ∈ closedBall xbar r₀, ‖A.comp (DF c - DF xbar)‖ ≤ Z₂₀ * r₀)
    (hZ₂₁ : ∀ c ∈ closedBall xbar r₁, ‖A.comp (DF c - DF xbar)‖ ≤ Z₂₁ * r₁)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂₁ r₁ < 0) :
    ∃ x ∈ ball xbar r₀, F x = 0 ∧ (∀ y ∈ closedBall xbar r₁, F y = 0 → y = x) ∧
      ‖ContinuousLinearMap.id 𝕜 X - A.comp (DF x)‖ < 1 := by
  have hsub : closedBall xbar r₀ ⊆ closedBall xbar r₁ := closedBall_subset_closedBall hr₀₁
  obtain ⟨x₀, hx₀, hFx₀, -, hnorm₀⟩ := radii_poly F DF A Adag xbar hA hr₀
    (fun x hx => (hF x (hsub hx)).mono hsub) hY₀ hZ₀ hZ₁ hZ₂₀ hp₀
  obtain ⟨x₁, -, -, huniq₁, -⟩ := radii_poly F DF A Adag xbar hA (hr₀.trans_le hr₀₁)
    hF hY₀ hZ₀ hZ₁ hZ₂₁ hp₁
  have hx₀₁ : x₀ = x₁ := huniq₁ x₀ (hsub (ball_subset_closedBall hx₀)) hFx₀
  exact ⟨x₀, hx₀, hFx₀, fun y hy hFy => (huniq₁ y hy hFy).trans hx₀₁.symm, hnorm₀⟩

end RadiiPolynomial
