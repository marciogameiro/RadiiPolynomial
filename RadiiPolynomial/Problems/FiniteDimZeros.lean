module

public import RadiiPolynomial.Abstract.RadiiPoly
public import RadiiPolynomial.Abstract.FiniteDim
public import RadiiPolynomial.Certificate.Exact
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Zeros of maps on finite-dimensional spaces

* `radii_poly_finiteDim`, `radii_poly_finiteDim_two_radii`: the radii polynomial theorem for a map
  `f : E → E` on a finite-dimensional space, with `A† = Df(x̄)` (so `Z₁ = 0`). The bounds give a
  nondegenerate zero of `f` near `x̄`, unique in the closed ball, and the invertibility of `A`
  (no injectivity hypothesis is needed: `Z₀ < 1` follows from `p(r₀) < 0`).
* `QuadraticSystem`: quadratic maps `f : ℝⁿ → ℝⁿ`,
  `f(x)ᵢ = cᵢ + ∑ⱼ Lᵢⱼ xⱼ + ∑ⱼ ∑ₖ Qᵢⱼₖ xⱼ xₖ`, with sup norm on `ℝⁿ`. Their derivative is the
  matrix `jac x`, and `A (Df(x) - Df(y))` is linear in `x - y` with coefficients `d2 A`, so the
  bound `Z₂` is a constant (valid for every radius). `QuadraticSystem.radii_poly_two_radii` states
  the theorem with entrywise real inequalities, and `QuadraticSystem.radii_poly_two_radii_of_rat`
  with exact rational data and rational inequalities, which are decided by the kernel.
-/

@[expose] public section

namespace RadiiPolynomial

open Metric Matrix

section General

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Radii polynomial theorem in finite dimension, with two radii `r₀ ≤ r₁`: if `p(r₀) < 0` and
`p(r₁) < 0` (with `Z₁ = 0`), then `A` is invertible and `f` has a nondegenerate zero in the open
ball of radius `r₀`, which is its unique zero in the closed ball of radius `r₁`. -/
theorem radii_poly_finiteDim_two_radii (f : E → E) (Df : E → E →L[𝕜] E) (A : E →L[𝕜] E)
    (xbar : E) {r₀ r₁ Y₀ Z₀ Z₂₀ Z₂₁ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hf : ∀ x ∈ closedBall xbar r₁, HasFDerivWithinAt f (Df x) (closedBall xbar r₁) x)
    (hY₀ : ‖A (f xbar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 E - A.comp (Df xbar)‖ ≤ Z₀)
    (hZ₂₀ : ∀ c ∈ closedBall xbar r₀, ‖A.comp (Df c - Df xbar)‖ ≤ Z₂₀ * r₀)
    (hZ₂₁ : ∀ c ∈ closedBall xbar r₁, ‖A.comp (Df c - Df xbar)‖ ≤ Z₂₁ * r₁)
    (hp₀ : radiiPoly Y₀ Z₀ 0 Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ 0 Z₂₁ r₁ < 0) :
    A.IsInvertible ∧ ∃ x ∈ ball xbar r₀, IsNondegenerateZero f Df x ∧
      ∀ y ∈ closedBall xbar r₁, f y = 0 → y = x := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  -- `p(r₀) < 0` with `Y₀ ≥ 0` and `Z₂₀ r₀ ≥ 0` forces `Z₀ < 1`, so `A` is invertible
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀
  have hZ₂nn : 0 ≤ Z₂₀ * r₀ := (norm_nonneg _).trans (hZ₂₀ xbar (mem_closedBall_self hr₀.le))
  have hZ₀1 : ‖ContinuousLinearMap.id 𝕜 E - A.comp (Df xbar)‖ < 1 := by
    simp only [radiiPoly] at hp₀
    have : Z₀ < 1 := by nlinarith [mul_nonneg hZ₂nn hr₀.le]
    linarith
  obtain ⟨hAinv, -⟩ := isInvertible_of_norm_id_sub_comp_lt_one A (Df xbar) hZ₀1
  have hAinj : Function.Injective A := by obtain ⟨e, rfl⟩ := hAinv; exact e.injective
  have hZ₁ : ‖A.comp (Df xbar - Df xbar)‖ ≤ 0 := by simp
  obtain ⟨x, hx, hfx, huniq, hDx⟩ := radii_poly_two_radii f Df A (Df xbar) xbar hAinj hr₀ hr₀₁
    hf hY₀ hZ₀ hZ₁ hZ₂₀ hZ₂₁ hp₀ hp₁
  -- `‖I - A Df(x̃)‖ < 1` makes `Df(x̃)` invertible
  exact ⟨hAinv, x, hx, ⟨hfx, (isInvertible_of_norm_id_sub_comp_lt_one A (Df x) hDx).2⟩, huniq⟩

/-- Radii polynomial theorem in finite dimension (single radius). -/
theorem radii_poly_finiteDim (f : E → E) (Df : E → E →L[𝕜] E) (A : E →L[𝕜] E) (xbar : E)
    {r₀ Y₀ Z₀ Z₂ : ℝ} (hr₀ : 0 < r₀)
    (hf : ∀ x ∈ closedBall xbar r₀, HasFDerivWithinAt f (Df x) (closedBall xbar r₀) x)
    (hY₀ : ‖A (f xbar)‖ ≤ Y₀)
    (hZ₀ : ‖ContinuousLinearMap.id 𝕜 E - A.comp (Df xbar)‖ ≤ Z₀)
    (hZ₂ : ∀ c ∈ closedBall xbar r₀, ‖A.comp (Df c - Df xbar)‖ ≤ Z₂ * r₀)
    (hp : radiiPoly Y₀ Z₀ 0 Z₂ r₀ < 0) :
    A.IsInvertible ∧ ∃ x ∈ ball xbar r₀, IsNondegenerateZero f Df x ∧
      ∀ y ∈ closedBall xbar r₀, f y = 0 → y = x :=
  radii_poly_finiteDim_two_radii f Df A xbar hr₀ le_rfl hf hY₀ hZ₀ hZ₂ hZ₂ hp hp

end General

/-- A quadratic map `f : Kⁿ → Kⁿ`, `f(x)ᵢ = cᵢ + ∑ⱼ Lᵢⱼ xⱼ + ∑ⱼ ∑ₖ Qᵢⱼₖ xⱼ xₖ`. -/
structure QuadraticSystem (K : Type*) (n : ℕ) where
  /-- constant term -/
  c : Fin n → K
  /-- linear term -/
  L : Matrix (Fin n) (Fin n) K
  /-- quadratic term -/
  Q : Fin n → Fin n → Fin n → K

namespace QuadraticSystem

variable {K : Type*} [CommRing K] {n : ℕ} (S : QuadraticSystem K n)

/-- The quadratic map `x ↦ f(x)`. -/
def eval (x : Fin n → K) : Fin n → K :=
  fun i => S.c i + ∑ j, S.L i j * x j + ∑ j, ∑ k, S.Q i j k * x j * x k

/-- The Jacobian matrix `Df(x)ᵢⱼ = Lᵢⱼ + ∑ₖ (Qᵢⱼₖ + Qᵢₖⱼ) xₖ`. -/
def jac (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => S.L i j + ∑ k, (S.Q i j k + S.Q i k j) * x k

/-- The second derivative contracted with a matrix `A`: `d2 A i j k = ∑ₗ Aᵢₗ (Qₗⱼₖ + Qₗₖⱼ)`. -/
def d2 (A : Matrix (Fin n) (Fin n) K) : Fin n → Fin n → Fin n → K :=
  fun i j k => ∑ l, A i l * (S.Q l j k + S.Q l k j)

/-- `A (Df(x) - Df(y))` is linear in `x - y`, with coefficients `d2 A`. -/
theorem mul_jac_sub_jac (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) (i j : Fin n) :
    (A * (S.jac x - S.jac y)) i j = ∑ k, S.d2 A i j k * (x k - y k) := by
  simp only [Matrix.mul_apply, Matrix.sub_apply, jac, d2, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The image of a quadratic system under a ring homomorphism of the coefficients. -/
def map {K' : Type*} [CommRing K'] (φ : K →+* K') : QuadraticSystem K' n :=
  ⟨fun i => φ (S.c i), S.L.map φ, fun i j k => φ (S.Q i j k)⟩

section map

variable {K' : Type*} [CommRing K'] (φ : K →+* K')

theorem map_eval (x : Fin n → K) :
    (S.map φ).eval (fun i => φ (x i)) = fun i => φ (S.eval x i) := by
  funext i; simp [eval, map, map_sum]

theorem map_jac (x : Fin n → K) : (S.map φ).jac (fun i => φ (x i)) = (S.jac x).map φ := by
  ext i j; simp [jac, map, map_sum]

theorem map_d2 (A : Matrix (Fin n) (Fin n) K) :
    (S.map φ).d2 (A.map φ) = fun i j k => φ (S.d2 A i j k) := by
  funext i j k; simp [d2, map, map_sum]

end map

section Real

variable (S : QuadraticSystem ℝ n)

theorem hasFDerivAt (x : Fin n → ℝ) : HasFDerivAt S.eval (matCLM (S.jac x)) x := by
  rw [hasFDerivAt_pi']
  intro i
  have hp : ∀ j, HasFDerivAt (fun y : Fin n → ℝ => y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x :=
    fun j => hasFDerivAt_apply j x
  have h := ((hasFDerivAt_const (S.c i) x).add
    (HasFDerivAt.sum (u := Finset.univ) fun j _ => (hp j).const_mul (S.L i j))).add
    (HasFDerivAt.sum (u := Finset.univ) fun j _ => HasFDerivAt.sum (u := Finset.univ) fun k _ =>
      ((hp j).const_mul (S.Q i j k)).mul (hp k))
  convert h using 1
  · funext y; simp [eval, Finset.sum_apply]
  ext v
  simp [jac, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `‖A (Df(x) - Df(y))‖ ≤ Z₂ ‖x - y‖` for any bound `Z₂` on the absolute sums `∑ⱼ ∑ₖ |d2 A i j k|`. -/
theorem norm_comp_jac_sub_le (A : Matrix (Fin n) (Fin n) ℝ) {Z₂ : ℝ} (hZ₂nn : 0 ≤ Z₂)
    (hZ₂ : ∀ i, ∑ j, ∑ k, |S.d2 A i j k| ≤ Z₂) (x y : Fin n → ℝ) :
    ‖(matCLM A).comp (matCLM (S.jac x) - matCLM (S.jac y))‖ ≤ Z₂ * ‖x - y‖ := by
  rw [← matCLM_sub, ← matCLM_mul]
  refine norm_matCLM_le _ (mul_nonneg hZ₂nn (norm_nonneg _)) fun i => ?_
  calc ∑ j, |(A * (S.jac x - S.jac y)) i j| = ∑ j, |∑ k, S.d2 A i j k * (x k - y k)| := by
        simp_rw [S.mul_jac_sub_jac]
    _ ≤ ∑ j, ∑ k, |S.d2 A i j k| * ‖x - y‖ :=
        Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) k) (abs_nonneg _))
    _ = (∑ j, ∑ k, |S.d2 A i j k|) * ‖x - y‖ := by simp [Finset.sum_mul]
    _ ≤ Z₂ * ‖x - y‖ := by gcongr; exact hZ₂ i

/-- Radii polynomial theorem for a quadratic system on `ℝⁿ` (sup norm) with two radii `r₀ ≤ r₁`,
from entrywise bounds: `|(A f(x̄))ᵢ| ≤ Y₀`, `∑ⱼ |(I - A Df(x̄))ᵢⱼ| ≤ Z₀` and
`∑ⱼ ∑ₖ |d2 A i j k| ≤ Z₂` for every row `i`. -/
theorem radii_poly_two_radii [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (xbar : Fin n → ℝ)
    {r₀ r₁ Y₀ Z₀ Z₂ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∀ i, |(A *ᵥ S.eval xbar) i| ≤ Y₀)
    (hZ₀ : ∀ i, ∑ j, |(1 - A * S.jac xbar) i j| ≤ Z₀)
    (hZ₂ : ∀ i, ∑ j, ∑ k, |S.d2 A i j k| ≤ Z₂)
    (hp₀ : radiiPoly Y₀ Z₀ 0 Z₂ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ 0 Z₂ r₁ < 0) :
    (matCLM A).IsInvertible ∧ ∃ x ∈ ball xbar r₀,
      IsNondegenerateZero S.eval (fun x => matCLM (S.jac x)) x ∧
      ∀ y ∈ closedBall xbar r₁, S.eval y = 0 → y = x := by
  have hY₀nn : 0 ≤ Y₀ := (abs_nonneg _).trans (hY₀ 0)
  have hZ₀nn : 0 ≤ Z₀ := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans (hZ₀ 0)
  have hZ₂nn : 0 ≤ Z₂ :=
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _).trans (hZ₂ 0)
  have hZ₂r : ∀ r, ∀ c ∈ closedBall xbar r,
      ‖(matCLM A).comp (matCLM (S.jac c) - matCLM (S.jac xbar))‖ ≤ Z₂ * r := fun r c hc =>
    (S.norm_comp_jac_sub_le A hZ₂nn hZ₂ c xbar).trans
      (by gcongr; rwa [mem_closedBall, dist_eq_norm] at hc)
  exact radii_poly_finiteDim_two_radii (𝕜 := ℝ) S.eval _ (matCLM A) xbar hr₀ hr₀₁
    (fun x _ => (S.hasFDerivAt x).hasFDerivWithinAt)
    (by rw [matCLM_apply]; exact norm_le_of_forall_abs_le _ hY₀nn hY₀)
    (by rw [← matCLM_mul, ← matCLM_one, ← matCLM_sub]; exact norm_matCLM_le _ hZ₀nn hZ₀)
    (hZ₂r r₀) (hZ₂r r₁) hp₀ hp₁

end Real

section Rat

/-- Radii polynomial theorem for a quadratic system with rational data, two radii `r₀ ≤ r₁`. All
hypotheses are inequalities between rational numbers, decidable by the kernel
(`decide +kernel`); the conclusion is about the real map. -/
theorem radii_poly_two_radii_of_rat [NeZero n] (S : QuadraticSystem ℚ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (xbar : Fin n → ℚ) {r₀ r₁ Y₀ Z₀ Z₂ : ℚ}
    (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∀ i, |(A *ᵥ S.eval xbar) i| ≤ Y₀)
    (hZ₀ : ∀ i, ∑ j, |(1 - A * S.jac xbar) i j| ≤ Z₀)
    (hZ₂ : ∀ i, ∑ j, ∑ k, |S.d2 A i j k| ≤ Z₂)
    (hp₀ : radiiPoly Y₀ Z₀ 0 Z₂ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ 0 Z₂ r₁ < 0) :
    ∃ x ∈ ball (castVec xbar) r₀,
      IsNondegenerateZero (S.map (Rat.castHom ℝ)).eval
        (fun x => matCLM ((S.map (Rat.castHom ℝ)).jac x)) x ∧
      ∀ y ∈ closedBall (castVec xbar) r₁, (S.map (Rat.castHom ℝ)).eval y = 0 → y = x := by
  let φ := Rat.castHom ℝ
  refine (radii_poly_two_radii (S.map φ) (A.map φ) (fun i => φ (xbar i))
    (Y₀ := Y₀) (Z₀ := Z₀) (Z₂ := Z₂) (by exact_mod_cast hr₀) (by exact_mod_cast hr₀₁)
    (fun i => ?_) (fun i => ?_) (fun i => ?_) (by simpa using (Rat.cast_lt (K := ℝ)).2 hp₀)
    (by simpa using (Rat.cast_lt (K := ℝ)).2 hp₁)).2
  · have h : (A.map φ *ᵥ (S.map φ).eval (fun i => φ (xbar i))) i = φ ((A *ᵥ S.eval xbar) i) := by
      rw [map_eval]; simp [φ, Matrix.mulVec, dotProduct, map_sum]
    rw [h]; simp only [φ, Rat.coe_castHom]; exact_mod_cast hY₀ i
  · have h : 1 - A.map φ * (S.map φ).jac (fun i => φ (xbar i)) = (1 - A * S.jac xbar).map φ := by
      rw [map_jac, ← Matrix.map_mul, Matrix.map_sub _ (map_sub φ), Matrix.map_one _ (map_zero φ) (map_one φ)]
    rw [h]; simp only [Matrix.map_apply, φ, Rat.coe_castHom]; exact_mod_cast hZ₀ i
  · rw [map_d2]; simp only [φ, Rat.coe_castHom]; exact_mod_cast hZ₂ i

variable {n : ℕ} (S : QuadraticSystem ℚ n) (A : Matrix (Fin n) (Fin n) ℚ) (xbar : Fin n → ℚ)

/-- The bound `Y₀ = ‖A f(x̄)‖ = maxᵢ |(A f(x̄))ᵢ|`, evaluated exactly. -/
def Y0 : ℚ := finMax fun i => |(A *ᵥ S.eval xbar) i|

/-- The bound `Z₀ = ‖I - A Df(x̄)‖ = maxᵢ ∑ⱼ |(I - A Df(x̄))ᵢⱼ|`, evaluated exactly. -/
def Z0 : ℚ := finMax fun i => ∑ j, |(1 - A * S.jac xbar) i j|

/-- The bound `Z₂ = maxᵢ ∑ⱼ ∑ₖ |d2 A i j k|`, evaluated exactly. -/
def Z2 : ℚ := finMax fun i => ∑ j, ∑ k, |S.d2 A i j k|

/-- Radii polynomial theorem for a quadratic system with rational data and exactly evaluated
bounds, two radii `r₀ ≤ r₁`. The hypotheses are decidable by the kernel (`decide +kernel`). -/
theorem radii_poly_two_radii_exact [NeZero n] {r₀ r₁ : ℚ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hp₀ : radiiPoly (S.Y0 A xbar) (S.Z0 A xbar) 0 (S.Z2 A) r₀ < 0)
    (hp₁ : radiiPoly (S.Y0 A xbar) (S.Z0 A xbar) 0 (S.Z2 A) r₁ < 0) :
    ∃ x ∈ ball (castVec xbar) r₀,
      IsNondegenerateZero (S.map (Rat.castHom ℝ)).eval
        (fun x => matCLM ((S.map (Rat.castHom ℝ)).jac x)) x ∧
      ∀ y ∈ closedBall (castVec xbar) r₁, (S.map (Rat.castHom ℝ)).eval y = 0 → y = x :=
  radii_poly_two_radii_of_rat S A xbar hr₀ hr₀₁ (le_finMax _) (le_finMax _) (le_finMax _) hp₀ hp₁

end Rat

end QuadraticSystem

end RadiiPolynomial
