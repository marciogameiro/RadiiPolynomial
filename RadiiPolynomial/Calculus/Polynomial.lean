module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Polynomial maps on Banach algebras

Let `X` be a commutative Banach algebra over `𝕜` (e.g. `ℓ¹_{ω,I}` with convolution) and `L` a
finite index set; `X^L = L → X` carries the max norm. A multivariate polynomial
`P = ∑_α c_α x^α ∈ 𝕜[x_j : j ∈ L]` defines the map `φ(a) = P(a) = ∑_α c_α a^α`, `X^L → X`
(`MvPolynomial.aeval a P`, with `a^α = ∏ⱼ aⱼ^{αⱼ}` computed in `X`).

* `hasFDerivAt_aeval`: `φ` is Fréchet differentiable, with
  `Dφ(a) h = ∑ⱼ (∂ⱼ P)(a) hⱼ` (`polyDeriv`), where `∂ⱼ P = ∑_α αⱼ c_α x^{α - εⱼ}` is the formal
  partial derivative (`MvPolynomial.pderiv j P`);
* `hasFDerivAt_aeval_pi`: the same for a vector of polynomials `Φ = (φ_l)_l : X^L → X^{L'}`,
  componentwise.

The proof is by induction on `P`: constants, sums, and products with a variable (product rule).

Degrees: `deg ∂ᵢP ≤ M - 1` if `deg P ≤ M` (`totalDegree_pderiv_le`).

Norm bounds: with `|P|(x) = ∑_d |c_d| ∏ᵢ xᵢ^{dᵢ}` (`absEval`), `‖P(a)‖ ≤ |P|(‖a₁‖, …, ‖a_L‖)`
when `‖1‖ = 1` (`norm_aeval_le`), and `|P|` is nondecreasing on `[0, ∞)^L` (`absEval_mono`).
`‖DP(a)‖ ≤ ∑ⱼ ‖∂ⱼP(a)‖` (`norm_polyDeriv_le`), and for `𝕜 = ℝ` or `ℂ` and `c` in the closed
ball of radius `r` about `a`, by the mean value inequality,
`‖P(c) - P(a)‖ ≤ (∑ₗ |∂ₗP|(‖a‖ + r)) r` (`norm_aeval_sub_le`) and
`‖DP(c) - DP(a)‖ ≤ (∑ₗ ∑ₘ |∂ₗ∂ₘP|(‖a‖ + r)) r` (`norm_polyDeriv_sub_le`). A vector of polynomials
is Lipschitz on every closed ball about `0` (`lipschitzOnWith_aeval_pi`).
-/

@[expose] public section

namespace RadiiPolynomial

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [NormedCommRing X]
  [NormedAlgebra 𝕜 X] {L : Type*} [Fintype L] [DecidableEq L]

/-- The derivative of `a ↦ P(a)` at `a`: `h ↦ ∑ⱼ (∂ⱼ P)(a) hⱼ`. -/
noncomputable def polyDeriv (P : MvPolynomial L 𝕜) (a : L → X) : (L → X) →L[𝕜] X :=
  ∑ j, (ContinuousLinearMap.mul 𝕜 X (aeval a (pderiv j P))).comp (ContinuousLinearMap.proj j)

omit [DecidableEq L] in
theorem polyDeriv_apply (P : MvPolynomial L 𝕜) (a h : L → X) :
    polyDeriv P a h = ∑ j, aeval a (pderiv j P) * h j := by
  simp [polyDeriv]

/-- `a ↦ P(a)` is Fréchet differentiable on `X^L`, with derivative `h ↦ ∑ⱼ (∂ⱼ P)(a) hⱼ`. -/
theorem hasFDerivAt_aeval (P : MvPolynomial L 𝕜) (a : L → X) :
    HasFDerivAt (fun x : L → X => aeval x P) (polyDeriv P a) a := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have : polyDeriv (C c) a = 0 := by
      ext h; simp [polyDeriv_apply]
    simpa [this] using hasFDerivAt_const (algebraMap 𝕜 X c) a
  | add p q hp hq =>
    have : polyDeriv (p + q) a = polyDeriv p a + polyDeriv q a := by
      ext h; simp [polyDeriv_apply, add_mul, Finset.sum_add_distrib]
    rw [this]
    convert hp.add hq using 1
    funext x
    simp
  | mul_X p i hp =>
    have hXi : HasFDerivAt (fun x : L → X => x i) (ContinuousLinearMap.proj i) a :=
      hasFDerivAt_apply (𝕜 := 𝕜) i a
    have := hp.mul hXi
    convert this using 1
    · funext x; simp
    · ext h
      simp only [polyDeriv_apply, pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_mul,
        Finset.sum_add_distrib, add_apply, smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
          (by simp)]
        simp
      · exact Finset.sum_congr rfl fun j _ => by ring

/-- A vector of polynomials `Φ = (P_l)_l`, `X^L → X^{L'}`, is Fréchet differentiable, with
`(DΦ(a) h)_l = ∑ⱼ (∂ⱼ P_l)(a) hⱼ`. -/
theorem hasFDerivAt_aeval_pi {L' : Type*} [Fintype L'] (P : L' → MvPolynomial L 𝕜) (a : L → X) :
    HasFDerivAt (fun x : L → X => fun l => aeval x (P l))
      (ContinuousLinearMap.pi fun l => polyDeriv (P l) a) a :=
  hasFDerivAt_pi.2 fun l => hasFDerivAt_aeval (P l) a

/-! ### Degrees -/

omit [DecidableEq L] in
/-- `deg ∂ᵢP ≤ M - 1` if `deg P ≤ M`. -/
theorem totalDegree_pderiv_le (P : MvPolynomial L 𝕜) (i : L) {M : ℕ} (hP : P.totalDegree ≤ M) :
    (pderiv i P).totalDegree ≤ M - 1 := by
  classical
  rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases hi : s i = 0
  · rw [hi, Nat.cast_zero, mul_zero, monomial_zero, totalDegree_zero]
    exact Nat.zero_le _
  · refine (totalDegree_monomial_le _ _).trans ?_
    have hs' : (s.sum fun _ => id) ≤ M := (le_totalDegree hs).trans hP
    have key : ((s - Finsupp.single i 1).sum fun _ => id) + 1 = s.sum fun _ => id := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl)]
      have h1 : ∑ j, (Finsupp.single i 1 : L →₀ ℕ) j = 1 := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
          (by simp)]
        simp
      have h2 : ∑ j, ((s - Finsupp.single i 1 : L →₀ ℕ) j + (Finsupp.single i 1 : L →₀ ℕ) j) = ∑ j, s j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finsupp.tsub_apply]
        refine Nat.sub_add_cancel ?_
        rw [Finsupp.single_apply]
        split_ifs with h
        · subst h; exact Nat.one_le_iff_ne_zero.2 hi
        · exact Nat.zero_le _
      rw [Finset.sum_add_distrib, h1] at h2
      simpa using h2
    omega

/-! ### Norm bounds -/

/-- `|P|(x) = ∑_d |c_d| ∏ᵢ xᵢ^{dᵢ}`: the polynomial with the absolute values of the coefficients
of `P`, evaluated at `x`. -/
noncomputable def absEval (P : MvPolynomial L 𝕜) (x : L → ℝ) : ℝ :=
  ∑ d ∈ P.support, ‖P.coeff d‖ * ∏ i, x i ^ d i

omit [DecidableEq L] in
theorem absEval_nonneg (P : MvPolynomial L 𝕜) {x : L → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ absEval P x :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

omit [DecidableEq L] in
/-- `|P|` is nondecreasing on `[0, ∞)^L`. -/
theorem absEval_mono (P : MvPolynomial L 𝕜) {x y : L → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxy : ∀ i, x i ≤ y i) : absEval P x ≤ absEval P y :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hx i) _)
      fun i _ => pow_le_pow_left₀ (hx i) (hxy i) _) (norm_nonneg _)

omit [DecidableEq L] in
/-- `‖P(a)‖ ≤ |P|(‖a₁‖, …, ‖a_L‖)`. -/
theorem norm_aeval_le [NormOneClass X] (P : MvPolynomial L 𝕜) (a : L → X) :
    ‖aeval a P‖ ≤ absEval P fun i => ‖a i‖ := by
  rw [aeval_def, eval₂_eq', absEval]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  refine (norm_mul_le _ _).trans ?_
  rw [norm_algebraMap']
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => norm_pow_le _ _)

omit [DecidableEq L] in
/-- `‖DP(a)‖ ≤ ∑ⱼ ‖∂ⱼP(a)‖`. -/
theorem norm_polyDeriv_le (P : MvPolynomial L 𝕜) (a : L → X) :
    ‖polyDeriv P a‖ ≤ ∑ j, ‖aeval a (pderiv j P)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun j _ => norm_nonneg _) fun h => ?_
  rw [polyDeriv_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm h j) (norm_nonneg _))

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedCommRing X] [NormedAlgebra 𝕜 X]
  [NormOneClass X] {L : Type*} [Fintype L]

omit [NormedAlgebra 𝕜 X] [NormOneClass X] in
/-- On the closed ball of radius `r` about `a`: `‖ξ_k‖ ≤ ‖a_k‖ + r`. -/
theorem norm_apply_le_of_mem_closedBall {a ξ : L → X} {r : ℝ} (hξ : ξ ∈ Metric.closedBall a r)
    (k : L) : ‖ξ k‖ ≤ ‖a k‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hξ
  calc ‖ξ k‖ = ‖a k + (ξ - a) k‖ := by simp
    _ ≤ ‖a k‖ + ‖(ξ - a) k‖ := norm_add_le _ _
    _ ≤ ‖a k‖ + r := by gcongr; exact (norm_le_pi_norm _ k).trans hξ

/-- Mean value inequality: `‖P(c) - P(a)‖ ≤ (∑ₗ |∂ₗP|(‖a‖ + r)) r` for `‖c - a‖ ≤ r`. -/
theorem norm_aeval_sub_le [DecidableEq L] (Q : MvPolynomial L 𝕜) {a c : L → X} {r : ℝ}
    (hc : c ∈ Metric.closedBall a r) :
    ‖aeval c Q - aeval a Q‖ ≤ (∑ l, absEval (pderiv l Q) fun k => ‖a k‖ + r) * r := by
  have hr : 0 ≤ r := le_trans dist_nonneg hc
  have hC : 0 ≤ ∑ l, absEval (pderiv l Q) fun k => ‖a k‖ + r :=
    Finset.sum_nonneg fun l _ => absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr
  let _ : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have h := (convex_closedBall a r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x : L → X => aeval x Q) (f' := fun x => polyDeriv Q x)
    (fun x _ => (hasFDerivAt_aeval Q x).hasFDerivWithinAt)
    (fun ξ hξ => (norm_polyDeriv_le Q ξ).trans (Finset.sum_le_sum fun l _ =>
      (norm_aeval_le _ ξ).trans (absEval_mono _ (fun k => norm_nonneg _)
        (norm_apply_le_of_mem_closedBall hξ))))
    (Metric.mem_closedBall_self hr) hc
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
  rwa [Metric.mem_closedBall, dist_eq_norm] at hc

/-- `‖DP(c) - DP(a)‖ ≤ (∑ₗ ∑ₘ |∂ₗ∂ₘP|(‖a‖ + r)) r` for `‖c - a‖ ≤ r`. -/
theorem norm_polyDeriv_sub_le [DecidableEq L] (P : MvPolynomial L 𝕜) {a c : L → X} {r : ℝ}
    (hc : c ∈ Metric.closedBall a r) :
    ‖polyDeriv P c - polyDeriv P a‖ ≤
      (∑ l, ∑ m, absEval (pderiv l (pderiv m P)) fun k => ‖a k‖ + r) * r := by
  have hr : 0 ≤ r := le_trans dist_nonneg hc
  have hB : ∀ m, 0 ≤ ∑ l, absEval (pderiv l (pderiv m P)) fun k => ‖a k‖ + r := fun m =>
    Finset.sum_nonneg fun l _ => absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr
  rw [Finset.sum_comm, Finset.sum_mul]
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun m _ => mul_nonneg (hB m) hr) fun h => ?_
  rw [sub_apply, polyDeriv_apply, polyDeriv_apply, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [← sub_mul]
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul (norm_aeval_sub_le _ hc) (norm_le_pi_norm h m) (norm_nonneg _)
    (mul_nonneg (hB m) hr)

/-- A vector of polynomials `x ↦ (P_l(x))_l` is Lipschitz on every closed ball about `0`. -/
theorem lipschitzOnWith_aeval_pi [DecidableEq L] {L' : Type*} [Fintype L']
    (P : L' → MvPolynomial L 𝕜) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun x : L → X => fun l => aeval x (P l)) (Metric.closedBall 0 R) := by
  let _ : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  set C : ℝ := ∑ l, ∑ j, absEval (pderiv j (P l)) (fun _ => max R 0) with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun j _ =>
    absEval_nonneg _ fun _ => le_max_right _ _
  refine ⟨⟨C, hC0⟩, (convex_closedBall (0 : L → X) R).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := fun x => ContinuousLinearMap.pi fun l => polyDeriv (P l) x)
    (fun x _ => (hasFDerivAt_aeval_pi P x).hasFDerivWithinAt) fun x hx => ?_⟩
  apply NNReal.coe_le_coe.1
  simp only [coe_nnnorm]
  have hxR : ∀ i, ‖x i‖ ≤ max R 0 := fun i =>
    (norm_le_pi_norm x i).trans ((mem_closedBall_zero_iff.1 hx).trans (le_max_left _ _))
  refine ContinuousLinearMap.norm_pi_le_of_le (fun l => ?_) hC0
  refine (norm_polyDeriv_le _ _).trans ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun l => ∑ j, absEval (pderiv j (P l))
    (fun _ => max R 0)) (fun l _ => Finset.sum_nonneg fun j _ =>
      absEval_nonneg _ fun _ => le_max_right _ _) (Finset.mem_univ l))
  exact Finset.sum_le_sum fun j _ => (norm_aeval_le _ x).trans
    (absEval_mono _ (fun i => norm_nonneg _) hxR)

end RCLike

/-- A real polynomial vector field `z ↦ (f_l(z))_l` is Lipschitz on every closed ball about `0`. -/
theorem lipschitzOnWith_eval_pi {L L' : Type*} [Fintype L] [DecidableEq L] [Fintype L']
    (f : L' → MvPolynomial L ℝ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun z : L → ℝ => fun l => eval z (f l)) (Metric.closedBall 0 R) := by
  obtain ⟨K, hK⟩ := lipschitzOnWith_aeval_pi (X := ℝ) f R
  have hae : (fun z : L → ℝ => fun l => aeval z (f l)) = fun z => fun l => eval z (f l) := by
    funext z l
    simp only [aeval_def, Algebra.algebraMap_self, eval]
    rfl
  exact ⟨K, hae ▸ hK⟩

end RadiiPolynomial
