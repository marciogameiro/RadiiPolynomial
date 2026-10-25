module

public import RadiiPolynomial.Problems.ChebyshevBVP
public import RadiiPolynomial.Convolution.ChebyshevSeries
public import RadiiPolynomial.Calculus.ODE
public import RadiiPolynomial.Abstract.RadiiPoly
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Solutions of boundary value problems from zeros of Chebyshev problems

Let `a = (a_1, …, a_n) ∈ X_ν^n` be a zero of the map `F` of a boundary value problem
`u' = L f(u)`, `B₋ u(-1) + B₊ u(1) = q` (`ChebBVP`), and `u_j(t) = (a_j)_0 + 2 ∑_{k ≥ 1} (a_j)_k T_k(t)`
(`Chebyshev.chebSeries`). The rows `k ≥ 1` of `F_j(a) = 0` read
`2k (a_j)_k = L ((c_j)_{k-1} - (c_j)_{k+1})` with `c_j = f_j(a)` (Chebyshev product), whose Chebyshev
series is `f_j(u(t))`. Hence `u' = L f(u)` on `[-1, 1]` (one-sided derivatives at the endpoints), and
the rows `k = 0` are the boundary conditions (`solves_of_F_eq_zero`). `exists_solution` collects these
facts for an isolated zero of `F` near `ā`, with `|u_j(t) - ū_j(t)| < r₀` on `[-1, 1]`.

Initial value problems (`ivp`, `B₋ = I`, `B₊ = 0`, `q = x₀`): for `L > 0`, `x(τ) = u(τ/L - 1)` solves
`x' = f(x)`, `x(0) = x₀` on `[0, 2L]`, and every solution on `[0, 2L]` coincides with it, since the
polynomial field is Lipschitz on bounded sets (`exists_ivp_solution`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace ChebBVP

open Chebyshev Set Metric MvPolynomial
open scoped Matrix

variable {n : ℕ} (P : ChebBVP n) {ν : ℝ} {hν : 1 ≤ ν}

theorem boundaryEval_eq (s : ℝ) (hs : |s| ≤ 1) (a : X ν hν) :
    boundaryEval ν hν s hs a = a 0 + 2 * ∑' k : ℕ, s ^ (k + 1) * a (k + 1) := by
  rw [boundaryEval_apply,
    (WeightedL1.summable_mul a (norm_evalWeight_le hs)).of_norm.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [evalWeight, ↓reduceIte, one_mul, Nat.add_one_ne_zero]
  congr 1
  exact tsum_congr fun k => by ring

theorem evalMinus_eq (a : X ν hν) : evalMinus ν hν a = chebSeries a (-1) := by
  rw [chebSeries_neg_one, boundaryEval_eq]

theorem evalPlus_eq (a : X ν hν) : evalPlus ν hν a = chebSeries a 1 := by
  rw [chebSeries_one, boundaryEval_eq]
  simp

/-- A zero of `F` solves the boundary value problem: `u' = L f(u)` on `[-1, 1]` and
`B₋ u(-1) + B₊ u(1) = q`, where `u_j(t) = (a_j)_0 + 2 ∑_{k ≥ 1} (a_j)_k T_k(t)`. -/
theorem solves_of_F_eq_zero {a : Fin n → X ν hν} (hF : P.F ν hν a = 0) :
    (∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt (fun s j => chebSeries (a j) s)
      (fun j => P.L * eval (fun i => chebSeries (a i) t) (P.f j)) (Icc (-1) 1) t) ∧
    P.Bm *ᵥ (fun i => chebSeries (a i) (-1)) + P.Bp *ᵥ (fun i => chebSeries (a i) 1) = P.q := by
  refine ⟨fun t ht => hasDerivWithinAt_pi.2 fun j => ?_, ?_⟩
  · have hrel : ∀ k : ℕ, k ≠ 0 →
        2 * k * a j k = P.L * ((aeval a (P.f j)) (k - 1) - (aeval a (P.f j)) (k + 1)) :=
      fun k hk => by
        have h := congrArg (fun y : Fin n → Y ν hν => y j k) hF
        simp only [P.F_apply_of_ne_zero ν hν a j hk, Pi.zero_apply, WeightedLp.zero_apply] at h
        linarith
    have h := hasDerivWithinAt_chebSeries (summable_abs (aeval a (P.f j))) hrel ht
    rwa [chebSeries_aeval a (P.f j) ht] at h
  · funext j
    have h := congrArg (fun y : Fin n → Y ν hν => y j 0) hF
    simp only [F_apply_zero, Pi.zero_apply, WeightedLp.zero_apply, sub_eq_zero] at h
    rw [h]
    simp [bcLin, Matrix.mulVec, dotProduct, evalMinus_eq, evalPlus_eq, Finset.sum_add_distrib]

/-- An isolated zero of `F` near `ā` gives a solution `u` of `u' = L f(u)` on `[-1, 1]`,
`B₋ u(-1) + B₊ u(1) = q`, within `r₀` of the Chebyshev series of `ā`; its Chebyshev coefficients form
the unique zero of `F` within `r₁` of `ā`. -/
theorem exists_solution {abar : Fin n → X ν hν} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) :
    ∃ a : Fin n → X ν hν, P.F ν hν a = 0 ∧ (∀ b ∈ closedBall abar r₁, P.F ν hν b = 0 → b = a) ∧
      ∃ u : ℝ → Fin n → ℝ, (∀ t ∈ Icc (-1 : ℝ) 1, ∀ j, u t j = chebSeries (a j) t) ∧
        (∀ t ∈ Icc (-1 : ℝ) 1,
          HasDerivWithinAt u (fun j => P.L * eval (u t) (P.f j)) (Icc (-1) 1) t) ∧
        P.Bm *ᵥ u (-1) + P.Bp *ᵥ u 1 = P.q ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, ∀ j, |u t j - chebSeries (abar j) t| < r₀ := by
  obtain ⟨a, ha, hFa, huniq⟩ := h
  obtain ⟨hd, hbc⟩ := P.solves_of_F_eq_zero hFa
  refine ⟨a, hFa, huniq, fun t j => chebSeries (a j) t, fun _ _ _ => rfl, hd, hbc,
    fun t ht j => ?_⟩
  rw [← chebSeries_sub_X _ _ ht]
  rw [mem_ball, dist_eq_norm] at ha
  exact (abs_chebSeries_le_norm _ ht).trans_lt ((norm_le_pi_norm (a - abar) j).trans_lt ha)

/-- The IVP `x' = f(x)`, `x(0) = x₀` on `[0, 2L]` (`L > 0`): an isolated zero of the IVP-operator
near `ā` gives the solution `x(τ) = u(τ/L - 1)`, within `r₀` of `ū(τ/L - 1)`, and every solution on
`[0, 2L]` coincides with it. -/
theorem exists_ivp_solution {f : Fin n → MvPolynomial (Fin n) ℝ} {L : ℝ} {x₀ : Fin n → ℝ}
    (hL : 0 < L) {abar : Fin n → X ν hν} {r₀ r₁ : ℝ}
    (h : HasIsolatedZero ((ivp f L x₀).F ν hν) abar r₀ r₁) :
    ∃ a : Fin n → X ν hν, (ivp f L x₀).F ν hν a = 0 ∧
      (∀ b ∈ closedBall abar r₁, (ivp f L x₀).F ν hν b = 0 → b = a) ∧
      ∃ x : ℝ → Fin n → ℝ, x 0 = x₀ ∧
        (∀ τ ∈ Icc 0 (2 * L), ∀ j, x τ j = chebSeries (a j) (τ / L - 1)) ∧
        (∀ τ ∈ Icc 0 (2 * L), HasDerivWithinAt x (fun j => eval (x τ) (f j)) (Icc 0 (2 * L)) τ) ∧
        (∀ τ ∈ Icc 0 (2 * L), ∀ j, |x τ j - chebSeries (abar j) (τ / L - 1)| < r₀) ∧
        ∀ y : ℝ → Fin n → ℝ, y 0 = x₀ →
          (∀ τ ∈ Icc 0 (2 * L),
            HasDerivWithinAt y (fun j => eval (y τ) (f j)) (Icc 0 (2 * L)) τ) →
          EqOn y x (Icc 0 (2 * L)) := by
  obtain ⟨a, hFa, huniq, u, hu, hd, hbc, herr⟩ := (ivp f L x₀).exists_solution h
  have hmaps : MapsTo (fun τ => τ / L - 1) (Icc 0 (2 * L)) (Icc (-1) 1) := fun τ hτ => by
    constructor
    · have : 0 ≤ τ / L := div_nonneg hτ.1 hL.le
      linarith
    · have : τ / L ≤ 2 := (div_le_iff₀ hL).2 (by linarith [hτ.2])
      linarith
  have hx0 : u (-1) = x₀ := by
    simpa [ivp, Matrix.one_mulVec, Matrix.zero_mulVec] using hbc
  have hxd : ∀ τ ∈ Icc 0 (2 * L), HasDerivWithinAt (fun τ => u (τ / L - 1))
      (fun j => eval (u (τ / L - 1)) (f j)) (Icc 0 (2 * L)) τ := fun τ hτ => by
    have hφ : HasDerivWithinAt (fun τ => τ / L - 1) (1 / L) (Icc 0 (2 * L)) τ :=
      (((hasDerivAt_id τ).div_const L).sub_const 1).hasDerivWithinAt
    have := (hd _ (hmaps hτ)).scomp τ hφ hmaps
    convert this using 1
    · rfl
    · funext j
      simp only [Pi.smul_apply, smul_eq_mul]
      show eval (u (τ / L - 1)) (f j) = 1 / L * (L * eval (u (τ / L - 1)) (f j))
      field_simp
  refine ⟨a, hFa, huniq, fun τ => u (τ / L - 1), by simpa using hx0,
    fun τ hτ j => hu _ (hmaps hτ) j, hxd, fun τ hτ j => herr _ (hmaps hτ) j,
    fun y hy0 hyd => ?_⟩
  exact eqOn_Icc_of_lipschitzOnWith_closedBall (lipschitzOnWith_eval_pi f) hyd hxd
    (by simpa using hy0.trans hx0.symm)

end ChebBVP

end RadiiPolynomial
