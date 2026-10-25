module

public import Mathlib.Analysis.Complex.Basic
public import RadiiPolynomial.Calculus.Polynomial

/-!
# Polynomials with rational coefficients, computably

A polynomial in `n` variables with rational coefficients is given by a list of monomials
`c x^α` (`PolyData n`); `PolyData.toMv` is the corresponding real polynomial
(`MvPolynomial (Fin n) ℝ`). Computable operations and their soundness:

* `PolyData.pderiv`: `∂ᵢ (toMv p) = toMv (pderiv i p)` (`toMv_pderiv`);
* `PolyData.degree`: `totalDegree (toMv p) ≤ degree p` (`totalDegree_toMv_le`);
* `PolyData.absEval`: `|toMv p|(x) ≤ absEval p x` for `x ≥ 0` (`absEval_toMv_le`), where
  `absEval p x = ∑_{c x^α ∈ p} |c| x^α` (with equality unless monomials repeat or cancel);
* `PolyData.toMvC`: the same polynomial with complex coefficients, with `toMvC_pderiv`,
  `totalDegree_toMvC_le`, `absEval_toMvC`.

Also `absEval_add_le`, `absEval_monomial`: `|·|` is subadditive on `MvPolynomial`.
-/

@[expose] public section

namespace RadiiPolynomial

open MvPolynomial

section AbsEval

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {L : Type*} [Fintype L]

theorem absEval_eq_sum_of_subset (P : MvPolynomial L 𝕜) (x : L → ℝ)
    {S : Finset (L →₀ ℕ)} (hS : P.support ⊆ S) :
    absEval P x = ∑ d ∈ S, ‖P.coeff d‖ * ∏ i, x i ^ d i := by
  rw [absEval]
  refine Finset.sum_subset hS fun d _ hd => ?_
  rw [MvPolynomial.notMem_support_iff.1 hd, norm_zero, zero_mul]

/-- `|·|` is subadditive on `[0, ∞)^L`. -/
theorem absEval_add_le [DecidableEq L] (p q : MvPolynomial L 𝕜) {x : L → ℝ} (hx : ∀ i, 0 ≤ x i) :
    absEval (p + q) x ≤ absEval p x + absEval q x := by
  classical
  rw [absEval_eq_sum_of_subset (p + q) x (support_add (p := p) (q := q)),
    absEval_eq_sum_of_subset p x Finset.subset_union_left,
    absEval_eq_sum_of_subset q x Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [show (p + q).coeff d = p.coeff d + q.coeff d by simp, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _)

theorem absEval_monomial (s : L →₀ ℕ) (c : 𝕜) (x : L → ℝ) :
    absEval (monomial s c) x = ‖c‖ * ∏ i, x i ^ s i := by
  classical
  rw [absEval_eq_sum_of_subset (monomial s c) x (support_monomial_subset), Finset.sum_singleton,
    coeff_monomial, ite_eq_left rfl]

theorem absEval_zero (x : L → ℝ) : absEval (0 : MvPolynomial L 𝕜) x = 0 := by
  simp [absEval]

end AbsEval

/-- A monomial `c x^α` with rational coefficient. -/
structure Monomial (n : ℕ) where
  /-- the coefficient -/
  coeff : ℚ
  /-- the exponents -/
  exp : Fin n → ℕ

/-- A polynomial with rational coefficients, as a list of monomials. -/
abbrev PolyData (n : ℕ) := List (Monomial n)

namespace PolyData

variable {n : ℕ}

/-- The real monomial `c x^α`. -/
noncomputable def termToMv (t : Monomial n) : MvPolynomial (Fin n) ℝ :=
  monomial (Finsupp.equivFunOnFinite.symm t.exp) (t.coeff : ℝ)

/-- The real polynomial `∑ c x^α`. -/
noncomputable def toMv (p : PolyData n) : MvPolynomial (Fin n) ℝ :=
  (p.map termToMv).sum

theorem termToMv_eq (t : Monomial n) :
    termToMv t = C (t.coeff : ℝ) * ∏ i, X i ^ t.exp i := by
  rw [termToMv, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

@[simp] theorem toMv_nil : toMv ([] : PolyData n) = 0 := rfl

@[simp] theorem toMv_cons (t : Monomial n) (p : PolyData n) :
    toMv (t :: p) = termToMv t + toMv p := by
  simp [toMv]

/-- `∂ᵢ (c x^α) = c αᵢ x^{α - eᵢ}`. -/
def pderivTerm (i : Fin n) (t : Monomial n) : Monomial n :=
  ⟨t.coeff * t.exp i, Function.update t.exp i (t.exp i - 1)⟩

/-- The partial derivative `∂ᵢ`. -/
def pderiv (i : Fin n) (p : PolyData n) : PolyData n := p.map (pderivTerm i)

theorem termToMv_pderiv (i : Fin n) (t : Monomial n) :
    MvPolynomial.pderiv i (termToMv t) = termToMv (pderivTerm i t) := by
  classical
  have hs : Finsupp.equivFunOnFinite.symm t.exp - Finsupp.single i 1 =
      Finsupp.equivFunOnFinite.symm (Function.update t.exp i (t.exp i - 1)) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [termToMv, termToMv, pderivTerm, pderiv_monomial, hs]
  congr 1
  push_cast
  simp

theorem toMv_pderiv (i : Fin n) (p : PolyData n) :
    MvPolynomial.pderiv i (toMv p) = toMv (pderiv i p) := by
  induction p with
  | nil => simp [pderiv]
  | cons t p ih => simp [pderiv, map_add, termToMv_pderiv, ih] at ih ⊢

/-- The largest total degree of the monomials. -/
def degree (p : PolyData n) : ℕ := (p.map fun t => ∑ i, t.exp i).foldr max 0

theorem totalDegree_toMv_le (p : PolyData n) : (toMv p).totalDegree ≤ degree p := by
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [toMv_cons, degree, List.map_cons, List.foldr_cons]
    refine (totalDegree_add _ _).trans (max_le_max ?_ ih)
    refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp

/-- `∑_{c x^α ∈ p} |c| x^α`, an upper bound for `|toMv p|(x)` when `x ≥ 0`. -/
def absEval (p : PolyData n) (x : Fin n → ℚ) : ℚ :=
  (p.map fun t => |t.coeff| * ∏ i, x i ^ t.exp i).sum

theorem absEval_toMv_le (p : PolyData n) (x : Fin n → ℚ) (hx : ∀ i, 0 ≤ x i) :
    RadiiPolynomial.absEval (toMv p) (fun i => (x i : ℝ)) ≤ (absEval p x : ℝ) := by
  induction p with
  | nil => simp [absEval, RadiiPolynomial.absEval_zero]
  | cons t p ih =>
    rw [toMv_cons]
    refine (absEval_add_le _ _ fun i => by exact_mod_cast hx i).trans ?_
    simp only [absEval, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    refine add_le_add (le_of_eq ?_) ih
    rw [termToMv, absEval_monomial, Real.norm_eq_abs]
    push_cast
    rfl

/-! ### Complex coefficients -/

/-- The polynomial with complex coefficients. -/
noncomputable def toMvC (p : PolyData n) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.map (algebraMap ℝ ℂ) (toMv p)

theorem toMvC_pderiv (i : Fin n) (p : PolyData n) :
    MvPolynomial.pderiv i (toMvC p) = toMvC (pderiv i p) := by
  rw [toMvC, pderiv_map, toMv_pderiv, toMvC]

theorem support_toMvC (p : PolyData n) : (toMvC p).support = (toMv p).support :=
  support_map_of_injective _ (algebraMap ℝ ℂ).injective

theorem totalDegree_toMvC_le (p : PolyData n) : (toMvC p).totalDegree ≤ degree p := by
  have : (toMvC p).totalDegree = (toMv p).totalDegree := by
    simp only [MvPolynomial.totalDegree, support_toMvC]
  rw [this]
  exact totalDegree_toMv_le p

theorem absEval_toMvC (p : PolyData n) (x : Fin n → ℝ) :
    RadiiPolynomial.absEval (toMvC p) x = RadiiPolynomial.absEval (toMv p) x := by
  rw [RadiiPolynomial.absEval, RadiiPolynomial.absEval, support_toMvC]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [toMvC, coeff_map, Complex.coe_algebraMap, Complex.norm_real]

end PolyData

end RadiiPolynomial
