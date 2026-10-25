module

public import RadiiPolynomial.Convolution.Chebyshev
public import RadiiPolynomial.Convolution.ChebyshevSeries
public import RadiiPolynomial.Certificate.Polynomial
public import RadiiPolynomial.Certificate.FinSeq

/-!
# Finite Chebyshev sequences, computably

A finitely supported Chebyshev sequence with rational coefficients is a list `a` of rationals
(`a_k = a.getD k 0`, `FinSeq.get`). Computable operations and their soundness with respect to the
Banach algebra `X_ν` (`toX a ∈ X_ν` is the sequence with coefficients `a`, `toXVec` its componentwise
version):

* `mul`: `(a * b)_k = ∑_{|j| < len a} a_{|j|} b_{|k - j|}`, `toX (mul a b) = toX a * toX b`;
* `evalPoly`, a polynomial `PolyData n` evaluated with the Chebyshev product (`FinSeq.evalPoly`):
  `toX (evalPoly p a) = aeval (toX ∘ a) (toMv p)` (`toX_evalPoly`);
* `mulUnit`: the product with a unit sequence `e_l` (`toX_mul_single`);
* `normX`: `‖toX a‖ = |a_0| + 2 ∑_{k ≥ 1} |a_k| ν^k`, and `evalAt s`: the value
  `a_0 + 2 ∑_{k ≥ 1} s^k a_k` (`boundaryEval_toX`);
* `evalSeries a t = a_0 + 2 ∑_{k ≥ 1} a_k T_k(t)`, the Chebyshev series of `toX a`
  (`chebSeries_toX`); at a rational point it is the exact value `evalT q a`, computed with the
  recurrence `T_{n+2} = 2 q T_{n+1} - T_n` (`evalSeries_ratCast`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace ChebSeq

open FinSeq (get get_eq_zero get_map_range add smul one get_add get_smul get_one get_nil)

/-- The Chebyshev product of finite sequences. -/
def mul (a b : List ℚ) : List ℚ :=
  (List.range (a.length + b.length - 1)).map fun (k : ℕ) =>
    ∑ j ∈ Finset.Icc (1 - (a.length : ℤ)) (a.length - 1),
      get a j.natAbs * get b ((k : ℤ) - j).natAbs

/-- A polynomial evaluated with the Chebyshev product. -/
def evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) : List ℚ := FinSeq.evalPoly mul p a

/-- `(b * e_l)_p`: `b_p` if `l = 0`, `b_{|p - l|} + b_{p + l}` otherwise. -/
def mulUnit (b : List ℚ) (l p : ℕ) : ℚ :=
  if l = 0 then get b p else get b ((p : ℤ) - l).natAbs + get b (p + l)

/-- `|a_0| + 2 ∑_{k ≥ 1} |a_k| ν^k`. -/
def normX (ν : ℚ) (a : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range a.length, (if k = 0 then 1 else 2 * ν ^ k) * |get a k|

/-- `a_0 + 2 ∑_{k ≥ 1} s^k a_k`. -/
def evalAt (s : ℚ) (a : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range a.length, (if k = 0 then 1 else 2 * s ^ k) * get a k

/-- `(T_n(q), T_{n+1}(q))`, by the recurrence `T_0 = 1`, `T_1 = q`, `T_{n+2} = 2 q T_{n+1} - T_n`. -/
def chebPair (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, q)
  | n + 1 => let p := chebPair q n; (p.2, 2 * q * p.2 - p.1)

/-- The value `T_n(q)` of the Chebyshev polynomial, computed by the recurrence. -/
def chebT (q : ℚ) (n : ℕ) : ℚ := (chebPair q n).1

/-- The value `a_0 + 2 ∑_{k ≥ 1} a_k T_k(q)`, computed exactly. -/
def evalT (q : ℚ) (a : List ℚ) : ℚ :=
  get a 0 + 2 * ∑ k ∈ Finset.range a.length, get a (k + 1) * chebT q (k + 1)

section Real

variable {ν : ℝ} {hν : 1 ≤ ν}

open Chebyshev

/-- The element of `X_ν` with coefficients `a`. -/
noncomputable def toX (a : List ℚ) : X ν hν :=
  WeightedL1.ofSummable (fun k => (get a k : ℝ))
    (summable_of_ne_finset_zero (s := Finset.range a.length) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      simp [get_eq_zero a hk])

/-- The element of `X_νⁿ` whose components have coefficients `a i`. -/
noncomputable def toXVec {n : ℕ} (a : Fin n → List ℚ) : Fin n → X ν hν := fun i => toX (a i)

@[simp] theorem toX_apply (a : List ℚ) (k : ℕ) : (toX a : X ν hν) k = (get a k : ℝ) := rfl

/-- The Chebyshev polynomial `a_0 + 2 ∑_{k ≥ 1} a_k T_k(t)` with the coefficients `a`. -/
noncomputable def evalSeries (a : List ℚ) (t : ℝ) : ℝ :=
  get a 0 + 2 * ∑ k ∈ Finset.range a.length,
    (get a (k + 1) : ℝ) * (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t

theorem chebPair_eq (q : ℚ) (n : ℕ) :
    ((chebPair q n).1 : ℝ) = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (q : ℝ) ∧
      ((chebPair q n).2 : ℝ) = (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval (q : ℝ) := by
  induction n with
  | zero => simp [chebPair, Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one]
  | succ n ih =>
    simp only [chebPair]
    refine ⟨by rw [ih.2]; push_cast; rfl, ?_⟩
    rw [show ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 by push_cast; ring,
      Polynomial.Chebyshev.T_add_two]
    push_cast
    rw [ih.1, ih.2]
    simp [Polynomial.eval_sub, Polynomial.eval_mul]

theorem chebT_eq (q : ℚ) (n : ℕ) :
    (chebT q n : ℝ) = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (q : ℝ) := (chebPair_eq q n).1

/-- The Chebyshev polynomial of `a` at a rational point, computed by the recurrence. -/
theorem evalSeries_ratCast (a : List ℚ) (q : ℚ) : evalSeries a q = evalT q a := by
  simp only [evalSeries, evalT]
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chebT_eq]
  push_cast
  rfl

theorem chebSeries_toX (a : List ℚ) (t : ℝ) : chebSeries (toX a : X ν hν) t = evalSeries a t := by
  rw [chebSeries, evalSeries, tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a (show a.length ≤ k + 1 by omega)]]
  simp

theorem suppLe_toX (a : List ℚ) : SuppLe (toX a : X ν hν) (a.length - 1) := fun k hk => by
  rw [toX_apply, get_eq_zero a (by omega), Rat.cast_zero]

theorem toX_add (a b : List ℚ) : (toX (add a b) : X ν hν) = toX a + toX b := by
  ext k; simp [get_add]

theorem toX_smul (c : ℚ) (a : List ℚ) : (toX (smul c a) : X ν hν) = (c : ℝ) • toX a := by
  ext k; simp [get_smul]

theorem toX_one : (toX one : X ν hν) = 1 := by
  ext k; rw [toX_apply, get_one, one_apply]; split_ifs <;> simp

theorem toX_nil : (toX [] : X ν hν) = 0 := by
  ext k; simp [get_nil]

theorem toX_mul (a b : List ℚ) : (toX (mul a b) : X ν hν) = toX a * toX b := by
  ext k
  rw [mul_apply, toX_apply]
  simp only [toX_apply]
  set S := Finset.Icc (1 - (a.length : ℤ)) (a.length - 1)
  have hS : ∀ j ∉ S, (get a j.natAbs : ℝ) * get b ((k : ℤ) - j).natAbs = 0 := fun j hj => by
    have : a.length ≤ j.natAbs := by
      simp only [S, Finset.mem_Icc, not_and_or, not_le] at hj; omega
    rw [get_eq_zero a this, Rat.cast_zero, zero_mul]
  rw [tsum_eq_sum (s := S) hS, mul, get_map_range]
  split_ifs with hk
  · push_cast; rfl
  · rw [Rat.cast_zero]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [S, Finset.mem_Icc] at hj
    have : b.length ≤ ((k : ℤ) - j).natAbs := by omega
    rw [get_eq_zero b this, Rat.cast_zero, mul_zero]

theorem toX_evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) :
    (toX (evalPoly p a) : X ν hν) = MvPolynomial.aeval (fun i => toX (a i)) p.toMv :=
  FinSeq.evalPoly_sound mul toX toX_add toX_smul toX_one toX_nil toX_mul p a

theorem toX_mul_single (b : List ℚ) (l p : ℕ) :
    ((toX b : X ν hν) * (WeightedL1.single l 1 : X ν hν)) p = (mulUnit b l p : ℝ) := by
  rw [mulUnit]
  split_ifs with hl
  · subst hl
    have h1 : (WeightedL1.single 0 1 : X ν hν) = 1 := by
      ext k; rw [WeightedL1.single_apply, one_apply]
    rw [h1, mul_one]
    rfl
  · rw [mul_single_apply _ hl, toX_apply, toX_apply]
    push_cast
    rfl

theorem norm_toX (νq : ℚ) (hνq : (νq : ℝ) = ν) (a : List ℚ) :
    ‖(toX a : X ν hν)‖ = (normX νq a : ℝ) := by
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a hk], normX]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weights_apply, toX_apply, Real.norm_eq_abs, ← hνq]
  split_ifs <;> simp

theorem boundaryEval_toX (s : ℝ) (hs : |s| ≤ 1) (sq : ℚ) (hsq : (sq : ℝ) = s) (a : List ℚ) :
    boundaryEval ν hν s hs (toX a) = (evalAt sq a : ℝ) := by
  rw [boundaryEval_apply, tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a hk], evalAt]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evalWeight, toX_apply, ← hsq]
  split_ifs <;> simp

end Real

end ChebSeq

end RadiiPolynomial
