module

public import RadiiPolynomial.Convolution.Taylor
public import RadiiPolynomial.Certificate.FinSeq

/-!
# Finite Taylor sequences, computably

A finitely supported sequence of Taylor coefficients with rational entries is a list `a`
(`a_k = a.getD k 0`, `FinSeq.get`). Computable operations and their soundness with respect to the
Banach algebra `ℓ¹_ν` (`toX a ∈ ℓ¹_ν` is the sequence with coefficients `a`, `toXVec` its
componentwise version):

* `mul`: the Cauchy product `(a * b)_k = ∑_{i ≤ k} a_i b_{k-i}`, `toX (mul a b) = toX a * toX b`;
* `evalPoly`, a polynomial `PolyData n` evaluated with the Cauchy product (`FinSeq.evalPoly`):
  `toX (evalPoly p a) = aeval (toX ∘ a) (toMv p)` (`toX_evalPoly`);
* `mulUnit`: the product with a unit sequence `e_l` (`toX_mul_single`);
* `normX`: `‖toX a‖ = ∑_k |a_k| ν^k` (`norm_toX`);
* `evalAt`: the polynomial `∑_k a_k s^k`, the sum of the power series of `toX a`
  (`tsum_toX_mul_pow`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace TaySeq

open FinSeq (get get_eq_zero get_map_range add smul one get_add get_smul get_one get_nil)

/-- The Cauchy product of finite sequences. -/
def mul (a b : List ℚ) : List ℚ :=
  (List.range (a.length + b.length - 1)).map fun (k : ℕ) =>
    ∑ i ∈ Finset.range (k + 1), get a i * get b (k - i)

/-- A polynomial evaluated with the Cauchy product. -/
def evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) : List ℚ := FinSeq.evalPoly mul p a

/-- `(b * e_l)_p`: `b_{p - l}` if `l ≤ p`, else `0`. -/
def mulUnit (b : List ℚ) (l p : ℕ) : ℚ := if l ≤ p then get b (p - l) else 0

/-- `∑_k |a_k| ν^k`. -/
def normX (ν : ℚ) (a : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range a.length, ν ^ k * |get a k|

/-- The value `∑_k a_k q^k` of the polynomial with coefficients `a`, computed exactly. -/
def evalQ (q : ℚ) (a : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range a.length, get a k * q ^ k

section Real

variable {ν : ℝ} {hν : 0 < ν}

open Taylor

/-- The element of `ℓ¹_ν` with coefficients `a`. -/
noncomputable def toX (a : List ℚ) : X ν hν :=
  WeightedL1.ofSummable (fun k => (get a k : ℝ))
    (summable_of_ne_finset_zero (s := Finset.range a.length) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      simp [get_eq_zero a hk])

/-- The element of `(ℓ¹_ν)ⁿ` whose components have coefficients `a i`. -/
noncomputable def toXVec {n : ℕ} (a : Fin n → List ℚ) : Fin n → X ν hν := fun i => toX (a i)

@[simp] theorem toX_apply (a : List ℚ) (k : ℕ) : (toX a : X ν hν) k = (get a k : ℝ) := rfl

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
  rw [mul_apply, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, toX_apply, mul, get_map_range]
  simp only [toX_apply]
  split_ifs with hk
  · push_cast; rfl
  · rw [Rat.cast_zero]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases ha : a.length ≤ i
    · rw [get_eq_zero a ha, Rat.cast_zero, zero_mul]
    · rw [get_eq_zero b (by omega), Rat.cast_zero, mul_zero]

theorem toX_evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) :
    (toX (evalPoly p a) : X ν hν) = MvPolynomial.aeval (fun i => toX (a i)) p.toMv :=
  FinSeq.evalPoly_sound mul toX toX_add toX_smul toX_one toX_nil toX_mul p a

theorem toX_mul_single (b : List ℚ) (l p : ℕ) :
    ((toX b : X ν hν) * (WeightedL1.single l 1 : X ν hν)) p = (mulUnit b l p : ℝ) := by
  rw [mul_single_apply, mulUnit]
  split_ifs <;> simp

theorem norm_toX (νq : ℚ) (hνq : (νq : ℝ) = ν) (a : List ℚ) :
    ‖(toX a : X ν hν)‖ = (normX νq a : ℝ) := by
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a hk], normX]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Weights.geom_apply, toX_apply, Real.norm_eq_abs, ← hνq]

/-- The polynomial `∑_k a_k s^k`. -/
noncomputable def evalAt (a : List ℚ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range a.length, (get a k : ℝ) * s ^ k

theorem evalAt_ratCast (a : List ℚ) (q : ℚ) : evalAt a q = evalQ q a := by
  simp [evalAt, evalQ]

theorem tsum_toX_mul_pow (a : List ℚ) (s : ℝ) :
    ∑' k, (toX a : X ν hν) k * s ^ k = evalAt a s := by
  rw [tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a hk]]
  rfl

end Real

end TaySeq

end RadiiPolynomial
