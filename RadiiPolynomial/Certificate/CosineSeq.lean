module

public import RadiiPolynomial.Convolution.Cosine
public import RadiiPolynomial.Certificate.ChebyshevSeq

/-!
# Finite cosine sequences, computably

A finitely supported one-sided sequence with rational entries is a list `a`
(`a_k = a.getD k 0`, `FinSeq.get`); `toX a ∈ ℓ¹_ν` (`Cosine.X`) is the sequence with these
coefficients. The symmetric product of `ℓ¹_ν` is the Chebyshev product, so it is computed with
`ChebSeq.mul`:

* `mul2_toX`, `mul3_toX`: `toX a * toX b = toX (ChebSeq.mul a b)` (and the triple product);
* `mul3_single_toX`: the product with a unit sequence `e_l`, via `ChebSeq.mulUnit`;
* `absX_toX`: `|toX a| = toX (absSeq a)`;
* `normX`: `‖toX a‖ = ∑_k |a_k| ν^k` (`norm_toX`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace CosSeq

open FinSeq (get get_eq_zero)

/-- `|a| = (|a_k|)_k`. -/
def absSeq (a : List ℚ) : List ℚ := a.map (|·|)

/-- `∑_k |a_k| ν^k`. -/
def normX (ν : ℚ) (a : List ℚ) : ℚ :=
  ∑ k ∈ Finset.range a.length, ν ^ k * |get a k|

theorem get_absSeq (a : List ℚ) (k : ℕ) : get (absSeq a) k = |get a k| := by
  rw [FinSeq.get, FinSeq.get, absSeq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases a[k]? <;> simp

section Real

variable {ν : ℝ} {hν : 1 ≤ ν}

open Cosine

/-- The element of `ℓ¹_ν` with coefficients `a`. -/
noncomputable def toX (a : List ℚ) : X ν hν :=
  WeightedL1.ofSummable (fun k => (get a k : ℝ))
    (summable_of_ne_finset_zero (s := Finset.range a.length) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      simp [get_eq_zero a hk])

@[simp] theorem toX_apply (a : List ℚ) (k : ℕ) : (toX a : X ν hν) k = (get a k : ℝ) := rfl

theorem toX_eq_zero (a : List ℚ) {k : ℕ} (hk : a.length ≤ k) : (toX a : X ν hν) k = 0 := by
  rw [toX_apply, get_eq_zero a hk, Rat.cast_zero]

theorem toCheb_toX (a : List ℚ) : toCheb ν hν (toX a) = ChebSeq.toX a := by
  ext k; simp

theorem mul2_toX (a b : List ℚ) :
    mul2 ν hν (toX a) (toX b) = toX (ChebSeq.mul a b) := by
  ext k
  rw [mul2, toCheb_toX, toCheb_toX, ← ChebSeq.toX_mul, ofCheb_apply, ChebSeq.toX_apply, toX_apply]

theorem mul3_toX (a b c : List ℚ) :
    mul3 ν hν (toX a) (toX b) (toX c) = toX (ChebSeq.mul (ChebSeq.mul a b) c) := by
  rw [mul3_eq_mul2, mul2_toX, mul2_toX]

theorem mul3_single_toX (a : List ℚ) (l p : ℕ) :
    mul3 ν hν (toX a) (toX a) (WeightedL1.single l 1) p =
      (ChebSeq.mulUnit (ChebSeq.mul a a) l p : ℝ) := by
  rw [mul3, ofCheb_apply, toCheb_toX, toCheb_single, ← ChebSeq.toX_mul, ChebSeq.toX_mul_single]

theorem absX_toX (a : List ℚ) : absX ν hν (toX a) = toX (absSeq a) := by
  ext k; simp [get_absSeq]

theorem norm_toX (νq : ℚ) (hνq : (νq : ℝ) = ν) (a : List ℚ) :
    ‖(toX a : X ν hν)‖ = (normX νq a : ℝ) := by
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum (s := Finset.range a.length) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    simp [get_eq_zero a hk], normX]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Cosine.weights_apply, toX_apply, Real.norm_eq_abs, ← hνq]

end Real

end CosSeq

end RadiiPolynomial
