module

public import RadiiPolynomial.Convolution.Basic
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Cauchy product and discrete convolution

* `I = ℕ`: the weights `ν^n` (`ν > 0`, `Weights.geom`) are submultiplicative, so
  `ℓ¹_{ν,ℕ} = WeightedL1 𝕜 (Weights.geom ν hν)` is a commutative Banach algebra with unit; the
  convolution is the Cauchy product `(a * b)_n = ∑_{k + l = n} a_k b_l`, a finite sum
  (`Convolution.conv_nat`).
* `I = ℤ`: the weights `ν^|n|` (`ν ≥ 1`, `Weights.geomInt`) are submultiplicative, so
  `ℓ¹_{ν,ℤ}` is a commutative Banach algebra with unit; the convolution is the discrete
  convolution `(a * b)_n = ∑_{j ∈ ℤ} a_j b_{n-j}` (`Convolution.conv_int`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace Weights

/-- The weights `ν^n` on `ℕ`, `ν > 0`. -/
def geom (ν : ℝ) (hν : 0 < ν) : Weights ℕ := ⟨fun n => ν ^ n, fun n => pow_pos hν n⟩

@[simp] theorem geom_apply (ν : ℝ) (hν : 0 < ν) (n : ℕ) : geom ν hν n = ν ^ n := rfl

instance (ν : ℝ) (hν : 0 < ν) : (geom ν hν).IsSubmultiplicative :=
  ⟨fun i j => by simp [pow_add]⟩

/-- The weights `ν^|n|` on `ℤ`, `ν ≥ 1`. -/
def geomInt (ν : ℝ) (hν : 1 ≤ ν) : Weights ℤ :=
  ⟨fun n => ν ^ n.natAbs, fun _ => pow_pos (lt_of_lt_of_le zero_lt_one hν) _⟩

@[simp] theorem geomInt_apply (ν : ℝ) (hν : 1 ≤ ν) (n : ℤ) : geomInt ν hν n = ν ^ n.natAbs := rfl

instance (ν : ℝ) (hν : 1 ≤ ν) : (geomInt ν hν).IsSubmultiplicative :=
  ⟨fun i j => by
    simp only [geomInt_apply]
    rw [← pow_add]
    exact pow_le_pow_right₀ hν (Int.natAbs_add_le i j)⟩

end Weights

namespace Convolution

variable {𝕜 : Type*} [RCLike 𝕜]

/-- On `ℕ` the convolution is the Cauchy product, a finite sum. -/
theorem conv_nat (a b : ℕ → 𝕜) (n : ℕ) :
    conv a b n = ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 := by
  let e : fiber n ≃ {p : ℕ × ℕ // p ∈ Finset.antidiagonal n} :=
    Equiv.subtypeEquivRight fun p => Finset.mem_antidiagonal.symm
  rw [conv, ← Finset.tsum_subtype, ← e.tsum_eq]
  rfl

/-- `fiber n ≃ ℤ`, `(j, n - j) ↤ j`. -/
def fiberIntEquiv (n : ℤ) : fiber n ≃ ℤ where
  toFun q := q.1.1
  invFun j := ⟨(j, n - j), by simp⟩
  left_inv q := Subtype.ext (Prod.ext rfl (by have := q.2; simp only at this ⊢; omega))
  right_inv j := rfl

/-- On `ℤ` the convolution is `(a * b)_n = ∑_{j ∈ ℤ} a_j b_{n-j}`. -/
theorem conv_int (a b : ℤ → 𝕜) (n : ℤ) : conv a b n = ∑' j : ℤ, a j * b (n - j) := by
  rw [conv, ← (fiberIntEquiv n).symm.tsum_eq]
  rfl

end Convolution

end RadiiPolynomial
