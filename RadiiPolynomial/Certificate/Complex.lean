module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor

/-!
# Exact complex arithmetic

A complex number with rational real and imaginary parts is a pair `z = (x, y) : ℚ × ℚ` (`QC`),
`QC.toC z = x + i y`. Sums, differences, negatives and rational multiples are those of `ℚ × ℚ`
(componentwise; `QC.toC` is additive); the product is `QC.mul`.

The modulus `|z| = √(x² + y²)` is in general irrational; it is enclosed by rationals obtained from
an integer square root at the fixed resolution `1/prec`:

* `QC.absUp z`, an upper bound: `‖toC z‖ ≤ absUp z` (`norm_toC_le_absUp`);
* `QC.absLo z`, a lower bound: `absLo z ≤ ‖toC z‖` (`absLo_le_norm_toC`).

Both are within `1/prec` of `|z|`.
-/

@[expose] public section

namespace RadiiPolynomial

/-- Complex numbers with rational real and imaginary parts. -/
abbrev QC := ℚ × ℚ

namespace QC

/-- The product `(x + iy)(x' + iy') = (x x' - y y') + i (x y' + y x')`. -/
def mul (z w : QC) : QC := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- `x² + y²`. -/
def normSq (z : QC) : ℚ := z.1 * z.1 + z.2 * z.2

/-- The resolution of the moduli. -/
def prec : ℕ := 10 ^ 30

/-- An upper bound for `√q`, from `⌈q prec²⌉` and an integer square root. -/
def sqrtUp (q : ℚ) : ℚ := ((Nat.sqrt ⌈q * (prec : ℚ) ^ 2⌉₊ + 1 : ℕ) : ℚ) / prec

/-- A lower bound for `√q` (`q ≥ 0`), from `⌊q prec²⌋` and an integer square root. -/
def sqrtLo (q : ℚ) : ℚ := ((Nat.sqrt ⌊q * (prec : ℚ) ^ 2⌋₊ : ℕ) : ℚ) / prec

/-- An upper bound for `|z|`. -/
def absUp (z : QC) : ℚ := sqrtUp (normSq z)

/-- A lower bound for `|z|`. -/
def absLo (z : QC) : ℚ := sqrtLo (normSq z)

/-- `(x, y) ↦ x + i y`. -/
noncomputable def toC : QC →+ ℂ where
  toFun z := ⟨z.1, z.2⟩
  map_zero' := by apply Complex.ext <;> simp
  map_add' z w := by apply Complex.ext <;> simp

@[simp] theorem toC_re (z : QC) : (toC z).re = z.1 := rfl

@[simp] theorem toC_im (z : QC) : (toC z).im = z.2 := rfl

theorem toC_mul (z w : QC) : toC (mul z w) = toC z * toC w := by
  apply Complex.ext <;> simp [mul]

theorem toC_smul (c : ℚ) (z : QC) : toC (c • z) = (c : ℂ) * toC z := by
  apply Complex.ext <;> simp

theorem toC_one : toC (1, 0) = 1 := by
  apply Complex.ext <;> simp

theorem toC_ofRat (c : ℚ) : toC (c, 0) = (c : ℂ) := by
  apply Complex.ext <;> simp

theorem prec_pos : (0 : ℚ) < prec := by norm_num [prec]

theorem normSq_nonneg (z : QC) : 0 ≤ normSq z := by
  unfold normSq; nlinarith [mul_self_nonneg z.1, mul_self_nonneg z.2]

theorem norm_toC (z : QC) : ‖toC z‖ = Real.sqrt (normSq z : ℚ) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, normSq]

theorem sqrtUp_nonneg (q : ℚ) : 0 ≤ sqrtUp q :=
  div_nonneg (Nat.cast_nonneg _) prec_pos.le

theorem sqrtLo_nonneg (q : ℚ) : 0 ≤ sqrtLo q :=
  div_nonneg (Nat.cast_nonneg _) prec_pos.le

theorem le_sqrtUp_sq (q : ℚ) : q ≤ sqrtUp q ^ 2 := by
  have h1 := Nat.le_ceil (q * (prec : ℚ) ^ 2)
  have h2 : (⌈q * (prec : ℚ) ^ 2⌉₊ : ℚ) < ((Nat.sqrt ⌈q * (prec : ℚ) ^ 2⌉₊ + 1 : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' _
  rw [sqrtUp, div_pow, le_div_iff₀ (pow_pos prec_pos 2)]
  linarith

theorem sqrtLo_sq_le {q : ℚ} (hq : 0 ≤ q) : sqrtLo q ^ 2 ≤ q := by
  have h1 := Nat.floor_le (mul_nonneg hq (pow_nonneg prec_pos.le 2) : 0 ≤ q * (prec : ℚ) ^ 2)
  have h2 : ((Nat.sqrt ⌊q * (prec : ℚ) ^ 2⌋₊ : ℕ) : ℚ) ^ 2 ≤ (⌊q * (prec : ℚ) ^ 2⌋₊ : ℚ) := by
    exact_mod_cast Nat.sqrt_le' _
  rw [sqrtLo, div_pow, div_le_iff₀ (pow_pos prec_pos 2)]
  linarith

theorem sqrt_le_sqrtUp (q : ℚ) : Real.sqrt q ≤ sqrtUp q := by
  have h : (q : ℝ) ≤ ((sqrtUp q : ℚ) : ℝ) ^ 2 := by exact_mod_cast le_sqrtUp_sq q
  calc Real.sqrt q ≤ Real.sqrt (((sqrtUp q : ℚ) : ℝ) ^ 2) := Real.sqrt_le_sqrt h
    _ = sqrtUp q := Real.sqrt_sq (by exact_mod_cast sqrtUp_nonneg q)

theorem sqrtLo_le_sqrt {q : ℚ} (hq : 0 ≤ q) : (sqrtLo q : ℝ) ≤ Real.sqrt q := by
  rw [Real.le_sqrt (by exact_mod_cast sqrtLo_nonneg q) (by exact_mod_cast hq)]
  exact_mod_cast sqrtLo_sq_le hq

theorem norm_toC_le_absUp (z : QC) : ‖toC z‖ ≤ absUp z := by
  rw [norm_toC]; exact sqrt_le_sqrtUp _

theorem absLo_le_norm_toC (z : QC) : (absLo z : ℝ) ≤ ‖toC z‖ := by
  rw [norm_toC]; exact sqrtLo_le_sqrt (normSq_nonneg z)

theorem absUp_nonneg (z : QC) : 0 ≤ absUp z := sqrtUp_nonneg _

theorem norm_toC_le_of_normSq_le {z w : QC} (h : normSq z ≤ normSq w) : ‖toC z‖ ≤ ‖toC w‖ := by
  rw [norm_toC, norm_toC]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h)

end QC

end RadiiPolynomial
