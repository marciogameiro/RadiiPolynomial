module

public import RadiiPolynomial.Convolution.Fourier
public import RadiiPolynomial.Convolution.FourierSeries
public import RadiiPolynomial.Certificate.Complex
public import RadiiPolynomial.Certificate.Polynomial

/-!
# Finite Fourier sequences, computably

A Fourier sequence supported in `{-N, …, N}` with coefficients in `QC` (complex numbers with
rational parts) is a list `a = [a_{-N}, …, a_N]` (`FourierSeq.get N a n = a_n`, `0` for `|n| > N`);
`toX N a ∈ ℓ¹_ν` (`Fourier.X`) is the sequence with these coefficients. Computable operations and
their soundness:

* `conv`: `(a * b)_n = ∑_{|j| ≤ N} a_j b_{n-j}`, `(toX N a * toX N b)_n = conv N a b n`
  (`toX_mul_apply`);
* `normUp`: `‖toX N a‖ ≤ ∑_{|n| ≤ N} absUp(a_n) ν^{|n|}` (`norm_toX_le`);
* `evalAt`: the trigonometric polynomial `∑_{|n| ≤ N} a_n e^{int}`, the Fourier series of `toX N a`
  (`fourierEval_toX`);
* `IsSymm`: `a_{-n} = a_n^*` for `|n| ≤ N` (decidable), then `(toX N a)^* = toX N a` (`conjX_toX`).

Sequences with their support bound, `FS = (M, [a_{-M}, …, a_M])`, form a computable model of the
algebra `ℓ¹_ν` (`FS.toXF`): `FS.add`, `FS.smul`, `FS.one`, `FS.zero` and the convolution `FS.mul`
(support bounds add) are mapped to the operations of `ℓ¹_ν`, and polynomials are evaluated with
them (`FS.evalPoly`): `toXF (evalPoly p a) = aeval (toXF ∘ a) (toMvC p)` (`FS.toXF_evalPoly`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace FourierSeq

open Fourier

/-- The coefficient `a_n` of `a = [a_{-N}, …, a_N]`, `0` for `|n| > N`. -/
def get (N : ℕ) (a : List QC) (n : ℤ) : QC := if n.natAbs ≤ N then a.getD (n + N).toNat 0 else 0

theorem get_eq_zero (N : ℕ) (a : List QC) {n : ℤ} (hn : N < n.natAbs) : get N a n = 0 := by
  rw [get, ite_eq_right (by omega)]

/-- `(a * b)_n = ∑_{|j| ≤ N} a_j b_{n-j}`. -/
def conv (N : ℕ) (a b : List QC) (n : ℤ) : QC :=
  ∑ j ∈ center N, QC.mul (get N a j) (get N b (n - j))

/-- `∑_{|n| ≤ N} absUp(a_n) ν^{|n|}`. -/
def normUp (ν : ℚ) (N : ℕ) (a : List QC) : ℚ :=
  ∑ n ∈ center N, QC.absUp (get N a n) * ν ^ n.natAbs

/-- The conjugate `(x, -y)` of `(x, y)`. -/
def conjQC (z : QC) : QC := (z.1, -z.2)

/-- `a_{-n} = a_n^*` for all `|n| ≤ N`. -/
def IsSymm (N : ℕ) (a : List QC) : Prop := ∀ n ∈ center N, get N a (-n) = conjQC (get N a n)

instance (N : ℕ) (a : List QC) : Decidable (IsSymm N a) := by unfold IsSymm; infer_instance

theorem toC_conjQC (z : QC) : QC.toC (conjQC z) = star (QC.toC z) := by
  apply Complex.ext <;> simp [conjQC]

section Real

variable {ν : ℝ} {hν : 1 ≤ ν}

/-- The trigonometric polynomial `∑_{|n| ≤ N} a_n e^{int}`. -/
noncomputable def evalAt (N : ℕ) (a : List QC) (t : ℝ) : ℂ :=
  ∑ n ∈ center N, QC.toC (get N a n) * expI t n

/-- The element of `ℓ¹_ν` with coefficients `a`. -/
noncomputable def toX (N : ℕ) (a : List QC) : X ν hν :=
  WeightedL1.ofSummable (fun n => QC.toC (get N a n))
    (summable_of_ne_finset_zero (s := center N) fun n hn => by
      rw [mem_center, not_le] at hn
      simp [get_eq_zero N a hn])

@[simp] theorem toX_apply (N : ℕ) (a : List QC) (n : ℤ) :
    (toX N a : X ν hν) n = QC.toC (get N a n) := rfl

theorem suppLe_toX (N : ℕ) (a : List QC) : SuppLe (toX N a : X ν hν) N := fun n hn => by
  rw [toX_apply, get_eq_zero N a hn, map_zero]

theorem toX_mul_apply (N : ℕ) (a b : List QC) (n : ℤ) :
    ((toX N a * toX N b : X ν hν)) n = QC.toC (conv N a b n) := by
  rw [mul_apply, tsum_eq_sum (s := center N) fun j hj => by
    rw [mem_center, not_le] at hj
    rw [toX_apply, get_eq_zero N a hj, map_zero, zero_mul], conv, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [QC.toC_mul]; rfl

theorem norm_toX_le (νq : ℚ) (hνq : (νq : ℝ) = ν) (N : ℕ) (a : List QC) :
    ‖(toX N a : X ν hν)‖ ≤ (normUp νq N a : ℝ) := by
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum (s := center N) fun n hn => by
    rw [mem_center, not_le] at hn
    simp [get_eq_zero N a hn], normUp]
  push_cast
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Weights.geomInt_apply, toX_apply, ← hνq, mul_comm]
  exact mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _)
    (pow_nonneg (by rw [hνq]; exact (nu_pos hν).le) _)

theorem fourierEval_toX (N : ℕ) (a : List QC) (t : ℝ) :
    fourierEval ν hν t (toX N a) = evalAt N a t := by
  rw [fourierEval_apply, tsum_eq_sum (s := center N) fun n hn => by
    rw [mem_center, not_le] at hn
    rw [toX_apply, get_eq_zero N a hn, map_zero, zero_mul]]
  rfl

theorem conjX_toX {N : ℕ} {a : List QC} (h : IsSymm N a) :
    conjX (toX N a : X ν hν) = toX N a := by
  ext n
  rw [conjX_apply, toX_apply, toX_apply]
  by_cases hn : n ∈ center N
  · rw [h n hn, toC_conjQC, star_star]
  · rw [mem_center, not_le] at hn
    rw [get_eq_zero N a (by simpa using hn), get_eq_zero N a hn, map_zero, star_zero]

theorem toX_mul_apply' (M₁ M₂ : ℕ) (a b : List QC) (n : ℤ) :
    ((toX M₁ a * toX M₂ b : X ν hν)) n =
      QC.toC (∑ j ∈ center M₁, QC.mul (get M₁ a j) (get M₂ b (n - j))) := by
  rw [mul_apply, tsum_eq_sum (s := center M₁) fun j hj => by
    rw [mem_center, not_le] at hj
    rw [toX_apply, get_eq_zero M₁ a hj, map_zero, zero_mul], map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [QC.toC_mul]; rfl

end Real

/-! ### Sequences with their support bound -/

/-- A finite Fourier sequence with its support bound, `(M, [a_{-M}, …, a_M])`. -/
abbrev FS := ℕ × List QC

namespace FS

/-- The coefficient `a_n`. -/
def get (a : FS) (n : ℤ) : QC := FourierSeq.get a.1 a.2 n

/-- The sequence `(g_{-M}, …, g_M)`. -/
def ofFun (M : ℕ) (g : ℤ → QC) : FS :=
  (M, (List.range (2 * M + 1)).map fun i : ℕ => g ((i : ℤ) - M))

/-- The sum. -/
def add (a b : FS) : FS := ofFun (max a.1 b.1) fun n => a.get n + b.get n

/-- A rational multiple. -/
def smul (c : ℚ) (a : FS) : FS := ofFun a.1 fun n => c • a.get n

/-- The unit `e_0`. -/
def one : FS := (0, [(1, 0)])

/-- The zero sequence. -/
def zero : FS := (0, [])

/-- The convolution `(a * b)_n = ∑_j a_j b_{n-j}`. -/
def mul (a b : FS) : FS :=
  ofFun (a.1 + b.1) fun n => ∑ j ∈ center a.1, QC.mul (a.get j) (b.get (n - j))

theorem get_eq_zero (a : FS) {n : ℤ} (hn : a.1 < n.natAbs) : a.get n = 0 :=
  FourierSeq.get_eq_zero _ _ hn

theorem get_ofFun (M : ℕ) (g : ℤ → QC) (n : ℤ) :
    (ofFun M g).get n = if n.natAbs ≤ M then g n else 0 := by
  rw [get, FourierSeq.get, ofFun]
  split_ifs with hn
  · simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    omega
  · rfl

theorem get_one (n : ℤ) : one.get n = if n = 0 then (1, 0) else 0 := by
  rw [get, FourierSeq.get]
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [ite_eq_right (by change ¬ n.natAbs ≤ 0; omega), ite_eq_right hn]

theorem get_zero (n : ℤ) : zero.get n = 0 := by
  rw [get, FourierSeq.get]; split_ifs <;> rfl

section Real

variable {ν : ℝ} {hν : 1 ≤ ν}

/-- The element of `ℓ¹_ν` with coefficients `a`. -/
noncomputable def toXF (a : FS) : X ν hν := toX a.1 a.2

@[simp] theorem toXF_apply (a : FS) (n : ℤ) : (toXF a : X ν hν) n = QC.toC (a.get n) := rfl

theorem suppLe_toXF (a : FS) : SuppLe (toXF a : X ν hν) a.1 := suppLe_toX _ _

theorem toXF_ofFun (M : ℕ) (g : ℤ → QC) (hg : ∀ n, M < n.natAbs → g n = 0) :
    (toXF (ofFun M g) : X ν hν) = WeightedL1.ofSummable (fun n => QC.toC (g n))
      (summable_of_ne_finset_zero (s := center M) fun n hn => by
        rw [mem_center, not_le] at hn; simp [hg n hn]) := by
  ext n
  rw [toXF_apply, get_ofFun, WeightedL1.ofSummable_apply]
  split_ifs with hn
  · rfl
  · rw [hg n (by omega), map_zero]

theorem toXF_add (a b : FS) : (toXF (add a b) : X ν hν) = toXF a + toXF b := by
  ext n
  rw [toXF_apply, add, get_ofFun, WeightedLp.add_apply, toXF_apply, toXF_apply]
  split_ifs with hn
  · rw [map_add]
  · rw [a.get_eq_zero (by omega), b.get_eq_zero (by omega), map_zero, add_zero]

theorem toXF_smul (c : ℚ) (a : FS) : (toXF (smul c a) : X ν hν) = (c : ℂ) • toXF a := by
  ext n
  rw [toXF_apply, smul, get_ofFun, WeightedLp.smul_apply, toXF_apply]
  split_ifs with hn
  · rw [QC.toC_smul]
  · rw [a.get_eq_zero (by omega), map_zero, mul_zero]

theorem toXF_one : (toXF one : X ν hν) = 1 := by
  ext n
  rw [toXF_apply, get_one, one_apply]
  split_ifs
  · exact QC.toC_one
  · exact map_zero _

theorem toXF_zero : (toXF zero : X ν hν) = 0 := by
  ext n
  rw [toXF_apply, get_zero, map_zero, WeightedLp.zero_apply]

theorem toXF_mul (a b : FS) : (toXF (mul a b) : X ν hν) = toXF a * toXF b := by
  ext n
  rw [toXF_apply, mul, get_ofFun]
  split_ifs with hn
  · exact (toX_mul_apply' a.1 b.1 a.2 b.2 n).symm
  · rw [map_zero]
    exact ((suppLe_toXF a).mul (suppLe_toXF b) n (by omega)).symm

/-- `‖toXF a‖ ≤ ∑_{|n| ≤ M} absUp(a_n) ν^{|n|}`. -/
theorem norm_toXF_le (νq : ℚ) (hνq : (νq : ℝ) = ν) (a : FS) :
    ‖(toXF a : X ν hν)‖ ≤ (normUp νq a.1 a.2 : ℝ) := norm_toX_le νq hνq _ _

/-- `‖a - π_N a‖ ≤ ∑_{N < |n| ≤ M} absUp(a_n) ν^{|n|}`. -/
theorem norm_sub_finPart_toXF_le (νq : ℚ) (hνq : (νq : ℝ) = ν) (N : ℕ) (a : FS) :
    ‖(toXF a : X ν hν) - finPart N (toXF a)‖ ≤
      ((∑ n ∈ center a.1 \ center N, QC.absUp (a.get n) * νq ^ n.natAbs : ℚ) : ℝ) := by
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum (s := center a.1 \ center N) fun n hn => by
    rw [Finset.mem_sdiff, not_and_or, not_not] at hn
    rw [sub_finPart_apply]
    rcases hn with hn | hn
    · by_cases h : n ∈ center N
      · rw [ite_eq_left h, norm_zero, mul_zero]
      · rw [ite_eq_right h, toXF_apply, a.get_eq_zero (by rw [mem_center, not_le] at hn; exact hn),
          map_zero, norm_zero, mul_zero]
    · rw [ite_eq_left hn, norm_zero, mul_zero]]
  push_cast
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_sdiff] at hn
  rw [sub_finPart_apply, ite_eq_right hn.2, Weights.geomInt_apply, toXF_apply, ← hνq, mul_comm]
  exact mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _)
    (pow_nonneg (by rw [hνq]; exact (nu_pos hν).le) _)

end Real

/-! ### Polynomials -/

/-- Powers. -/
def pow (a : FS) : ℕ → FS
  | 0 => one
  | e + 1 => mul (pow a e) a

/-- `∏ᵢ fᵢ`. -/
def prodFin {n : ℕ} (f : Fin n → FS) : FS := (List.finRange n).foldr (fun i acc => mul (f i) acc) one

/-- A monomial `c a^α`. -/
def evalTerm {n : ℕ} (a : Fin n → FS) (t : Monomial n) : FS :=
  smul t.coeff (prodFin fun i => pow (a i) (t.exp i))

/-- A polynomial evaluated with the convolution. -/
def evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → FS) : FS :=
  (p.map (evalTerm a)).foldr add zero

section Real

variable {ν : ℝ} {hν : 1 ≤ ν}

theorem toXF_pow (a : FS) (e : ℕ) : (toXF (pow a e) : X ν hν) = toXF a ^ e := by
  induction e with
  | zero => rw [pow, toXF_one, _root_.pow_zero]
  | succ e ih => rw [pow, toXF_mul, ih, _root_.pow_succ]

theorem toXF_prodFin {n : ℕ} (f : Fin n → FS) :
    (toXF (prodFin f) : X ν hν) = ∏ i, toXF (f i) := by
  have h : ∀ l : List (Fin n), (toXF (l.foldr (fun i acc => mul (f i) acc) one) : X ν hν) =
      (l.map fun i => (toXF (f i) : X ν hν)).prod := fun l => by
    induction l with
    | nil => exact toXF_one
    | cons i l ih => rw [List.foldr_cons, toXF_mul, ih, List.map_cons, List.prod_cons]
  rw [prodFin, h, Fin.prod_univ_def]

theorem toXF_evalTerm {n : ℕ} (a : Fin n → FS) (t : Monomial n) :
    (toXF (evalTerm a t) : X ν hν) =
      MvPolynomial.aeval (fun i => toXF (a i)) (MvPolynomial.map (algebraMap ℝ ℂ)
        (PolyData.termToMv t)) := by
  rw [evalTerm, toXF_smul, toXF_prodFin, PolyData.termToMv, MvPolynomial.map_monomial,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => _root_.pow_zero _),
    Algebra.smul_def]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [toXF_pow]; rfl

theorem toXF_evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → FS) :
    (toXF (evalPoly p a) : X ν hν) = MvPolynomial.aeval (fun i => toXF (a i)) (PolyData.toMvC p) := by
  induction p with
  | nil => simp [evalPoly, toXF_zero, PolyData.toMvC]
  | cons t p ih =>
    rw [evalPoly, List.map_cons, List.foldr_cons, toXF_add, ← evalPoly, ih, toXF_evalTerm]
    simp only [PolyData.toMvC, PolyData.toMv_cons, map_add]

end Real

end FS

end FourierSeq

end RadiiPolynomial
