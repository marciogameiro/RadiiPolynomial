module

public import RadiiPolynomial.Certificate.Polynomial

/-!
# Finite sequences of rationals

A finitely supported sequence with rational coefficients is a list `a` (`a_k = a.getD k 0`,
`FinSeq.get`).

* The operations that do not depend on a product: `add`, `smul`, the unit `one` (`(1, 0, 0, …)`),
  with their coefficient formulas.
* Polynomials evaluated with a given product `mul` (`pow`, `prodFin`, `evalTerm`, `evalPoly`). If
  `φ : List ℚ → R` maps `add`, `smul`, `one`, `[]` and `mul` to the operations of a real
  commutative algebra `R`, then `φ (evalPoly mul p a) = aeval (φ ∘ a) (toMv p)` (`evalPoly_sound`).

The products themselves (Cauchy, Chebyshev) are in `Certificate/TaylorSeq` and
`Certificate/ChebyshevSeq`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace FinSeq

/-- The coefficient `a_k` (zero beyond the list). -/
def get (a : List ℚ) (k : ℕ) : ℚ := a.getD k 0

theorem get_eq_zero (a : List ℚ) {k : ℕ} (hk : a.length ≤ k) : get a k = 0 := by
  rw [get, List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

theorem get_map_range (m : ℕ) (f : ℕ → ℚ) (k : ℕ) :
    get ((List.range m).map f) k = if k < m then f k else 0 := by
  by_cases hk : k < m
  · simp [get, List.getD_eq_getElem?_getD, hk]
  · simp [get, List.getD_eq_getElem?_getD, hk]

/-- The sum of finite sequences. -/
def add (a b : List ℚ) : List ℚ :=
  (List.range (max a.length b.length)).map fun k => get a k + get b k

/-- A scalar multiple. -/
def smul (c : ℚ) (a : List ℚ) : List ℚ := a.map (c * ·)

/-- The unit `(1, 0, 0, …)`. -/
def one : List ℚ := [1]

theorem get_add (a b : List ℚ) (k : ℕ) : get (add a b) k = get a k + get b k := by
  rw [add, get_map_range]
  split_ifs with hk
  · rfl
  · rw [get_eq_zero a (by omega), get_eq_zero b (by omega), add_zero]

theorem get_smul (c : ℚ) (a : List ℚ) (k : ℕ) : get (smul c a) k = c * get a k := by
  rw [get, get, smul, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[k]? <;> simp

theorem get_one (k : ℕ) : get one k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · rfl
  · rw [get, List.getD_eq_getElem?_getD]; simp [one]

theorem get_nil (k : ℕ) : get [] k = 0 := rfl

/-! ### Polynomials evaluated with a given product -/

section Eval

variable (mul : List ℚ → List ℚ → List ℚ)

/-- Powers for the product `mul`. -/
def pow (a : List ℚ) : ℕ → List ℚ
  | 0 => one
  | e + 1 => mul (pow a e) a

/-- `∏ᵢ fᵢ` for the product `mul`. -/
def prodFin {n : ℕ} (f : Fin n → List ℚ) : List ℚ :=
  (List.finRange n).foldr (fun i acc => mul (f i) acc) one

/-- A monomial `c a^α` evaluated with the product `mul`. -/
def evalTerm {n : ℕ} (a : Fin n → List ℚ) (t : Monomial n) : List ℚ :=
  smul t.coeff (prodFin mul fun i => pow mul (a i) (t.exp i))

/-- A polynomial evaluated with the product `mul`. -/
def evalPoly {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) : List ℚ :=
  (p.map (evalTerm mul a)).foldr add []

variable {R : Type*} [CommRing R] [Algebra ℝ R] (φ : List ℚ → R)
  (hadd : ∀ a b, φ (add a b) = φ a + φ b) (hsmul : ∀ (c : ℚ) a, φ (smul c a) = (c : ℝ) • φ a)
  (hone : φ one = 1) (hnil : φ [] = 0) (hmul : ∀ a b, φ (mul a b) = φ a * φ b)

omit [Algebra ℝ R] in
include hone hmul in
theorem pow_sound (a : List ℚ) (e : ℕ) : φ (pow mul a e) = φ a ^ e := by
  induction e with
  | zero => rw [pow, hone, pow_zero]
  | succ e ih => rw [pow, hmul, ih, pow_succ]

omit [Algebra ℝ R] in
include hone hmul in
theorem prodFin_sound {n : ℕ} (f : Fin n → List ℚ) : φ (prodFin mul f) = ∏ i, φ (f i) := by
  have h : ∀ l : List (Fin n), φ (l.foldr (fun i acc => mul (f i) acc) one) =
      (l.map fun i => φ (f i)).prod := fun l => by
    induction l with
    | nil => exact hone
    | cons i l ih => rw [List.foldr_cons, hmul, ih, List.map_cons, List.prod_cons]
  rw [prodFin, h, Fin.prod_univ_def]

include hsmul hone hmul in
theorem evalTerm_sound {n : ℕ} (a : Fin n → List ℚ) (t : Monomial n) :
    φ (evalTerm mul a t) = MvPolynomial.aeval (fun i => φ (a i)) (PolyData.termToMv t) := by
  rw [evalTerm, hsmul, prodFin_sound mul φ hone hmul, PolyData.termToMv,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [pow_sound mul φ hone hmul]; rfl

include hadd hsmul hone hnil hmul in
theorem evalPoly_sound {n : ℕ} (p : PolyData n) (a : Fin n → List ℚ) :
    φ (evalPoly mul p a) = MvPolynomial.aeval (fun i => φ (a i)) p.toMv := by
  induction p with
  | nil => simp [evalPoly, hnil]
  | cons t p ih =>
    rw [evalPoly, List.map_cons, List.foldr_cons, hadd, ← evalPoly, ih, PolyData.toMv_cons,
      map_add, evalTerm_sound mul φ hsmul hone hmul]

end Eval

end FinSeq

end RadiiPolynomial
