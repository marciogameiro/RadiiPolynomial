module

public import RadiiPolynomial.Abstract.RadiiPoly
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Rat.Cast.Order

/-!
# Exact rational certificates

Matrices on `ℝⁿ = Fin n → ℝ` with the sup norm, and the bridge from exact rational computations
to real inequalities.

* `matCLM M`: a real matrix as a continuous linear map; `matCLM` turns products, differences and the
  identity matrix into composition, difference and the identity map.
* `norm_le_of_forall_abs_le`, `norm_matCLM_le`: the sup norm of a vector is bounded by any bound on
  its entries, and the induced operator norm of a matrix is bounded by any bound on its absolute row
  sums (`‖M‖ = maxᵢ ∑ⱼ |Mᵢⱼ|`).
* `castVec`, `Rat.cast_radiiPoly`, `Rat.cast_matrix_apply`: casting exact rational data to `ℝ`.
* `finMax`, `maxOver`: computable maxima (over `Fin n`, over a finite set of indices), used to
  evaluate bounds exactly; `getD_ofFn`: reading back precomputed tables.
* `lowerTriInv`: the exact inverse of a lower triangular matrix (forward substitution).

The rational inequalities (entry bounds, row-sum bounds, signs of the radii polynomial) are
decidable and are checked by the kernel with `decide +kernel`. Problem theorems consume only the
real inequalities, so other certification backends (e.g. interval arithmetic) can be added later.
-/

@[expose] public section

namespace RadiiPolynomial

open Matrix

variable {m n : ℕ}

/-- A real `m × n` matrix as a continuous linear map `ℝⁿ → ℝᵐ` (sup norms). -/
noncomputable def matCLM (M : Matrix (Fin m) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

@[simp] theorem matCLM_apply (M : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    matCLM M x = M *ᵥ x := rfl

theorem matCLM_mul {l : ℕ} (M : Matrix (Fin l) (Fin m) ℝ) (N : Matrix (Fin m) (Fin n) ℝ) :
    matCLM (M * N) = (matCLM M).comp (matCLM N) := by
  ext1 x; simp [Matrix.mulVec_mulVec]

theorem matCLM_sub (M N : Matrix (Fin m) (Fin n) ℝ) : matCLM (M - N) = matCLM M - matCLM N := by
  ext1 x; simp [Matrix.sub_mulVec]

theorem matCLM_one : matCLM (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext1 x; simp

/-- The sup norm of a vector is at most any nonnegative bound on the absolute values of its
entries. -/
theorem norm_le_of_forall_abs_le (v : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i| ≤ c) :
    ‖v‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun i => by simpa [Real.norm_eq_abs] using h i

/-- The operator norm (induced by the sup norm) of a matrix is at most any nonnegative bound on its
absolute row sums. -/
theorem norm_matCLM_le (M : Matrix (Fin m) (Fin n) ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |M i j| ≤ c) : ‖matCLM M‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  refine norm_le_of_forall_abs_le _ (mul_nonneg hc (norm_nonneg x)) fun i => ?_
  rw [matCLM_apply, Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * x j| ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ c * ‖x‖ := by gcongr; exact h i

/-- The maximum of `0` and the values `f i`, `i : Fin n`; defined by structural recursion so that
the kernel can evaluate it. -/
def finMax : {n : ℕ} → (Fin n → ℚ) → ℚ
  | 0, _ => 0
  | _ + 1, f => max (f 0) (finMax fun i => f i.succ)

theorem le_finMax {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : f i ≤ finMax f := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_max_left _ _
    · exact (ih (fun i => f i.succ) j).trans (le_max_right _ _)

theorem finMax_nonneg {n : ℕ} (f : Fin n → ℚ) : 0 ≤ finMax f := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (ih fun i => f i.succ).trans (le_max_right _ _)

/-- The maximum of `0` and the values `g x`, `x ∈ S`. -/
def maxOver {ι : Type*} (S : Finset ι) (g : ι → ℚ) : ℚ := S.fold max 0 g

theorem le_maxOver {ι : Type*} {S : Finset ι} {g : ι → ℚ} {x : ι} (hx : x ∈ S) : g x ≤ maxOver S g :=
  (Finset.le_fold_max _).2 (Or.inr ⟨x, hx, le_rfl⟩)

theorem maxOver_nonneg {ι : Type*} (S : Finset ι) (g : ι → ℚ) : 0 ≤ maxOver S g :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

/-- From `S / w ≤ K` with `w > 0` to `S ≤ K w` (column bounds stored as quotients). -/
theorem le_mul_of_div_le {S K w : ℚ} (hw : 0 < w) (h : S / w ≤ K) : S ≤ K * w := by
  rwa [div_le_iff₀ hw] at h

/-- Reading back a table built with `Array.ofFn`. -/
theorem getD_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) (d : α) :
    (Array.ofFn f).getD i.val d = f i := by
  simp [Array.getD]

/-- The inverse of a lower triangular matrix `T` (indices `0, …, N`, nonzero diagonal) by forward
substitution: row `m` of `X = T⁻¹` is `X_{m,l} = (δ_{ml} - ∑_{k < m} T_{m,k} X_{k,l}) / T_{m,m}`.
Used to compute approximate inverses exactly; no soundness is needed, since the radii polynomial
theorems hold for any approximate inverse. -/
def lowerTriInv (N : ℕ) (T : ℕ → ℕ → ℚ) : Array (Array ℚ) :=
  (List.range (N + 1)).foldl (fun rows m =>
    rows.push (Array.ofFn fun l : Fin (N + 1) =>
      ((if m = l.val then 1 else 0) -
        ∑ k ∈ Finset.range m, T m k * (rows.getD k #[]).getD l.val 0) / T m m)) #[]

/-- A rational vector cast to a real vector. -/
def castVec {ι : Type*} (v : ι → ℚ) : ι → ℝ := fun i => (v i : ℝ)

@[simp] theorem castVec_apply {ι : Type*} (v : ι → ℚ) (i : ι) : castVec v i = (v i : ℝ) := rfl

/-- Casting the radii polynomial from `ℚ` to `ℝ`. -/
@[simp, norm_cast] theorem Rat.cast_radiiPoly (Y₀ Z₀ Z₁ Z₂ r : ℚ) :
    ((radiiPoly Y₀ Z₀ Z₁ Z₂ r : ℚ) : ℝ) = radiiPoly (Y₀ : ℝ) Z₀ Z₁ Z₂ r := by
  simp [radiiPoly]

/-- Entries of a rational matrix cast to `ℝ`. -/
@[simp] theorem Rat.cast_matrix_apply {p q : Type*} (M : Matrix p q ℚ) (i : p) (j : q) :
    M.map (Rat.castHom ℝ) i j = (M i j : ℝ) := rfl

/-- An enclosure from an approximation with rational data: `|x - e| < r` and `|e - c| + r ≤ δ`
give `|x - c| ≤ δ`. -/
theorem abs_sub_le_of_approx {x : ℝ} {e c r δ : ℚ} (hx : |x - e| < r) (h : |e - c| + r ≤ δ) :
    |x - c| ≤ δ := by
  have h' : |(e : ℝ) - c| + r ≤ δ := by exact_mod_cast h
  have := abs_sub_le x e c
  linarith

end RadiiPolynomial
