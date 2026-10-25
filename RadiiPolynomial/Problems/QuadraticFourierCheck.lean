module

public import RadiiPolynomial.Problems.QuadraticFourierRadii
public import RadiiPolynomial.Certificate.FourierSeq
public import RadiiPolynomial.Certificate.Exact

/-!
# A computable checker for forced quadratic problems in Fourier series

`QuadraticFourierData` holds exact data, with complex numbers as pairs of rationals (`QC`): the
eigenvalues `λ`, the forcing `g` (only `g_n`, `|n| ≤ N`, is used), the truncation dimension `N`, the weight `ν`, the
approximate solution `ā_{-N}, …, ā_N`, the matrix `A_N = (A_{kl})_{|k|,|l| ≤ N}` and the radii
`r₀ ≤ r₁`. From these data the checker computes all quantities of the bound theorem
`QuadraticFourier.radii_poly_two_radii`: `F(ā)` (`Fv`), the entries of `DF^{(N)}(ā)` (`DFe`),
`E = I - A_N DF^{(N)}(ā)`, and the bounds `Y₀`, `Z₀`, `Z₁`, `Z₂`. Sums and products are exact; each
modulus `|z|` is replaced by a rational upper bound `QC.absUp z`, and in denominators by a rational
lower bound (`QC.absLo`): `κ = absLo(λ_{N+1})` is the tail constant, and `|λ_n|` in `Y₀` is bounded
below by `max (absLo λ_n) κ`. `QuadraticFourierData.check` then only compares numbers: `κ > 0`,
`p(r₀) < 0`, `p(r₁) < 0` and a few structural conditions.

`QuadraticFourierData.verify`: if `D.check` holds and `|λ_n| ≥ |λ_{N+1}|` for all `|n| > N` (an
infinite condition, stated for `x² + y²` and proved separately for a given family of eigenvalues),
then `F` has a zero in the open ball of radius `r₀` about `ā`, unique in the closed ball of radius
`r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

open Fourier FourierSeq

/-- Exact data for a forced quadratic problem in Fourier series and its approximate solution. -/
structure QuadraticFourierData where
  /-- the eigenvalues -/
  lam : ℤ → QC
  /-- the forcing (truncated to `|n| ≤ N`, `gN`) -/
  g : ℤ → QC
  /-- the truncation dimension -/
  N : ℕ
  /-- the weight `ν ≥ 1` -/
  ν : ℚ
  /-- the approximate solution: coefficients `-N, …, N` -/
  abar : List QC
  /-- the approximate inverse `A_N` -/
  A : ℤ → ℤ → QC
  /-- the radius `r₀` (existence) -/
  r0 : ℚ
  /-- the radius `r₁` (uniqueness) -/
  r1 : ℚ

namespace QuadraticFourierData

variable (D : QuadraticFourierData)

/-- The forcing truncated to `|n| ≤ N`. -/
def gN (n : ℤ) : QC := if n.natAbs ≤ D.N then D.g n else 0

theorem gN_eq_zero {n : ℤ} (hn : D.N < n.natAbs) : D.gN n = 0 := by
  rw [gN, ite_eq_right (by omega)]

/-- The entries `(DF(ā) e_l)_n = λ_n δ_{nl} - 2 ā_{n-l}`. -/
def DFe (n l : ℤ) : QC := (if n = l then D.lam n else 0) - (2 : ℚ) • get D.N D.abar (n - l)

/-- `F(ā)_n = λ_n ā_n - (ā * ā)_n - g_n`. -/
def Fv (n : ℤ) : QC :=
  QC.mul (D.lam n) (get D.N D.abar n) - conv D.N D.abar D.abar n - D.gN n

/-- `E = I - A_N DF^{(N)}(ā)`. -/
def Emat (k l : ℤ) : QC :=
  (if k = l then (1, 0) else 0) - ∑ n ∈ center D.N, QC.mul (D.A k n) (D.DFe n l)

/-- The tail constant `κ`, a lower bound for `|λ_{N+1}|`. -/
def kappa : ℚ := QC.absLo (D.lam (D.N + 1))

/-- A lower bound for `|λ_n|`, `|n| > N`. -/
def lamLo (n : ℤ) : ℚ := max (QC.absLo (D.lam n)) D.kappa

/-- The weighted column sums `∑_{|k| ≤ N} |A_{kl}| ν^{|k|}` (upper bounds). -/
def colA (l : ℤ) : ℚ := ∑ k ∈ center D.N, QC.absUp (D.A k l) * D.ν ^ k.natAbs

/-- `α = max {max_l ν^{-|l|} colA_l, 1/κ}`, a bound for `A` on `ℓ¹_ν`. -/
def alpha : ℚ := max (maxOver (center D.N) fun l => D.colA l / D.ν ^ l.natAbs) D.kappa⁻¹

/-- `β = max_l ν^{|l|-2N-2} colA_l`, a bound for the column norm of `A_N Γ`. -/
def beta : ℚ := maxOver (center D.N) fun l => D.colA l * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)

/-- The bound `Y₀`. -/
def Y0 : ℚ :=
  ∑ k ∈ center D.N, QC.absUp (∑ l ∈ center D.N, QC.mul (D.A k l) (D.Fv l)) * D.ν ^ k.natAbs +
    ∑ k ∈ center (2 * D.N) \ center D.N, QC.absUp (D.Fv k) * D.ν ^ k.natAbs / D.lamLo k

/-- The bound `Z₀`. -/
def Z0 : ℚ :=
  maxOver (center D.N) fun l =>
    (∑ k ∈ center D.N, QC.absUp (D.Emat k l) * D.ν ^ k.natAbs) / D.ν ^ l.natAbs

/-- The bound `Z₁ = 2 (β + 1/κ) ‖ā‖`. -/
def Z1 : ℚ := 2 * (D.beta + D.kappa⁻¹) * normUp D.ν D.N D.abar

/-- The bound `Z₂ = 2 α`. -/
def Z2 : ℚ := 2 * D.alpha

/-- The conditions on the computed bounds. -/
def check : Prop :=
  1 ≤ D.ν ∧ 0 < D.kappa ∧ 0 < D.r0 ∧ D.r0 ≤ D.r1 ∧
    radiiPoly D.Y0 D.Z0 D.Z1 D.Z2 D.r0 < 0 ∧ radiiPoly D.Y0 D.Z0 D.Z1 D.Z2 D.r1 < 0

instance : Decidable D.check := by unfold check; infer_instance

/-! ### Soundness -/

/-- The problem with the data cast to `ℂ`. -/
noncomputable def toProblem : QuadraticFourier where
  lam n := QC.toC (D.lam n)
  g := Finsupp.onFinset (center D.N) (fun n => QC.toC (D.gN n)) fun n hn => by
    by_contra h
    rw [mem_center, not_le] at h
    exact hn (by rw [D.gN_eq_zero h, map_zero])

theorem toProblem_lam (n : ℤ) : D.toProblem.lam n = QC.toC (D.lam n) := rfl

theorem toProblem_g (n : ℤ) : D.toProblem.g n = QC.toC (D.gN n) := rfl

variable (hν : 1 ≤ (D.ν : ℝ))

theorem F_sound (n : ℤ) :
    D.toProblem.F (D.ν : ℝ) hν (toX D.N D.abar) n = QC.toC (D.Fv n) := by
  rw [QuadraticFourier.F_apply, toX_mul_apply, toX_apply, toProblem_g, toProblem_lam, Fv, map_sub,
    map_sub, QC.toC_mul]

theorem DFN_sound (n l : ℤ) :
    D.toProblem.DFN (D.ν : ℝ) hν (toX D.N D.abar) n l = QC.toC (D.DFe n l) := by
  rw [QuadraticFourier.DFN, QuadraticFourier.DF_apply_coeff, mul_single_apply,
    WeightedL1.single_apply, toX_apply, toProblem_lam, DFe, map_sub, QC.toC_smul]
  split_ifs with h
  · subst h; simp
  · simp

theorem matE_sound (k l : ℤ) :
    D.toProblem.matE (D.ν : ℝ) hν D.N (fun k l => QC.toC (D.A k l)) (toX D.N D.abar) k l =
      QC.toC (D.Emat k l) := by
  rw [QuadraticFourier.matE, Emat, map_sub, map_sum]
  congr 1
  · split_ifs <;> simp [QC.toC_one]
  · exact Finset.sum_congr rfl fun n _ => by rw [QC.toC_mul, DFN_sound]

/-- **The checker is sound.** If `D.check` holds and `|λ_n| ≥ |λ_{N+1}|` for all `|n| > N`, then
`F` has a zero in the open ball of radius `r₀` about `ā`, and it is the unique zero in the closed
ball of radius `r₁`. -/
theorem verify
    (htail : ∀ n : ℤ, D.N < n.natAbs → QC.normSq (D.lam (D.N + 1)) ≤ QC.normSq (D.lam n))
    (h : D.check) :
    HasIsolatedZero (D.toProblem.F (D.ν : ℝ) hν) (toX D.N D.abar) D.r0 D.r1 := by
  obtain ⟨hν1, hκ0, hr0, hr01, hp0, hp1⟩ := h
  have hνpos : (0 : ℚ) < D.ν := by linarith
  have hw : ∀ n : ℤ, (0 : ℚ) < D.ν ^ n.natAbs := fun n => pow_pos hνpos _
  have hνR : (0 : ℝ) ≤ (D.ν : ℝ) := by exact_mod_cast hνpos.le
  -- the tail condition
  have hκ : D.toProblem.TailCond D.N (D.kappa : ℝ) :=
    ⟨by exact_mod_cast hκ0, fun n hn =>
      (QC.absLo_le_norm_toC _).trans (QC.norm_toC_le_of_normSq_le (htail n hn))⟩
  have hlamLo : ∀ n ∉ center D.N,
      (0 : ℝ) < D.lamLo n ∧ (D.lamLo n : ℝ) ≤ ‖D.toProblem.lam n‖ := fun n hn =>
    ⟨by exact_mod_cast hκ0.trans_le (le_max_right _ _), by
      rw [lamLo, Rat.cast_max]
      exact max_le (QC.absLo_le_norm_toC _) (hκ.le hn)⟩
  -- `Y₀`
  have hY : ∑ k ∈ center D.N, ‖∑ l ∈ center D.N, QC.toC (D.A k l) *
        D.toProblem.F (D.ν : ℝ) hν (toX D.N D.abar) l‖ * (D.ν : ℝ) ^ k.natAbs +
      ∑ k ∈ center (2 * D.N) \ center D.N, ‖D.toProblem.F (D.ν : ℝ) hν (toX D.N D.abar) k‖ *
        (D.ν : ℝ) ^ k.natAbs / ‖D.toProblem.lam k‖ ≤ (D.Y0 : ℝ) := by
    simp only [F_sound]
    rw [Y0]
    push_cast
    refine add_le_add (Finset.sum_le_sum fun k _ => ?_) (Finset.sum_le_sum fun k hk => ?_)
    · have : ∑ l ∈ center D.N, QC.toC (D.A k l) * QC.toC (D.Fv l) =
          QC.toC (∑ l ∈ center D.N, QC.mul (D.A k l) (D.Fv l)) := by
        rw [map_sum]; simp only [QC.toC_mul]
      rw [this]
      exact mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _) (pow_nonneg hνR _)
    · rw [Finset.mem_sdiff] at hk
      obtain ⟨h1, h2⟩ := hlamLo k hk.2
      exact div_le_div₀ (mul_nonneg (by exact_mod_cast QC.absUp_nonneg _) (pow_nonneg hνR _))
        (mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _) (pow_nonneg hνR _)) h1 h2
  -- `Z₀`
  have hZ0 : ∀ l ∈ center D.N, ∑ k ∈ center D.N,
      ‖D.toProblem.matE (D.ν : ℝ) hν D.N (fun k l => QC.toC (D.A k l)) (toX D.N D.abar) k l‖ *
        (D.ν : ℝ) ^ k.natAbs ≤ (D.Z0 : ℝ) * (D.ν : ℝ) ^ l.natAbs := by
    intro l hl
    simp only [matE_sound]
    have h1 := le_mul_of_div_le (hw l) (le_maxOver (g := fun l =>
      (∑ k ∈ center D.N, QC.absUp (D.Emat k l) * D.ν ^ k.natAbs) / D.ν ^ l.natAbs) hl)
    have h2 : ∑ k ∈ center D.N, ‖QC.toC (D.Emat k l)‖ * (D.ν : ℝ) ^ k.natAbs ≤
        ((∑ k ∈ center D.N, QC.absUp (D.Emat k l) * D.ν ^ k.natAbs : ℚ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _) (pow_nonneg hνR _)
    exact h2.trans (by exact_mod_cast h1)
  -- the column sums of `A_N`
  have hcol : ∀ l, ∑ k ∈ center D.N, ‖QC.toC (D.A k l)‖ * (D.ν : ℝ) ^ k.natAbs ≤
      (D.colA l : ℝ) := fun l => by
    rw [colA]
    push_cast
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (QC.norm_toC_le_absUp _) (pow_nonneg hνR _)
  -- `Z₁`
  have hβ : ∀ l ∈ center D.N,
      (∑ k ∈ center D.N, ‖QC.toC (D.A k l)‖ * (D.ν : ℝ) ^ k.natAbs) * (D.ν : ℝ) ^ l.natAbs ≤
        (D.beta : ℝ) * (D.ν : ℝ) ^ (2 * D.N + 2) := by
    intro l hl
    have h1 : D.colA l * D.ν ^ l.natAbs ≤ D.beta * D.ν ^ (2 * D.N + 2) :=
      le_mul_of_div_le (pow_pos hνpos _) (le_maxOver (g := fun l =>
        D.colA l * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)) hl)
    calc (∑ k ∈ center D.N, ‖QC.toC (D.A k l)‖ * (D.ν : ℝ) ^ k.natAbs) * (D.ν : ℝ) ^ l.natAbs
        ≤ (D.colA l : ℝ) * (D.ν : ℝ) ^ l.natAbs :=
          mul_le_mul_of_nonneg_right (hcol l) (pow_nonneg hνR _)
      _ ≤ (D.beta : ℝ) * (D.ν : ℝ) ^ (2 * D.N + 2) := by exact_mod_cast h1
  have hβ0 : (0 : ℝ) ≤ D.beta := by exact_mod_cast maxOver_nonneg _ _
  have hZ1 : 2 * ((D.beta : ℝ) + (D.kappa : ℝ)⁻¹) * ‖(toX D.N D.abar : X (D.ν : ℝ) hν)‖ ≤
      (D.Z1 : ℝ) := by
    rw [Z1]
    push_cast
    exact mul_le_mul_of_nonneg_left (norm_toX_le D.ν rfl _ _)
      (mul_nonneg zero_le_two (add_nonneg hβ0 (inv_nonneg.2 hκ.1.le)))
  -- `Z₂`
  have hKA : ∀ l ∈ center D.N, ∑ k ∈ center D.N, ‖QC.toC (D.A k l)‖ * (D.ν : ℝ) ^ k.natAbs ≤
      (D.alpha : ℝ) * (D.ν : ℝ) ^ l.natAbs := by
    intro l hl
    have h1 := le_mul_of_div_le (K := D.alpha) (hw l) ((le_maxOver (g := fun l =>
      D.colA l / D.ν ^ l.natAbs) hl).trans (le_max_left _ _))
    exact (hcol l).trans (by exact_mod_cast h1)
  have hακ : (D.kappa : ℝ)⁻¹ ≤ (D.alpha : ℝ) := by
    have : D.kappa⁻¹ ≤ D.alpha := le_max_right _ _
    exact_mod_cast this
  have hZ2 : 2 * (D.alpha : ℝ) ≤ (D.Z2 : ℝ) := by rw [Z2]; push_cast; exact le_rfl
  have hp0' : radiiPoly (D.Y0 : ℝ) D.Z0 D.Z1 D.Z2 D.r0 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp0
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  have hp1' : radiiPoly (D.Y0 : ℝ) D.Z0 D.Z1 D.Z2 D.r1 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp1
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  exact D.toProblem.radii_poly_two_radii (toX D.N D.abar) (suppLe_toX _ _)
    (fun n hn => by rw [toProblem_g, D.gN_eq_zero hn, map_zero]) hκ
    (fun k l => QC.toC (D.A k l)) (by exact_mod_cast hr0) (by exact_mod_cast hr01) hY hZ0 hβ hZ1
    hKA hακ hZ2 hp0' hp1'

end QuadraticFourierData

end RadiiPolynomial
