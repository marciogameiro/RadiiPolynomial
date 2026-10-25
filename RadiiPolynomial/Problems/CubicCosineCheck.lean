module

public import RadiiPolynomial.Problems.CubicCosineRadii
public import RadiiPolynomial.Certificate.CosineSeq
public import RadiiPolynomial.Certificate.Exact

/-!
# A computable checker for cubic equilibrium problems in cosine series

`CubicCosineData` holds rational data: the eigenvalues `μ`, the Galerkin dimension `m`, the weight
`ν`, the approximate solution `ā` (`ā_k`, `k < m`), the matrix `A_m` and the radii `r₀ ≤ r₁`. From
these data the checker computes exactly (in `ℚ`) all quantities of the bound theorem
`CubicCosine.radii_poly_two_radii`: `ā²`, `ā³`, `|ā|²`, `F(ā)`, the entries of `DF^{(m)}(ā)`,
`E = I - A_m DF^{(m)}(ā)`, `W = (|ā|² ω̃)_F`, `α`, and the bounds `Y₀`, `Z⁽⁰⁾`, `Z⁽¹⁾`, `Z₂(r)`.
`CubicCosineData.check` then only compares numbers: `μ_m ≠ 0`, `p(r₀) < 0`, `p(r₁) < 0` and a few
structural conditions.

`CubicCosineData.verify`: if `D.check` holds and `|μ_k| ≥ |μ_m|` for all `k ≥ m` (an infinite
condition, proved separately for a given family of eigenvalues), then `F` has a zero in the open
ball of radius `r₀` about `ā`, unique in the closed ball of radius `r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

open CosSeq
open FinSeq (get get_eq_zero)

/-- Rational data for a cubic equilibrium problem in cosine series and its approximate solution. -/
structure CubicCosineData where
  /-- the eigenvalues -/
  μ : ℕ → ℚ
  /-- the Galerkin dimension -/
  m : ℕ
  /-- the weight `ν ≥ 1` -/
  ν : ℚ
  /-- the approximate solution: coefficients `0, …, m - 1` -/
  abar : List ℚ
  /-- the approximate inverse `A_m` -/
  A : ℕ → ℕ → ℚ
  /-- the radius `r₀` (existence) -/
  r0 : ℚ
  /-- the radius `r₁` (uniqueness) -/
  r1 : ℚ

namespace CubicCosineData

variable (D : CubicCosineData)

/-- The finite part `{0, …, m - 1}`. -/
def fin : Finset ℕ := Finset.range D.m

/-- The entries `(DF(ā) e_l)_n = μ_n δ_{nl} - 3 (ā² * e_l)_n`, from `ā²`. -/
def DFWith (A2 : List ℚ) (n l : ℕ) : ℚ :=
  (if n = l then D.μ n else 0) - 3 * ChebSeq.mulUnit A2 l n

/-- The quantities from which the bounds are computed: `ā²`, `ā³`, `|ā|²` and the entries of
`DF^{(m)}(ā)`. They are computed either directly (`direct`, used in the proofs) or once, with a
table for `DF^{(m)}(ā)` (`fast`, used by the checker); `fast_eq` shows that both agree. -/
structure Impl where
  /-- `ā²` -/
  A2 : List ℚ
  /-- `ā³` -/
  c3 : List ℚ
  /-- `|ā|²` -/
  S : List ℚ
  /-- the entries of `DF(ā)` -/
  DF : ℕ → ℕ → ℚ

/-- The direct definitions. -/
def direct : Impl :=
  ⟨ChebSeq.mul D.abar D.abar, ChebSeq.mul (ChebSeq.mul D.abar D.abar) D.abar,
    ChebSeq.mul (absSeq D.abar) (absSeq D.abar), D.DFWith (ChebSeq.mul D.abar D.abar)⟩

/-- Each quantity computed once. -/
def fast : Impl :=
  let A2 := ChebSeq.mul D.abar D.abar
  let DFT : Array ℚ := Array.ofFn fun x : Fin (D.m * D.m) =>
    D.DFWith A2 (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2
  ⟨A2, ChebSeq.mul A2 D.abar, ChebSeq.mul (absSeq D.abar) (absSeq D.abar),
    fun n l => if h : n < D.m ∧ l < D.m then
      DFT.getD (finProdFinEquiv (⟨n, h.1⟩, ⟨l, h.2⟩)).val 0 else D.DFWith A2 n l⟩

/-- `F(ā)_k = μ_k ā_k - (ā³)_k`. -/
def Fv (I : Impl) (k : ℕ) : ℚ := D.μ k * get D.abar k - get I.c3 k

/-- `E = I - A_m DF^{(m)}(ā)`. -/
def Emat (I : Impl) (k l : ℕ) : ℚ :=
  (if k = l then 1 else 0) - ∑ n ∈ D.fin, D.A k n * I.DF n l

/-- `W_n = ∑_{m ≤ j ≤ 3m-3} ν^{-j} (S_{j-n} + S_{n+j})`, `S = |ā|²`. -/
def W (I : Impl) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc D.m (3 * D.m - 3), (get I.S (j - n) + get I.S (n + j)) / D.ν ^ j

/-- `α = max {max_{l < m} ν^{-l} ∑_{k < m} |(A_m)_{kl}| ν^k, 1/|μ_m|}`. -/
def alpha : ℚ :=
  max (maxOver D.fin fun l => (∑ k ∈ D.fin, |D.A k l| * D.ν ^ k) / D.ν ^ l) |D.μ D.m|⁻¹

/-- The bound `Y₀`. -/
def Y0 (I : Impl) : ℚ :=
  ∑ k ∈ D.fin, |∑ l ∈ D.fin, D.A k l * D.Fv I l| * D.ν ^ k +
    ∑ k ∈ Finset.Ico D.m (3 * D.m - 2), |D.Fv I k| * D.ν ^ k / |D.μ k|

/-- The bound `Z⁽⁰⁾`. -/
def Z0 (I : Impl) : ℚ :=
  maxOver D.fin fun l => (∑ k ∈ D.fin, |D.Emat I k l| * D.ν ^ k) / D.ν ^ l

/-- The bound `Z⁽¹⁾`. -/
def Z1 (I : Impl) : ℚ :=
  3 * ∑ k ∈ D.fin, (∑ n ∈ D.fin, |D.A k n| * D.W I n) * D.ν ^ k +
    48 * normX D.ν D.abar ^ 2 / |D.μ D.m|

/-- The bound `Z₂(r) = 96 α ‖ā‖ + 48 α r`. -/
def Z2 (r : ℚ) : ℚ := 96 * D.alpha * normX D.ν D.abar + 48 * D.alpha * r

/-- The conditions on the computed bounds. -/
def checkWith (I : Impl) : Prop :=
  1 ≤ D.ν ∧ 1 ≤ D.m ∧ D.abar.length ≤ D.m ∧ D.μ D.m ≠ 0 ∧ 0 < D.r0 ∧ D.r0 ≤ D.r1 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0

instance (I : Impl) : Decidable (D.checkWith I) := by unfold checkWith; infer_instance

/-- The check, with the quantities computed once. -/
def check : Prop := D.checkWith D.fast

instance : Decidable D.check := by unfold check; infer_instance

/-- The table agrees with the direct definitions. -/
theorem fast_eq : D.fast = D.direct := by
  simp only [fast, direct]
  congr 1
  funext n l
  split_ifs with h
  · rw [getD_ofFn]; simp
  · rfl

/-! ### Soundness -/

/-- The problem with the eigenvalues cast to `ℝ`. -/
def toProblem : CubicCosine := ⟨fun k => (D.μ k : ℝ)⟩

variable (hν : 1 ≤ (D.ν : ℝ))

theorem cube_sound :
    Cosine.cube (D.ν : ℝ) hν (toX D.abar) = toX (D.direct.c3) := by
  rw [Cosine.cube, mul3_toX]; rfl

theorem F_sound (k : ℕ) :
    D.toProblem.F (D.ν : ℝ) hν (toX D.abar) k = (D.Fv D.direct k : ℝ) := by
  rw [CubicCosine.F_apply, cube_sound, Fv]
  push_cast
  rfl

theorem DFN_sound (n l : ℕ) :
    D.toProblem.DFN (D.ν : ℝ) hν (toX D.abar) n l = (D.DFWith (D.direct.A2) n l : ℝ) := by
  rw [CubicCosine.DFN, CubicCosine.DF_apply, WeightedLp.sub_apply, CubicCosine.diag_apply,
    CubicCosine.incl_apply, WeightedLp.smul_apply, mul3_single_toX, WeightedL1.single_apply,
    DFWith]
  simp only [toProblem, direct]
  split_ifs <;> push_cast <;> ring

theorem matE_sound (k l : ℕ) :
    D.toProblem.matE (D.ν : ℝ) hν D.m (fun k l => (D.A k l : ℝ)) (toX D.abar) k l =
      (D.Emat D.direct k l : ℝ) := by
  rw [CubicCosine.matE, Emat]
  push_cast
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun n _ => by rw [DFN_sound]; rfl

theorem W_sound (n : ℕ) :
    CubicCosine.W (D.ν : ℝ) hν D.m (toX D.abar) n = (D.W D.direct n : ℝ) := by
  rw [CubicCosine.W, W, absX_toX, mul2_toX]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toX_apply, toX_apply]
  rfl

theorem norm_abar : ‖(toX D.abar : Cosine.X (D.ν : ℝ) hν)‖ = (normX D.ν D.abar : ℝ) :=
  norm_toX D.ν rfl _

/-- **The checker is sound.** If `D.check` holds and `|μ_k| ≥ |μ_m|` for all `k ≥ m`, then `F` has
a zero in the open ball of radius `r₀` about `ā`, and it is the unique zero in the closed ball of
radius `r₁`. -/
theorem verify (htail : ∀ k, D.m ≤ k → |D.μ D.m| ≤ |D.μ k|) (h : D.check) :
    HasIsolatedZero (D.toProblem.F (D.ν : ℝ) hν) (toX D.abar) D.r0 D.r1 := by
  rw [check, fast_eq] at h
  obtain ⟨hν1, hm, hlen, hμm, hr0, hr01, hp0, hp1⟩ := h
  set I := D.direct
  have hνpos : (0 : ℚ) < D.ν := by linarith
  have hwX : ∀ k, (0 : ℚ) < D.ν ^ k := fun k => pow_pos hνpos k
  have habar : ∀ k, D.m ≤ k → (toX D.abar : Cosine.X (D.ν : ℝ) hν) k = 0 := fun k hk =>
    toX_eq_zero _ (hlen.trans hk)
  have hμ : D.toProblem.TailCond D.m :=
    ⟨by simpa [toProblem] using hμm, fun k hk => by
      simp only [toProblem]; exact_mod_cast htail k hk⟩
  have hμabs : ∀ k, |D.toProblem.μ k| = ((|D.μ k| : ℚ) : ℝ) := fun k => by
    simp [toProblem]
  -- `Y₀`
  have hY : ∑ k ∈ Finset.range D.m, |∑ l ∈ Finset.range D.m, (D.A k l : ℝ) *
        D.toProblem.F (D.ν : ℝ) hν (toX D.abar) l| * (D.ν : ℝ) ^ k +
      ∑ k ∈ Finset.Ico D.m (3 * D.m - 2), |D.toProblem.F (D.ν : ℝ) hν (toX D.abar) k| *
        (D.ν : ℝ) ^ k / |D.toProblem.μ k| ≤ (D.Y0 I : ℝ) := by
    simp only [F_sound, hμabs]
    rw [Y0, fin]
    push_cast
    exact le_rfl
  -- `Z⁽⁰⁾`
  have hZ0 : ∀ l ∈ Finset.range D.m, ∑ k ∈ Finset.range D.m,
      |D.toProblem.matE (D.ν : ℝ) hν D.m (fun k l => (D.A k l : ℝ)) (toX D.abar) k l| *
        (D.ν : ℝ) ^ k ≤ (D.Z0 I : ℝ) * (D.ν : ℝ) ^ l := by
    intro l hl
    simp only [matE_sound]
    have := le_mul_of_div_le (hwX l) (le_maxOver (g := fun l =>
      (∑ k ∈ D.fin, |D.Emat I k l| * D.ν ^ k) / D.ν ^ l) hl)
    exact_mod_cast this
  -- `Z⁽¹⁾`
  have hZ1 : 3 * ∑ k ∈ Finset.range D.m, (∑ n ∈ Finset.range D.m,
      |(D.A k n : ℝ)| * CubicCosine.W (D.ν : ℝ) hν D.m (toX D.abar) n) * (D.ν : ℝ) ^ k +
      48 * ‖(toX D.abar : Cosine.X (D.ν : ℝ) hν)‖ ^ 2 / |D.toProblem.μ D.m| ≤ (D.Z1 I : ℝ) := by
    simp only [W_sound, norm_abar, hμabs]
    rw [Z1, fin]
    push_cast
    exact le_rfl
  -- `Z₂`
  have hKA : ∀ l ∈ Finset.range D.m, ∑ k ∈ Finset.range D.m, |(D.A k l : ℝ)| * (D.ν : ℝ) ^ k ≤
      (D.alpha : ℝ) * (D.ν : ℝ) ^ l := by
    intro l hl
    have := le_mul_of_div_le (K := D.alpha) (hwX l) ((le_maxOver (g := fun l =>
      (∑ k ∈ D.fin, |D.A k l| * D.ν ^ k) / D.ν ^ l) hl).trans (le_max_left _ _))
    exact_mod_cast this
  have hαμ : |D.toProblem.μ D.m|⁻¹ ≤ (D.alpha : ℝ) := by
    rw [hμabs]
    have : |D.μ D.m|⁻¹ ≤ D.alpha := le_max_right _ _
    exact_mod_cast this
  have hZ2 : ∀ r : ℚ, 96 * (D.alpha : ℝ) * ‖(toX D.abar : Cosine.X (D.ν : ℝ) hν)‖ +
      48 * (D.alpha : ℝ) * (r : ℝ) ≤ (D.Z2 r : ℝ) := fun r => by
    rw [norm_abar, Z2]
    push_cast
    exact le_rfl
  have hp0' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp0
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  have hp1' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp1
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  exact D.toProblem.radii_poly_two_radii (toX D.abar) hm habar hμ (fun k l => (D.A k l : ℝ))
    (by exact_mod_cast hr0) (by exact_mod_cast hr01) hY hZ0 hZ1 hKA hαμ (hZ2 D.r0) (hZ2 D.r1)
    hp0' hp1'

end CubicCosineData

end RadiiPolynomial
