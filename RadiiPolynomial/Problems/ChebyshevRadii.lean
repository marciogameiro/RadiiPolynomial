module

public import RadiiPolynomial.Problems.ChebyshevBVP
public import RadiiPolynomial.BlockTail.FiniteTail
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# The radii polynomial theorem for Chebyshev boundary value problems

Let `F : X_ν^n → Y_ν^n` be the operator of a boundary value problem (`ChebBVP.F`), `ā ∈ X_ν^n`
with `(āⱼ)_k = 0` for `k > N`, and `A^{(N)}` a finite matrix (indexed by `(j, m), (i, l)` with
`m, l ≤ N`). With `s = {0, …, N}`:

* `opA`: the approximate inverse `A : Y → X`, the finite block `A^{(N)}` and the tail `1/(2k)`;
* `opD`: the approximate derivative `A† : X → Y`, the finite block of `DF(ā)` (`DFN`) and the tail
  `2k`;
* `DFN j m i l = (DF(ā) e_{i,l})_{j,m}`, the matrix of `DF(ā)`; for `l > N` these are the entries of
  the matrix `𝒞`.

The bounds are stated in column form: each of `Y₀`, `Z₀`, `Z₁`, `Z₂(r)` is any number dominating
the corresponding finite expression, so the theorem applies in particular to the exact maxima.

* `norm_opA_F_le` (`Y₀`), `norm_id_sub_opA_opD_le` (`Z₀`), `norm_opA_DF_sub_opD_le` (`Z₁`),
  `norm_opA_DF_sub_DF_le` (`Z₂(r)`), `opA_injective`;
* `radii_poly_two_radii`: if `p(r₀) < 0` and `p(r₁) < 0`, `F` has a zero in the open ball of
  radius `r₀` about `ā`, unique in the closed ball of radius `r₁` (`HasIsolatedZero`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace ChebBVP

open Chebyshev MvPolynomial Metric

variable {n : ℕ} (P : ChebBVP n) {ν : ℝ} {hν : 1 ≤ ν}

/-- The tail `1/(2k)` of the approximate inverse. -/
noncomputable def tailA (k : ℕ) : ℝ := (2 * k : ℝ)⁻¹

/-- The tail `2k` of the approximate derivative. -/
def tailD (k : ℕ) : ℝ := 2 * k

theorem tailA_bound (N : ℕ) (l : ℕ) (hl : l ∉ Finset.range (N + 1)) :
    ‖tailA l‖ * weights ν hν l ≤ 1 * weightsY ν hν l := by
  have hl0 : l ≠ 0 := by rw [Finset.mem_range] at hl; omega
  have hl' : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl0
  simp only [weights_apply, weightsY_apply, hl0, ↓reduceIte, tailA, one_mul, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  field_simp
  exact le_rfl

theorem tailD_bound (N : ℕ) (l : ℕ) (hl : l ∉ Finset.range (N + 1)) :
    ‖tailD l‖ * weightsY ν hν l ≤ 1 * weights ν hν l := by
  have hl0 : l ≠ 0 := by rw [Finset.mem_range] at hl; omega
  have hl' : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl0
  simp only [weights_apply, weightsY_apply, hl0, ↓reduceIte, tailD, one_mul, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity)]
  field_simp
  exact le_rfl

variable (ν hν)

/-- The approximate inverse `A : Y → X`: finite block `A^{(N)}`, tail `1/(2k)`. -/
noncomputable def opA (N : ℕ) (AN : Fin n → ℕ → Fin n → ℕ → ℝ) :
    (Fin n → Y ν hν) →L[ℝ] (Fin n → X ν hν) :=
  FiniteTail.op (FiniteTail.crudeBound (s := Finset.range (N + 1)) (M := AN) (tl := tailA)
    (ω := weights ν hν) (ω' := weightsY ν hν) zero_le_one (tailA_bound N))

/-- The matrix of `DF(ā)`: `DFN j m i l = (DF(ā) e_{i,l})_{j,m}`. -/
noncomputable def DFN (abar : Fin n → X ν hν) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℝ :=
  P.DF ν hν abar (FiniteTail.unitVec i l) j m

/-- The approximate derivative `A† : X → Y`: finite block of `DF(ā)`, tail `2k`. -/
noncomputable def opD (N : ℕ) (abar : Fin n → X ν hν) :
    (Fin n → X ν hν) →L[ℝ] (Fin n → Y ν hν) :=
  FiniteTail.op (FiniteTail.crudeBound (s := Finset.range (N + 1)) (M := P.DFN ν hν abar)
    (tl := tailD) (ω := weightsY ν hν) (ω' := weights ν hν) zero_le_one (tailD_bound N))

/-- `E = I - A^{(N)} DF^{(N)}(ā)`. -/
noncomputable def matE (N : ℕ) (AN : Fin n → ℕ → Fin n → ℕ → ℝ) (abar : Fin n → X ν hν)
    (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℝ :=
  (if j = i ∧ m = l then 1 else 0) -
    ∑ i', ∑ l' ∈ Finset.range (N + 1), AN j m i' l' * P.DFN ν hν abar i' l' i l

/-- `A^{(N)} 𝒞`: for `k > N`, the entries of `A^{(N)}` times the tail columns of `DF(ā)`. -/
noncomputable def matAC (N : ℕ) (AN : Fin n → ℕ → Fin n → ℕ → ℝ) (abar : Fin n → X ν hν)
    (j : Fin n) (m : ℕ) (i : Fin n) (k : ℕ) : ℝ :=
  ∑ i', ∑ l' ∈ Finset.range (N + 1), AN j m i' l' * P.DFN ν hν abar i' l' i k

/-- `b^{ji} = ∂ᵢ φ_j(ā)`. -/
noncomputable def bmat (abar : Fin n → X ν hν) (j i : Fin n) : X ν hν :=
  aeval abar (pderiv i (P.f j))

/-- `Θᵢ(r) = ∑_{l,m} |∂_l ∂_m fᵢ|(‖ā₁‖ + r, …, ‖āₙ‖ + r)`. -/
noncomputable def Theta (abar : Fin n → X ν hν) (i : Fin n) (r : ℝ) : ℝ :=
  ∑ l, ∑ m, absEval (pderiv l (pderiv m (P.f i))) fun k => ‖abar k‖ + r

variable {ν hν}

/-! ### The bounds -/

section Bounds

variable [NeZero n] (abar : Fin n → X ν hν) {N : ℕ} (AN : Fin n → ℕ → Fin n → ℕ → ℝ)

omit [NeZero n] in
/-- `F(ā)_k = 0` for `k > M N + 1`. -/
theorem F_suppLe (habar : ∀ i, SuppLe (abar i) N) {M : ℕ} (hM : 1 ≤ M)
    (hdeg : ∀ j, (P.f j).totalDegree ≤ M) (j : Fin n) {k : ℕ} (hk : M * N + 1 < k) :
    P.F ν hν abar j k = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  have hc := suppLe_aeval (P.f j) abar habar (hdeg j)
  rw [P.F_apply_of_ne_zero ν hν abar j hk0, habar j k (by omega), hc (k + 1) (by omega),
    hc (k - 1) (by omega)]
  ring

/-- The bound `Y₀`. -/
theorem norm_opA_F_le (habar : ∀ i, SuppLe (abar i) N) {M : ℕ} (hM : 1 ≤ M)
    (hdeg : ∀ j, (P.f j).totalDegree ≤ M) {Y₀ : ℝ}
    (hY₀ : ∀ j, ∑ k ∈ Finset.range (N + 1),
        |∑ i, ∑ l ∈ Finset.range (N + 1), AN j k i l * P.F ν hν abar i l| * weights ν hν k +
        ∑ k ∈ Finset.Ico (N + 1) (M * N + 2), |P.F ν hν abar j k| * (ν ^ k / k) ≤ Y₀) :
    ‖opA ν hν N AN (P.F ν hν abar)‖ ≤ Y₀ := by
  have hν0 := nu_pos hν
  have hY₀nn : 0 ≤ Y₀ := le_trans (add_nonneg
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) ((weights ν hν).pos k).le)
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (by positivity))) (hY₀ 0)
  have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  refine (pi_norm_le_iff_of_nonneg hY₀nn).2 fun j => ?_
  rw [WeightedL1.norm_eq_tsum]
  have hsupp : ∀ k ∉ Finset.range (M * N + 2),
      weights ν hν k * ‖opA ν hν N AN (P.F ν hν abar) j k‖ = 0 := fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [opA, FiniteTail.op_apply, ite_eq_right (by rw [Finset.mem_range]; omega),
      P.F_suppLe abar habar hM hdeg j (by omega), mul_zero, norm_zero, mul_zero]
  rw [tsum_eq_sum hsupp, ← Finset.sum_range_add_sum_Ico _ (by omega : N + 1 ≤ M * N + 2)]
  refine le_of_eq_of_le ?_ (hY₀ j)
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [opA, FiniteTail.op_apply, ite_eq_left hk, Real.norm_eq_abs, mul_comm]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hk0 : k ≠ 0 := by omega
    have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    rw [opA, FiniteTail.op_apply, ite_eq_right (by rw [Finset.mem_range]; omega), weights_apply,
      ite_eq_right hk0, Real.norm_eq_abs, abs_mul, tailA, abs_of_pos (by positivity : (0 : ℝ) < (2 * (k : ℝ))⁻¹)]
    field_simp

/-- The bound `Z₀`. -/
theorem norm_id_sub_opA_opD_le {KE : Fin n → Fin n → ℝ} (hKE0 : ∀ j i, 0 ≤ KE j i)
    (hKE : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |P.matE ν hν N AN abar j m i l| * weights ν hν m ≤ KE j i * weights ν hν l)
    {Z₀ : ℝ} (hZ₀ : ∀ j, ∑ i, KE j i ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ _ - (opA ν hν N AN).comp (P.opD ν hν N abar)‖ ≤ Z₀ := by
  have hE : FiniteTail.Bound (Finset.range (N + 1)) (P.matE ν hν N AN abar) (fun _ => 0)
      (weights ν hν) (weights ν hν) KE :=
    ⟨hKE0, fun j i l hl => by simpa [Real.norm_eq_abs] using hKE j i l hl, fun j l _ => by
      rw [norm_zero, zero_mul]
      exact mul_nonneg (hKE0 j j) ((weights ν hν).pos l).le⟩
  have hZ₀nn : 0 ≤ Z₀ := (Finset.sum_nonneg fun i _ => hKE0 0 i).trans (hZ₀ 0)
  rw [opA, opD, FiniteTail.id_sub_op_comp_op _ _ hE (fun j m i l _ _ => rfl) (fun m hm => by
    have hm0 : m ≠ 0 := by rw [Finset.mem_range] at hm; omega
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    simp only [tailA, tailD]
    field_simp
    ring)]
  exact FiniteTail.norm_op_le hE hZ₀nn hZ₀

/-! #### The columns of `𝒞` -/

omit [NeZero n] in
/-- The coefficients of `DF(a) h`. -/
theorem DF_apply_coeff (a h : Fin n → X ν hν) (j : Fin n) (m : ℕ) :
    P.DF ν hν a h j m = (if m = 0 then -(P.bcLin ν hν j h) else 0) + 2 * m * h j m +
      P.L * (if m = 0 then 0 else
        (polyDeriv (P.f j) a h) (m + 1) - (polyDeriv (P.f j) a h) (m - 1)) := by
  simp only [DF, ContinuousLinearMap.pi_apply, add_apply, neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.proj_apply, WeightedLp.add_apply,
    WeightedLp.neg_apply, WeightedLp.smul_apply, e0_apply, diffOp_apply, shiftOp_apply]
  split_ifs <;> ring

omit [NeZero n] in
theorem boundaryEval_single (t : ℝ) (ht : |t| ≤ 1) (q : ℕ) :
    boundaryEval ν hν t ht (WeightedL1.single q 1) = evalWeight t q := by
  rw [boundaryEval_apply, tsum_eq_single q fun k hk => by simp [WeightedL1.single_apply, hk]]
  simp

omit [NeZero n] in
theorem bcLin_unitVec (j i : Fin n) (q : ℕ) :
    P.bcLin ν hν j (FiniteTail.unitVec i q) =
      P.Bm j i * evalWeight (-1) q + P.Bp j i * evalWeight 1 q := by
  rw [bcLin, sum_apply, Finset.sum_eq_single i (fun i' _ hi' => by
    simp [FiniteTail.unitVec, hi']) (by simp)]
  simp [FiniteTail.unitVec, boundaryEval_single]

omit [NeZero n] in
/-- Row `0` of `𝒞`: `-((B₋)_{ji} 2 (-1)^q + (B₊)_{ji} 2)` for `q ≥ 1`. -/
theorem DFN_row_zero (abar : Fin n → X ν hν) (j i : Fin n) {q : ℕ} (hq : q ≠ 0) :
    P.DFN ν hν abar j 0 i q = -(P.Bm j i * (2 * (-1) ^ q) + P.Bp j i * 2) := by
  rw [DFN, DF_apply_coeff, bcLin_unitVec]
  simp [evalWeight, hq]

omit [NeZero n] in
theorem unitVec_apply (i j : Fin n) (l m : ℕ) :
    (FiniteTail.unitVec (𝕜 := ℝ) (ω := weights ν hν) i l j) m = if j = i ∧ m = l then 1 else 0 := by
  by_cases hji : j = i
  · subst hji; simp [FiniteTail.unitVec, WeightedL1.single_apply]
  · simp [FiniteTail.unitVec, hji]

omit [NeZero n] in
/-- `Dφ_j(ā) e_{i,l} = bʲⁱ * e_l`. -/
theorem polyDeriv_unitVec (abar : Fin n → X ν hν) (j i : Fin n) (l : ℕ) :
    polyDeriv (P.f j) abar (FiniteTail.unitVec i l) =
      P.bmat ν hν abar j i * WeightedL1.single l 1 := by
  rw [polyDeriv_apply, Finset.sum_eq_single i (fun i' _ hi' => by
    simp [FiniteTail.unitVec, hi']) (by simp)]
  simp [FiniteTail.unitVec, bmat]

omit [NeZero n] in
theorem bcLin_apply (a : Fin n → X ν hν) (j : Fin n) :
    P.bcLin ν hν j a = ∑ i, (P.Bm j i * evalMinus ν hν (a i) + P.Bp j i * evalPlus ν hν (a i)) := by
  simp [bcLin]

omit [NeZero n] in
/-- Rows `1 ≤ l ≤ N` of `𝒞` vanish for `q ≥ M N + 2`. -/
theorem DFN_tail_zero (abar : Fin n → X ν hν) {N : ℕ} (habar : ∀ i, SuppLe (abar i) N) {M : ℕ}
    (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M) (j i : Fin n) {l q : ℕ} (hl0 : l ≠ 0)
    (hl : l ≤ N) (hq : M * N + 2 ≤ q) : P.DFN ν hν abar j l i q = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hMN : (M - 1) * N + N = M * N := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM]
  have hb : SuppLe (P.bmat ν hν abar j i) ((M - 1) * N) :=
    suppLe_aeval (pderiv i (P.f j)) abar habar (totalDegree_pderiv_le _ i (hdeg j))
  have hg : polyDeriv (P.f j) abar (FiniteTail.unitVec i q) =
      P.bmat ν hν abar j i * WeightedL1.single q 1 := by
    rw [polyDeriv_apply, Finset.sum_eq_single i (fun i' _ hi' => by
      simp [FiniteTail.unitVec, hi']) (by simp)]
    simp [FiniteTail.unitVec, bmat]
  have hu : (FiniteTail.unitVec (𝕜 := ℝ) (ω := weights ν hν) i q j) l = 0 := by
    by_cases hji : j = i
    · subst hji; simp [FiniteTail.unitVec, WeightedL1.single_apply, show l ≠ q by omega]
    · simp [FiniteTail.unitVec, hji]
  rw [DFN, DF_apply_coeff, hg, mul_single_apply _ hq0, mul_single_apply _ hq0, hu]
  simp only [hl0, ↓reduceIte, mul_zero, add_zero, zero_add]
  rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
  ring

omit [NeZero n] in
/-- For `q ≥ M N + 2` the column `q` of `𝒞` equals the column `q'` of the same parity with
`q' ∈ {M N + 2, M N + 3}`. -/
theorem DFN_periodic (abar : Fin n → X ν hν) {N : ℕ} (habar : ∀ i, SuppLe (abar i) N) {M : ℕ}
    (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M) (j i : Fin n) {l q : ℕ} (hl : l ≤ N)
    (hq : M * N + 2 ≤ q) :
    P.DFN ν hν abar j l i q = P.DFN ν hν abar j l i (M * N + 2 + (q - (M * N + 2)) % 2) := by
  by_cases hl0 : l = 0
  · subst hl0
    rw [DFN_row_zero _ _ _ _ (by omega), DFN_row_zero _ _ _ _ (by omega)]
    have : (-1 : ℝ) ^ q = (-1) ^ (M * N + 2 + (q - (M * N + 2)) % 2) := by
      rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := M * N + 2 + _)]
      congr 1
      omega
    rw [this]
  · rw [P.DFN_tail_zero abar habar hM hdeg j i hl0 hl hq,
      P.DFN_tail_zero abar habar hM hdeg j i hl0 hl (by omega)]

theorem weights_mono {k k' : ℕ} (hk : k ≠ 0) (hkk' : k ≤ k') :
    weights ν hν k ≤ weights ν hν k' := by
  rw [weights_apply, weights_apply, ite_eq_right hk, ite_eq_right (by omega)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hν hkk') zero_le_two

omit [NeZero n] in
/-- The column bound for every tail column `q > N`, from the columns `N < q ≤ M N + 3`. -/
theorem matAC_col_bound (abar : Fin n → X ν hν) {N : ℕ} (habar : ∀ i, SuppLe (abar i) N) {M : ℕ}
    (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M) (AN : Fin n → ℕ → Fin n → ℕ → ℝ)
    {K1 : Fin n → Fin n → ℝ}
    (hK1 : ∀ j i, ∀ k ∈ Finset.Ioc N (M * N + 3), ∑ m ∈ Finset.range (N + 1),
      |P.matAC ν hν N AN abar j m i k| * weights ν hν m ≤ K1 j i * weights ν hν k)
    (hK10 : ∀ j i, 0 ≤ K1 j i) (j i : Fin n) {q : ℕ} (hq : N < q) :
    ∑ m ∈ Finset.range (N + 1), |P.matAC ν hν N AN abar j m i q| * weights ν hν m ≤
      K1 j i * weights ν hν q := by
  by_cases hq3 : q ≤ M * N + 3
  · exact hK1 j i q (Finset.mem_Ioc.2 ⟨hq, hq3⟩)
  · set q' := M * N + 2 + (q - (M * N + 2)) % 2
    have hq' : q' ∈ Finset.Ioc N (M * N + 3) := by
      have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
      rw [Finset.mem_Ioc]; omega
    have hcol : ∀ m ∈ Finset.range (N + 1),
        P.matAC ν hν N AN abar j m i q = P.matAC ν hν N AN abar j m i q' := fun m _ =>
      Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' hl' => by
        rw [P.DFN_periodic abar habar hM hdeg i' i (Finset.mem_range_succ_iff.1 hl') (by omega)]
    rw [Finset.sum_congr rfl fun m hm => by rw [hcol m hm]]
    refine (hK1 j i q' hq').trans (mul_le_mul_of_nonneg_left ?_ (hK10 j i))
    exact weights_mono (by omega) (by omega)

/-! #### The tail estimate -/

omit [NeZero n] in
/-- `∑_{k > N} (ν^k / k) |g_{k+1} - g_{k-1}| ≤ (ν + ν⁻¹) / (2 (N + 1)) ‖g‖` for `N ≥ 1`. -/
theorem tail_shift_le {N : ℕ} (hN : 1 ≤ N) (g : X ν hν) :
    Summable (fun k : ℕ => if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0) ∧
    ∑' k : ℕ, (if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0) ≤
      (ν + ν⁻¹) / (2 * (N + 1)) * ‖g‖ := by
  have hν0 := nu_pos hν
  set W : ℕ → ℝ := fun p => weights ν hν p * ‖g p‖ with hW
  have hWs : Summable W := g.summable
  have hW0 : ∀ p, 0 ≤ W p := fun p => mul_nonneg ((weights ν hν).pos p).le (norm_nonneg _)
  have hWt : ∑' p, W p = ‖g‖ := (WeightedL1.norm_eq_tsum g).symm
  -- the two pieces
  set A : ℕ → ℝ := fun k => (2 * ν)⁻¹ * W (k + 1)
  set B : ℕ → ℝ := fun k => if N < k then ν / 2 * W (k - 1) else 0
  have hAs : Summable A := ((summable_nat_add_iff 1).2 hWs).mul_left _
  have hWs' : Summable fun k => W (k - 1) :=
    (summable_nat_add_iff 1).1 (by simpa using hWs)
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    simp only [B]
    split_ifs
    · exact mul_nonneg (by positivity) (hW0 _)
    · exact le_rfl
  have hBs : Summable B := Summable.of_nonneg_of_le hB0
    (fun k => by
      simp only [B]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by positivity) (hW0 _)) (hWs'.mul_left (ν / 2))
  have hA : ∑' k, A k ≤ (2 * ν)⁻¹ * ‖g‖ := by
    rw [tsum_mul_left, ← hWt, hWs.tsum_eq_zero_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hW0 0)) (by positivity)
  have hB : ∑' k, B k ≤ ν / 2 * ‖g‖ := by
    rw [hBs.tsum_eq_zero_add]
    have h0 : B 0 = 0 := by simp [B]
    rw [h0, zero_add, ← hWt]
    calc ∑' k, B (k + 1) ≤ ∑' k, ν / 2 * W k :=
          ((summable_nat_add_iff 1).2 hBs).tsum_le_tsum (fun k => by
            simp only [B, Nat.add_sub_cancel]
            split_ifs
            · exact le_rfl
            · exact mul_nonneg (by positivity) (hW0 _)) (hWs.mul_left _)
      _ = ν / 2 * ∑' k, W k := tsum_mul_left
  -- the termwise bound
  have hterm : ∀ k, (if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0) ≤
      ((N : ℝ) + 1)⁻¹ * (A k + B k) := fun k => by
    split_ifs with hk
    · have hk1 : (N : ℝ) + 1 ≤ k := by exact_mod_cast hk
      have hkpos : (0 : ℝ) < k := by linarith
      have hk1' : k - 1 ≠ 0 := by omega
      have hwA : W (k + 1) = 2 * ν ^ (k + 1) * |g (k + 1)| := by
        simp [hW, weights_apply, Real.norm_eq_abs]
      have hwB : W (k - 1) = 2 * ν ^ (k - 1) * |g (k - 1)| := by
        simp [hW, weights_apply, Real.norm_eq_abs, hk1']
      have hpow : ν ^ k = ν * ν ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      have hpow2 : ν ^ (k + 1) = ν * ν * ν ^ (k - 1) := by
        rw [pow_succ, hpow]; ring
      simp only [A, B, hk, ↓reduceIte, hwA, hwB]
      have habs := abs_sub (g (k + 1)) (g (k - 1))
      have hdiv : ν ^ k / k ≤ ν ^ k / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hk1
      calc ν ^ k / k * |g (k + 1) - g (k - 1)| ≤ ν ^ k / ((N : ℝ) + 1) * (|g (k + 1)| + |g (k - 1)|) :=
            mul_le_mul hdiv habs (abs_nonneg _) (by positivity)
        _ = ((N : ℝ) + 1)⁻¹ * ((2 * ν)⁻¹ * (2 * ν ^ (k + 1) * |g (k + 1)|) +
              ν / 2 * (2 * ν ^ (k - 1) * |g (k - 1)|)) := by
            rw [hpow2, hpow]; field_simp
    · exact mul_nonneg (by positivity) (add_nonneg
        (mul_nonneg (by positivity) (hW0 (k + 1))) (hB0 k))
  have hsum : Summable fun k : ℕ => if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0 :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) hterm
      ((hAs.add hBs).mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℕ, (if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0)
      ≤ ∑' k, ((N : ℝ) + 1)⁻¹ * (A k + B k) := hsum.tsum_le_tsum hterm ((hAs.add hBs).mul_left _)
    _ = ((N : ℝ) + 1)⁻¹ * (∑' k, A k + ∑' k, B k) := by rw [tsum_mul_left, hAs.tsum_add hBs]
    _ ≤ ((N : ℝ) + 1)⁻¹ * ((2 * ν)⁻¹ * ‖g‖ + ν / 2 * ‖g‖) := by gcongr
    _ = (ν + ν⁻¹) / (2 * (N + 1)) * ‖g‖ := by field_simp; ring

/-! #### The operator `DF(ā) - A†` -/

omit [NeZero n] in
theorem summable_DFN_mul (abar h : Fin n → X ν hν) (j i : Fin n) (m : ℕ) :
    Summable fun q => P.DFN ν hν abar j m i q * h i q :=
  (FiniteTail.hasSum_apply (P.DF ν hν abar) h i j m).summable

omit [NeZero n] in
/-- Rows `m ≤ N` of `(DF(ā) - A†) h`: only the tail columns `q > N` remain. -/
theorem DF_sub_opD_apply_fin (abar : Fin n → X ν hν) {N : ℕ} (h : Fin n → X ν hν) (j : Fin n)
    {m : ℕ} (hm : m ∈ Finset.range (N + 1)) :
    (P.DF ν hν abar - P.opD ν hν N abar) h j m =
      ∑ i, ∑' q, (if q ∈ Finset.range (N + 1) then 0 else P.DFN ν hν abar j m i q * h i q) := by
  rw [sub_apply, Pi.sub_apply, WeightedLp.sub_apply, FiniteTail.apply_eq_sum_tsum, opD,
    FiniteTail.op_apply, ite_eq_left hm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑' k, P.DFN ν hν abar j m i k * h i k - _ = _
  rw [tsum_eq_sum_add_tsum_ite (P.summable_DFN_mul abar h j i m) (Finset.range (N + 1)),
    add_sub_cancel_left]

omit [NeZero n] in
/-- Rows `m > N` of `(DF(ā) - A†) h`: `L (g_{m+1} - g_{m-1})`, `g = Dφ_j(ā) h`. -/
theorem DF_sub_opD_apply_tail (abar : Fin n → X ν hν) {N : ℕ} (h : Fin n → X ν hν) (j : Fin n)
    {m : ℕ} (hm : m ∉ Finset.range (N + 1)) :
    (P.DF ν hν abar - P.opD ν hν N abar) h j m =
      P.L * ((polyDeriv (P.f j) abar h) (m + 1) - (polyDeriv (P.f j) abar h) (m - 1)) := by
  have hm0 : m ≠ 0 := by rw [Finset.mem_range] at hm; omega
  rw [sub_apply, Pi.sub_apply, WeightedLp.sub_apply, DF_apply_coeff, opD, FiniteTail.op_apply]
  simp [hm0, hm, tailD]

/-- The bound `Z₁`. -/
theorem norm_opA_DF_sub_opD_le (hN : 1 ≤ N) (habar : ∀ i, SuppLe (abar i) N) {M : ℕ}
    (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M) {K1 : Fin n → Fin n → ℝ}
    (hK10 : ∀ j i, 0 ≤ K1 j i)
    (hK1 : ∀ j i, ∀ k ∈ Finset.Ioc N (M * N + 3), ∑ m ∈ Finset.range (N + 1),
      |P.matAC ν hν N AN abar j m i k| * weights ν hν m ≤ K1 j i * weights ν hν k)
    {Z₁ : ℝ} (hZ₁ : ∀ j, ∑ i, K1 j i +
      |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) * ∑ i, ‖P.bmat ν hν abar j i‖ ≤ Z₁) :
    ‖(opA ν hν N AN).comp (P.DF ν hν abar - P.opD ν hν N abar)‖ ≤ Z₁ := by
  have hν0 := nu_pos hν
  set s := Finset.range (N + 1) with hs
  have hc0 : 0 ≤ |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) := by positivity
  have hZ₁nn : 0 ≤ Z₁ := le_trans (add_nonneg (Finset.sum_nonneg fun i _ => hK10 0 i)
    (mul_nonneg hc0 (Finset.sum_nonneg fun i _ => norm_nonneg _))) (hZ₁ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hZ₁nn (norm_nonneg h))).2 fun j => ?_
  rw [ContinuousLinearMap.comp_apply]
  set T := P.DF ν hν abar - P.opD ν hν N abar with hTdef
  set v := opA ν hν N AN (T h) j with hv
  set g := polyDeriv (P.f j) abar h with hg
  -- the tail columns of `DF(ā)`, applied to `h`
  have hG : ∀ i' l' i, Summable fun q =>
      (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) := fun i' l' i =>
    ((P.summable_DFN_mul abar h i' i l').sub (summable_of_ne_finset_zero (s := s)
      (f := fun q => if q ∈ s then P.DFN ν hν abar i' l' i q * h i q else 0)
      fun q hq => by simp [hq])).congr fun q => by split_ifs <;> simp
  -- the rows `k ≤ N` of `v`
  have hv_fin : ∀ k ∈ s, v k =
      ∑ i, ∑' q, (if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q) := by
    intro k hk
    rw [hv, opA, FiniteTail.op_apply, ite_eq_left hk]
    calc ∑ i', ∑ l' ∈ s, AN j k i' l' * T h i' l'
        = ∑ i', ∑ l' ∈ s, ∑ i, ∑' q,
            AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) := by
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' hl' => ?_
          rw [P.DF_sub_opD_apply_fin abar h i' hl', Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => tsum_mul_left.symm
      _ = ∑ i, ∑ i', ∑ l' ∈ s, ∑' q,
            AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) := by
          rw [Finset.sum_congr rfl fun i' _ => Finset.sum_comm]
          exact Finset.sum_comm
      _ = ∑ i, ∑' q, ∑ i', ∑ l' ∈ s,
            AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc ∑ i', ∑ l' ∈ s, ∑' q,
                AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q)
              = ∑ i', ∑' q, ∑ l' ∈ s,
                AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) :=
                Finset.sum_congr rfl fun i' _ =>
                  (Summable.tsum_finsetSum fun l' _ => (hG i' l' i).mul_left _).symm
            _ = ∑' q, ∑ i', ∑ l' ∈ s,
                AN j k i' l' * (if q ∈ s then 0 else P.DFN ν hν abar i' l' i q * h i q) :=
                (Summable.tsum_finsetSum fun i' _ => summable_sum fun l' _ =>
                  (hG i' l' i).mul_left _).symm
      _ = ∑ i, ∑' q, (if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q) := by
          refine Finset.sum_congr rfl fun i _ => tsum_congr fun q => ?_
          split_ifs with hq
          · simp
          · simp only [matAC, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => by ring
  -- entries of the tail columns of `A^{(N)} 𝒞`, weighted
  have hAC : ∀ k ∈ s, ∀ i q, q ∉ s →
      |P.matAC ν hν N AN abar j k i q| * weights ν hν k ≤ K1 j i * weights ν hν q := by
    intro k hk i q hq
    have hNq : N < q := by rw [hs, Finset.mem_range] at hq; omega
    exact (Finset.single_le_sum (f := fun k' => |P.matAC ν hν N AN abar j k' i q| *
      weights ν hν k') (fun k' _ => mul_nonneg (abs_nonneg _) ((weights ν hν).pos k').le) hk).trans
      (P.matAC_col_bound abar habar hM hdeg AN hK1 hK10 j i hNq)
  have hterm : ∀ k ∈ s, ∀ i q, weights ν hν k *
      ‖(if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖ ≤
        K1 j i * (weights ν hν q * ‖h i q‖) := by
    intro k hk i q
    split_ifs with hq
    · simp only [norm_zero, mul_zero]
      exact mul_nonneg (hK10 j i) (mul_nonneg ((weights ν hν).pos q).le (norm_nonneg _))
    · rw [norm_mul, Real.norm_eq_abs, ← mul_assoc, mul_comm (weights ν hν k), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hAC k hk i q hq) (norm_nonneg _)
  have hsumm : ∀ k ∈ s, ∀ i, Summable fun q =>
      ‖(if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖ := by
    intro k hk i
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      ((h i).summable.mul_left (K1 j i / weights ν hν k))
    have := hterm k hk i q
    rw [div_mul_eq_mul_div, le_div_iff₀ ((weights ν hν).pos k), mul_comm]
    linarith
  -- the first part: rows `k ≤ N`
  have hpart1 : ∑ k ∈ s, weights ν hν k * ‖v k‖ ≤ (∑ i, K1 j i) * ‖h‖ := by
    calc ∑ k ∈ s, weights ν hν k * ‖v k‖
        ≤ ∑ k ∈ s, ∑ i, ∑' q, weights ν hν k *
            ‖(if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [hv_fin k hk]
          calc weights ν hν k * ‖∑ i, ∑' q,
                (if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖
              ≤ weights ν hν k * ∑ i, ∑' q,
                ‖(if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖ :=
                mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
                  norm_tsum_le_tsum_norm (hsumm k hk i))) ((weights ν hν).pos k).le
            _ = _ := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => tsum_mul_left.symm
      _ = ∑ i, ∑' q, ∑ k ∈ s, weights ν hν k *
            ‖(if q ∈ s then 0 else P.matAC ν hν N AN abar j k i q * h i q)‖ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (Summable.tsum_finsetSum fun k hk => (hsumm k hk i).mul_left _).symm
      _ ≤ ∑ i, ∑' q, K1 j i * (weights ν hν q * ‖h i q‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine Summable.tsum_le_tsum (fun q => ?_)
            (summable_sum fun k hk => (hsumm k hk i).mul_left _)
            ((h i).summable.mul_left _)
          by_cases hq : q ∈ s
          · simp only [hq, ↓reduceIte, norm_zero, mul_zero, Finset.sum_const_zero]
            exact mul_nonneg (hK10 j i) (mul_nonneg ((weights ν hν).pos q).le (norm_nonneg _))
          · simp only [hq, ↓reduceIte, norm_mul, Real.norm_eq_abs]
            calc ∑ k ∈ s, weights ν hν k * (|P.matAC ν hν N AN abar j k i q| * |h i q|)
                = (∑ k ∈ s, |P.matAC ν hν N AN abar j k i q| * weights ν hν k) * |h i q| := by
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun k _ => by ring
              _ ≤ K1 j i * weights ν hν q * |h i q| :=
                  mul_le_mul_of_nonneg_right (P.matAC_col_bound abar habar hM hdeg AN hK1 hK10 j i
                    (by rw [hs, Finset.mem_range] at hq; omega)) (abs_nonneg _)
              _ = K1 j i * (weights ν hν q * |h i q|) := by ring
      _ = ∑ i, K1 j i * ‖h i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [tsum_mul_left, WeightedL1.norm_eq_tsum]
      _ ≤ (∑ i, K1 j i) * ‖h‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (hK10 j i)
  -- the second part: rows `k > N`
  have hgnorm : ‖g‖ ≤ (∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖ := by
    rw [hg, polyDeriv_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _))
  have hval : ∀ k, (if k ∈ s then 0 else weights ν hν k * ‖v k‖) =
      |P.L| * (if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0) := by
    intro k
    by_cases hk : k ∈ s
    · have : ¬ N < k := by rw [hs, Finset.mem_range] at hk; omega
      simp [hk, this]
    · have hNk : N < k := by rw [hs, Finset.mem_range] at hk; omega
      have hk0 : k ≠ 0 := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      simp only [hk, hNk, ↓reduceIte]
      rw [hv, opA, FiniteTail.op_apply, ite_eq_right hk, P.DF_sub_opD_apply_tail abar h j hk,
        weights_apply, ite_eq_right hk0, tailA, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (2 * (k : ℝ))⁻¹)]
      field_simp
      rfl
  have hpart2 : ∑' k, (if k ∈ s then 0 else weights ν hν k * ‖v k‖) ≤
      |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) * ((∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖) := by
    rw [tsum_congr hval, tsum_mul_left]
    obtain ⟨-, ht⟩ := tail_shift_le hN g
    calc |P.L| * ∑' k : ℕ, (if N < k then ν ^ k / k * |g (k + 1) - g (k - 1)| else 0)
        ≤ |P.L| * ((ν + ν⁻¹) / (2 * (N + 1)) * ‖g‖) :=
          mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ ≤ |P.L| * ((ν + ν⁻¹) / (2 * (N + 1)) * ((∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖)) := by
          gcongr
      _ = _ := by ring
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum_add_tsum_ite v.summable s]
  calc ∑ k ∈ s, weights ν hν k * ‖v k‖ + ∑' k, (if k ∈ s then 0 else weights ν hν k * ‖v k‖)
      ≤ (∑ i, K1 j i) * ‖h‖ +
          |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) * ((∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖) :=
        add_le_add hpart1 hpart2
    _ = (∑ i, K1 j i + |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) * ∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖ := by
        ring
    _ ≤ Z₁ * ‖h‖ := mul_le_mul_of_nonneg_right (hZ₁ j) (norm_nonneg h)

omit [NeZero n] in
/-- `(DF(c) - DF(a)) h = L S ((Dφ(c) - Dφ(a)) h)`, componentwise: the boundary rows and `D` cancel. -/
theorem DF_sub_DF_apply (c a h : Fin n → X ν hν) (j : Fin n) :
    (P.DF ν hν c - P.DF ν hν a) h j =
      P.L • shiftOp ν hν ((polyDeriv (P.f j) c - polyDeriv (P.f j) a) h) := by
  simp only [DF, sub_apply, ContinuousLinearMap.pi_apply, Pi.sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.comp_apply, map_sub, smul_sub]
  abel

omit [NeZero n] in
theorem norm_L_shiftOp_le (y : X ν hν) :
    ‖P.L • shiftOp ν hν y‖ ≤ |P.L| * (ν + (2 * ν)⁻¹) * ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (((shiftOp ν hν).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right norm_shiftOp_le (norm_nonneg _))) (abs_nonneg _)

omit [NeZero n] in
theorem Theta_nonneg (i : Fin n) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ P.Theta ν hν abar i r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    absEval_nonneg _ fun _ => add_nonneg (norm_nonneg _) hr

/-- The bound `Z₂(r)`, valid for every `r ≥ 0`. -/
theorem norm_opA_DF_sub_DF_le {KA : Fin n → Fin n → ℝ} (hKA0 : ∀ j i, 0 ≤ KA j i)
    (hKAd : ∀ j, 1 ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |AN j m i l| * weights ν hν m ≤ KA j i * weightsY ν hν l)
    {r Z₂ : ℝ} (hr : 0 ≤ r)
    (hZ₂ : ∀ j, |P.L| * (ν + (2 * ν)⁻¹) * ∑ i, KA j i * P.Theta ν hν abar i r ≤ Z₂)
    (c : Fin n → X ν hν) (hc : c ∈ closedBall abar r) :
    ‖(opA ν hν N AN).comp (P.DF ν hν c - P.DF ν hν abar)‖ ≤ Z₂ * r := by
  have hν0 := nu_pos hν
  have hKAb : FiniteTail.Bound (Finset.range (N + 1)) AN tailA (weights ν hν) (weightsY ν hν) KA :=
    ⟨hKA0, fun j i l hl => by simpa [Real.norm_eq_abs] using hKA j i l hl, fun j l hl =>
      (tailA_bound N l hl).trans (mul_le_mul_of_nonneg_right (hKAd j) ((weightsY ν hν).pos l).le)⟩
  have hopA : opA ν hν N AN = FiniteTail.op hKAb := FiniteTail.op_congr _ _
  have hc0 : 0 ≤ |P.L| * (ν + (2 * ν)⁻¹) := mul_nonneg (abs_nonneg _) (by positivity)
  have hZ₂nn : 0 ≤ Z₂ := le_trans (mul_nonneg hc0 (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hKA0 0 i) (P.Theta_nonneg abar i hr))) (hZ₂ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hZ₂nn hr) fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hZ₂nn hr) (norm_nonneg h))).2
    fun j => ?_
  rw [ContinuousLinearMap.comp_apply, hopA]
  refine (FiniteTail.norm_op_apply_le hKAb _ j).trans ?_
  have hi : ∀ i, ‖(P.DF ν hν c - P.DF ν hν abar) h i‖ ≤
      |P.L| * (ν + (2 * ν)⁻¹) * (P.Theta ν hν abar i r * r) * ‖h‖ := fun i => by
    rw [P.DF_sub_DF_apply]
    refine (P.norm_L_shiftOp_le _).trans ?_
    rw [mul_assoc _ _ ‖h‖]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    exact ((polyDeriv (P.f i) c - polyDeriv (P.f i) abar).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (norm_polyDeriv_sub_le (P.f i) hc) (norm_nonneg h))
  calc ∑ i, KA j i * ‖(P.DF ν hν c - P.DF ν hν abar) h i‖
      ≤ ∑ i, KA j i * (|P.L| * (ν + (2 * ν)⁻¹) * (P.Theta ν hν abar i r * r) * ‖h‖) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (hKA0 j i)
    _ = |P.L| * (ν + (2 * ν)⁻¹) * (∑ i, KA j i * P.Theta ν hν abar i r) * r * ‖h‖ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ Z₂ * r * ‖h‖ := by
        gcongr
        exact hZ₂ j

omit [NeZero n] in
/-- If `‖I - A A†‖ < 1`, then `A` is injective. -/
theorem opA_injective
    (h : ‖ContinuousLinearMap.id ℝ _ - (opA ν hν N AN).comp (P.opD ν hν N abar)‖ < 1) :
    Function.Injective (opA ν hν N AN) :=
  FiniteTail.injective_op _ _ (fun m hm => by
    have hm0 : m ≠ 0 := by rw [Finset.mem_range] at hm; omega
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    simp [tailA, this]) h

end Bounds

/-! ### The theorem -/

/-- The radii polynomial theorem for a Chebyshev boundary value problem, with two radii
`r₀ ≤ r₁` (the bounds in column form, see the module docstring). -/
theorem radii_poly_two_radii [NeZero n] (abar : Fin n → X ν hν) {N : ℕ} (hN : 1 ≤ N)
    (habar : ∀ i, SuppLe (abar i) N) {M : ℕ} (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M)
    (AN : Fin n → ℕ → Fin n → ℕ → ℝ) {r₀ r₁ Y₀ Z₀ Z₁ Z₂₀ Z₂₁ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∀ j, ∑ k ∈ Finset.range (N + 1),
        |∑ i, ∑ l ∈ Finset.range (N + 1), AN j k i l * P.F ν hν abar i l| * weights ν hν k +
        ∑ k ∈ Finset.Ico (N + 1) (M * N + 2), |P.F ν hν abar j k| * (ν ^ k / k) ≤ Y₀)
    {KE : Fin n → Fin n → ℝ} (hKE0 : ∀ j i, 0 ≤ KE j i)
    (hKE : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |P.matE ν hν N AN abar j m i l| * weights ν hν m ≤ KE j i * weights ν hν l)
    (hZ₀ : ∀ j, ∑ i, KE j i ≤ Z₀)
    {K1 : Fin n → Fin n → ℝ} (hK10 : ∀ j i, 0 ≤ K1 j i)
    (hK1 : ∀ j i, ∀ k ∈ Finset.Ioc N (M * N + 3), ∑ m ∈ Finset.range (N + 1),
      |P.matAC ν hν N AN abar j m i k| * weights ν hν m ≤ K1 j i * weights ν hν k)
    (hZ₁ : ∀ j, ∑ i, K1 j i +
      |P.L| * (ν + ν⁻¹) / (2 * (N + 1)) * ∑ i, ‖P.bmat ν hν abar j i‖ ≤ Z₁)
    {KA : Fin n → Fin n → ℝ} (hKA0 : ∀ j i, 0 ≤ KA j i) (hKAd : ∀ j, 1 ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |AN j m i l| * weights ν hν m ≤ KA j i * weightsY ν hν l)
    (hZ₂₀ : ∀ j, |P.L| * (ν + (2 * ν)⁻¹) * ∑ i, KA j i * P.Theta ν hν abar i r₀ ≤ Z₂₀)
    (hZ₂₁ : ∀ j, |P.L| * (ν + (2 * ν)⁻¹) * ∑ i, KA j i * P.Theta ν hν abar i r₁ ≤ Z₂₁)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂₁ r₁ < 0) :
    HasIsolatedZero (P.F ν hν) abar r₀ r₁ := by
  have hZ₀' := P.norm_id_sub_opA_opD_le abar AN hKE0 hKE hZ₀
  have hZ₁' := P.norm_opA_DF_sub_opD_le abar AN hN habar hM hdeg hK10 hK1 hZ₁
  have hY₀' := P.norm_opA_F_le abar AN habar hM hdeg hY₀
  -- `Z₀ < 1`, hence `A` is injective
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀'
  have hZ₁nn : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁'
  have hZ₂nn : 0 ≤ Z₂₀ * r₀ := (norm_nonneg _).trans
    (P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA hr₀.le hZ₂₀ abar (mem_closedBall_self hr₀.le))
  have hZ₀1 : Z₀ < 1 := by
    simp only [radiiPoly] at hp₀
    nlinarith [mul_nonneg hZ₂nn hr₀.le, mul_nonneg hZ₁nn hr₀.le]
  have hinj := P.opA_injective abar AN (hZ₀'.trans_lt hZ₀1)
  obtain ⟨x, hx, hFx, huniq, -⟩ := RadiiPolynomial.radii_poly_two_radii (𝕜 := ℝ) (P.F ν hν) (P.DF ν hν)
    (opA ν hν N AN) (P.opD ν hν N abar) abar hinj hr₀ hr₀₁
    (fun x _ => (P.hasFDerivAt_F ν hν x).hasFDerivWithinAt) hY₀' hZ₀' hZ₁'
    (fun c hc => P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA hr₀.le hZ₂₀ c hc)
    (fun c hc => P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA (hr₀.le.trans hr₀₁) hZ₂₁ c hc)
    hp₀ hp₁
  unfold HasIsolatedZero
  exact ⟨x, hx, hFx, huniq⟩

end ChebBVP

end RadiiPolynomial
