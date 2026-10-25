module

public import RadiiPolynomial.Problems.TaylorIVP
public import RadiiPolynomial.BlockTail.FiniteTail
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# The radii polynomial theorem for Taylor initial value problems

Let `F : (ℓ¹_ν)^n → (ℓ¹_ω)^n` be the operator of an initial value problem (`TaylorIVP.F`),
`ā ∈ (ℓ¹_ν)^n` with `(āⱼ)_k = 0` for `k > N`, and `A^{(N)}` a finite matrix (indexed by
`(j, m), (i, l)` with `m, l ≤ N`). With `s = {0, …, N}`:

* `opA`: the approximate inverse `A : Y → X`, the finite block `A^{(N)}` and the tail `1/k`;
* `opD`: the approximate derivative `A† : X → Y`, the finite block of `DF(ā)` (`DFN`) and the tail
  `k`;
* `DFN j m i l = (DF(ā) e_{i,l})_{j,m}`, the matrix of `DF(ā)`; it is lower triangular
  (`DFN_eq_zero`), so `DF(ā) - A†` vanishes on the rows `m ≤ N`.

The bounds are stated in column form: each of `Y₀`, `Z₀`, `Z₁`, `Z₂(r)` is any number dominating
the corresponding finite expression.

* `norm_opA_F_le` (`Y₀`), `norm_id_sub_opA_opD_le` (`Z₀`);
* `norm_opA_DF_sub_opD_le` (`Z₁ = |τ| ν / (N + 1) ∑ᵢ ‖∂ᵢφ_j(ā)‖`);
* `norm_opA_DF_sub_DF_le` (`Z₂(r) = |τ| ν ∑ᵢ K_{ji} Θᵢ(r)`, where `K_{ji}` bounds the block `(j, i)` of
  `A` as an operator on `ℓ¹_ν`, including the tail `1/(N + 1)` on the diagonal);
* `opA_injective`;
* `radii_poly_two_radii`: if `p(r₀) < 0` and `p(r₁) < 0`, `F` has a zero in the open ball of
  radius `r₀` about `ā`, unique in the closed ball of radius `r₁` (`HasIsolatedZero`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace TaylorIVP

open Taylor MvPolynomial Metric

variable {n : ℕ} (P : TaylorIVP n) {ν : ℝ} {hν : 0 < ν}

/-- The tail `1/k` of the approximate inverse. -/
noncomputable def tailA (k : ℕ) : ℝ := (k : ℝ)⁻¹

/-- The tail `k` of the approximate derivative. -/
def tailD (k : ℕ) : ℝ := k

theorem tailA_bound (N : ℕ) (l : ℕ) (hl : l ∉ Finset.range (N + 1)) :
    ‖tailA l‖ * Weights.geom ν hν l ≤ (2 / ν) * weightsY ν hν l := by
  have hl' : (1 : ℝ) ≤ l := by rw [Finset.mem_range] at hl; exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < l := by linarith
  rw [tailA, Weights.geom_apply, weightsY_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hlpos),
    pow_succ]
  have h2 : 2 / ν * (ν ^ l * ν / ((l : ℝ) + 1)) = 2 * ν ^ l / ((l : ℝ) + 1) := by
    field_simp
  rw [h2, inv_mul_eq_div, div_le_div_iff₀ hlpos (by positivity)]
  nlinarith [pow_pos hν l]

theorem tailD_bound (N : ℕ) (l : ℕ) (_hl : l ∉ Finset.range (N + 1)) :
    ‖tailD l‖ * weightsY ν hν l ≤ ν * Weights.geom ν hν l := by
  rw [tailD, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg l), mul_comm]
  have h := diff_bound (ν := ν) (hν := hν) l
  by_cases hl0 : l = 0
  · subst hl0
    simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg hν.le ((Weights.geom ν hν).pos 0).le
  · simpa [hl0, Real.norm_eq_abs, mul_comm] using h

theorem tailA_le (N : ℕ) (l : ℕ) (hl : l ∉ Finset.range (N + 1)) :
    ‖tailA l‖ ≤ ((N : ℝ) + 1)⁻¹ := by
  have hl' : (N : ℝ) + 1 ≤ l := by rw [Finset.mem_range] at hl; exact_mod_cast (by omega : N + 1 ≤ l)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [tailA, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith))]
  exact inv_anti₀ (by positivity) hl'

variable (ν hν)

/-- The approximate inverse `A : Y → X`: finite block `A^{(N)}`, tail `1/k`. -/
noncomputable def opA (N : ℕ) (AN : Fin n → ℕ → Fin n → ℕ → ℝ) :
    (Fin n → Y ν hν) →L[ℝ] (Fin n → X ν hν) :=
  FiniteTail.op (FiniteTail.crudeBound (s := Finset.range (N + 1)) (M := AN) (tl := tailA)
    (ω := Weights.geom ν hν) (ω' := weightsY ν hν) (by positivity) (tailA_bound N))

/-- The matrix of `DF(ā)`: `DFN j m i l = (DF(ā) e_{i,l})_{j,m}`. -/
noncomputable def DFN (abar : Fin n → X ν hν) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℝ :=
  P.DF ν hν abar (FiniteTail.unitVec i l) j m

/-- The approximate derivative `A† : X → Y`: finite block of `DF(ā)`, tail `k`. -/
noncomputable def opD (N : ℕ) (abar : Fin n → X ν hν) :
    (Fin n → X ν hν) →L[ℝ] (Fin n → Y ν hν) :=
  FiniteTail.op (FiniteTail.crudeBound (s := Finset.range (N + 1)) (M := P.DFN ν hν abar)
    (tl := tailD) (ω := weightsY ν hν) (ω' := Weights.geom ν hν) hν.le (tailD_bound N))

/-- `E = I - A^{(N)} DF^{(N)}(ā)`. -/
noncomputable def matE (N : ℕ) (AN : Fin n → ℕ → Fin n → ℕ → ℝ) (abar : Fin n → X ν hν)
    (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℝ :=
  (if j = i ∧ m = l then 1 else 0) -
    ∑ i', ∑ l' ∈ Finset.range (N + 1), AN j m i' l' * P.DFN ν hν abar i' l' i l

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
  rw [P.F_apply_of_ne_zero ν hν abar j hk0, habar j k (by omega), hc (k - 1) (by omega)]
  ring

/-- The bound `Y₀`. -/
theorem norm_opA_F_le (habar : ∀ i, SuppLe (abar i) N) {M : ℕ} (hM : 1 ≤ M)
    (hdeg : ∀ j, (P.f j).totalDegree ≤ M) {Y₀ : ℝ}
    (hY₀ : ∀ j, ∑ k ∈ Finset.range (N + 1),
        |∑ i, ∑ l ∈ Finset.range (N + 1), AN j k i l * P.F ν hν abar i l| * ν ^ k +
        ∑ k ∈ Finset.Ico (N + 1) (M * N + 2), |P.F ν hν abar j k| * (ν ^ k / k) ≤ Y₀) :
    ‖opA ν hν N AN (P.F ν hν abar)‖ ≤ Y₀ := by
  have hY₀nn : 0 ≤ Y₀ := le_trans (add_nonneg
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (pow_pos hν k).le)
    (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (by positivity))) (hY₀ 0)
  have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  refine (pi_norm_le_iff_of_nonneg hY₀nn).2 fun j => ?_
  rw [WeightedL1.norm_eq_tsum]
  have hsupp : ∀ k ∉ Finset.range (M * N + 2),
      Weights.geom ν hν k * ‖opA ν hν N AN (P.F ν hν abar) j k‖ = 0 := fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [opA, FiniteTail.op_apply, ite_eq_right (by rw [Finset.mem_range]; omega),
      P.F_suppLe abar habar hM hdeg j (by omega), mul_zero, norm_zero, mul_zero]
  rw [tsum_eq_sum hsupp, ← Finset.sum_range_add_sum_Ico _ (by omega : N + 1 ≤ M * N + 2)]
  refine le_of_eq_of_le ?_ (hY₀ j)
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [opA, FiniteTail.op_apply, ite_eq_left hk, Real.norm_eq_abs, Weights.geom_apply, mul_comm]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [opA, FiniteTail.op_apply, ite_eq_right (by rw [Finset.mem_range]; omega),
      Weights.geom_apply, Real.norm_eq_abs, abs_mul, tailA,
      abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ)⁻¹)]
    field_simp

/-- The bound `Z₀`. -/
theorem norm_id_sub_opA_opD_le {KE : Fin n → Fin n → ℝ} (hKE0 : ∀ j i, 0 ≤ KE j i)
    (hKE : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |P.matE ν hν N AN abar j m i l| * ν ^ m ≤ KE j i * ν ^ l)
    {Z₀ : ℝ} (hZ₀ : ∀ j, ∑ i, KE j i ≤ Z₀) :
    ‖ContinuousLinearMap.id ℝ _ - (opA ν hν N AN).comp (P.opD ν hν N abar)‖ ≤ Z₀ := by
  have hE : FiniteTail.Bound (Finset.range (N + 1)) (P.matE ν hν N AN abar) (fun _ => 0)
      (Weights.geom ν hν) (Weights.geom ν hν) KE :=
    ⟨hKE0, fun j i l hl => by simpa [Real.norm_eq_abs] using hKE j i l hl, fun j l _ => by
      rw [norm_zero, zero_mul]
      exact mul_nonneg (hKE0 j j) ((Weights.geom ν hν).pos l).le⟩
  have hZ₀nn : 0 ≤ Z₀ := (Finset.sum_nonneg fun i _ => hKE0 0 i).trans (hZ₀ 0)
  rw [opA, opD, FiniteTail.id_sub_op_comp_op _ _ hE (fun j m i l _ _ => rfl) (fun m hm => by
    have hm0 : m ≠ 0 := by rw [Finset.mem_range] at hm; omega
    have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    simp only [tailA, tailD]
    field_simp
    ring)]
  exact FiniteTail.norm_op_le hE hZ₀nn hZ₀

/-! #### The matrix of `DF(ā)` -/

omit [NeZero n] in
/-- The coefficients of `DF(a) h`. -/
theorem DF_apply_coeff (a h : Fin n → X ν hν) (j : Fin n) (m : ℕ) :
    P.DF ν hν a h j m = (if m = 0 then 1 else m) * h j m -
      P.τ * (if m = 0 then 0 else (polyDeriv (P.f j) a h) (m - 1)) := by
  simp only [DF, ContinuousLinearMap.pi_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, WeightedLp.sub_apply,
    WeightedLp.smul_apply, diffOp_apply, incl_apply, shift_apply]

omit [NeZero n] in
theorem unitVec_apply (i j : Fin n) (l m : ℕ) :
    (FiniteTail.unitVec (𝕜 := ℝ) (ω := Weights.geom ν hν) i l j) m =
      if j = i ∧ m = l then 1 else 0 := by
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
/-- `DF(ā)` is lower triangular: `(DF(ā) e_{i,q})_{j,m} = 0` for `m < q`. -/
theorem DFN_eq_zero (abar : Fin n → X ν hν) (j i : Fin n) {m q : ℕ} (hmq : m < q) :
    P.DFN ν hν abar j m i q = 0 := by
  rw [DFN, DF_apply_coeff, unitVec_apply, polyDeriv_unitVec, mul_single_apply]
  have h1 : ¬ (j = i ∧ m = q) := fun h => by omega
  have h2 : ¬ q ≤ m - 1 := by omega
  simp [h1, h2]

/-! #### The operator `DF(ā) - A†` -/

omit [NeZero n] in
theorem summable_DFN_mul (abar h : Fin n → X ν hν) (j i : Fin n) (m : ℕ) :
    Summable fun q => P.DFN ν hν abar j m i q * h i q :=
  (FiniteTail.hasSum_apply (P.DF ν hν abar) h i j m).summable

omit [NeZero n] in
/-- Rows `m ≤ N` of `(DF(ā) - A†) h` vanish. -/
theorem DF_sub_opD_apply_fin (abar : Fin n → X ν hν) {N : ℕ} (h : Fin n → X ν hν) (j : Fin n)
    {m : ℕ} (hm : m ∈ Finset.range (N + 1)) :
    (P.DF ν hν abar - P.opD ν hν N abar) h j m = 0 := by
  rw [sub_apply, Pi.sub_apply, WeightedLp.sub_apply, FiniteTail.apply_eq_sum_tsum, opD,
    FiniteTail.op_apply, ite_eq_left hm, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  change ∑' q, P.DFN ν hν abar j m i q * h i q - _ = 0
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun q hq => by
    rw [Finset.mem_range] at hm hq
    rw [P.DFN_eq_zero abar j i (by omega), zero_mul], sub_self]

omit [NeZero n] in
/-- Rows `m > N` of `(DF(ā) - A†) h`: `-τ g_{m-1}`, `g = Dφ_j(ā) h`. -/
theorem DF_sub_opD_apply_tail (abar : Fin n → X ν hν) {N : ℕ} (h : Fin n → X ν hν) (j : Fin n)
    {m : ℕ} (hm : m ∉ Finset.range (N + 1)) :
    (P.DF ν hν abar - P.opD ν hν N abar) h j m = -(P.τ * (polyDeriv (P.f j) abar h) (m - 1)) := by
  have hm0 : m ≠ 0 := by rw [Finset.mem_range] at hm; omega
  rw [sub_apply, Pi.sub_apply, WeightedLp.sub_apply, DF_apply_coeff, opD, FiniteTail.op_apply]
  simp [hm0, hm, tailD]

omit [NeZero n] in
/-- `∑_{k > N} (ν^k / k) |g_{k-1}| ≤ ν / (N + 1) ‖g‖`. -/
theorem tail_shift_le (N : ℕ) (g : X ν hν) :
    Summable (fun k : ℕ => if N < k then ν ^ k / k * |g (k - 1)| else 0) ∧
    ∑' k : ℕ, (if N < k then ν ^ k / k * |g (k - 1)| else 0) ≤ ν / (N + 1) * ‖g‖ := by
  set f : ℕ → ℝ := fun k => if N < k then ν ^ k / k * |g (k - 1)| else 0 with hf
  set W : ℕ → ℝ := fun p => Weights.geom ν hν p * ‖g p‖ with hW
  have hWs : Summable W := g.summable
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; split_ifs <;> positivity
  have hterm : ∀ k, f (k + 1) ≤ ν / (N + 1) * W k := fun k => by
    simp only [hf, hW, Nat.add_sub_cancel, Weights.geom_apply, Real.norm_eq_abs]
    split_ifs with hk
    · have hk1 : (N : ℝ) + 1 ≤ k + 1 := by exact_mod_cast hk
      have hdiv : ν ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ ν ^ (k + 1) / ((N : ℝ) + 1) := by
        push_cast
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hk1
      calc ν ^ (k + 1) / ((k + 1 : ℕ) : ℝ) * |g k| ≤ ν ^ (k + 1) / ((N : ℝ) + 1) * |g k| :=
            mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
        _ = ν / (N + 1) * (ν ^ k * |g k|) := by rw [pow_succ]; ring
    · positivity
  have hs1 : Summable fun k => f (k + 1) :=
    Summable.of_nonneg_of_le (fun k => hf0 _) hterm (hWs.mul_left _)
  have hs : Summable f := (summable_nat_add_iff 1).1 hs1
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have h0 : f 0 = 0 := by simp [hf]
  rw [h0, zero_add]
  calc ∑' k, f (k + 1) ≤ ∑' k, ν / (N + 1) * W k := hs1.tsum_le_tsum hterm (hWs.mul_left _)
    _ = ν / (N + 1) * ‖g‖ := by rw [tsum_mul_left, WeightedL1.norm_eq_tsum]

/-- The bound `Z₁`. -/
theorem norm_opA_DF_sub_opD_le {Z₁ : ℝ}
    (hZ₁ : ∀ j, |P.τ| * ν / (N + 1) * ∑ i, ‖P.bmat ν hν abar j i‖ ≤ Z₁) :
    ‖(opA ν hν N AN).comp (P.DF ν hν abar - P.opD ν hν N abar)‖ ≤ Z₁ := by
  set s := Finset.range (N + 1) with hs
  have hc0 : 0 ≤ |P.τ| * ν / (N + 1) := by positivity
  have hZ₁nn : 0 ≤ Z₁ :=
    le_trans (mul_nonneg hc0 (Finset.sum_nonneg fun i _ => norm_nonneg _)) (hZ₁ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hZ₁nn (norm_nonneg h))).2 fun j => ?_
  rw [ContinuousLinearMap.comp_apply]
  set T := P.DF ν hν abar - P.opD ν hν N abar with hTdef
  set v := opA ν hν N AN (T h) j with hv
  set g := polyDeriv (P.f j) abar h with hg
  have hgnorm : ‖g‖ ≤ (∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖ := by
    rw [hg, polyDeriv_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) (norm_nonneg _))
  have hval : ∀ k, Weights.geom ν hν k * ‖v k‖ =
      |P.τ| * (if N < k then ν ^ k / k * |g (k - 1)| else 0) := by
    intro k
    by_cases hk : k ∈ s
    · have : ¬ N < k := by rw [hs, Finset.mem_range] at hk; omega
      rw [hv, opA, FiniteTail.op_apply, ite_eq_left hk, Finset.sum_eq_zero fun i _ =>
        Finset.sum_eq_zero fun l hl => by rw [P.DF_sub_opD_apply_fin abar h i hl, mul_zero]]
      simp [this]
    · have hNk : N < k := by rw [hs, Finset.mem_range] at hk; omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      rw [hv, opA, FiniteTail.op_apply, ite_eq_right hk, P.DF_sub_opD_apply_tail abar h j hk,
        Weights.geom_apply, tailA, ite_eq_left hNk, Real.norm_eq_abs, abs_mul, abs_neg, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ)⁻¹)]
      field_simp
      rfl
  obtain ⟨-, ht⟩ := tail_shift_le N g
  rw [WeightedL1.norm_eq_tsum, tsum_congr hval, tsum_mul_left]
  calc |P.τ| * ∑' k : ℕ, (if N < k then ν ^ k / k * |g (k - 1)| else 0)
      ≤ |P.τ| * (ν / (N + 1) * ‖g‖) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ ≤ |P.τ| * (ν / (N + 1) * ((∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖)) := by gcongr
    _ = |P.τ| * ν / (N + 1) * (∑ i, ‖P.bmat ν hν abar j i‖) * ‖h‖ := by ring
    _ ≤ Z₁ * ‖h‖ := mul_le_mul_of_nonneg_right (hZ₁ j) (norm_nonneg h)

/-! #### The bound `Z₂` -/

omit [NeZero n] in
/-- `(DF(c) - DF(a)) h = ι(-τ S ((Dφ(c) - Dφ(a)) h))`, componentwise: the terms `D h` cancel. -/
theorem DF_sub_DF_apply (c a h : Fin n → X ν hν) (j : Fin n) :
    (P.DF ν hν c - P.DF ν hν a) h j =
      incl ν hν (-P.τ • shift ν hν ((polyDeriv (P.f j) c - polyDeriv (P.f j) a) h)) := by
  simp only [DF, sub_apply, ContinuousLinearMap.pi_apply, Pi.sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul, smul_sub, neg_smul, map_neg]
  abel

omit [NeZero n] in
/-- On sequences in `ℓ¹_ν`, `A` acts as the operator with the same matrix on `ℓ¹_ν`. -/
theorem opA_incl {K : Fin n → Fin n → ℝ}
    (hK : FiniteTail.Bound (Finset.range (N + 1)) AN tailA (Weights.geom ν hν)
      (Weights.geom ν hν) K) (y : Fin n → X ν hν) :
    opA ν hν N AN (fun i => incl ν hν (y i)) = FiniteTail.op hK y := by
  funext j; ext m
  rw [opA, FiniteTail.op_apply, FiniteTail.op_apply]
  simp only [incl_apply]

omit [NeZero n] in
theorem Theta_nonneg (i : Fin n) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ P.Theta ν hν abar i r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    absEval_nonneg _ fun _ => add_nonneg (norm_nonneg _) hr

/-- The bound `Z₂(r)`, valid for every `r ≥ 0`. -/
theorem norm_opA_DF_sub_DF_le {KA : Fin n → Fin n → ℝ} (hKA0 : ∀ j i, 0 ≤ KA j i)
    (hKAd : ∀ j, ((N : ℝ) + 1)⁻¹ ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |AN j m i l| * ν ^ m ≤ KA j i * ν ^ l)
    {r Z₂ : ℝ} (hr : 0 ≤ r)
    (hZ₂ : ∀ j, |P.τ| * ν * ∑ i, KA j i * P.Theta ν hν abar i r ≤ Z₂)
    (c : Fin n → X ν hν) (hc : c ∈ closedBall abar r) :
    ‖(opA ν hν N AN).comp (P.DF ν hν c - P.DF ν hν abar)‖ ≤ Z₂ * r := by
  have hKAb : FiniteTail.Bound (Finset.range (N + 1)) AN tailA (Weights.geom ν hν)
      (Weights.geom ν hν) KA :=
    ⟨hKA0, fun j i l hl => by simpa [Real.norm_eq_abs] using hKA j i l hl, fun j l hl =>
      mul_le_mul_of_nonneg_right ((tailA_le N l hl).trans (hKAd j))
        ((Weights.geom ν hν).pos l).le⟩
  have hc0 : 0 ≤ |P.τ| * ν := by positivity
  have hZ₂nn : 0 ≤ Z₂ := le_trans (mul_nonneg hc0 (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hKA0 0 i) (P.Theta_nonneg abar i hr))) (hZ₂ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hZ₂nn hr) fun h => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hZ₂nn hr) (norm_nonneg h))).2
    fun j => ?_
  set y : Fin n → X ν hν :=
    fun i => -P.τ • shift ν hν ((polyDeriv (P.f i) c - polyDeriv (P.f i) abar) h) with hy
  have hDy : (P.DF ν hν c - P.DF ν hν abar) h = fun i => incl ν hν (y i) :=
    funext fun i => P.DF_sub_DF_apply c abar h i
  rw [ContinuousLinearMap.comp_apply, hDy, opA_incl AN hKAb]
  refine (FiniteTail.norm_op_apply_le hKAb _ j).trans ?_
  have hi : ∀ i, ‖y i‖ ≤ |P.τ| * ν * (P.Theta ν hν abar i r * r) * ‖h‖ := fun i => by
    set w := (polyDeriv (P.f i) c - polyDeriv (P.f i) abar) h
    rw [hy]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    calc |P.τ| * ‖shift ν hν w‖ ≤ |P.τ| * (ν * ‖w‖) :=
          mul_le_mul_of_nonneg_left (((shift ν hν).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right norm_shift_le (norm_nonneg _))) (abs_nonneg _)
      _ ≤ |P.τ| * (ν * (P.Theta ν hν abar i r * r * ‖h‖)) := by
          gcongr
          exact ((polyDeriv (P.f i) c - polyDeriv (P.f i) abar).le_opNorm h).trans
            (mul_le_mul_of_nonneg_right (norm_polyDeriv_sub_le (P.f i) hc) (norm_nonneg h))
      _ = |P.τ| * ν * (P.Theta ν hν abar i r * r) * ‖h‖ := by ring
  calc ∑ i, KA j i * ‖y i‖
      ≤ ∑ i, KA j i * (|P.τ| * ν * (P.Theta ν hν abar i r * r) * ‖h‖) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (hKA0 j i)
    _ = |P.τ| * ν * (∑ i, KA j i * P.Theta ν hν abar i r) * r * ‖h‖ := by
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

/-- The radii polynomial theorem for a Taylor initial value problem, with two radii `r₀ ≤ r₁`
(the bounds in column form, see the module docstring). -/
theorem radii_poly_two_radii [NeZero n] (abar : Fin n → X ν hν) {N : ℕ}
    (habar : ∀ i, SuppLe (abar i) N) {M : ℕ} (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M)
    (AN : Fin n → ℕ → Fin n → ℕ → ℝ) {r₀ r₁ Y₀ Z₀ Z₁ Z₂₀ Z₂₁ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∀ j, ∑ k ∈ Finset.range (N + 1),
        |∑ i, ∑ l ∈ Finset.range (N + 1), AN j k i l * P.F ν hν abar i l| * ν ^ k +
        ∑ k ∈ Finset.Ico (N + 1) (M * N + 2), |P.F ν hν abar j k| * (ν ^ k / k) ≤ Y₀)
    {KE : Fin n → Fin n → ℝ} (hKE0 : ∀ j i, 0 ≤ KE j i)
    (hKE : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |P.matE ν hν N AN abar j m i l| * ν ^ m ≤ KE j i * ν ^ l)
    (hZ₀ : ∀ j, ∑ i, KE j i ≤ Z₀)
    (hZ₁ : ∀ j, |P.τ| * ν / (N + 1) * ∑ i, ‖P.bmat ν hν abar j i‖ ≤ Z₁)
    {KA : Fin n → Fin n → ℝ} (hKA0 : ∀ j i, 0 ≤ KA j i) (hKAd : ∀ j, ((N : ℝ) + 1)⁻¹ ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      |AN j m i l| * ν ^ m ≤ KA j i * ν ^ l)
    (hZ₂₀ : ∀ j, |P.τ| * ν * ∑ i, KA j i * P.Theta ν hν abar i r₀ ≤ Z₂₀)
    (hZ₂₁ : ∀ j, |P.τ| * ν * ∑ i, KA j i * P.Theta ν hν abar i r₁ ≤ Z₂₁)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂₁ r₁ < 0) :
    HasIsolatedZero (P.F ν hν) abar r₀ r₁ := by
  have hZ₀' := P.norm_id_sub_opA_opD_le abar AN hKE0 hKE hZ₀
  have hZ₁' := P.norm_opA_DF_sub_opD_le abar AN hZ₁
  have hY₀' := P.norm_opA_F_le abar AN habar hM hdeg hY₀
  -- `Z₀ < 1`, hence `A` is injective
  have hZ₁nn : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁'
  have hZ₂nn : 0 ≤ Z₂₀ * r₀ := (norm_nonneg _).trans
    (P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA hr₀.le hZ₂₀ abar (mem_closedBall_self hr₀.le))
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀'
  have hZ₀1 : Z₀ < 1 := by
    simp only [radiiPoly] at hp₀
    nlinarith [mul_nonneg hZ₂nn hr₀.le, mul_nonneg hZ₁nn hr₀.le]
  have hinj := P.opA_injective abar AN (hZ₀'.trans_lt hZ₀1)
  obtain ⟨x, hx, hFx, huniq, -⟩ := RadiiPolynomial.radii_poly_two_radii (𝕜 := ℝ) (P.F ν hν)
    (P.DF ν hν) (opA ν hν N AN) (P.opD ν hν N abar) abar hinj hr₀ hr₀₁
    (fun x _ => (P.hasFDerivAt_F ν hν x).hasFDerivWithinAt) hY₀' hZ₀' hZ₁'
    (fun c hc => P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA hr₀.le hZ₂₀ c hc)
    (fun c hc => P.norm_opA_DF_sub_DF_le abar AN hKA0 hKAd hKA (hr₀.le.trans hr₀₁) hZ₂₁ c hc)
    hp₀ hp₁
  unfold HasIsolatedZero
  exact ⟨x, hx, hFx, huniq⟩

end TaylorIVP

end RadiiPolynomial
