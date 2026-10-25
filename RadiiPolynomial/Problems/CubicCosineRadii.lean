module

public import RadiiPolynomial.Problems.CubicCosine
public import RadiiPolynomial.BlockTail.FiniteTail
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# The radii polynomial theorem for cubic equilibrium problems in cosine series

Let `F(a) = Λ a - ι(a³)` be the operator of a `CubicCosine` problem with eigenvalues `μ`, `ν ≥ 1`,
`m ≥ 1` a Galerkin dimension with the tail condition `μ_m ≠ 0`, `|μ_k| ≥ |μ_m|` for `k ≥ m`
(`TailCond`), `ā ∈ ℓ¹_ν` with `ā_k = 0` for `k ≥ m`, and `A_m` an `m × m` matrix. With
`s = {0, …, m - 1}`:

* `opA`: the approximate inverse `A : Y → X`, the finite block `A_m` and the tail `1/μ_k`;
* `opD`: the approximate derivative `A† : X → Y`, the finite block of `DF(ā)` (`DFN`) and the tail
  `μ_k`.

The bounds (each any number dominating the corresponding expression):

* `norm_opA_F_le` (`Y₀`): `∑_{k < m} |(A_m F(ā))_k| ν^k + ∑_{m ≤ k ≤ 3m-3} |F_k(ā)| ν^k / |μ_k|`;
* `norm_id_sub_opA_opD_le` (`Z⁽⁰⁾`): the column norm of `I - A_m DF^{(m)}(ā)`;
* `norm_opA_DF_sub_opD_le` (`Z⁽¹⁾`): `3 ∑_{k < m} ν^k ∑_{n < m} |(A_m)_{kn}| W_n + 48 ‖ā‖² / |μ_m|`,
  where `W_n = ∑_{m ≤ j ≤ 3m-3} ν^{-j} (S_{j-n} + S_{n+j})` and `S = |ā| * |ā|`, i.e.
  `W = (|ā|² ω̃)_F` with `ω̃_j = ν^{-j}` for `m ≤ j ≤ 3m - 3`;
* `norm_opA_DF_sub_DF_le` (`Z₂(r) = Z⁽²⁾ + Z⁽³⁾ r = 96 α ‖ā‖ + 48 α r`), where `α` bounds `A` as an
  operator on `ℓ¹_ν`: `α ≥ ν^{-l} ∑_{k < m} |(A_m)_{kl}| ν^k` and `α ≥ 1/|μ_m|`;
* `opA_injective`, and `radii_poly_two_radii`: if `p(r₀) < 0` and `p(r₁) < 0`, `F` has a zero in
  the open ball of radius `r₀` about `ā`, unique in the closed ball of radius `r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace CubicCosine

open Cosine Metric

variable (P : CubicCosine) {ν : ℝ} {hν : 1 ≤ ν}

/-- The tail condition on the Galerkin dimension `m`: `μ_m ≠ 0` and `|μ_k| ≥ |μ_m|` for `k ≥ m`. -/
def TailCond (m : ℕ) : Prop := P.μ m ≠ 0 ∧ ∀ k, m ≤ k → |P.μ m| ≤ |P.μ k|

variable {P}

theorem TailCond.pos {m : ℕ} (h : P.TailCond m) {k : ℕ} (hk : m ≤ k) : 0 < |P.μ k| :=
  (abs_pos.2 h.1).trans_le (h.2 k hk)

theorem TailCond.inv_le {m : ℕ} (h : P.TailCond m) {k : ℕ} (hk : m ≤ k) :
    |P.μ k|⁻¹ ≤ |P.μ m|⁻¹ :=
  inv_anti₀ (abs_pos.2 h.1) (h.2 k hk)

variable (P)

/-- The tail `1/μ_k` of the approximate inverse. -/
noncomputable def tailA (k : ℕ) : ℝ := (P.μ k)⁻¹

theorem tailA_bound {m : ℕ} (hμ : P.TailCond m) (l : ℕ) (hl : l ∉ Finset.range m) :
    ‖P.tailA l‖ * Cosine.weights ν hν l ≤ (1 + |P.μ m|⁻¹) * P.weightsY ν hν l := by
  have hl' : m ≤ l := by rw [Finset.mem_range] at hl; omega
  have hpos := hμ.pos hl'
  have hinv := hμ.inv_le hl'
  have hν0 : 0 < ν ^ l := pow_pos (Chebyshev.nu_pos hν) l
  rw [tailA, Real.norm_eq_abs, abs_inv, Cosine.weights_apply, weightsY_apply]
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have h1 : |P.μ l|⁻¹ * (1 + |P.μ l|) = |P.μ l|⁻¹ + 1 := by field_simp
  calc |P.μ l|⁻¹ * ν ^ l * (1 + |P.μ l|) = (|P.μ l|⁻¹ + 1) * ν ^ l := by rw [← h1]; ring
    _ ≤ (1 + |P.μ m|⁻¹) * ν ^ l := mul_le_mul_of_nonneg_right (by linarith) hν0.le

/-- The tail bound of `A` as an operator on `ℓ¹_ν`. -/
theorem tailA_bound_X {m : ℕ} (hμ : P.TailCond m) {α : ℝ} (hα : |P.μ m|⁻¹ ≤ α) (l : ℕ)
    (hl : l ∉ Finset.range m) :
    ‖P.tailA l‖ * Cosine.weights ν hν l ≤ α * Cosine.weights ν hν l := by
  have hl' : m ≤ l := by rw [Finset.mem_range] at hl; omega
  rw [tailA, Real.norm_eq_abs, abs_inv]
  exact mul_le_mul_of_nonneg_right ((hμ.inv_le hl').trans hα) ((Cosine.weights ν hν).pos l).le

theorem tailD_bound (m : ℕ) (l : ℕ) (_hl : l ∉ Finset.range m) :
    ‖P.μ l‖ * P.weightsY ν hν l ≤ 1 * Cosine.weights ν hν l := P.diag_bound l

variable (ν hν)

/-- The approximate inverse `A : Y → X`: finite block `A_m`, tail `1/μ_k`. -/
noncomputable def opA {m : ℕ} (hμ : P.TailCond m) (AN : ℕ → ℕ → ℝ) : P.Y ν hν →L[ℝ] X ν hν :=
  FiniteTail.op1 (FiniteTail.crudeBound (s := Finset.range m) (M := fun _ k _ l => AN k l)
    (tl := P.tailA) (ω := Cosine.weights ν hν) (ω' := P.weightsY ν hν) (by positivity)
    (P.tailA_bound hμ))

/-- The matrix of `DF(ā)`: `DFN n l = (DF(ā) e_l)_n`. -/
noncomputable def DFN (abar : X ν hν) (n l : ℕ) : ℝ := P.DF ν hν abar (WeightedL1.single l 1) n

/-- The approximate derivative `A† : X → Y`: finite block of `DF(ā)`, tail `μ_k`. -/
noncomputable def opD (m : ℕ) (abar : X ν hν) : X ν hν →L[ℝ] P.Y ν hν :=
  FiniteTail.op1 (FiniteTail.crudeBound (s := Finset.range m)
    (M := fun _ n _ l => P.DFN ν hν abar n l) (tl := P.μ) (ω := P.weightsY ν hν)
    (ω' := Cosine.weights ν hν) zero_le_one (P.tailD_bound m))

/-- `E = I - A_m DF^{(m)}(ā)`. -/
noncomputable def matE (m : ℕ) (AN : ℕ → ℕ → ℝ) (abar : X ν hν) (k l : ℕ) : ℝ :=
  (if k = l then 1 else 0) - ∑ n ∈ Finset.range m, AN k n * P.DFN ν hν abar n l

/-- `W_n = ∑_{m ≤ j ≤ 3m-3} ν^{-j} (S_{j-n} + S_{n+j})`, `S = |ā| * |ā|`: the worst case of
`(|ā|² |h_I|)_n` over `‖h‖ ≤ 1`, `h_I` the tail of `h`. -/
noncomputable def W (ν : ℝ) (hν : 1 ≤ ν) (m : ℕ) (abar : X ν hν) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc m (3 * m - 3),
    (mul2 ν hν (absX ν hν abar) (absX ν hν abar) (j - n) +
      mul2 ν hν (absX ν hν abar) (absX ν hν abar) (n + j)) / ν ^ j

variable {ν hν}

/-! ### The bounds -/

section Bounds

variable (abar : X ν hν) {m : ℕ} (hμ : P.TailCond m) (AN : ℕ → ℕ → ℝ)

theorem cube_eq_zero (hm : 1 ≤ m) (habar : ∀ k, m ≤ k → abar k = 0) {k : ℕ}
    (hk : 3 * m - 2 ≤ k) : cube ν hν abar k = 0 := by
  have h1 : Chebyshev.SuppLe (toCheb ν hν abar) (m - 1) := fun k hk => by
    rw [toCheb_apply, habar k (by omega)]
  rw [cube_eq, ofCheb_apply, h1.pow 3 k (by omega)]

/-- `F(ā)_k = 0` for `k ≥ 3m - 2`. -/
theorem F_eq_zero (hm : 1 ≤ m) (habar : ∀ k, m ≤ k → abar k = 0) {k : ℕ} (hk : 3 * m - 2 ≤ k) :
    P.F ν hν abar k = 0 := by
  rw [F_apply, habar k (by omega), cube_eq_zero abar hm habar hk]
  ring

/-- The bound `Y₀`. -/
theorem norm_opA_F_le (hm : 1 ≤ m) (habar : ∀ k, m ≤ k → abar k = 0) {Y₀ : ℝ}
    (hY₀ : ∑ k ∈ Finset.range m, |∑ l ∈ Finset.range m, AN k l * P.F ν hν abar l| * ν ^ k +
        ∑ k ∈ Finset.Ico m (3 * m - 2), |P.F ν hν abar k| * ν ^ k / |P.μ k| ≤ Y₀) :
    ‖P.opA ν hν hμ AN (P.F ν hν abar)‖ ≤ Y₀ := by
  rw [WeightedL1.norm_eq_tsum]
  have hsupp : ∀ k ∉ Finset.range (3 * m - 2),
      Cosine.weights ν hν k * ‖P.opA ν hν hμ AN (P.F ν hν abar) k‖ = 0 := fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [opA, FiniteTail.op1_apply, ite_eq_right (by rw [Finset.mem_range]; omega),
      P.F_eq_zero abar hm habar hk, mul_zero, norm_zero, mul_zero]
  rw [tsum_eq_sum hsupp, ← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ 3 * m - 2)]
  refine le_of_eq_of_le ?_ hY₀
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [opA, FiniteTail.op1_apply, ite_eq_left hk, Real.norm_eq_abs, Cosine.weights_apply,
      mul_comm]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [opA, FiniteTail.op1_apply, ite_eq_right (by rw [Finset.mem_range]; omega),
      Cosine.weights_apply, Real.norm_eq_abs, abs_mul, tailA, abs_inv]
    field_simp

/-- The bound `Z⁽⁰⁾`. -/
theorem norm_id_sub_opA_opD_le {Z₀ : ℝ} (hZ₀0 : 0 ≤ Z₀)
    (hZ₀ : ∀ l ∈ Finset.range m, ∑ k ∈ Finset.range m,
      |P.matE ν hν m AN abar k l| * ν ^ k ≤ Z₀ * ν ^ l) :
    ‖ContinuousLinearMap.id ℝ _ - (P.opA ν hν hμ AN).comp (P.opD ν hν m abar)‖ ≤ Z₀ := by
  have hE : FiniteTail.Bound (Finset.range m)
      (fun (_ : Fin 1) k (_ : Fin 1) l => P.matE ν hν m AN abar k l)
      (fun _ => (0 : ℝ)) (Cosine.weights ν hν) (Cosine.weights ν hν)
      (fun (_ : Fin 1) (_ : Fin 1) => Z₀) :=
    ⟨fun _ _ => hZ₀0, fun _ _ l hl => by
      simpa only [Real.norm_eq_abs, Cosine.weights_apply] using hZ₀ l hl, fun _ l _ => by
      rw [norm_zero, zero_mul]
      exact mul_nonneg hZ₀0 ((Cosine.weights ν hν).pos l).le⟩
  rw [opA, opD, FiniteTail.id_sub_op1_comp_op1 _ _ hE (fun j k i l _ _ => by
    simp [matE, Subsingleton.elim j i]) (fun k hk => by
    have hk' : m ≤ k := by rw [Finset.mem_range] at hk; omega
    have := hμ.pos hk'
    simp only [tailA]
    field_simp [abs_pos.1 this]
    ring)]
  exact FiniteTail.norm_op1_le hE

/-! #### The operator `DF(ā) - A†` -/

/-- Rows `n < m`, columns `l ≥ m` of `DF(ā)`: `-3 ((ā * ā)_{l-n} + (ā * ā)_{n+l})`. -/
theorem DFN_tail (n l : ℕ) (hl0 : l ≠ 0) (hnl : n ≠ l) :
    P.DFN ν hν abar n l =
      -(3 * (mul2 ν hν abar abar ((n : ℤ) - l).natAbs + mul2 ν hν abar abar (n + l))) := by
  rw [DFN, DF_apply, WeightedLp.sub_apply, diag_apply, incl_apply, WeightedLp.smul_apply,
    mul3_single_apply _ _ hl0, WeightedL1.single_apply, ite_eq_right hnl]
  simp only [mul_zero]
  ring

theorem abs_DFN_le (habar : ∀ k, m ≤ k → abar k = 0) {n l : ℕ} (hn : n < m)
    (hl : m ≤ l) :
    |P.DFN ν hν abar n l| ≤ 3 * (mul2 ν hν (absX ν hν abar) (absX ν hν abar) (l - n) +
      mul2 ν hν (absX ν hν abar) (absX ν hν abar) (n + l)) := by
  rw [P.DFN_tail abar n l (by omega) (by omega), abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h1 : ((n : ℤ) - l).natAbs = l - n := by omega
  rw [h1]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by norm_num)
  · exact abs_mul2_le abar habar _
  · exact abs_mul2_le abar habar _

theorem summable_DFN_mul (h : X ν hν) (n : ℕ) :
    Summable fun l => P.DFN ν hν abar n l * h l :=
  (FiniteTail.hasSum_apply1 (P.DF ν hν abar) h n).summable

/-- Rows `n < m` of `(DF(ā) - A†) h`: only the columns `l ≥ m` remain. -/
theorem DF_sub_opD_apply_fin (h : X ν hν) {n : ℕ} (hn : n ∈ Finset.range m) :
    (P.DF ν hν abar - P.opD ν hν m abar) h n =
      ∑' l, (if l ∈ Finset.range m then 0 else P.DFN ν hν abar n l * h l) := by
  rw [sub_apply, WeightedLp.sub_apply,
    ← (FiniteTail.hasSum_apply1 (P.DF ν hν abar) h n).tsum_eq, opD, FiniteTail.op1_apply,
    ite_eq_left hn]
  change ∑' l, P.DFN ν hν abar n l * h l - _ = _
  rw [tsum_eq_sum_add_tsum_ite (P.summable_DFN_mul abar h n) (Finset.range m), add_sub_cancel_left]

/-- Rows `k ≥ m` of `(DF(ā) - A†) h`: `-3 (ā * ā * h)_k`. -/
theorem DF_sub_opD_apply_tail (h : X ν hν) {k : ℕ} (hk : k ∉ Finset.range m) :
    (P.DF ν hν abar - P.opD ν hν m abar) h k = -(3 * mul3 ν hν abar abar h k) := by
  rw [sub_apply, WeightedLp.sub_apply, DF_apply, opD, FiniteTail.op1_apply,
    ite_eq_right hk]
  simp only [WeightedLp.sub_apply, diag_apply, incl_apply, WeightedLp.smul_apply]
  ring

theorem S_nonneg (i : ℕ) : 0 ≤ mul2 ν hν (absX ν hν abar) (absX ν hν abar) i :=
  mul2_nonneg (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) i

theorem W_nonneg (n : ℕ) : 0 ≤ W ν hν m abar n :=
  Finset.sum_nonneg fun j _ => div_nonneg (add_nonneg (S_nonneg abar _) (S_nonneg abar _))
    (pow_pos (Chebyshev.nu_pos hν) j).le

omit hμ in
/-- `|(DF(ā) - A†) h|_n ≤ 3 W_n ‖h‖` for `n < m`. -/
theorem abs_DF_sub_opD_fin_le (hm : 1 ≤ m) (habar : ∀ k, m ≤ k → abar k = 0) (h : X ν hν)
    {n : ℕ} (hn : n ∈ Finset.range m) :
    |(P.DF ν hν abar - P.opD ν hν m abar) h n| ≤ 3 * W ν hν m abar n * ‖h‖ := by
  have hn' : n < m := Finset.mem_range.1 hn
  have hA2 : ∀ i, 2 * m - 1 ≤ i → mul2 ν hν abar abar i = 0 := fun i hi =>
    mul2_eq_zero abar abar habar habar hm hm (by omega)
  rw [P.DF_sub_opD_apply_fin abar h hn, tsum_eq_sum (s := Finset.Icc m (3 * m - 3)) fun l hl => by
    by_cases hls : l ∈ Finset.range m
    · rw [ite_eq_left hls]
    · rw [ite_eq_right hls]
      simp only [Finset.mem_Icc, not_and_or, not_le] at hl
      rw [Finset.mem_range, not_lt] at hls
      rcases hl with hl | hl
      · omega
      · rw [P.DFN_tail abar n l (by omega) (by omega), hA2 _ (by omega), hA2 _ (by omega)]
        ring]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [W, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun l hl => ?_
  rw [Finset.mem_Icc] at hl
  have hls : l ∉ Finset.range m := by rw [Finset.mem_range]; omega
  rw [ite_eq_right hls, abs_mul]
  have hνl : 0 < ν ^ l := pow_pos (Chebyshev.nu_pos hν) l
  have hh : |h l| ≤ ‖h‖ / ν ^ l := by
    rw [le_div_iff₀ hνl, mul_comm, ← Real.norm_eq_abs]
    exact WeightedLp.norm_apply_le h l
  calc |P.DFN ν hν abar n l| * |h l|
      ≤ (3 * (mul2 ν hν (absX ν hν abar) (absX ν hν abar) (l - n) +
          mul2 ν hν (absX ν hν abar) (absX ν hν abar) (n + l))) * (‖h‖ / ν ^ l) :=
        mul_le_mul (P.abs_DFN_le abar habar hn' hl.1) hh (abs_nonneg _)
          (by positivity [S_nonneg abar (l - n), S_nonneg abar (n + l)])
    _ = 3 * ((mul2 ν hν (absX ν hν abar) (absX ν hν abar) (l - n) +
          mul2 ν hν (absX ν hν abar) (absX ν hν abar) (n + l)) / ν ^ l) * ‖h‖ := by
        rw [add_comm n l]; ring

/-- The bound `Z⁽¹⁾`. -/
theorem norm_opA_DF_sub_opD_le (hm : 1 ≤ m) (habar : ∀ k, m ≤ k → abar k = 0) {Z₁ : ℝ}
    (hZ₁ : 3 * ∑ k ∈ Finset.range m, (∑ n ∈ Finset.range m, |AN k n| * W ν hν m abar n) * ν ^ k +
      48 * ‖abar‖ ^ 2 / |P.μ m| ≤ Z₁) :
    ‖(P.opA ν hν hμ AN).comp (P.DF ν hν abar - P.opD ν hν m abar)‖ ≤ Z₁ := by
  set s := Finset.range m with hs
  have hμm := hμ.pos (le_refl m)
  have hpart0 : 0 ≤ 3 * ∑ k ∈ s, (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ν ^ k :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => mul_nonneg
      (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (W_nonneg abar n))
      (pow_pos (Chebyshev.nu_pos hν) k).le)
  have hZ₁nn : 0 ≤ Z₁ := le_trans (add_nonneg hpart0 (by positivity)) hZ₁
  refine ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun h => ?_
  rw [ContinuousLinearMap.comp_apply]
  set T := P.DF ν hν abar - P.opD ν hν m abar with hT
  set v := P.opA ν hν hμ AN (T h) with hv
  -- rows `k < m`
  have hv_fin : ∀ k ∈ s, |v k| ≤ 3 * (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ‖h‖ := by
    intro k hk
    rw [hv, opA, FiniteTail.op1_apply, ite_eq_left hk]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [abs_mul]
    calc |AN k n| * |T h n| ≤ |AN k n| * (3 * W ν hν m abar n * ‖h‖) :=
          mul_le_mul_of_nonneg_left (P.abs_DF_sub_opD_fin_le abar hm habar h hn) (abs_nonneg _)
      _ = 3 * (|AN k n| * W ν hν m abar n) * ‖h‖ := by ring
  -- rows `k ≥ m`
  have hv_tail : ∀ k, (if k ∈ s then 0 else Cosine.weights ν hν k * ‖v k‖) ≤
      3 * |P.μ m|⁻¹ * (Cosine.weights ν hν k * ‖mul3 ν hν abar abar h k‖) := by
    intro k
    by_cases hk : k ∈ s
    · rw [ite_eq_left hk]
      exact mul_nonneg (by positivity) (mul_nonneg ((Cosine.weights ν hν).pos k).le (norm_nonneg _))
    · rw [ite_eq_right hk, hv, opA, FiniteTail.op1_apply, ite_eq_right hk,
        P.DF_sub_opD_apply_tail abar h hk, tailA]
      have hk' : m ≤ k := by rw [hs, Finset.mem_range, not_lt] at hk; exact hk
      rw [norm_mul, norm_neg, norm_mul, norm_inv, Real.norm_eq_abs (P.μ k),
        Real.norm_eq_abs (3 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have hinv := hμ.inv_le hk'
      have hw := ((Cosine.weights ν hν).pos k).le
      calc Cosine.weights ν hν k * (|P.μ k|⁻¹ * (3 * ‖mul3 ν hν abar abar h k‖))
          = 3 * |P.μ k|⁻¹ * (Cosine.weights ν hν k * ‖mul3 ν hν abar abar h k‖) := by ring
        _ ≤ 3 * |P.μ m|⁻¹ * (Cosine.weights ν hν k * ‖mul3 ν hν abar abar h k‖) := by
          gcongr
  have hsum3 : Summable fun k => 3 * |P.μ m|⁻¹ *
      (Cosine.weights ν hν k * ‖mul3 ν hν abar abar h k‖) :=
    (mul3 ν hν abar abar h).summable.mul_left _
  have hpart1 : ∑ k ∈ s, Cosine.weights ν hν k * ‖v k‖ ≤
      3 * (∑ k ∈ s, (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ν ^ k) * ‖h‖ := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Cosine.weights_apply, Real.norm_eq_abs]
    calc ν ^ k * |v k| ≤ ν ^ k * (3 * (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ‖h‖) :=
          mul_le_mul_of_nonneg_left (hv_fin k hk) (pow_pos (Chebyshev.nu_pos hν) k).le
      _ = 3 * ((∑ n ∈ s, |AN k n| * W ν hν m abar n) * ν ^ k) * ‖h‖ := by ring
  have hpart2 : ∑' k, (if k ∈ s then 0 else Cosine.weights ν hν k * ‖v k‖) ≤
      48 * ‖abar‖ ^ 2 / |P.μ m| * ‖h‖ := by
    refine (Summable.tsum_le_tsum hv_tail (Summable.of_nonneg_of_le (fun k => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg ((Cosine.weights ν hν).pos k).le (norm_nonneg _)) hv_tail hsum3)
      hsum3).trans ?_
    rw [tsum_mul_left, ← WeightedL1.norm_eq_tsum]
    have h8 := norm_mul3_le (ν := ν) (hν := hν) abar abar h
    calc 3 * |P.μ m|⁻¹ * ‖mul3 ν hν abar abar h‖ ≤ 3 * |P.μ m|⁻¹ * (8 * ‖abar‖ * ‖abar‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ ≤ 48 * ‖abar‖ ^ 2 / |P.μ m| * ‖h‖ := by
          rw [div_eq_mul_inv]
          have : 0 ≤ ‖abar‖ ^ 2 * |P.μ m|⁻¹ * ‖h‖ := by positivity
          nlinarith
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum_add_tsum_ite v.summable s]
  calc ∑ k ∈ s, Cosine.weights ν hν k * ‖v k‖ +
        ∑' k, (if k ∈ s then 0 else Cosine.weights ν hν k * ‖v k‖)
      ≤ 3 * (∑ k ∈ s, (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ν ^ k) * ‖h‖ +
          48 * ‖abar‖ ^ 2 / |P.μ m| * ‖h‖ := add_le_add hpart1 hpart2
    _ = (3 * ∑ k ∈ s, (∑ n ∈ s, |AN k n| * W ν hν m abar n) * ν ^ k +
          48 * ‖abar‖ ^ 2 / |P.μ m|) * ‖h‖ := by ring
    _ ≤ Z₁ * ‖h‖ := mul_le_mul_of_nonneg_right hZ₁ (norm_nonneg h)

/-! #### The bound `Z₂` -/

omit hμ in
/-- `(DF(c) - DF(a)) h = ι(3 (a * a * h - c * c * h))`. -/
theorem DF_sub_DF_apply (c a h : X ν hν) :
    (P.DF ν hν c - P.DF ν hν a) h =
      P.incl ν hν ((3 : ℝ) • (mul3 ν hν a a h - mul3 ν hν c c h)) := by
  rw [sub_apply, DF_apply, DF_apply, smul_sub, map_sub]
  abel

/-- On sequences in `ℓ¹_ν`, `A` acts as the operator with the same matrix on `ℓ¹_ν`. -/
theorem opA_incl {α : ℝ}
    (hK : FiniteTail.Bound (Finset.range m) (fun (_ : Fin 1) k (_ : Fin 1) l => AN k l) P.tailA
      (Cosine.weights ν hν) (Cosine.weights ν hν) (fun _ _ => α)) (y : X ν hν) :
    P.opA ν hν hμ AN (P.incl ν hν y) = FiniteTail.op1 hK y := by
  ext k
  rw [opA, FiniteTail.op1_apply, FiniteTail.op1_apply]
  simp only [incl_apply]

/-- The bound `Z₂(r) = 96 α ‖ā‖ + 48 α r`, valid for every `r ≥ 0`. -/
theorem norm_opA_DF_sub_DF_le {α : ℝ}
    (hKA : ∀ l ∈ Finset.range m, ∑ k ∈ Finset.range m, |AN k l| * ν ^ k ≤ α * ν ^ l)
    (hαμ : |P.μ m|⁻¹ ≤ α) {r Z₂ : ℝ} (hr : 0 ≤ r)
    (hZ₂ : 96 * α * ‖abar‖ + 48 * α * r ≤ Z₂) (c : X ν hν) (hc : c ∈ closedBall abar r) :
    ‖(P.opA ν hν hμ AN).comp (P.DF ν hν c - P.DF ν hν abar)‖ ≤ Z₂ * r := by
  have hα0 : 0 ≤ α := (inv_nonneg.2 (abs_nonneg _)).trans hαμ
  have hKAb : FiniteTail.Bound (Finset.range m) (fun (_ : Fin 1) k (_ : Fin 1) l => AN k l)
      P.tailA (Cosine.weights ν hν) (Cosine.weights ν hν) (fun _ _ => α) :=
    ⟨fun _ _ => hα0, fun _ _ l hl => by
      simpa only [Real.norm_eq_abs, Cosine.weights_apply] using hKA l hl,
      fun _ l hl => P.tailA_bound_X hμ hαμ l hl⟩
  have hca : ‖c - abar‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hc
  have hcpa : ‖c + abar‖ ≤ 2 * ‖abar‖ + r := by
    calc ‖c + abar‖ = ‖(c - abar) + (abar + abar)‖ := by congr 1; abel
      _ ≤ ‖c - abar‖ + (‖abar‖ + ‖abar‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ 2 * ‖abar‖ + r := by linarith
  have hZ₂nn : 0 ≤ Z₂ := le_trans (by positivity) hZ₂
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hZ₂nn hr) fun h => ?_
  rw [ContinuousLinearMap.comp_apply, P.DF_sub_DF_apply, P.opA_incl hμ AN hKAb]
  refine (FiniteTail.norm_op1_apply_le hKAb _).trans ?_
  have hy : ‖(3 : ℝ) • (mul3 ν hν abar abar h - mul3 ν hν c c h)‖ ≤
      24 * r * (2 * ‖abar‖ + r) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3), norm_sub_rev]
    calc 3 * ‖mul3 ν hν c c h - mul3 ν hν abar abar h‖
        ≤ 3 * (8 * ‖c - abar‖ * ‖c + abar‖ * ‖h‖) :=
          mul_le_mul_of_nonneg_left (norm_mul3_sub_le c abar h) (by norm_num)
      _ ≤ 3 * (8 * r * (2 * ‖abar‖ + r) * ‖h‖) := by gcongr
      _ = 24 * r * (2 * ‖abar‖ + r) * ‖h‖ := by ring
  calc α * ‖(3 : ℝ) • (mul3 ν hν abar abar h - mul3 ν hν c c h)‖
      ≤ α * (24 * r * (2 * ‖abar‖ + r) * ‖h‖) := mul_le_mul_of_nonneg_left hy hα0
    _ ≤ (96 * α * ‖abar‖ + 48 * α * r) * r * ‖h‖ := by
        have : 0 ≤ α * r * ‖h‖ * (2 * ‖abar‖ + r) := by positivity
        nlinarith [norm_nonneg abar, norm_nonneg h]
    _ ≤ Z₂ * r * ‖h‖ := by gcongr

/-- If `‖I - A A†‖ < 1`, then `A` is injective. -/
theorem opA_injective
    (h : ‖ContinuousLinearMap.id ℝ _ - (P.opA ν hν hμ AN).comp (P.opD ν hν m abar)‖ < 1) :
    Function.Injective (P.opA ν hν hμ AN) :=
  FiniteTail.injective_op1 _ _ (fun k hk => by
    have hk' : m ≤ k := by rw [Finset.mem_range] at hk; omega
    simpa [tailA] using (abs_pos.1 (hμ.pos hk'))) h

end Bounds

/-! ### The theorem -/

/-- The radii polynomial theorem for a cubic equilibrium problem in cosine series, with two radii
`r₀ ≤ r₁` (see the module docstring for the bounds). -/
theorem radii_poly_two_radii (abar : X ν hν) {m : ℕ} (hm : 1 ≤ m)
    (habar : ∀ k, m ≤ k → abar k = 0) (hμ : P.TailCond m) (AN : ℕ → ℕ → ℝ)
    {r₀ r₁ Y₀ Z₀ Z₁ Z₂₀ Z₂₁ α : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∑ k ∈ Finset.range m, |∑ l ∈ Finset.range m, AN k l * P.F ν hν abar l| * ν ^ k +
        ∑ k ∈ Finset.Ico m (3 * m - 2), |P.F ν hν abar k| * ν ^ k / |P.μ k| ≤ Y₀)
    (hZ₀ : ∀ l ∈ Finset.range m, ∑ k ∈ Finset.range m,
      |P.matE ν hν m AN abar k l| * ν ^ k ≤ Z₀ * ν ^ l)
    (hZ₁ : 3 * ∑ k ∈ Finset.range m, (∑ n ∈ Finset.range m, |AN k n| * W ν hν m abar n) * ν ^ k +
      48 * ‖abar‖ ^ 2 / |P.μ m| ≤ Z₁)
    (hKA : ∀ l ∈ Finset.range m, ∑ k ∈ Finset.range m, |AN k l| * ν ^ k ≤ α * ν ^ l)
    (hαμ : |P.μ m|⁻¹ ≤ α)
    (hZ₂₀ : 96 * α * ‖abar‖ + 48 * α * r₀ ≤ Z₂₀) (hZ₂₁ : 96 * α * ‖abar‖ + 48 * α * r₁ ≤ Z₂₁)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂₁ r₁ < 0) :
    HasIsolatedZero (P.F ν hν) abar r₀ r₁ := by
  have hZ₀0 : 0 ≤ Z₀ := by
    have h0 := hZ₀ 0 (Finset.mem_range.2 (by omega))
    rw [pow_zero, mul_one] at h0
    exact le_trans (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
      (pow_pos (Chebyshev.nu_pos hν) k).le) h0
  have hZ₀' := P.norm_id_sub_opA_opD_le abar hμ AN hZ₀0 hZ₀
  have hZ₁' := P.norm_opA_DF_sub_opD_le abar hμ AN hm habar hZ₁
  have hY₀' := P.norm_opA_F_le abar hμ AN hm habar hY₀
  have hZ₁nn : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁'
  have hZ₂nn : 0 ≤ Z₂₀ * r₀ := (norm_nonneg _).trans
    (P.norm_opA_DF_sub_DF_le abar hμ AN hKA hαμ hr₀.le hZ₂₀ abar (mem_closedBall_self hr₀.le))
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀'
  have hZ₀1 : Z₀ < 1 := by
    simp only [radiiPoly] at hp₀
    nlinarith [mul_nonneg hZ₂nn hr₀.le, mul_nonneg hZ₁nn hr₀.le]
  have hinj := P.opA_injective abar hμ AN (hZ₀'.trans_lt hZ₀1)
  obtain ⟨x, hx, hFx, huniq, -⟩ := RadiiPolynomial.radii_poly_two_radii (𝕜 := ℝ) (P.F ν hν)
    (P.DF ν hν) (P.opA ν hν hμ AN) (P.opD ν hν m abar) abar hinj hr₀ hr₀₁
    (fun x _ => (P.hasFDerivAt_F x).hasFDerivWithinAt) hY₀' hZ₀' hZ₁'
    (fun c hc => P.norm_opA_DF_sub_DF_le abar hμ AN hKA hαμ hr₀.le hZ₂₀ c hc)
    (fun c hc => P.norm_opA_DF_sub_DF_le abar hμ AN hKA hαμ (hr₀.le.trans hr₀₁) hZ₂₁ c hc)
    hp₀ hp₁
  unfold HasIsolatedZero
  exact ⟨x, hx, hFx, huniq⟩

end CubicCosine

end RadiiPolynomial
