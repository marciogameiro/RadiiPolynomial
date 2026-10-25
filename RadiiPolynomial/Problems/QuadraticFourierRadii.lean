module

public import RadiiPolynomial.Problems.QuadraticFourier
public import RadiiPolynomial.BlockTail.FiniteTail
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# The radii polynomial theorem for forced quadratic problems in Fourier series

Let `F(a) = Λ a - ι(a * a + g)` be the operator of a `QuadraticFourier` problem with eigenvalues `λ`
and forcing `g`, `ν ≥ 1`, `N` a truncation dimension with `g_n = 0` for `|n| > N` and the tail
condition `|λ_n| ≥ κ > 0` for `|n| > N` (`TailCond`), `ā ∈ ℓ¹_ν` with `ā_n = 0` for `|n| > N`, and
`A_N = (A_{kl})_{|k|, |l| ≤ N}` a `(2N+1) × (2N+1)` matrix. With `s = {-N, …, N}` (`Fourier.center`):

* `opA`: the approximate inverse `A : Y → X`, the finite block `A_N` and the tail `1/λ_n`;
* `opD`: the approximate derivative `A† : X → Y`, the finite block of `DF(ā)` (`DFN`) and the tail
  `λ_n`.

The bounds (each any number dominating the corresponding expression):

* `norm_opA_F_le` (`Y₀`): `∑_{|k| ≤ N} |(A_N F(ā))_k| ν^{|k|} + ∑_{N < |k| ≤ 2N} |F_k(ā)| ν^{|k|} / |λ_k|`;
* `norm_id_sub_opA_opD_le` (`Z₀`): the column norm of `I - A_N DF^{(N)}(ā)`;
* `norm_opA_DF_sub_opD_le` (`Z₁ = 2 (β + 1/κ) ‖ā‖`), where `β` bounds the column norm of `A_N Γ`,
  `Γ = diag(ν^{2|n| - 2N - 2})`: `ν^{|l|} ∑_{|k| ≤ N} |A_{kl}| ν^{|k|} ≤ β ν^{2N+2}`; the estimate
  uses `Fourier.sum_center_mul_le`;
* `norm_opA_DF_sub_DF_le` (`Z₂ = 2 α`, valid for every radius), where `α` bounds `A` as an operator
  on `ℓ¹_ν`: `α ≥ ν^{-|l|} ∑_{|k| ≤ N} |A_{kl}| ν^{|k|}` and `α ≥ 1/κ`;
* `opA_injective`, and `radii_poly_two_radii`: if `p(r₀) < 0` and `p(r₁) < 0`, `F` has a zero in
  the open ball of radius `r₀` about `ā`, unique in the closed ball of radius `r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace QuadraticFourier

open Fourier Metric

variable (P : QuadraticFourier) {ν : ℝ} {hν : 1 ≤ ν}

/-- The tail condition on the truncation dimension `N`: `|λ_n| ≥ κ > 0` for `|n| > N`. -/
def TailCond (N : ℕ) (κ : ℝ) : Prop := 0 < κ ∧ ∀ n : ℤ, N < n.natAbs → κ ≤ ‖P.lam n‖

variable {P}

theorem TailCond.le {N : ℕ} {κ : ℝ} (h : P.TailCond N κ) {n : ℤ} (hn : n ∉ center N) :
    κ ≤ ‖P.lam n‖ :=
  h.2 n (by rw [mem_center, not_le] at hn; exact hn)

theorem TailCond.pos {N : ℕ} {κ : ℝ} (h : P.TailCond N κ) {n : ℤ} (hn : n ∉ center N) :
    0 < ‖P.lam n‖ :=
  h.1.trans_le (h.le hn)

theorem TailCond.ne_zero {N : ℕ} {κ : ℝ} (h : P.TailCond N κ) {n : ℤ} (hn : n ∉ center N) :
    P.lam n ≠ 0 :=
  norm_pos_iff.1 (h.pos hn)

theorem TailCond.inv_le {N : ℕ} {κ : ℝ} (h : P.TailCond N κ) {n : ℤ} (hn : n ∉ center N) :
    ‖P.lam n‖⁻¹ ≤ κ⁻¹ :=
  inv_anti₀ h.1 (h.le hn)

variable (P)

/-- The tail `1/λ_n` of the approximate inverse. -/
noncomputable def tailA (n : ℤ) : ℂ := (P.lam n)⁻¹

theorem tailA_bound {N : ℕ} {κ : ℝ} (hκ : P.TailCond N κ) (l : ℤ) (hl : l ∉ center N) :
    ‖P.tailA l‖ * Weights.geomInt ν hν l ≤ (1 + κ⁻¹) * P.weightsY ν hν l := by
  have hpos := hκ.pos hl
  have hinv := hκ.inv_le hl
  have hν0 : 0 < ν ^ l.natAbs := pow_pos (nu_pos hν) _
  rw [tailA, norm_inv, Weights.geomInt_apply, weightsY_apply, mul_div_assoc',
    le_div_iff₀ (by positivity)]
  have h1 : ‖P.lam l‖⁻¹ * (1 + ‖P.lam l‖) = ‖P.lam l‖⁻¹ + 1 := by field_simp
  calc ‖P.lam l‖⁻¹ * ν ^ l.natAbs * (1 + ‖P.lam l‖) = (‖P.lam l‖⁻¹ + 1) * ν ^ l.natAbs := by
        rw [← h1]; ring
    _ ≤ (1 + κ⁻¹) * ν ^ l.natAbs := mul_le_mul_of_nonneg_right (by linarith) hν0.le

/-- The tail bound of `A` as an operator on `ℓ¹_ν`. -/
theorem tailA_bound_X {N : ℕ} {κ : ℝ} (hκ : P.TailCond N κ) {α : ℝ} (hα : κ⁻¹ ≤ α) (l : ℤ)
    (hl : l ∉ center N) :
    ‖P.tailA l‖ * Weights.geomInt ν hν l ≤ α * Weights.geomInt ν hν l := by
  rw [tailA, norm_inv]
  exact mul_le_mul_of_nonneg_right ((hκ.inv_le hl).trans hα) ((Weights.geomInt ν hν).pos l).le

variable (ν hν)

/-- The approximate inverse `A : Y → X`: finite block `A_N`, tail `1/λ_n`. -/
noncomputable def opA {N : ℕ} {κ : ℝ} (hκ : P.TailCond N κ) (AN : ℤ → ℤ → ℂ) :
    P.Y ν hν →L[ℂ] X ν hν :=
  FiniteTail.op1 (FiniteTail.crudeBound (s := center N) (M := fun _ k _ l => AN k l)
    (tl := P.tailA) (ω := Weights.geomInt ν hν) (ω' := P.weightsY ν hν)
    (add_nonneg zero_le_one (inv_nonneg.2 hκ.1.le)) (P.tailA_bound hκ))

/-- The matrix of `DF(ā)`: `DFN n l = (DF(ā) e_l)_n`. -/
noncomputable def DFN (abar : X ν hν) (n l : ℤ) : ℂ := P.DF ν hν abar (WeightedL1.single l 1) n

/-- The approximate derivative `A† : X → Y`: finite block of `DF(ā)`, tail `λ_n`. -/
noncomputable def opD (N : ℕ) (abar : X ν hν) : X ν hν →L[ℂ] P.Y ν hν :=
  FiniteTail.op1 (FiniteTail.crudeBound (s := center N)
    (M := fun _ n _ l => P.DFN ν hν abar n l) (tl := P.lam) (ω := P.weightsY ν hν)
    (ω' := Weights.geomInt ν hν) zero_le_one (fun l _ => P.diag_bound l))

/-- `E = I - A_N DF^{(N)}(ā)`. -/
noncomputable def matE (N : ℕ) (AN : ℤ → ℤ → ℂ) (abar : X ν hν) (k l : ℤ) : ℂ :=
  (if k = l then 1 else 0) - ∑ n ∈ center N, AN k n * P.DFN ν hν abar n l

variable {ν hν}

/-! ### The bounds -/

section Bounds

variable (abar : X ν hν) {N : ℕ} {κ : ℝ} (hκ : P.TailCond N κ) (AN : ℤ → ℤ → ℂ)

/-- `F(ā)_n = 0` for `|n| > 2N`. -/
theorem F_eq_zero (habar : SuppLe abar N) (hg : ∀ n : ℤ, N < n.natAbs → P.g n = 0) {n : ℤ}
    (hn : 2 * N < n.natAbs) : P.F ν hν abar n = 0 := by
  rw [F_apply, habar n (by omega), (habar.mul habar) n (by omega), hg n (by omega)]
  ring

/-- The bound `Y₀`. -/
theorem norm_opA_F_le (habar : SuppLe abar N) (hg : ∀ n : ℤ, N < n.natAbs → P.g n = 0) {Y₀ : ℝ}
    (hY₀ : ∑ k ∈ center N, ‖∑ l ∈ center N, AN k l * P.F ν hν abar l‖ * ν ^ k.natAbs +
        ∑ k ∈ center (2 * N) \ center N, ‖P.F ν hν abar k‖ * ν ^ k.natAbs / ‖P.lam k‖ ≤ Y₀) :
    ‖P.opA ν hν hκ AN (P.F ν hν abar)‖ ≤ Y₀ := by
  rw [WeightedL1.norm_eq_tsum]
  have hsupp : ∀ k ∉ center (2 * N),
      Weights.geomInt ν hν k * ‖P.opA ν hν hκ AN (P.F ν hν abar) k‖ = 0 := fun k hk => by
    rw [mem_center, not_le] at hk
    rw [opA, FiniteTail.op1_apply, ite_eq_right (by rw [mem_center]; omega),
      P.F_eq_zero abar habar hg hk, mul_zero, norm_zero, mul_zero]
  rw [tsum_eq_sum hsupp, ← Finset.sum_sdiff (center_mono (by omega : N ≤ 2 * N)), add_comm]
  refine le_of_eq_of_le ?_ hY₀
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [opA, FiniteTail.op1_apply, ite_eq_left hk, Weights.geomInt_apply, mul_comm]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_sdiff] at hk
    rw [opA, FiniteTail.op1_apply, ite_eq_right hk.2, Weights.geomInt_apply, norm_mul, tailA,
      norm_inv]
    field_simp

/-- The bound `Z₀`. -/
theorem norm_id_sub_opA_opD_le {Z₀ : ℝ} (hZ₀0 : 0 ≤ Z₀)
    (hZ₀ : ∀ l ∈ center N, ∑ k ∈ center N,
      ‖P.matE ν hν N AN abar k l‖ * ν ^ k.natAbs ≤ Z₀ * ν ^ l.natAbs) :
    ‖ContinuousLinearMap.id ℂ _ - (P.opA ν hν hκ AN).comp (P.opD ν hν N abar)‖ ≤ Z₀ := by
  have hE : FiniteTail.Bound (center N)
      (fun (_ : Fin 1) k (_ : Fin 1) l => P.matE ν hν N AN abar k l)
      (fun _ => (0 : ℂ)) (Weights.geomInt ν hν) (Weights.geomInt ν hν)
      (fun (_ : Fin 1) (_ : Fin 1) => Z₀) :=
    ⟨fun _ _ => hZ₀0, fun _ _ l hl => by
      simpa only [Weights.geomInt_apply] using hZ₀ l hl, fun _ l _ => by
      rw [norm_zero, zero_mul]
      exact mul_nonneg hZ₀0 ((Weights.geomInt ν hν).pos l).le⟩
  rw [opA, opD, FiniteTail.id_sub_op1_comp_op1 _ _ hE (fun j k i l _ _ => by
    simp [matE, Subsingleton.elim j i]) (fun k hk => by
    rw [tailA, inv_mul_cancel₀ (hκ.ne_zero hk), sub_self])]
  exact FiniteTail.norm_op1_le hE

/-! #### The operator `DF(ā) - A†` -/

omit hκ in
/-- Rows `|n| ≤ N` of `A† h`: `DF(ā)` applied to the finite part of `h`. -/
theorem opD_apply_fin (h : X ν hν) {n : ℤ} (hn : n ∈ center N) :
    P.opD ν hν N abar h n = P.DF ν hν abar (finPart N h) n := by
  rw [opD, FiniteTail.op1_apply, ite_eq_left hn, finPart, map_sum, WeightedLp.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, WeightedLp.smul_apply, DFN, mul_comm]

omit hκ in
/-- Rows `|n| ≤ N` of `(DF(ā) - A†) h`: `-2 (ā * h_∞)_n`, `h_∞ = h - finPart N h`. -/
theorem DF_sub_opD_apply_fin (h : X ν hν) {n : ℤ} (hn : n ∈ center N) :
    (P.DF ν hν abar - P.opD ν hν N abar) h n = -(2 * (abar * (h - finPart N h)) n) := by
  rw [sub_apply, WeightedLp.sub_apply, P.opD_apply_fin abar h hn, ← WeightedLp.sub_apply,
    ← map_sub, DF_apply_coeff, sub_finPart_apply, ite_eq_left hn]
  ring

omit hκ in
/-- Rows `|n| > N` of `(DF(ā) - A†) h`: `-2 (ā * h)_n`. -/
theorem DF_sub_opD_apply_tail (h : X ν hν) {n : ℤ} (hn : n ∉ center N) :
    (P.DF ν hν abar - P.opD ν hν N abar) h n = -(2 * (abar * h) n) := by
  rw [sub_apply, WeightedLp.sub_apply, DF_apply_coeff, opD, FiniteTail.op1_apply, ite_eq_right hn]
  ring

/-- The bound `Z₁`. -/
theorem norm_opA_DF_sub_opD_le {β Z₁ : ℝ}
    (hβ : ∀ l ∈ center N,
      (∑ k ∈ center N, ‖AN k l‖ * ν ^ k.natAbs) * ν ^ l.natAbs ≤ β * ν ^ (2 * N + 2))
    (hZ₁ : 2 * (β + κ⁻¹) * ‖abar‖ ≤ Z₁) :
    ‖(P.opA ν hν hκ AN).comp (P.DF ν hν abar - P.opD ν hν N abar)‖ ≤ Z₁ := by
  set s := center N with hs
  have hν0 := nu_pos hν
  have hνN : 0 < ν ^ (2 * N + 2) := pow_pos hν0 _
  have hβ0 : 0 ≤ β := by
    have h0 := hβ 0 (zero_mem_center N)
    have : 0 ≤ β * ν ^ (2 * N + 2) := le_trans (mul_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (pow_pos hν0 _).le) (pow_pos hν0 _).le) h0
    exact (mul_nonneg_iff_of_pos_right hνN).1 this
  have hκ0 : 0 ≤ κ⁻¹ := inv_nonneg.2 hκ.1.le
  have hZ₁nn : 0 ≤ Z₁ := le_trans (by positivity) hZ₁
  refine ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun h => ?_
  rw [ContinuousLinearMap.comp_apply]
  set T := P.DF ν hν abar - P.opD ν hν N abar with hT
  set v := P.opA ν hν hκ AN (T h) with hv
  -- rows `|n| ≤ N` of `T h`, divided by `ν^{|n|}`
  have hΓ : ∑ n ∈ s, ‖T h n‖ / ν ^ n.natAbs ≤ 2 * (‖abar‖ * ‖h‖ / ν ^ (2 * N + 2)) := by
    calc ∑ n ∈ s, ‖T h n‖ / ν ^ n.natAbs
        = 2 * ∑ n ∈ s, ‖(abar * (h - finPart N h)) n‖ / ν ^ n.natAbs := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hT, P.DF_sub_opD_apply_fin abar h hn, norm_neg, norm_mul, Complex.norm_two]
          ring
      _ ≤ 2 * (‖abar‖ * ‖h - finPart N h‖ / ν ^ (2 * N + 2)) :=
          mul_le_mul_of_nonneg_left (sum_center_mul_le abar _ fun n hn => by
            rw [sub_finPart_apply, ite_eq_left hn]) zero_le_two
      _ ≤ 2 * (‖abar‖ * ‖h‖ / ν ^ (2 * N + 2)) := by
          gcongr
          exact norm_sub_finPart_le h
  -- the finite part of `v`
  have hpart1 : ∑ k ∈ s, Weights.geomInt ν hν k * ‖v k‖ ≤ 2 * β * ‖abar‖ * ‖h‖ := by
    have hcol : ∀ n ∈ s, ∑ k ∈ s, ‖AN k n‖ * ν ^ k.natAbs ≤ β * ν ^ (2 * N + 2) / ν ^ n.natAbs :=
      fun n hn => by rw [le_div_iff₀ (pow_pos hν0 _)]; exact hβ n hn
    calc ∑ k ∈ s, Weights.geomInt ν hν k * ‖v k‖
        ≤ ∑ k ∈ s, ν ^ k.natAbs * ∑ n ∈ s, ‖AN k n‖ * ‖T h n‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [hv, opA, FiniteTail.op1_apply, ite_eq_left hk, Weights.geomInt_apply]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_))
            (pow_pos hν0 _).le
          exact Finset.sum_congr rfl fun n _ => norm_mul _ _
      _ = ∑ n ∈ s, (∑ k ∈ s, ‖AN k n‖ * ν ^ k.natAbs) * ‖T h n‖ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑ n ∈ s, β * ν ^ (2 * N + 2) / ν ^ n.natAbs * ‖T h n‖ :=
          Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hcol n hn) (norm_nonneg _)
      _ = β * ν ^ (2 * N + 2) * ∑ n ∈ s, ‖T h n‖ / ν ^ n.natAbs := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ β * ν ^ (2 * N + 2) * (2 * (‖abar‖ * ‖h‖ / ν ^ (2 * N + 2))) :=
          mul_le_mul_of_nonneg_left hΓ (by positivity)
      _ = 2 * β * ‖abar‖ * ‖h‖ := by field_simp
  -- the tail of `v`
  have hv_tail : ∀ k, (if k ∈ s then 0 else Weights.geomInt ν hν k * ‖v k‖) ≤
      2 * κ⁻¹ * (Weights.geomInt ν hν k * ‖(abar * h) k‖) := by
    intro k
    by_cases hk : k ∈ s
    · rw [ite_eq_left hk]
      exact mul_nonneg (by positivity)
        (mul_nonneg ((Weights.geomInt ν hν).pos k).le (norm_nonneg _))
    · rw [ite_eq_right hk, hv, opA, FiniteTail.op1_apply, ite_eq_right hk, hT,
        P.DF_sub_opD_apply_tail abar h hk, tailA, norm_mul, norm_inv, norm_neg, norm_mul,
        Complex.norm_two]
      have hinv := hκ.inv_le hk
      have hw := ((Weights.geomInt ν hν).pos k).le
      calc Weights.geomInt ν hν k * (‖P.lam k‖⁻¹ * (2 * ‖(abar * h) k‖))
          = 2 * ‖P.lam k‖⁻¹ * (Weights.geomInt ν hν k * ‖(abar * h) k‖) := by ring
        _ ≤ 2 * κ⁻¹ * (Weights.geomInt ν hν k * ‖(abar * h) k‖) := by gcongr
  have hsum2 : Summable fun k => 2 * κ⁻¹ * (Weights.geomInt ν hν k * ‖(abar * h) k‖) :=
    (abar * h).summable.mul_left _
  have hpart2 : ∑' k, (if k ∈ s then 0 else Weights.geomInt ν hν k * ‖v k‖) ≤
      2 * κ⁻¹ * ‖abar‖ * ‖h‖ := by
    refine (Summable.tsum_le_tsum hv_tail (Summable.of_nonneg_of_le (fun k => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg ((Weights.geomInt ν hν).pos k).le (norm_nonneg _)) hv_tail hsum2)
      hsum2).trans ?_
    rw [tsum_mul_left, ← WeightedL1.norm_eq_tsum, mul_assoc (2 * κ⁻¹)]
    exact mul_le_mul_of_nonneg_left (norm_mul_le abar h) (by positivity)
  rw [WeightedL1.norm_eq_tsum, tsum_eq_sum_add_tsum_ite v.summable s]
  calc ∑ k ∈ s, Weights.geomInt ν hν k * ‖v k‖ +
        ∑' k, (if k ∈ s then 0 else Weights.geomInt ν hν k * ‖v k‖)
      ≤ 2 * β * ‖abar‖ * ‖h‖ + 2 * κ⁻¹ * ‖abar‖ * ‖h‖ := add_le_add hpart1 hpart2
    _ = 2 * (β + κ⁻¹) * ‖abar‖ * ‖h‖ := by ring
    _ ≤ Z₁ * ‖h‖ := mul_le_mul_of_nonneg_right hZ₁ (norm_nonneg h)

/-! #### The bound `Z₂` -/

omit hκ in
/-- `(DF(c) - DF(a)) h = ι(2 (a - c) * h)`. -/
theorem DF_sub_DF_apply (c a h : X ν hν) :
    (P.DF ν hν c - P.DF ν hν a) h = P.incl ν hν ((2 : ℂ) • ((a - c) * h)) := by
  rw [sub_apply, DF_apply, DF_apply, sub_mul, smul_sub, map_sub]
  abel

/-- On sequences in `ℓ¹_ν`, `A` acts as the operator with the same matrix on `ℓ¹_ν`. -/
theorem opA_incl {α : ℝ}
    (hK : FiniteTail.Bound (center N) (fun (_ : Fin 1) k (_ : Fin 1) l => AN k l) P.tailA
      (Weights.geomInt ν hν) (Weights.geomInt ν hν) (fun _ _ => α)) (y : X ν hν) :
    P.opA ν hν hκ AN (P.incl ν hν y) = FiniteTail.op1 hK y := by
  ext k
  rw [opA, FiniteTail.op1_apply, FiniteTail.op1_apply]
  simp only [incl_apply]

/-- The bound `Z₂ = 2 α`, valid for every radius `r ≥ 0`. -/
theorem norm_opA_DF_sub_DF_le {α : ℝ}
    (hKA : ∀ l ∈ center N, ∑ k ∈ center N, ‖AN k l‖ * ν ^ k.natAbs ≤ α * ν ^ l.natAbs)
    (hακ : κ⁻¹ ≤ α) {r Z₂ : ℝ} (hr : 0 ≤ r) (hZ₂ : 2 * α ≤ Z₂) (c : X ν hν)
    (hc : c ∈ closedBall abar r) :
    ‖(P.opA ν hν hκ AN).comp (P.DF ν hν c - P.DF ν hν abar)‖ ≤ Z₂ * r := by
  have hα0 : 0 ≤ α := (inv_nonneg.2 hκ.1.le).trans hακ
  have hKAb : FiniteTail.Bound (center N) (fun (_ : Fin 1) k (_ : Fin 1) l => AN k l)
      P.tailA (Weights.geomInt ν hν) (Weights.geomInt ν hν) (fun _ _ => α) :=
    ⟨fun _ _ => hα0, fun _ _ l hl => by
      simpa only [Weights.geomInt_apply] using hKA l hl,
      fun _ l hl => P.tailA_bound_X hκ hακ l hl⟩
  have hca : ‖abar - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm'] at hc
  have hZ₂nn : 0 ≤ Z₂ := le_trans (by positivity) hZ₂
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hZ₂nn hr) fun h => ?_
  rw [ContinuousLinearMap.comp_apply, P.DF_sub_DF_apply, P.opA_incl hκ AN hKAb]
  refine (FiniteTail.norm_op1_apply_le hKAb _).trans ?_
  have hy : ‖(2 : ℂ) • ((abar - c) * h)‖ ≤ 2 * r * ‖h‖ := by
    rw [norm_smul, Complex.norm_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right hca (norm_nonneg h))) zero_le_two
  calc α * ‖(2 : ℂ) • ((abar - c) * h)‖ ≤ α * (2 * r * ‖h‖) := mul_le_mul_of_nonneg_left hy hα0
    _ = 2 * α * r * ‖h‖ := by ring
    _ ≤ Z₂ * r * ‖h‖ := by gcongr

/-- If `‖I - A A†‖ < 1`, then `A` is injective. -/
theorem opA_injective
    (h : ‖ContinuousLinearMap.id ℂ _ - (P.opA ν hν hκ AN).comp (P.opD ν hν N abar)‖ < 1) :
    Function.Injective (P.opA ν hν hκ AN) :=
  FiniteTail.injective_op1 _ _ (fun _ hk => inv_ne_zero (hκ.ne_zero hk)) h

end Bounds

/-! ### The theorem -/

/-- The radii polynomial theorem for a forced quadratic problem in Fourier series, with two radii
`r₀ ≤ r₁` (see the module docstring for the bounds). -/
theorem radii_poly_two_radii (abar : X ν hν) {N : ℕ} (habar : SuppLe abar N)
    (hg : ∀ n : ℤ, N < n.natAbs → P.g n = 0) {κ : ℝ} (hκ : P.TailCond N κ) (AN : ℤ → ℤ → ℂ)
    {r₀ r₁ Y₀ Z₀ Z₁ Z₂ α β : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    (hY₀ : ∑ k ∈ center N, ‖∑ l ∈ center N, AN k l * P.F ν hν abar l‖ * ν ^ k.natAbs +
        ∑ k ∈ center (2 * N) \ center N, ‖P.F ν hν abar k‖ * ν ^ k.natAbs / ‖P.lam k‖ ≤ Y₀)
    (hZ₀ : ∀ l ∈ center N, ∑ k ∈ center N,
      ‖P.matE ν hν N AN abar k l‖ * ν ^ k.natAbs ≤ Z₀ * ν ^ l.natAbs)
    (hβ : ∀ l ∈ center N,
      (∑ k ∈ center N, ‖AN k l‖ * ν ^ k.natAbs) * ν ^ l.natAbs ≤ β * ν ^ (2 * N + 2))
    (hZ₁ : 2 * (β + κ⁻¹) * ‖abar‖ ≤ Z₁)
    (hKA : ∀ l ∈ center N, ∑ k ∈ center N, ‖AN k l‖ * ν ^ k.natAbs ≤ α * ν ^ l.natAbs)
    (hακ : κ⁻¹ ≤ α) (hZ₂ : 2 * α ≤ Z₂)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂ r₁ < 0) :
    HasIsolatedZero (P.F ν hν) abar r₀ r₁ := by
  have hZ₀0 : 0 ≤ Z₀ := by
    have h0 := hZ₀ 0 (zero_mem_center N)
    rw [Int.natAbs_zero, pow_zero, mul_one] at h0
    exact le_trans (Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _)
      (pow_pos (nu_pos hν) _).le) h0
  have hZ₀' := P.norm_id_sub_opA_opD_le abar hκ AN hZ₀0 hZ₀
  have hZ₁' := P.norm_opA_DF_sub_opD_le abar hκ AN hβ hZ₁
  have hY₀' := P.norm_opA_F_le abar hκ AN habar hg hY₀
  have hZ₁nn : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁'
  have hZ₂nn : 0 ≤ Z₂ * r₀ := (norm_nonneg _).trans
    (P.norm_opA_DF_sub_DF_le abar hκ AN hKA hακ hr₀.le hZ₂ abar (mem_closedBall_self hr₀.le))
  have hZ₀1 : Z₀ < 1 := by
    have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀'
    simp only [radiiPoly] at hp₀
    nlinarith [mul_nonneg hZ₂nn hr₀.le, mul_nonneg hZ₁nn hr₀.le]
  have hinj := P.opA_injective abar hκ AN (hZ₀'.trans_lt hZ₀1)
  obtain ⟨x, hx, hFx, huniq, -⟩ := RadiiPolynomial.radii_poly_two_radii (𝕜 := ℂ) (P.F ν hν)
    (P.DF ν hν) (P.opA ν hν hκ AN) (P.opD ν hν N abar) abar hinj hr₀ hr₀₁
    (fun x _ => (P.hasFDerivAt_F x).hasFDerivWithinAt) hY₀' hZ₀' hZ₁'
    (fun c hc => P.norm_opA_DF_sub_DF_le abar hκ AN hKA hακ hr₀.le hZ₂ c hc)
    (fun c hc => P.norm_opA_DF_sub_DF_le abar hκ AN hKA hακ (hr₀.le.trans hr₀₁) hZ₂ c hc)
    hp₀ hp₁
  unfold HasIsolatedZero
  exact ⟨x, hx, hFx, huniq⟩

end QuadraticFourier

end RadiiPolynomial
