module

public import RadiiPolynomial.Problems.FourierPeriodic
public import RadiiPolynomial.BlockTail.ParamTail
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# The radii polynomial theorem for periodic orbits in Fourier series

Let `F : X → Y` be the operator of a `FourierPeriodic` problem, `ν ≥ 1`, `N` a truncation dimension
with `N₀ ≤ N`, `x̄ = (τ̄, ā) ∈ X` with `ā_{j,k} = 0` for `|k| > N`, `deg f_j ≤ M` (`M ≥ 1`), and
`A^{(N)}` a matrix on `ℂ × (ℂ^{2N+1})^n`, given by its border `A` (the entries involving the scalar
unknown, `ParamTail.Border`) and its block `AM`. With `s = {-N, …, N}` (`Fourier.center`):

* `opA`: the approximate inverse `A : Y → X`, the matrix `A^{(N)}` and the tail `1/(ik)`;
* `opD`: the approximate derivative `A† : X → Y`, the matrix of `DF(x̄)` on the modes `|k| ≤ N`
  (`DFb`, `DFM`) and the tail `ik`.

The bounds (each any number dominating the corresponding expression); `|·|` on `ℂ` and `‖·‖` on
`ℓ¹_ν`, `max` over the components `0, …, n`:

* `norm_opA_F_le` (`Y₀`): `|(A^{(N)} F^{(N)}(x̄))₀|` and, for each `j`,
  `∑_{|k| ≤ N} |(A^{(N)} F^{(N)}(x̄))_{j,k}| ν^{|k|} + ∑_{N < |k| ≤ MN} |F_j(x̄)_k| ν^{|k|} / |k|`;
* `norm_id_sub_opA_opD_le` (`Z₀`): the norms of the blocks of `B = I - A^{(N)} DF^{(N)}(x̄)`
  (`matEb`, `matEM`), `|B₀₀| + ∑ᵢ ‖B₀ᵢ‖ ≤ Z₀` and `‖B_{j0}‖ + ∑ᵢ ‖B_{ji}‖ ≤ Z₀`;
* `norm_opA_DF_sub_opD_le` (`Z₁`): with `κ_{0i} ≥ ‖A_{0i} Γ‖`, `κ_{ji} ≥ ‖A_{ji} Γ‖`
  (`Γ = diag(ν^{2|k| - 2N - 2})`), `Dφ_{i'i} ≥ ‖∂_{i'}φ_i(ā)‖` and `Φ_j ≥ ‖π_∞ φ_j(ā)‖`:
  `|τ̄| ∑ᵢ κ_{0i} ∑_{i'} Dφ_{i'i} ≤ Z₁` and
  `|τ̄| ∑ᵢ κ_{ji} ∑_{i'} Dφ_{i'i} + (Φ_j + |τ̄| ∑_{i'} Dφ_{i'j}) / (N + 1) ≤ Z₁`;
* `norm_opA_DF_sub_DF_le` (`Z₂(r)`): with `Rᵢ ≥ ‖A_{0i}‖`, `K_{ji} ≥ ‖A_{ji}‖` (`A` on `ℓ¹_ν`,
  `K_{jj} ≥ 1/(N+1)`) and `Θᵢ(r) = 2 ∑_l η_{il}(r) + |τ̄| ∑_{l,m} ζ_{i,l,m}(r)` (`Theta`), where
  `η_{il}(r) = |∂_l f_i|(‖ā‖ + r)` and `ζ_{ilm}(r) = |∂_l ∂_m f_i|(‖ā‖ + r)`:
  `∑ᵢ Rᵢ Θᵢ(r) ≤ Z₂` and `∑ᵢ K_{ji} Θᵢ(r) ≤ Z₂`;
* `opA_injective`, and `radii_poly_two_radii`: if `p(r₀) < 0` and `p(r₁) < 0`, `F` has a zero in
  the open ball of radius `r₀` about `x̄`, unique in the closed ball of radius `r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace FourierPeriodic

open Fourier Metric MvPolynomial ParamTail

variable {n : ℕ} (P : FourierPeriodic n) {ν : ℝ} {hν : 1 ≤ ν}

/-- The tail `1/(ik)` of the approximate inverse. -/
noncomputable def tailA (k : ℤ) : ℂ := (Complex.I * k)⁻¹

theorem norm_tailA (k : ℤ) : ‖tailA k‖ = ((k.natAbs : ℕ) : ℝ)⁻¹ := by
  rw [tailA, norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Nat.cast_natAbs,
    Int.cast_abs]

theorem succ_le_natAbs {N : ℕ} {k : ℤ} (hk : k ∉ center N) : N + 1 ≤ k.natAbs := by
  rw [mem_center, not_le] at hk; exact hk

theorem I_mul_ne_zero {N : ℕ} {k : ℤ} (hk : k ∉ center N) : Complex.I * k ≠ 0 := by
  have : k ≠ 0 := fun h => hk (h ▸ zero_mem_center N)
  exact mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.2 this)

theorem inv_natAbs_le {N : ℕ} {k : ℤ} (hk : k ∉ center N) :
    ((k.natAbs : ℕ) : ℝ)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ :=
  inv_anti₀ (by positivity) (by exact_mod_cast succ_le_natAbs hk)

theorem tailA_bound (N : ℕ) (l : ℤ) (hl : l ∉ center N) :
    ‖tailA l‖ * Weights.geomInt ν hν l ≤ 2 * weightsY ν hν l := by
  have h1 : (1 : ℝ) ≤ l.natAbs := by
    have := succ_le_natAbs hl; exact_mod_cast (by omega : 1 ≤ l.natAbs)
  rw [norm_tailA, Weights.geomInt_apply, weightsY_apply, mul_div_assoc', le_div_iff₀ (by positivity)]
  have hν0 : 0 < ν ^ l.natAbs := pow_pos (nu_pos hν) _
  have h2 : ((l.natAbs : ℕ) : ℝ)⁻¹ * (1 + l.natAbs) ≤ 2 := by
    rw [mul_add, mul_one, inv_mul_cancel₀ (by positivity)]
    linarith [inv_le_one_of_one_le₀ h1]
  calc ((l.natAbs : ℕ) : ℝ)⁻¹ * ν ^ l.natAbs * (1 + l.natAbs)
      = ((l.natAbs : ℕ) : ℝ)⁻¹ * (1 + l.natAbs) * ν ^ l.natAbs := by ring
    _ ≤ 2 * ν ^ l.natAbs := mul_le_mul_of_nonneg_right h2 hν0.le

theorem tailA_bound_X {N : ℕ} {α : ℝ} (hα : ((N : ℝ) + 1)⁻¹ ≤ α) (l : ℤ) (hl : l ∉ center N) :
    ‖tailA l‖ * Weights.geomInt ν hν l ≤ α * Weights.geomInt ν hν l := by
  rw [norm_tailA]
  exact mul_le_mul_of_nonneg_right ((inv_natAbs_le hl).trans hα)
    ((Weights.geomInt ν hν).pos l).le

variable (ν hν)

/-- The approximate inverse `A : Y → X`: border `A`, finite block `AM`, tail `1/(ik)`. -/
noncomputable def opA (N : ℕ) (A : Border n ℤ ℂ) (AM : Fin n → ℤ → Fin n → ℤ → ℂ) :
    Y n ν hν →L[ℂ] X n ν hν :=
  ParamTail.op (center N) A (FiniteTail.crudeBound (s := center N) (M := AM) (tl := tailA)
    (ω := Weights.geomInt ν hν) (ω' := weightsY ν hν) zero_le_two (tailA_bound N))

/-- The border of the matrix of `DF(x̄)`: `DF(x̄)` applied to `(1, 0)` and to `(0, e_{i,l})`. -/
noncomputable def DFb (xbar : X n ν hν) : Border n ℤ ℂ where
  a00 := (P.DF ν hν xbar (1, 0)).1
  row i l := (P.DF ν hν xbar (0, FiniteTail.unitVec i l)).1
  col j m := (P.DF ν hν xbar (1, 0)).2 j m

/-- The block of the matrix of `DF(x̄)`: `DFM j m i l = (DF(x̄) (0, e_{i,l}))_{j,m}`. -/
noncomputable def DFM (xbar : X n ν hν) (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : ℂ :=
  (P.DF ν hν xbar (0, FiniteTail.unitVec i l)).2 j m

/-- The approximate derivative `A† : X → Y`: the matrix of `DF(x̄)` on `|k| ≤ N`, tail `ik`. -/
noncomputable def opD (N : ℕ) (xbar : X n ν hν) : X n ν hν →L[ℂ] Y n ν hν :=
  ParamTail.op (center N) (P.DFb ν hν xbar) (FiniteTail.crudeBound (s := center N)
    (M := P.DFM ν hν xbar) (tl := fun k => Complex.I * k) (ω := weightsY ν hν)
    (ω' := Weights.geomInt ν hν) zero_le_one (fun l _ => diff_bound l))

/-- The border of `B = I - A^{(N)} DF^{(N)}(x̄)`. -/
noncomputable def matEb (N : ℕ) (A : Border n ℤ ℂ) (AM : Fin n → ℤ → Fin n → ℤ → ℂ)
    (xbar : X n ν hν) : Border n ℤ ℂ where
  a00 := 1 - (A.a00 * (P.DFb ν hν xbar).a00 +
    ∑ i, ∑ l ∈ center N, A.row i l * (P.DFb ν hν xbar).col i l)
  row i l := -(A.a00 * (P.DFb ν hν xbar).row i l +
    ∑ i', ∑ l' ∈ center N, A.row i' l' * P.DFM ν hν xbar i' l' i l)
  col j m := -(A.col j m * (P.DFb ν hν xbar).a00 +
    ∑ i', ∑ l' ∈ center N, AM j m i' l' * (P.DFb ν hν xbar).col i' l')

/-- The block of `B = I - A^{(N)} DF^{(N)}(x̄)`. -/
noncomputable def matEM (N : ℕ) (A : Border n ℤ ℂ) (AM : Fin n → ℤ → Fin n → ℤ → ℂ)
    (xbar : X n ν hν) (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : ℂ :=
  (if j = i ∧ m = l then 1 else 0) - (A.col j m * (P.DFb ν hν xbar).row i l +
    ∑ i', ∑ l' ∈ center N, AM j m i' l' * P.DFM ν hν xbar i' l' i l)

/-- `Θᵢ(r) = 2 ∑_l |∂_l f_i|(‖ā‖ + r) + |τ̄| ∑_{l,m} |∂_l ∂_m f_i|(‖ā‖ + r)`. -/
noncomputable def Theta (xbar : X n ν hν) (i : Fin n) (r : ℝ) : ℝ :=
  2 * ∑ l, absEval (pderiv l (P.f i)) (fun k => ‖xbar.2 k‖ + r) +
    ‖xbar.1‖ * ∑ l, ∑ m, absEval (pderiv l (pderiv m (P.f i))) (fun k => ‖xbar.2 k‖ + r)

/-- The finite part `(h₀, (π_N h_j)_j)`. -/
noncomputable def finPartX (N : ℕ) (h : X n ν hν) : X n ν hν := (h.1, fun j => finPart N (h.2 j))

variable {ν hν}

/-! ### The finite part and the approximate derivative -/

theorem finPartX_eq (N : ℕ) (h : X n ν hν) :
    finPartX ν hν N h = h.1 • ((1 : ℂ), (0 : Fin n → Fourier.X ν hν)) +
      ∑ i, ∑ l ∈ center N, h.2 i l • ((0 : ℂ), FiniteTail.unitVec i l) := by
  refine Prod.ext ?_ ?_
  · simp [finPartX, Prod.fst_sum]
  · funext j
    ext k
    simp only [finPartX, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, zero_add,
      Finset.sum_apply, Pi.smul_apply, WeightedLp.sum_apply, WeightedLp.smul_apply,
      FiniteTail.unitVec, finPart_apply]
    rw [Finset.sum_eq_single j (fun i _ hij => Finset.sum_eq_zero fun l _ => by
      rw [Pi.single_eq_of_ne' hij, WeightedLp.zero_apply, mul_zero]) (by simp)]
    simp only [Pi.single_eq_same, WeightedL1.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq]

/-- A linear map applied to the finite part, in terms of its values on the unit vectors. -/
theorem map_finPartX {Z : Type*} [AddCommGroup Z] [Module ℂ Z] (T : X n ν hν →ₗ[ℂ] Z) (N : ℕ)
    (h : X n ν hν) :
    T (finPartX ν hν N h) = h.1 • T (1, 0) +
      ∑ i, ∑ l ∈ center N, h.2 i l • T (0, FiniteTail.unitVec i l) := by
  rw [finPartX_eq, map_add, map_smul, map_sum]
  simp only [map_sum, map_smul]

theorem opD_fst (N : ℕ) (xbar h : X n ν hν) :
    (P.opD ν hν N xbar h).1 = (P.DF ν hν xbar (finPartX ν hν N h)).1 := by
  rw [opD, op_fst]
  have := congrArg Prod.fst (map_finPartX (P.DF ν hν xbar : X n ν hν →ₗ[ℂ] Y n ν hν) N h)
  simp only [ContinuousLinearMap.coe_coe, Prod.fst_add, Prod.smul_fst, Prod.fst_sum,
    smul_eq_mul] at this
  rw [this, DFb, mul_comm]
  simp only
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem opD_snd (N : ℕ) (xbar h : X n ν hν) (j : Fin n) {m : ℤ} (hm : m ∈ center N) :
    (P.opD ν hν N xbar h).2 j m = (P.DF ν hν xbar (finPartX ν hν N h)).2 j m := by
  rw [opD, op_snd, ite_eq_left hm]
  have := congrArg (fun y : Y n ν hν => y.2 j m)
    (map_finPartX (P.DF ν hν xbar : X n ν hν →ₗ[ℂ] Y n ν hν) N h)
  simp only [ContinuousLinearMap.coe_coe, Prod.snd_add, Prod.smul_snd, Prod.snd_sum,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, WeightedLp.add_apply, WeightedLp.smul_apply,
    WeightedLp.sum_apply] at this
  rw [this, DFb, mul_comm]
  simp only
  congr 1
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [DFM, mul_comm]

/-! ### The bounds -/

section Bounds

variable (xbar : X n ν hν) {N : ℕ} (A : Border n ℤ ℂ) (AM : Fin n → ℤ → Fin n → ℤ → ℂ)

/-- `F_j(x̄)_k = 0` for `|k| > MN`. -/
theorem F_snd_eq_zero {M : ℕ} (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M)
    (habar : ∀ j, SuppLe (xbar.2 j) N) (j : Fin n) {k : ℤ} (hk : M * N < k.natAbs) :
    (P.F ν hν xbar).2 j k = 0 := by
  have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
  rw [F_snd_apply, habar j k (lt_of_le_of_lt hNM hk),
    suppLe_aeval (P.f j) xbar.2 habar (hdeg j) k hk]
  ring

/-- The bound `Y₀`. -/
theorem norm_opA_F_le {M : ℕ} (hM : 1 ≤ M) (hdeg : ∀ j, (P.f j).totalDegree ≤ M)
    (habar : ∀ j, SuppLe (xbar.2 j) N) {Y₀ : ℝ}
    (hY₀0 : ‖A.a00 * (P.F ν hν xbar).1 +
      ∑ i, ∑ l ∈ center N, A.row i l * (P.F ν hν xbar).2 i l‖ ≤ Y₀)
    (hY₀ : ∀ j, ∑ k ∈ center N, ‖A.col j k * (P.F ν hν xbar).1 +
        ∑ i, ∑ l ∈ center N, AM j k i l * (P.F ν hν xbar).2 i l‖ * ν ^ k.natAbs +
      ∑ k ∈ center (M * N) \ center N,
        ‖(P.F ν hν xbar).2 j k‖ * ν ^ k.natAbs / (k.natAbs : ℝ) ≤ Y₀) :
    ‖opA ν hν N A AM (P.F ν hν xbar)‖ ≤ Y₀ := by
  have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀0
  refine max_le ?_ ((pi_norm_le_iff_of_nonneg hY₀nn).2 fun j => ?_)
  · rw [opA, op_fst]; exact hY₀0
  · rw [WeightedL1.norm_eq_tsum]
    have hNM : N ≤ M * N := Nat.le_mul_of_pos_left N hM
    have hsupp : ∀ k ∉ center (M * N),
        Weights.geomInt ν hν k * ‖(opA ν hν N A AM (P.F ν hν xbar)).2 j k‖ = 0 := fun k hk => by
      have hk' : k ∉ center N := fun h => hk (center_mono hNM h)
      rw [mem_center, not_le] at hk
      rw [opA, op_snd, ite_eq_right hk', P.F_snd_eq_zero xbar hM hdeg habar j hk, mul_zero,
        norm_zero, mul_zero]
    rw [tsum_eq_sum hsupp, ← Finset.sum_sdiff (center_mono hNM), add_comm]
    refine le_of_eq_of_le ?_ (hY₀ j)
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [opA, op_snd, ite_eq_left hk, Weights.geomInt_apply, mul_comm]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_sdiff] at hk
      rw [opA, op_snd, ite_eq_right hk.2, Weights.geomInt_apply, norm_mul, norm_tailA]
      field_simp

/-- The bound `Z₀`. -/
theorem norm_id_sub_opA_opD_le {ER EC : Fin n → ℝ} {EK : Fin n → Fin n → ℝ} {Z₀ : ℝ}
    (hER0 : ∀ i, 0 ≤ ER i)
    (hER : ∀ i, ∀ l ∈ center N, ‖(P.matEb ν hν N A AM xbar).row i l‖ ≤ ER i * ν ^ l.natAbs)
    (hEC : ∀ j, ∑ m ∈ center N, ‖(P.matEb ν hν N A AM xbar).col j m‖ * ν ^ m.natAbs ≤ EC j)
    (hEK0 : ∀ j i, 0 ≤ EK j i)
    (hEK : ∀ j i, ∀ l ∈ center N, ∑ m ∈ center N,
      ‖P.matEM ν hν N A AM xbar j m i l‖ * ν ^ m.natAbs ≤ EK j i * ν ^ l.natAbs)
    (hZ₀0 : ‖(P.matEb ν hν N A AM xbar).a00‖ + ∑ i, ER i ≤ Z₀)
    (hZ₀ : ∀ j, EC j + ∑ i, EK j i ≤ Z₀) :
    ‖ContinuousLinearMap.id ℂ _ - (opA ν hν N A AM).comp (P.opD ν hν N xbar)‖ ≤ Z₀ := by
  have hE : FiniteTail.Bound (center N) (P.matEM ν hν N A AM xbar) (fun _ => (0 : ℂ))
      (Weights.geomInt ν hν) (Weights.geomInt ν hν) EK :=
    ⟨hEK0, fun j i l hl => by simpa only [Weights.geomInt_apply] using hEK j i l hl,
      fun j l _ => by
        rw [norm_zero, zero_mul]
        exact mul_nonneg (hEK0 j j) ((Weights.geomInt ν hν).pos l).le⟩
  rw [opA, opD, ParamTail.id_sub_op_comp_op _ _ (P.matEb ν hν N A AM xbar) _ _ hE rfl
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun m hm => by
      rw [tailA, inv_mul_cancel₀ (I_mul_ne_zero hm), sub_self])]
  exact ParamTail.norm_op_le _ hE hER0
    (fun i l hl => by simpa only [Weights.geomInt_apply] using hER i l hl)
    (fun j => by simpa only [Weights.geomInt_apply] using hEC j) hZ₀0 hZ₀

/-! #### The operator `DF(x̄) - A†` -/

theorem fst_DF_sub_opD (hN₀ : P.N₀ ≤ N) (h : X n ν hν) :
    ((P.DF ν hν xbar - P.opD ν hν N xbar) h).1 = 0 := by
  rw [sub_apply, Prod.fst_sub, P.opD_fst, ← Prod.fst_sub, ← map_sub, DF_fst]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_eq_zero fun k hk => ?_, mul_zero]
  simp only [finPartX, Prod.snd_sub, Pi.sub_apply]
  rw [sub_finPart_apply, ite_eq_left (center_mono hN₀ hk)]

/-- Rows `|m| ≤ N`: `-τ̄ (Dφ_j(ā) h_∞)_m`, `h_∞ = h - π_N h`. -/
theorem snd_DF_sub_opD_fin (h : X n ν hν) (j : Fin n) {m : ℤ} (hm : m ∈ center N) :
    ((P.DF ν hν xbar - P.opD ν hν N xbar) h).2 j m =
      -(xbar.1 * (polyDeriv (P.f j) xbar.2 (fun i => h.2 i - finPart N (h.2 i))) m) := by
  rw [sub_apply, Prod.snd_sub, Pi.sub_apply, WeightedLp.sub_apply, P.opD_snd N xbar h j hm,
    ← WeightedLp.sub_apply, ← Pi.sub_apply, ← Prod.snd_sub, ← map_sub, DF_snd_apply]
  simp only [finPartX, Prod.fst_sub, Prod.snd_sub, sub_self, zero_mul, Pi.sub_apply]
  rw [sub_finPart_apply, ite_eq_left hm]
  have : (h.2 - fun j => finPart N (h.2 j)) = fun i => h.2 i - finPart N (h.2 i) := rfl
  rw [this]
  ring

/-- Rows `|m| > N`: `-h₀ φ_j(ā)_m - τ̄ (Dφ_j(ā) h)_m`. -/
theorem snd_DF_sub_opD_tail (h : X n ν hν) (j : Fin n) {m : ℤ} (hm : m ∉ center N) :
    ((P.DF ν hν xbar - P.opD ν hν N xbar) h).2 j m =
      -(h.1 * (aeval xbar.2 (P.f j)) m + xbar.1 * (polyDeriv (P.f j) xbar.2 h.2) m) := by
  rw [sub_apply, Prod.snd_sub, Pi.sub_apply, WeightedLp.sub_apply, DF_snd_apply, opD, op_snd,
    ite_eq_right hm]
  ring

/-- `∑_{|l| ≤ N} |(Dφ_i(ā) h_∞)_l| ν^{-|l|} ≤ ν^{-2N-2} ∑_{i'} ‖∂_{i'}φ_i(ā)‖ ‖h‖`. -/
theorem sum_center_polyDeriv_le (i : Fin n) {Dphi : Fin n → Fin n → ℝ}
    (hDphi : ∀ i' i, ‖aeval xbar.2 (pderiv i' (P.f i))‖ ≤ Dphi i' i) (h : X n ν hν) :
    ∑ l ∈ center N, ‖(polyDeriv (P.f i) xbar.2 (fun i => h.2 i - finPart N (h.2 i))) l‖ /
      ν ^ l.natAbs ≤ (∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2) := by
  have hνN : 0 < ν ^ (2 * N + 2) := pow_pos (nu_pos hν) _
  calc ∑ l ∈ center N, ‖(polyDeriv (P.f i) xbar.2 (fun i => h.2 i - finPart N (h.2 i))) l‖ /
        ν ^ l.natAbs
      ≤ ∑ l ∈ center N, ∑ i', ‖(aeval xbar.2 (pderiv i' (P.f i)) *
          (h.2 i' - finPart N (h.2 i'))) l‖ / ν ^ l.natAbs := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [polyDeriv_apply, WeightedLp.sum_apply, ← Finset.sum_div]
        exact div_le_div_of_nonneg_right (norm_sum_le _ _) (pow_pos (nu_pos hν) _).le
    _ = ∑ i', ∑ l ∈ center N, ‖(aeval xbar.2 (pderiv i' (P.f i)) *
          (h.2 i' - finPart N (h.2 i'))) l‖ / ν ^ l.natAbs := Finset.sum_comm
    _ ≤ ∑ i', ‖aeval xbar.2 (pderiv i' (P.f i))‖ * ‖h.2 i' - finPart N (h.2 i')‖ /
          ν ^ (2 * N + 2) :=
        Finset.sum_le_sum fun i' _ => sum_center_mul_le _ _ fun l hl => by
          rw [sub_finPart_apply, ite_eq_left hl]
    _ ≤ ∑ i', Dphi i' i * ‖h‖ / ν ^ (2 * N + 2) := by
        refine Finset.sum_le_sum fun i' _ => div_le_div_of_nonneg_right ?_ hνN.le
        exact mul_le_mul (hDphi i' i) ((norm_sub_finPart_le _).trans
          ((norm_le_pi_norm h.2 i').trans (norm_snd_le h))) (norm_nonneg _)
          ((norm_nonneg _).trans (hDphi i' i))
    _ = (∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2) := by
        rw [← Finset.sum_div, ← Finset.sum_mul]

/-- The bound `Z₁`. -/
theorem norm_opA_DF_sub_opD_le (hN₀ : P.N₀ ≤ N) {κ0 : Fin n → ℝ} {κ : Fin n → Fin n → ℝ}
    {Dphi : Fin n → Fin n → ℝ} {Φ : Fin n → ℝ} {Z₁ : ℝ}
    (hκ00 : ∀ i, 0 ≤ κ0 i) (hκ0 : ∀ i, ∀ l ∈ center N,
      ‖A.row i l‖ * ν ^ l.natAbs ≤ κ0 i * ν ^ (2 * N + 2))
    (hκ0' : ∀ j i, 0 ≤ κ j i) (hκ : ∀ j i, ∀ l ∈ center N,
      (∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs) * ν ^ l.natAbs ≤ κ j i * ν ^ (2 * N + 2))
    (hDphi : ∀ i' i, ‖aeval xbar.2 (pderiv i' (P.f i))‖ ≤ Dphi i' i)
    (hΦ : ∀ j, ‖aeval xbar.2 (P.f j) - finPart N (aeval xbar.2 (P.f j))‖ ≤ Φ j)
    (hZ₁0 : ‖xbar.1‖ * ∑ i, κ0 i * ∑ i', Dphi i' i ≤ Z₁)
    (hZ₁ : ∀ j, ‖xbar.1‖ * ∑ i, κ j i * ∑ i', Dphi i' i +
      (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) / ((N : ℝ) + 1) ≤ Z₁) :
    ‖(opA ν hν N A AM).comp (P.DF ν hν xbar - P.opD ν hν N xbar)‖ ≤ Z₁ := by
  have hν0 := nu_pos hν
  have hνN : 0 < ν ^ (2 * N + 2) := pow_pos hν0 _
  have hDphi0 : ∀ i' i, 0 ≤ Dphi i' i := fun i' i => (norm_nonneg _).trans (hDphi i' i)
  have hΦ0 : ∀ j, 0 ≤ Φ j := fun j => (norm_nonneg _).trans (hΦ j)
  have hZ₁nn : 0 ≤ Z₁ := le_trans (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hκ00 i) (Finset.sum_nonneg fun i' _ => hDphi0 i' i))) hZ₁0
  refine ContinuousLinearMap.opNorm_le_bound _ hZ₁nn fun h => ?_
  rw [ContinuousLinearMap.comp_apply]
  set T := P.DF ν hν xbar - P.opD ν hν N xbar with hT
  set z := T h with hz
  have hz1 : z.1 = 0 := P.fst_DF_sub_opD xbar hN₀ h
  -- the rows `|l| ≤ N` of `z`, divided by `ν^{|l|}`
  have hzΓ : ∀ i, ∑ l ∈ center N, ‖z.2 i l‖ / ν ^ l.natAbs ≤
      ‖xbar.1‖ * (∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2) := fun i => by
    calc ∑ l ∈ center N, ‖z.2 i l‖ / ν ^ l.natAbs
        = ‖xbar.1‖ * ∑ l ∈ center N,
            ‖(polyDeriv (P.f i) xbar.2 (fun i => h.2 i - finPart N (h.2 i))) l‖ / ν ^ l.natAbs := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [hz, hT, P.snd_DF_sub_opD_fin xbar h i hl, norm_neg, norm_mul, mul_div_assoc]
      _ ≤ ‖xbar.1‖ * ((∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2)) :=
          mul_le_mul_of_nonneg_left (P.sum_center_polyDeriv_le xbar i hDphi h) (norm_nonneg _)
      _ = ‖xbar.1‖ * (∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2) := by ring
  -- a finite row of `A` against the finite part of `z`
  have hrow : ∀ (c : Fin n → ℤ → ℂ) (C : Fin n → ℝ), (∀ i, 0 ≤ C i) →
      (∀ i, ∀ l ∈ center N, ‖c i l‖ * ν ^ l.natAbs ≤ C i * ν ^ (2 * N + 2)) →
      ∑ i, ∑ l ∈ center N, ‖c i l‖ * ‖z.2 i l‖ ≤
        ‖xbar.1‖ * (∑ i, C i * ∑ i', Dphi i' i) * ‖h‖ := by
    intro c C hC0 hC
    calc ∑ i, ∑ l ∈ center N, ‖c i l‖ * ‖z.2 i l‖
        ≤ ∑ i, ∑ l ∈ center N, C i * ν ^ (2 * N + 2) * (‖z.2 i l‖ / ν ^ l.natAbs) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l hl => ?_
          have hνl : 0 < ν ^ l.natAbs := pow_pos hν0 _
          rw [mul_div_assoc', le_div_iff₀ hνl, mul_right_comm]
          exact mul_le_mul_of_nonneg_right (hC i l hl) (norm_nonneg _)
      _ = ∑ i, C i * ν ^ (2 * N + 2) * ∑ l ∈ center N, ‖z.2 i l‖ / ν ^ l.natAbs := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ i, C i * ν ^ (2 * N + 2) *
            (‖xbar.1‖ * (∑ i', Dphi i' i) * ‖h‖ / ν ^ (2 * N + 2)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hzΓ i)
            (mul_nonneg (hC0 i) hνN.le)
      _ = ‖xbar.1‖ * (∑ i, C i * ∑ i', Dphi i' i) * ‖h‖ := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by field_simp
  have hh1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  refine max_le ?_ ((pi_norm_le_iff_of_nonneg (mul_nonneg hZ₁nn (norm_nonneg h))).2 fun j => ?_)
  · -- the scalar component
    rw [opA, op_fst, hz1, mul_zero, zero_add]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
    simp only [norm_mul]
    exact (hrow A.row κ0 hκ00 hκ0).trans (mul_le_mul_of_nonneg_right hZ₁0 (norm_nonneg h))
  · -- the sequence components
    set v := (opA ν hν N A AM z).2 j with hv
    have hfin : ∑ m ∈ center N, Weights.geomInt ν hν m * ‖v m‖ ≤
        ‖xbar.1‖ * (∑ i, κ j i * ∑ i', Dphi i' i) * ‖h‖ := by
      have hcol : ∀ i, ∀ l ∈ center N,
          ‖∑ m ∈ center N, (‖AM j m i l‖ * ν ^ m.natAbs : ℝ)‖ * ν ^ l.natAbs ≤
            κ j i * ν ^ (2 * N + 2) := fun i l hl => by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun m _ =>
          mul_nonneg (norm_nonneg _) (pow_pos hν0 _).le)]
        exact hκ j i l hl
      calc ∑ m ∈ center N, Weights.geomInt ν hν m * ‖v m‖
          ≤ ∑ m ∈ center N, ν ^ m.natAbs * ∑ i, ∑ l ∈ center N, ‖AM j m i l‖ * ‖z.2 i l‖ := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [hv, opA, op_snd, ite_eq_left hm, hz1, mul_zero, zero_add, Weights.geomInt_apply]
            refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
              (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (le_of_eq
                (Finset.sum_congr rfl fun l _ => norm_mul _ _)))) (pow_pos hν0 _).le
        _ = ∑ i, ∑ l ∈ center N, ‖((∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs : ℝ) : ℂ)‖ *
              ‖z.2 i l‖ := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun m _ =>
              mul_nonneg (norm_nonneg _) (pow_pos hν0 _).le), Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
        _ ≤ ‖xbar.1‖ * (∑ i, κ j i * ∑ i', Dphi i' i) * ‖h‖ :=
            hrow (fun i l => ((∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs : ℝ) : ℂ)) (κ j)
              (hκ0' j) (fun i l hl => by rw [Complex.norm_real]; exact hcol i l hl)
    -- the tail
    set φj := aeval xbar.2 (P.f j) with hφj
    set pd := polyDeriv (P.f j) xbar.2 h.2 with hpd
    have hpd_le : ‖pd‖ ≤ (∑ i', Dphi i' j) * ‖h‖ :=
      ((polyDeriv (P.f j) xbar.2).le_opNorm h.2).trans (mul_le_mul
        ((norm_polyDeriv_le _ _).trans (Finset.sum_le_sum fun i' _ => hDphi i' j))
        (norm_snd_le h) (norm_nonneg _) (Finset.sum_nonneg fun i' _ => hDphi0 i' j))
    have hv_tail : ∀ m, (if m ∈ center N then 0 else Weights.geomInt ν hν m * ‖v m‖) ≤
        ((N : ℝ) + 1)⁻¹ * (‖h.1‖ * (Weights.geomInt ν hν m * ‖(φj - finPart N φj) m‖) +
          ‖xbar.1‖ * (Weights.geomInt ν hν m * ‖pd m‖)) := by
      intro m
      have hw := ((Weights.geomInt ν hν).pos m).le
      by_cases hm : m ∈ center N
      · rw [ite_eq_left hm]
        positivity
      · rw [ite_eq_right hm, hv, opA, op_snd, ite_eq_right hm, hz, hT,
          P.snd_DF_sub_opD_tail xbar h j hm, norm_mul, norm_tailA, norm_neg, sub_finPart_apply,
          ite_eq_right hm]
        calc Weights.geomInt ν hν m * (((m.natAbs : ℕ) : ℝ)⁻¹ *
              ‖h.1 * φj m + xbar.1 * pd m‖)
            ≤ Weights.geomInt ν hν m * (((N : ℝ) + 1)⁻¹ * (‖h.1‖ * ‖φj m‖ + ‖xbar.1‖ * ‖pd m‖)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul (inv_natAbs_le hm) ?_ (norm_nonneg _)
                (by positivity)) hw
              exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
          _ = ((N : ℝ) + 1)⁻¹ * (‖h.1‖ * (Weights.geomInt ν hν m * ‖φj m‖) +
              ‖xbar.1‖ * (Weights.geomInt ν hν m * ‖pd m‖)) := by ring
    have hs1 : Summable fun m => Weights.geomInt ν hν m * ‖(φj - finPart N φj) m‖ :=
      WeightedL1.summable _
    have hs2 : Summable fun m => Weights.geomInt ν hν m * ‖pd m‖ := WeightedL1.summable _
    have hsR : Summable fun m => ((N : ℝ) + 1)⁻¹ *
        (‖h.1‖ * (Weights.geomInt ν hν m * ‖(φj - finPart N φj) m‖) +
          ‖xbar.1‖ * (Weights.geomInt ν hν m * ‖pd m‖)) :=
      ((hs1.mul_left _).add (hs2.mul_left _)).mul_left _
    have htail : ∑' m, (if m ∈ center N then 0 else Weights.geomInt ν hν m * ‖v m‖) ≤
        (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) / ((N : ℝ) + 1) * ‖h‖ := by
      refine (Summable.tsum_le_tsum hv_tail (Summable.of_nonneg_of_le (fun m => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg ((Weights.geomInt ν hν).pos m).le (norm_nonneg _)) hv_tail hsR)
        hsR).trans ?_
      rw [tsum_mul_left, (hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
        ← WeightedL1.norm_eq_tsum, ← WeightedL1.norm_eq_tsum]
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hN1]
      calc ‖h.1‖ * ‖φj - finPart N φj‖ + ‖xbar.1‖ * ‖pd‖
          ≤ ‖h‖ * Φ j + ‖xbar.1‖ * ((∑ i', Dphi i' j) * ‖h‖) :=
            add_le_add (mul_le_mul hh1 (hΦ j) (norm_nonneg _) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hpd_le (norm_nonneg _))
        _ = (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) * ‖h‖ := by ring
    rw [WeightedL1.norm_eq_tsum, tsum_eq_sum_add_tsum_ite (WeightedL1.summable v) (center N)]
    calc ∑ m ∈ center N, Weights.geomInt ν hν m * ‖v m‖ +
          ∑' m, (if m ∈ center N then 0 else Weights.geomInt ν hν m * ‖v m‖)
        ≤ ‖xbar.1‖ * (∑ i, κ j i * ∑ i', Dphi i' i) * ‖h‖ +
            (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) / ((N : ℝ) + 1) * ‖h‖ := add_le_add hfin htail
      _ = (‖xbar.1‖ * ∑ i, κ j i * ∑ i', Dphi i' i +
            (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) / ((N : ℝ) + 1)) * ‖h‖ := by ring
      _ ≤ Z₁ * ‖h‖ := mul_le_mul_of_nonneg_right (hZ₁ j) (norm_nonneg h)

/-! #### The bound `Z₂` -/

omit A AM in
/-- `(DF(c) - DF(x̄)) h = (0, ι v)`, `v_j = -(h₀ (φ_j(c) - φ_j(ā)) + c₀ Dφ_j(c) h - τ̄ Dφ_j(ā) h)`. -/
theorem DF_sub_DF_apply (c h : X n ν hν) :
    (P.DF ν hν c - P.DF ν hν xbar) h = (0, fun j => incl ν hν
      (-(h.1 • (aeval c.2 (P.f j) - aeval xbar.2 (P.f j)) +
        (c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2)))) := by
  refine Prod.ext ?_ ?_
  · rw [sub_apply, Prod.fst_sub, DF_fst, DF_fst, sub_self]
  · funext j
    ext k
    rw [sub_apply, Prod.snd_sub, Pi.sub_apply, WeightedLp.sub_apply, DF_snd_apply, DF_snd_apply,
      incl_apply]
    simp only [WeightedLp.neg_apply, WeightedLp.add_apply, WeightedLp.sub_apply,
      WeightedLp.smul_apply]
    ring

/-- On sequences in `ℓ¹_ν`, `A` acts as the operator with the same matrix on `ℓ¹_ν`. -/
theorem opA_incl {K : Fin n → Fin n → ℝ}
    (hK : FiniteTail.Bound (center N) AM tailA (Weights.geomInt ν hν) (Weights.geomInt ν hν) K)
    (y₀ : ℂ) (v : Fin n → Fourier.X ν hν) :
    opA ν hν N A AM (y₀, fun j => incl ν hν (v j)) = ParamTail.op (center N) A hK (y₀, v) := by
  refine Prod.ext ?_ ?_
  · rw [opA, op_fst, op_fst]
    simp only [incl_apply]
  · funext j
    ext m
    rw [opA, op_snd, op_snd]
    simp only [incl_apply]

/-- `‖v_j‖ ≤ Θ_j(r) r ‖h‖`. -/
theorem norm_v_le {r : ℝ} (c : X n ν hν) (hc : c ∈ closedBall xbar r) (h : X n ν hν) (j : Fin n) :
    ‖-(h.1 • (aeval c.2 (P.f j) - aeval xbar.2 (P.f j)) +
        (c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2))‖ ≤
      P.Theta ν hν xbar j r * r * ‖h‖ := by
  have hr : 0 ≤ r := le_trans dist_nonneg hc
  have hcx : ‖c - xbar‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hc
  have hc2 : c.2 ∈ closedBall xbar.2 r := by
    rw [mem_closedBall, dist_eq_norm]; exact (norm_snd_le (c - xbar)).trans hcx
  have hc1 : ‖c.1 - xbar.1‖ ≤ r := (norm_fst_le (c - xbar)).trans hcx
  set S1 := ∑ l, absEval (pderiv l (P.f j)) (fun k => ‖xbar.2 k‖ + r) with hS1
  set S2 := ∑ l, ∑ m, absEval (pderiv l (pderiv m (P.f j))) (fun k => ‖xbar.2 k‖ + r) with hS2
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun l _ =>
    absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr
  have hpdc : ‖polyDeriv (P.f j) c.2‖ ≤ S1 :=
    (norm_polyDeriv_le _ _).trans (Finset.sum_le_sum fun l _ =>
      (norm_aeval_le _ c.2).trans (absEval_mono _ (fun k => norm_nonneg _)
        (norm_apply_le_of_mem_closedBall hc2)))
  have hh1 : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  have hh2 : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have e1 : ‖h.1 • (aeval c.2 (P.f j) - aeval xbar.2 (P.f j))‖ ≤ S1 * r * ‖h‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (norm_aeval_sub_le _ hc2) hh1 (norm_nonneg _) (mul_nonneg hS1nn hr)
  have e2 : ‖c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2‖ ≤
      (S1 + ‖xbar.1‖ * S2) * r * ‖h‖ := by
    have hsplit : c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2 =
        (c.1 - xbar.1) • polyDeriv (P.f j) c.2 h.2 +
          xbar.1 • (polyDeriv (P.f j) c.2 - polyDeriv (P.f j) xbar.2) h.2 := by
      rw [sub_smul, sub_apply, smul_sub]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have t1 : ‖c.1 - xbar.1‖ * ‖polyDeriv (P.f j) c.2 h.2‖ ≤ r * (S1 * ‖h‖) :=
      mul_le_mul hc1 (((polyDeriv (P.f j) c.2).le_opNorm h.2).trans
        (mul_le_mul hpdc hh2 (norm_nonneg _) hS1nn)) (norm_nonneg _) hr
    have t2 : ‖xbar.1‖ * ‖(polyDeriv (P.f j) c.2 - polyDeriv (P.f j) xbar.2) h.2‖ ≤
        ‖xbar.1‖ * (S2 * r * ‖h‖) :=
      mul_le_mul_of_nonneg_left (((polyDeriv (P.f j) c.2 - polyDeriv (P.f j) xbar.2).le_opNorm
        h.2).trans (mul_le_mul (norm_polyDeriv_sub_le _ hc2) hh2 (norm_nonneg _)
          (mul_nonneg (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ =>
            absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr) hr))) (norm_nonneg _)
    calc ‖c.1 - xbar.1‖ * ‖polyDeriv (P.f j) c.2 h.2‖ +
          ‖xbar.1‖ * ‖(polyDeriv (P.f j) c.2 - polyDeriv (P.f j) xbar.2) h.2‖
        ≤ r * (S1 * ‖h‖) + ‖xbar.1‖ * (S2 * r * ‖h‖) := add_le_add t1 t2
      _ = (S1 + ‖xbar.1‖ * S2) * r * ‖h‖ := by ring
  rw [Theta, ← hS1, ← hS2]
  calc ‖-(h.1 • (aeval c.2 (P.f j) - aeval xbar.2 (P.f j)) +
        (c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2))‖
      ≤ S1 * r * ‖h‖ + (S1 + ‖xbar.1‖ * S2) * r * ‖h‖ := by
        rw [norm_neg]; exact (norm_add_le _ _).trans (add_le_add e1 e2)
    _ = (2 * S1 + ‖xbar.1‖ * S2) * r * ‖h‖ := by ring

/-- The bound `Z₂(r)`. -/
theorem norm_opA_DF_sub_DF_le {R : Fin n → ℝ} {KA : Fin n → Fin n → ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : ∀ i, ∀ l ∈ center N, ‖A.row i l‖ ≤ R i * ν ^ l.natAbs)
    (hKA0 : ∀ j i, 0 ≤ KA j i) (hKAd : ∀ j, ((N : ℝ) + 1)⁻¹ ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ center N, ∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs ≤
      KA j i * ν ^ l.natAbs)
    {r Z₂ : ℝ} (hr : 0 ≤ r)
    (hZ₂0 : ∑ i, R i * P.Theta ν hν xbar i r ≤ Z₂)
    (hZ₂ : ∀ j, ∑ i, KA j i * P.Theta ν hν xbar i r ≤ Z₂)
    (c : X n ν hν) (hc : c ∈ closedBall xbar r) :
    ‖(opA ν hν N A AM).comp (P.DF ν hν c - P.DF ν hν xbar)‖ ≤ Z₂ * r := by
  have hKAb : FiniteTail.Bound (center N) AM tailA (Weights.geomInt ν hν)
      (Weights.geomInt ν hν) KA :=
    ⟨hKA0, fun j i l hl => by simpa only [Weights.geomInt_apply] using hKA j i l hl,
      fun j l hl => tailA_bound_X (hKAd j) l hl⟩
  have hΘ : ∀ i, 0 ≤ P.Theta ν hν xbar i r := fun i =>
    add_nonneg (mul_nonneg zero_le_two (Finset.sum_nonneg fun l _ =>
      absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr))
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ =>
        absEval_nonneg _ fun k => add_nonneg (norm_nonneg _) hr))
  have hZ₂nn : 0 ≤ Z₂ :=
    le_trans (Finset.sum_nonneg fun i _ => mul_nonneg (hR0 i) (hΘ i)) hZ₂0
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hZ₂nn hr) fun h => ?_
  rw [ContinuousLinearMap.comp_apply, P.DF_sub_DF_apply xbar c h, opA_incl A AM hKAb]
  set v : Fin n → Fourier.X ν hν := fun j =>
    -(h.1 • (aeval c.2 (P.f j) - aeval xbar.2 (P.f j)) +
      (c.1 • polyDeriv (P.f j) c.2 h.2 - xbar.1 • polyDeriv (P.f j) xbar.2 h.2)) with hv
  have hvj : ∀ j, ‖v j‖ ≤ P.Theta ν hν xbar j r * r * ‖h‖ := fun j => P.norm_v_le xbar c hc h j
  have hsum : ∀ (C : Fin n → ℝ), (∀ i, 0 ≤ C i) → ∑ i, C i * P.Theta ν hν xbar i r ≤ Z₂ →
      ∑ i, C i * ‖v i‖ ≤ Z₂ * r * ‖h‖ := fun C hC0 hC => by
    calc ∑ i, C i * ‖v i‖ ≤ ∑ i, C i * (P.Theta ν hν xbar i r * r * ‖h‖) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvj i) (hC0 i)
      _ = (∑ i, C i * P.Theta ν hν xbar i r) * r * ‖h‖ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ Z₂ * r * ‖h‖ := by gcongr
  refine max_le ?_ ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_)
  · refine (norm_op_fst_le A hKAb hR0 (fun i l hl => by
      simpa only [Weights.geomInt_apply] using hR i l hl) _).trans ?_
    simp only [norm_zero, mul_zero, zero_add]
    exact hsum R hR0 hZ₂0
  · refine (norm_op_snd_le A hKAb (C := fun j => ∑ m ∈ center N, ‖A.col j m‖ *
      Weights.geomInt ν hν m) (fun _ => le_rfl) _ j).trans ?_
    simp only [norm_zero, mul_zero, zero_add]
    exact hsum (KA j) (hKA0 j) (hZ₂ j)

/-- If `‖I - A A†‖ < 1`, then `A` is injective. -/
theorem opA_injective
    (h : ‖ContinuousLinearMap.id ℂ _ - (opA ν hν N A AM).comp (P.opD ν hν N xbar)‖ < 1) :
    Function.Injective (opA ν hν N A AM) :=
  ParamTail.injective_op _ _ _ _ (fun _ hk => inv_ne_zero (I_mul_ne_zero hk)) h

end Bounds

/-! ### The theorem -/

/-- The radii polynomial theorem for periodic orbits of polynomial vector fields in Fourier series,
with two radii `r₀ ≤ r₁` (see the module docstring for the bounds). -/
theorem radii_poly_two_radii (xbar : X n ν hν) {N M : ℕ} (hN₀ : P.N₀ ≤ N) (hM : 1 ≤ M)
    (hdeg : ∀ j, (P.f j).totalDegree ≤ M) (habar : ∀ j, SuppLe (xbar.2 j) N)
    (A : Border n ℤ ℂ) (AM : Fin n → ℤ → Fin n → ℤ → ℂ)
    {r₀ r₁ Y₀ Z₀ Z₁ Z₂₀ Z₂₁ : ℝ} (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ r₁)
    -- `Y₀`
    (hY₀0 : ‖A.a00 * (P.F ν hν xbar).1 +
      ∑ i, ∑ l ∈ center N, A.row i l * (P.F ν hν xbar).2 i l‖ ≤ Y₀)
    (hY₀ : ∀ j, ∑ k ∈ center N, ‖A.col j k * (P.F ν hν xbar).1 +
        ∑ i, ∑ l ∈ center N, AM j k i l * (P.F ν hν xbar).2 i l‖ * ν ^ k.natAbs +
      ∑ k ∈ center (M * N) \ center N,
        ‖(P.F ν hν xbar).2 j k‖ * ν ^ k.natAbs / (k.natAbs : ℝ) ≤ Y₀)
    -- `Z₀`
    {ER EC : Fin n → ℝ} {EK : Fin n → Fin n → ℝ} (hER0 : ∀ i, 0 ≤ ER i)
    (hER : ∀ i, ∀ l ∈ center N, ‖(P.matEb ν hν N A AM xbar).row i l‖ ≤ ER i * ν ^ l.natAbs)
    (hEC : ∀ j, ∑ m ∈ center N, ‖(P.matEb ν hν N A AM xbar).col j m‖ * ν ^ m.natAbs ≤ EC j)
    (hEK0 : ∀ j i, 0 ≤ EK j i)
    (hEK : ∀ j i, ∀ l ∈ center N, ∑ m ∈ center N,
      ‖P.matEM ν hν N A AM xbar j m i l‖ * ν ^ m.natAbs ≤ EK j i * ν ^ l.natAbs)
    (hZ₀0 : ‖(P.matEb ν hν N A AM xbar).a00‖ + ∑ i, ER i ≤ Z₀)
    (hZ₀ : ∀ j, EC j + ∑ i, EK j i ≤ Z₀)
    -- `Z₁`
    {κ0 : Fin n → ℝ} {κ : Fin n → Fin n → ℝ} {Dphi : Fin n → Fin n → ℝ} {Φ : Fin n → ℝ}
    (hκ00 : ∀ i, 0 ≤ κ0 i) (hκ0 : ∀ i, ∀ l ∈ center N,
      ‖A.row i l‖ * ν ^ l.natAbs ≤ κ0 i * ν ^ (2 * N + 2))
    (hκ0' : ∀ j i, 0 ≤ κ j i) (hκ : ∀ j i, ∀ l ∈ center N,
      (∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs) * ν ^ l.natAbs ≤ κ j i * ν ^ (2 * N + 2))
    (hDphi : ∀ i' i, ‖aeval xbar.2 (pderiv i' (P.f i))‖ ≤ Dphi i' i)
    (hΦ : ∀ j, ‖aeval xbar.2 (P.f j) - finPart N (aeval xbar.2 (P.f j))‖ ≤ Φ j)
    (hZ₁0 : ‖xbar.1‖ * ∑ i, κ0 i * ∑ i', Dphi i' i ≤ Z₁)
    (hZ₁ : ∀ j, ‖xbar.1‖ * ∑ i, κ j i * ∑ i', Dphi i' i +
      (Φ j + ‖xbar.1‖ * ∑ i', Dphi i' j) / ((N : ℝ) + 1) ≤ Z₁)
    -- `Z₂`
    {R : Fin n → ℝ} {KA : Fin n → Fin n → ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : ∀ i, ∀ l ∈ center N, ‖A.row i l‖ ≤ R i * ν ^ l.natAbs)
    (hKA0 : ∀ j i, 0 ≤ KA j i) (hKAd : ∀ j, ((N : ℝ) + 1)⁻¹ ≤ KA j j)
    (hKA : ∀ j i, ∀ l ∈ center N, ∑ m ∈ center N, ‖AM j m i l‖ * ν ^ m.natAbs ≤
      KA j i * ν ^ l.natAbs)
    (hZ₂₀0 : ∑ i, R i * P.Theta ν hν xbar i r₀ ≤ Z₂₀)
    (hZ₂₀ : ∀ j, ∑ i, KA j i * P.Theta ν hν xbar i r₀ ≤ Z₂₀)
    (hZ₂₁0 : ∑ i, R i * P.Theta ν hν xbar i r₁ ≤ Z₂₁)
    (hZ₂₁ : ∀ j, ∑ i, KA j i * P.Theta ν hν xbar i r₁ ≤ Z₂₁)
    (hp₀ : radiiPoly Y₀ Z₀ Z₁ Z₂₀ r₀ < 0) (hp₁ : radiiPoly Y₀ Z₀ Z₁ Z₂₁ r₁ < 0) :
    HasIsolatedZero (P.F ν hν) xbar r₀ r₁ := by
  have hZ₀' := P.norm_id_sub_opA_opD_le xbar A AM hER0 hER hEC hEK0 hEK hZ₀0 hZ₀
  have hZ₁' := P.norm_opA_DF_sub_opD_le xbar A AM hN₀ hκ00 hκ0 hκ0' hκ hDphi hΦ hZ₁0 hZ₁
  have hY₀' := P.norm_opA_F_le xbar A AM hM hdeg habar hY₀0 hY₀
  have hZ₁nn : 0 ≤ Z₁ := (norm_nonneg _).trans hZ₁'
  have hZ₂nn : 0 ≤ Z₂₀ * r₀ := (norm_nonneg _).trans
    (P.norm_opA_DF_sub_DF_le xbar A AM hR0 hR hKA0 hKAd hKA hr₀.le hZ₂₀0 hZ₂₀ xbar
      (mem_closedBall_self hr₀.le))
  have hZ₀1 : Z₀ < 1 := by
    have hY₀nn : 0 ≤ Y₀ := (norm_nonneg _).trans hY₀'
    simp only [radiiPoly] at hp₀
    nlinarith [mul_nonneg hZ₂nn hr₀.le, mul_nonneg hZ₁nn hr₀.le]
  have hinj := P.opA_injective xbar A AM (hZ₀'.trans_lt hZ₀1)
  obtain ⟨x, hx, hFx, huniq, -⟩ := RadiiPolynomial.radii_poly_two_radii (𝕜 := ℂ) (P.F ν hν)
    (P.DF ν hν) (opA ν hν N A AM) (P.opD ν hν N xbar) xbar hinj hr₀ hr₀₁
    (fun x _ => (P.hasFDerivAt_F x).hasFDerivWithinAt) hY₀' hZ₀' hZ₁'
    (fun c hc => P.norm_opA_DF_sub_DF_le xbar A AM hR0 hR hKA0 hKAd hKA hr₀.le hZ₂₀0 hZ₂₀ c hc)
    (fun c hc => P.norm_opA_DF_sub_DF_le xbar A AM hR0 hR hKA0 hKAd hKA (hr₀.le.trans hr₀₁)
      hZ₂₁0 hZ₂₁ c hc)
    hp₀ hp₁
  unfold HasIsolatedZero
  exact ⟨x, hx, hFx, huniq⟩

end FourierPeriodic

end RadiiPolynomial
