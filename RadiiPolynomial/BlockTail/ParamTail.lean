module

public import RadiiPolynomial.BlockTail.FiniteTail

/-!
# Operators with a scalar unknown, a finite block and a diagonal tail

On `𝕜 × (Fin n → ℓ¹_{ω',I})` (max norm: an extra scalar unknown `x₀` next to `n` sequences) consider
operators of the form

  `(T x)₀     = a₀₀ x₀ + ∑ᵢ ∑_{l ∈ s} r_{il} x_{i,l}`,
  `(T x)_{j,m} = c_{jm} x₀ + ∑ᵢ ∑_{l ∈ s} M_{jmil} x_{i,l}`   for `m ∈ s`,
  `(T x)_{j,m} = λ_m x_{j,m}`                                for `m ∉ s`,

given by a finite matrix with border: the corner `a₀₀`, the row `r`, the column `c` (`Border`), the
finite block `M` and the diagonal tail `λ` of a `FiniteTail.Bound` (`ParamTail.op`).

* `op_fst`, `op_snd`: the coefficient formulas above;
* `norm_op_fst_le`, `norm_op_snd_le`, `norm_op_le`: with `|r_{il}| ≤ R_i ω'_l` and
  `∑_{m ∈ s} |c_{jm}| ω_m ≤ C_j`, `|(T x)₀| ≤ |a₀₀| |x₀| + ∑ᵢ Rᵢ ‖xᵢ‖`,
  `‖(T x)_j‖ ≤ C_j |x₀| + ∑ᵢ K_{ji} ‖xᵢ‖`, and `‖T‖ ≤ max (|a₀₀| + ∑ᵢ Rᵢ, maxⱼ (C_j + ∑ᵢ K_{ji}))`;
* `id_sub_op_comp_op`: `I - T D` is again of this form, with the border and block of
  `I - (matrix of T)(matrix of D)` and the tail `1 - λ λ_D`;
* `injective_op`: if the tail `λ` does not vanish and `‖I - T D‖ < 1` for an operator `D` of the
  same form, then `T` is injective.
-/

@[expose] public section

namespace RadiiPolynomial

namespace ParamTail

open FiniteTail

variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} [DecidableEq I] (s : Finset I) {n : ℕ}
  {ω ω' : Weights I}

/-- The border of a finite matrix with an extra scalar row and column: the corner `a₀₀`, the row
`(r_{il})` and the column `(c_{jm})`. -/
structure Border (n : ℕ) (I 𝕜 : Type*) where
  /-- the corner -/
  a00 : 𝕜
  /-- the row: coefficient of `x_{i,l}` in `(T x)₀` -/
  row : Fin n → I → 𝕜
  /-- the column: coefficient of `x₀` in `(T x)_{j,m}` -/
  col : Fin n → I → 𝕜

/-- The column `(c_{j,m})_{m ∈ s}` as a tuple of sequences. -/
noncomputable def colVec (c : Fin n → I → 𝕜) : Fin n → WeightedL1 𝕜 ω :=
  fun j => ∑ m ∈ s, c j m • WeightedL1.single m 1

/-- The row functional `x ↦ ∑ᵢ ∑_{l ∈ s} r_{il} x_{i,l}`. -/
noncomputable def rowCLM (r : Fin n → I → 𝕜) : (Fin n → WeightedL1 𝕜 ω') →L[𝕜] 𝕜 :=
  ∑ i, ∑ l ∈ s, r i l • (WeightedLp.evalCLM l).comp (ContinuousLinearMap.proj i)

variable {s}

theorem colVec_apply (c : Fin n → I → 𝕜) (j : Fin n) (m : I) :
    (colVec s c j : WeightedL1 𝕜 ω) m = if m ∈ s then c j m else 0 := by
  rw [colVec, WeightedLp.sum_apply]
  simp only [WeightedLp.smul_apply, WeightedL1.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]

omit [DecidableEq I] in
theorem rowCLM_apply (r : Fin n → I → 𝕜) (x : Fin n → WeightedL1 𝕜 ω') :
    rowCLM s r x = ∑ i, ∑ l ∈ s, r i l * x i l := by
  simp [rowCLM, sum_apply]

theorem norm_colVec_le (c : Fin n → I → 𝕜) (j : Fin n) :
    ‖(colVec s c j : WeightedL1 𝕜 ω)‖ ≤ ∑ m ∈ s, ‖c j m‖ * ω m := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun m _ => ?_))
  rw [norm_smul, WeightedL1.norm_single, norm_one, mul_one]

variable (s)

/-- The operator with border `B`, finite block `M` and diagonal tail `λ`. -/
noncomputable def op {M : Fin n → I → Fin n → I → 𝕜} {tl : I → 𝕜} {K : Fin n → Fin n → ℝ}
    (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) :
    𝕜 × (Fin n → WeightedL1 𝕜 ω') →L[𝕜] 𝕜 × (Fin n → WeightedL1 𝕜 ω) :=
  (B.a00 • ContinuousLinearMap.fst 𝕜 _ _ + (rowCLM s B.row).comp (ContinuousLinearMap.snd 𝕜 _ _)).prod
    ((FiniteTail.op h).comp (ContinuousLinearMap.snd 𝕜 _ _) +
      (ContinuousLinearMap.fst 𝕜 _ _).smulRight (colVec s B.col))

variable {s} {M : Fin n → I → Fin n → I → 𝕜} {tl : I → 𝕜} {K : Fin n → Fin n → ℝ}

theorem op_fst (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) (x : 𝕜 × (Fin n → WeightedL1 𝕜 ω')) :
    (op s B h x).1 = B.a00 * x.1 + ∑ i, ∑ l ∈ s, B.row i l * x.2 i l := by
  simp [op, rowCLM_apply]

theorem op_snd (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) (x : 𝕜 × (Fin n → WeightedL1 𝕜 ω'))
    (j : Fin n) (m : I) :
    (op s B h x).2 j m = if m ∈ s then B.col j m * x.1 + ∑ i, ∑ l ∈ s, M j m i l * x.2 i l
      else tl m * x.2 j m := by
  simp only [op, ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', Pi.add_apply, Pi.smul_apply, WeightedLp.add_apply,
    WeightedLp.smul_apply, colVec_apply, FiniteTail.op_apply]
  split_ifs <;> ring

/-! ### Norm bounds -/

omit [DecidableEq I] in
/-- `∑_{l ∈ s} |r_l| |x_l| ≤ R ‖x‖` when `|r_l| ≤ R ω'_l`. -/
theorem sum_norm_mul_le {r : I → 𝕜} {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ l ∈ s, ‖r l‖ ≤ R * ω' l)
    (x : WeightedL1 𝕜 ω') : ‖∑ l ∈ s, r l * x l‖ ≤ R * ‖x‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l ∈ s, ‖r l * x l‖ ≤ ∑ l ∈ s, R * (ω' l * ‖x l‖) :=
        Finset.sum_le_sum fun l hl => by
          rw [norm_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hR l hl) (norm_nonneg _)
    _ = R * ∑ l ∈ s, ω' l * ‖x l‖ := by rw [Finset.mul_sum]
    _ ≤ R * ‖x‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hR0
        rw [WeightedL1.norm_eq_tsum]
        exact (WeightedL1.summable x).sum_le_tsum _ fun l _ =>
          mul_nonneg (ω'.pos l).le (norm_nonneg _)

theorem norm_op_fst_le (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) {R : Fin n → ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : ∀ i, ∀ l ∈ s, ‖B.row i l‖ ≤ R i * ω' l)
    (x : 𝕜 × (Fin n → WeightedL1 𝕜 ω')) :
    ‖(op s B h x).1‖ ≤ ‖B.a00‖ * ‖x.1‖ + ∑ i, R i * ‖x.2 i‖ := by
  rw [op_fst]
  refine (norm_add_le _ _).trans (add_le_add (norm_mul _ _).le ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => sum_norm_mul_le (hR0 i) (hR i) _)

theorem norm_op_snd_le (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) {C : Fin n → ℝ}
    (hC : ∀ j, ∑ m ∈ s, ‖B.col j m‖ * ω m ≤ C j) (x : 𝕜 × (Fin n → WeightedL1 𝕜 ω'))
    (j : Fin n) : ‖(op s B h x).2 j‖ ≤ C j * ‖x.1‖ + ∑ i, K j i * ‖x.2 i‖ := by
  have : (op s B h x).2 j = FiniteTail.op h x.2 j + x.1 • colVec s B.col j := by
    simp [op]
  rw [this, add_comm]
  refine (norm_add_le _ _).trans (add_le_add ?_ (FiniteTail.norm_op_apply_le h x.2 j))
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((norm_colVec_le _ j).trans (hC j)) (norm_nonneg _)

/-- `‖T‖ ≤ Z` if `|a₀₀| + ∑ᵢ Rᵢ ≤ Z` and `C_j + ∑ᵢ K_{ji} ≤ Z` for all `j`. -/
theorem norm_op_le (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) {R C : Fin n → ℝ} {Z : ℝ}
    (hR0 : ∀ i, 0 ≤ R i) (hR : ∀ i, ∀ l ∈ s, ‖B.row i l‖ ≤ R i * ω' l)
    (hC : ∀ j, ∑ m ∈ s, ‖B.col j m‖ * ω m ≤ C j)
    (hZ0 : ‖B.a00‖ + ∑ i, R i ≤ Z) (hZ : ∀ j, C j + ∑ i, K j i ≤ Z) : ‖op s B h‖ ≤ Z := by
  have hZnn : 0 ≤ Z :=
    le_trans (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => hR0 i)) hZ0
  refine ContinuousLinearMap.opNorm_le_bound _ hZnn fun x => ?_
  have hx1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
  have hx2 : ∀ i, ‖x.2 i‖ ≤ ‖x‖ := fun i => (norm_le_pi_norm x.2 i).trans (norm_snd_le x)
  refine max_le ?_ ((pi_norm_le_iff_of_nonneg (mul_nonneg hZnn (norm_nonneg x))).2 fun j => ?_)
  · refine (norm_op_fst_le B h hR0 hR x).trans ?_
    calc ‖B.a00‖ * ‖x.1‖ + ∑ i, R i * ‖x.2 i‖ ≤ ‖B.a00‖ * ‖x‖ + ∑ i, R i * ‖x‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hx1 (norm_nonneg _))
            (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx2 i) (hR0 i))
      _ = (‖B.a00‖ + ∑ i, R i) * ‖x‖ := by rw [add_mul, Finset.sum_mul]
      _ ≤ Z * ‖x‖ := mul_le_mul_of_nonneg_right hZ0 (norm_nonneg x)
  · have hC0 : 0 ≤ C j := le_trans (Finset.sum_nonneg fun m _ =>
      mul_nonneg (norm_nonneg _) (ω.pos m).le) (hC j)
    refine (norm_op_snd_le B h hC x j).trans ?_
    calc C j * ‖x.1‖ + ∑ i, K j i * ‖x.2 i‖ ≤ C j * ‖x‖ + ∑ i, K j i * ‖x‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hx1 hC0)
            (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx2 i) (h.nonneg j i))
      _ = (C j + ∑ i, K j i) * ‖x‖ := by rw [add_mul, Finset.sum_mul]
      _ ≤ Z * ‖x‖ := mul_le_mul_of_nonneg_right (hZ j) (norm_nonneg x)

/-! ### Composition -/

omit [DecidableEq I] in
variable (s) in
/-- `∑_{i',l'} f_{i'l'} ∑_{i,l} g_{i'l'il} x_{il} = ∑_{i,l} (∑_{i',l'} f_{i'l'} g_{i'l'il}) x_{il}`. -/
theorem sum_mul_sum (f : Fin n → I → 𝕜) (g : Fin n → I → Fin n → I → 𝕜) (x : Fin n → I → 𝕜) :
    ∑ i', ∑ l' ∈ s, f i' l' * ∑ i, ∑ l ∈ s, g i' l' i l * x i l =
      ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, f i' l' * g i' l' i l) * x i l := by
  calc ∑ i', ∑ l' ∈ s, f i' l' * ∑ i, ∑ l ∈ s, g i' l' i l * x i l
      = ∑ i', ∑ l' ∈ s, ∑ i, ∑ l ∈ s, f i' l' * g i' l' i l * x i l := by
        refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
    _ = ∑ i, ∑ l ∈ s, ∑ i', ∑ l' ∈ s, f i' l' * g i' l' i l * x i l :=
        sum_sum_comm4 fun i' l' i l => f i' l' * g i' l' i l * x i l
    _ = ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, f i' l' * g i' l' i l) * x i l := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i' _ => by rw [Finset.sum_mul]

omit [DecidableEq I] in
variable (s) in
theorem sum_mul_const (f : Fin n → I → 𝕜) (c : Fin n → I → 𝕜) (t : 𝕜) :
    ∑ i, ∑ l ∈ s, f i l * (c i l * t) = (∑ i, ∑ l ∈ s, f i l * c i l) * t := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- `I - T D` is again an operator with border, finite block and diagonal tail: its matrix is
`I - (matrix of T)(matrix of D)` and its tail is `1 - λ λ_D`. -/
theorem id_sub_op_comp_op {MD : Fin n → I → Fin n → I → 𝕜} {tlD : I → 𝕜} {KD : Fin n → Fin n → ℝ}
    {ME : Fin n → I → Fin n → I → 𝕜} {tlE : I → 𝕜} {KE : Fin n → Fin n → ℝ}
    (B BD BE : Border n I 𝕜)
    (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD) (hE : Bound s ME tlE ω ω KE)
    (h00 : BE.a00 = 1 - (B.a00 * BD.a00 + ∑ i, ∑ l ∈ s, B.row i l * BD.col i l))
    (hrow : ∀ i l, l ∈ s →
      BE.row i l = -(B.a00 * BD.row i l + ∑ i', ∑ l' ∈ s, B.row i' l' * MD i' l' i l))
    (hcol : ∀ j m, m ∈ s →
      BE.col j m = -(B.col j m * BD.a00 + ∑ i', ∑ l' ∈ s, M j m i' l' * BD.col i' l'))
    (hEfin : ∀ j m i l, m ∈ s → l ∈ s →
      ME j m i l = (if j = i ∧ m = l then 1 else 0) -
        (B.col j m * BD.row i l + ∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l))
    (hEtail : ∀ m ∉ s, tlE m = 1 - tl m * tlD m) :
    ContinuousLinearMap.id 𝕜 _ - (op s B hA).comp (op s BD hD) = op s BE hE := by
  refine ContinuousLinearMap.ext fun x => ?_
  -- the tail coordinates of `D x`, in terms of the finite part of `x`
  have hDx : ∀ i, ∀ l ∈ s, (op s BD hD x).2 i l =
      BD.col i l * x.1 + ∑ i', ∑ l' ∈ s, MD i l i' l' * x.2 i' l' := fun i l hl => by
    rw [op_snd, ite_eq_left hl]
  have hsub : ∀ i, ∑ l ∈ s, (fun l => ∑ i', ∑ l' ∈ s, MD i l i' l' * x.2 i' l') l =
      ∑ l ∈ s, ∑ i', ∑ l' ∈ s, MD i l i' l' * x.2 i' l' := fun _ => rfl
  refine Prod.ext ?_ ?_
  · -- the scalar component
    simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      Prod.fst_sub]
    rw [op_fst, op_fst, op_fst, h00]
    have h1 : ∑ i, ∑ l ∈ s, B.row i l * (op s BD hD x).2 i l =
        (∑ i, ∑ l ∈ s, B.row i l * BD.col i l) * x.1 +
          ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, B.row i' l' * MD i' l' i l) * x.2 i l := by
      rw [← sum_mul_const s B.row BD.col x.1, ← sum_mul_sum s B.row MD (fun i l => x.2 i l),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hDx i l hl]
      ring
    have h2 : ∑ i, ∑ l ∈ s, BE.row i l * x.2 i l = ∑ i, ∑ l ∈ s,
        -(B.a00 * BD.row i l + ∑ i', ∑ l' ∈ s, B.row i' l' * MD i' l' i l) * x.2 i l :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by rw [hrow i l hl]
    rw [h1, h2]
    simp only [neg_mul, add_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum]
    ring
  · -- the sequence components
    funext j
    ext m
    simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      Prod.snd_sub, Pi.sub_apply, WeightedLp.sub_apply]
    rw [op_snd, op_snd, op_snd]
    split_ifs with hm
    · rw [op_fst, hcol j m hm]
      have h1 : ∑ i, ∑ l ∈ s, M j m i l * (op s BD hD x).2 i l =
          (∑ i, ∑ l ∈ s, M j m i l * BD.col i l) * x.1 +
            ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l) * x.2 i l := by
        rw [← sum_mul_const s (M j m) BD.col x.1, ← sum_mul_sum s (M j m) MD (fun i l => x.2 i l),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [hDx i l hl]
        ring
      have hδ : ∑ i, ∑ l ∈ s, (if j = i ∧ m = l then (1 : 𝕜) else 0) * x.2 i l = x.2 j m := by
        rw [Finset.sum_eq_single j (fun i _ hij => Finset.sum_eq_zero fun l _ => by
          simp [Ne.symm hij]) (by simp)]
        rw [Finset.sum_eq_single m (fun l _ hlm => by simp [Ne.symm hlm]) (by simp [hm])]
        simp
      have h2 : ∑ i, ∑ l ∈ s, ME j m i l * x.2 i l = ∑ i, ∑ l ∈ s,
          ((if j = i ∧ m = l then (1 : 𝕜) else 0) * x.2 i l -
            B.col j m * (BD.row i l * x.2 i l) -
            (∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l) * x.2 i l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by
          rw [hEfin j m i l hm hl]; ring
      rw [h1, h2]
      simp only [Finset.sum_sub_distrib, hδ, ← Finset.mul_sum]
      ring
    · rw [hEtail m hm]; ring

/-! ### Injectivity -/

section Proj

variable (s ω n) in
/-- The projection `(x₀, x) ↦ (x₀, finite part of x)`. -/
noncomputable def proj : (𝕜 × (Fin n → WeightedL1 𝕜 ω)) →ₗ[𝕜] (𝕜 × (Fin n → WeightedL1 𝕜 ω)) :=
  LinearMap.prodMap LinearMap.id (finProj s n ω)

variable (s ω n) in
/-- The finite parts, `𝕜 × (Fin n → s → 𝕜) → 𝕜 × (Fin n → ℓ¹)`. -/
noncomputable def ofFinP : (𝕜 × (Fin n → s → 𝕜)) →ₗ[𝕜] (𝕜 × (Fin n → WeightedL1 𝕜 ω)) :=
  LinearMap.prodMap LinearMap.id (ofFin s n ω)

theorem proj_apply (x : 𝕜 × (Fin n → WeightedL1 𝕜 ω)) :
    proj s n ω x = (x.1, finProj s n ω x.2) := rfl

theorem ofFinP_injective : Function.Injective (ofFinP s n ω : (𝕜 × (Fin n → s → 𝕜)) → _) :=
  fun c d h => by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (ofFin_injective h2)

theorem isIdempotentElem_proj : IsIdempotentElem (proj s n ω : _ →ₗ[𝕜] _) := by
  change proj s n ω * proj s n ω = proj s n ω
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, proj_apply, proj_apply]
  congr 1
  exact LinearMap.congr_fun (isIdempotentElem_finProj (𝕜 := 𝕜) (s := s) (n := n) (ω := ω)).eq x.2

theorem range_proj :
    LinearMap.range (proj s n ω : _ →ₗ[𝕜] _) = LinearMap.range (ofFinP s n ω) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact ⟨(x.1, finPart s n ω x.2), rfl⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨ofFinP s n ω c, ?_⟩
    rw [proj_apply]
    exact Prod.ext rfl (by
      change ofFin s n ω (finPart s n ω (ofFin s n ω c.2)) = ofFin s n ω c.2
      rw [finPart_ofFin])

instance : FiniteDimensional 𝕜 (LinearMap.range (proj s n ω : _ →ₗ[𝕜] _)) := by
  rw [range_proj]; exact LinearMap.finiteDimensional_range _

theorem finrank_range_proj :
    Module.finrank 𝕜 (LinearMap.range (proj s n ω : _ →ₗ[𝕜] _)) =
      Module.finrank 𝕜 (𝕜 × (Fin n → s → 𝕜)) := by
  rw [range_proj, LinearMap.finrank_range_of_inj ofFinP_injective]

/-- An operator with border, finite block and tail commutes with the projections. -/
theorem op_comp_proj (B : Border n I 𝕜) (h : Bound s M tl ω ω' K) :
    (op s B h : _ →ₗ[𝕜] _) ∘ₗ proj s n ω' = proj s n ω ∘ₗ (op s B h : _ →ₗ[𝕜] _) := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, proj_apply]
  refine Prod.ext ?_ ?_
  · rw [op_fst, op_fst]
    simp only
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by
      rw [finProj_apply, ite_eq_left hl]
  · funext j
    ext m
    rw [finProj_apply (𝕜 := 𝕜) (op s B h x).2, op_snd, op_snd]
    split_ifs with hm
    · simp only
      congr 1
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by
        rw [finProj_apply, ite_eq_left hl]
    · rw [finProj_apply, ite_eq_right hm, mul_zero]

end Proj

/-- Injectivity: if the tail `λ` of `T` does not vanish, `D` is another operator of the same form
and `‖I - T D‖ < 1`, then `T` is injective. -/
theorem injective_op {MD : Fin n → I → Fin n → I → 𝕜} {tlD : I → 𝕜} {KD : Fin n → Fin n → ℝ}
    (B BD : Border n I 𝕜) (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD)
    (htl : ∀ m ∉ s, tl m ≠ 0)
    (hnorm : ‖ContinuousLinearMap.id 𝕜 _ - (op s B hA).comp (op s BD hD)‖ < 1) :
    Function.Injective (op s B hA) := by
  refine injective_of_decomposition (op s B hA) (op s BD hD) (proj s n ω) (proj s n ω')
    isIdempotentElem_proj isIdempotentElem_proj (op_comp_proj B hA) (op_comp_proj BD hD)
    (by rw [finrank_range_proj, finrank_range_proj]) (fun y hy hAy => ?_) hnorm
  rw [proj_apply, Prod.mk_eq_zero] at hy
  refine Prod.ext hy.1 ?_
  funext j; ext m
  by_cases hm : m ∈ s
  · have := congrArg (fun z : Fin n → WeightedL1 𝕜 ω' => z j m) hy.2
    simpa [finProj_apply, hm] using this
  · have := congrArg (fun z : 𝕜 × (Fin n → WeightedL1 𝕜 ω) => z.2 j m) hAy
    simp only [op_snd, hm, ↓reduceIte, Prod.snd_zero, Pi.zero_apply, WeightedLp.zero_apply] at this
    simpa [htl m hm] using this

end ParamTail

end RadiiPolynomial
