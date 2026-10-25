module

public import RadiiPolynomial.WeightedLp.Operators
public import RadiiPolynomial.Abstract.Injectivity

/-!
# Operators made of a finite block and a diagonal tail

Let `s` be a finite set of indices (the "finite part"). On `n`-tuples of weighted ℓ¹ sequences
(`Fin n → ℓ¹_{ω',I}`, max norm) consider operators of the form

  `(T x)_{j,m} = ∑ᵢ ∑_{l ∈ s} M_{j m i l} x_{i,l}`   for `m ∈ s`,
  `(T x)_{j,m} = λ_m x_{j,m}`                        for `m ∉ s`,

given by a finite matrix `M` (indexed by `(j, m), (i, l)` with `m, l ∈ s`) and a diagonal tail `λ`
(`FiniteTail.op`). Approximate inverses and approximate derivatives of the radii polynomial
approach on sequence spaces are of this form.

* `FiniteTail.Bound s M λ ω ω' K`: the column-norm conditions `∑_{m ∈ s} |M_{j m i l}| ω_m ≤ K_{ji} ω'_l`
  (`l ∈ s`) and `|λ_l| ω_l ≤ K_{jj} ω'_l` (`l ∉ s`); then `‖T‖ ≤ maxⱼ ∑ᵢ K_{ji}` (`norm_op_le`)
  and `‖(T x)_j‖ ≤ ∑ᵢ K_{ji} ‖xᵢ‖` (`norm_op_apply_le`).
* `op_apply`: the coefficient formula above; `op_congr`: the operator does not depend on the bound.
* `finProj`: the projection onto the finite part, and `injective_op`: if the tail `λ` does not
  vanish, `T` commutes with the finite-part projections, and `‖I - T D‖ < 1` for an operator `D` of
  the same form, then `T` is injective.
* `op1`: the scalar case `n = 1` (operators `ℓ¹_{ω'} → ℓ¹_ω`), with `op1_apply`, `norm_op1_le`,
  `id_sub_op1_comp_op1`, `injective_op1`; `hasSum_apply1`: the matrix of a scalar operator.
-/

@[expose] public section

namespace RadiiPolynomial

/-- Splitting a sum into a finite part and the rest. -/
theorem tsum_eq_sum_add_tsum_ite {ι : Type*} [DecidableEq ι] {f : ι → ℝ} (hf : Summable f)
    (S : Finset ι) :
    ∑' k, f k = ∑ k ∈ S, f k + ∑' k, (if k ∈ S then 0 else f k) := by
  have h1 : ∑' k, (if k ∈ S then f k else 0) = ∑ k ∈ S, f k := by
    rw [tsum_eq_sum (s := S) fun k hk => by simp [hk]]
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have hs1 : Summable fun k => if k ∈ S then f k else 0 :=
    summable_of_ne_finset_zero (s := S) fun k hk => by simp [hk]
  rw [← h1, ← hs1.tsum_add (hf.sub hs1 |>.congr fun k => by split_ifs <;> simp)]
  exact tsum_congr fun k => by split_ifs <;> simp

namespace FiniteTail

variable {𝕜 : Type*} [RCLike 𝕜] {I : Type*} [DecidableEq I] (s : Finset I) {n : ℕ}
  {ω ω' : Weights I}

/-- The entries of the block `(j, i)`: the finite matrix on `s × s`, the diagonal tail outside. -/
def entry (M : Fin n → I → Fin n → I → 𝕜) (tl : I → 𝕜) (j i : Fin n) (m l : I) : 𝕜 :=
  if l ∈ s then (if m ∈ s then M j m i l else 0) else (if i = j ∧ m = l then tl l else 0)

/-- Column-norm bounds for the finite block and the tail. -/
structure Bound (M : Fin n → I → Fin n → I → 𝕜) (tl : I → 𝕜) (ω ω' : Weights I)
    (K : Fin n → Fin n → ℝ) : Prop where
  nonneg : ∀ j i, 0 ≤ K j i
  fin : ∀ j i, ∀ l ∈ s, ∑ m ∈ s, ‖M j m i l‖ * ω m ≤ K j i * ω' l
  tail : ∀ j, ∀ l ∉ s, ‖tl l‖ * ω l ≤ K j j * ω' l

variable {s} {M : Fin n → I → Fin n → I → 𝕜} {tl : I → 𝕜} {K : Fin n → Fin n → ℝ}

theorem entry_eq_zero_of_not_mem {j i : Fin n} {m l : I} (hl : l ∈ s ∨ m ≠ l) (hm : m ∉ s) :
    entry s M tl j i m l = 0 := by
  unfold entry
  rcases hl with hl | hl
  · simp [hl, hm]
  · split_ifs <;> simp_all

/-- Each block satisfies the column-norm bound of `ColNormBound`. -/
theorem Bound.colNormBound (h : Bound s M tl ω ω' K) (j i : Fin n) :
    ColNormBound (entry s M tl j i) ω ω' (K j i) where
  nonneg := h.nonneg j i
  summable l := summable_of_ne_finset_zero (s := insert l s) fun m hm => by
    rw [Finset.mem_insert, not_or] at hm
    rw [entry_eq_zero_of_not_mem (Or.inr hm.1) hm.2, norm_zero, zero_mul]
  le l := by
    rw [tsum_eq_sum (s := insert l s) fun m hm => by
      rw [Finset.mem_insert, not_or] at hm
      rw [entry_eq_zero_of_not_mem (Or.inr hm.1) hm.2, norm_zero, zero_mul]]
    by_cases hl : l ∈ s
    · rw [Finset.insert_eq_of_mem hl]
      refine le_of_eq_of_le (Finset.sum_congr rfl fun m hm => ?_) (h.fin j i l hl)
      simp [entry, hl, hm]
    · rw [Finset.sum_insert hl, Finset.sum_eq_zero fun m hm => by
        have : m ≠ l := fun h' => hl (h' ▸ hm)
        simp [entry, hl, this], add_zero]
      by_cases hij : i = j
      · subst hij
        simpa [entry, hl] using h.tail i l hl
      · simp only [entry, hl, ↓reduceIte, hij, false_and, norm_zero, zero_mul]
        exact mul_nonneg (h.nonneg j i) (ω'.pos l).le

/-- The operator with finite block `M` and diagonal tail `λ`. -/
noncomputable def op (h : Bound s M tl ω ω' K) :
    (Fin n → WeightedL1 𝕜 ω') →L[𝕜] (Fin n → WeightedL1 𝕜 ω) :=
  blockCLM fun j i => (h.colNormBound j i).toCLM

/-- The coefficients of `T x`. -/
theorem op_apply (h : Bound s M tl ω ω' K) (x : Fin n → WeightedL1 𝕜 ω') (j : Fin n) (m : I) :
    op h x j m = if m ∈ s then ∑ i, ∑ l ∈ s, M j m i l * x i l else tl m * x j m := by
  rw [op, blockCLM_apply, WeightedLp.sum_apply]
  simp only [ColNormBound.toCLM_apply]
  split_ifs with hm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [tsum_eq_sum (s := s) fun l hl => by
      have : m ≠ l := fun e => hl (e ▸ hm)
      simp [entry, hl, this]]
    exact Finset.sum_congr rfl fun l hl => by simp [entry, hl, hm]
  · rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [tsum_eq_sum (s := ∅) fun l _ => by
        unfold entry
        split_ifs <;> simp_all]
      simp) (by simp)]
    rw [tsum_eq_single m fun l hl => by
      unfold entry
      split_ifs <;> simp_all [Ne.symm hl]]
    simp [entry, hm]

/-- The operator does not depend on the bound used to construct it. -/
theorem op_congr {K' : Fin n → Fin n → ℝ} (h : Bound s M tl ω ω' K) (h' : Bound s M tl ω ω' K') :
    op h = op h' := by
  ext x j m
  rw [op_apply, op_apply]

/-- `‖T‖ ≤ C` whenever `∑ᵢ K_{ji} ≤ C` for all `j`. -/
theorem norm_op_le (h : Bound s M tl ω ω' K) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j, ∑ i, K j i ≤ C) :
    ‖op h‖ ≤ C :=
  norm_blockCLM_le _ hC0 fun j =>
    (Finset.sum_le_sum fun i _ => (h.colNormBound j i).norm_toCLM_le).trans (hC j)

/-- `‖(T x)_j‖ ≤ ∑ᵢ K_{ji} ‖xᵢ‖`. -/
theorem norm_op_apply_le (h : Bound s M tl ω ω' K) (x : Fin n → WeightedL1 𝕜 ω') (j : Fin n) :
    ‖op h x j‖ ≤ ∑ i, K j i * ‖x i‖ := by
  rw [op, blockCLM_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact ((h.colNormBound j i).toCLM.le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_right (h.colNormBound j i).norm_toCLM_le (norm_nonneg _))

/-! ### The finite part -/

section Proj

variable (s ω n)

/-- The finite part `(x_{j,l})_{j, l ∈ s}`. -/
def finPart : (Fin n → WeightedL1 𝕜 ω) →ₗ[𝕜] (Fin n → s → 𝕜) where
  toFun x j l := x j l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The tuple of sequences supported in `s` with the given finite part. -/
noncomputable def ofFin : (Fin n → s → 𝕜) →ₗ[𝕜] (Fin n → WeightedL1 𝕜 ω) where
  toFun c j := WeightedL1.ofSummable (fun l => if h : l ∈ s then c j ⟨l, h⟩ else 0)
    (summable_of_ne_finset_zero (s := s) fun l hl => by simp [hl])
  map_add' c d := by
    funext j; ext l
    simp only [WeightedL1.ofSummable_apply, Pi.add_apply, WeightedLp.add_apply]
    split_ifs <;> simp
  map_smul' c d := by
    funext j; ext l
    simp only [WeightedL1.ofSummable_apply, Pi.smul_apply, WeightedLp.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

/-- The projection onto the finite part. -/
noncomputable def finProj : (Fin n → WeightedL1 𝕜 ω) →ₗ[𝕜] (Fin n → WeightedL1 𝕜 ω) :=
  ofFin s n ω ∘ₗ finPart s n ω

variable {s ω n}

theorem ofFin_apply (c : Fin n → s → 𝕜) (j : Fin n) (l : I) :
    ofFin s n ω c j l = if h : l ∈ s then c j ⟨l, h⟩ else 0 := rfl

theorem finProj_apply (x : Fin n → WeightedL1 𝕜 ω) (j : Fin n) (l : I) :
    finProj s n ω x j l = if l ∈ s then x j l else 0 := by
  simp only [finProj, LinearMap.comp_apply, ofFin_apply]
  split_ifs <;> rfl

theorem finPart_ofFin (c : Fin n → s → 𝕜) : finPart s n ω (ofFin s n ω c) = c := by
  funext j l
  change ofFin s n ω c j l = c j l
  simp [ofFin_apply, l.2]

theorem ofFin_injective : Function.Injective (ofFin s n ω : (Fin n → s → 𝕜) → _) :=
  fun c d h => by rw [← finPart_ofFin (ω := ω) c, h, finPart_ofFin]

theorem isIdempotentElem_finProj : IsIdempotentElem (finProj s n ω : _ →ₗ[𝕜] _) := by
  change finProj s n ω * finProj s n ω = finProj s n ω
  refine LinearMap.ext fun x => ?_
  funext j
  ext l
  rw [Module.End.mul_apply, finProj_apply, finProj_apply]
  split_ifs <;> rfl

theorem range_finProj : LinearMap.range (finProj s n ω : _ →ₗ[𝕜] _) = LinearMap.range (ofFin s n ω) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact ⟨_, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨ofFin s n ω c, by rw [finProj, LinearMap.comp_apply, finPart_ofFin]⟩

instance : FiniteDimensional 𝕜 (LinearMap.range (finProj s n ω : _ →ₗ[𝕜] _)) := by
  rw [range_finProj]; exact LinearMap.finiteDimensional_range _

theorem finrank_range_finProj :
    Module.finrank 𝕜 (LinearMap.range (finProj s n ω : _ →ₗ[𝕜] _)) =
      Module.finrank 𝕜 (Fin n → s → 𝕜) := by
  rw [range_finProj, LinearMap.finrank_range_of_inj ofFin_injective]

/-- A finite-block-and-tail operator commutes with the finite-part projections. -/
theorem op_comp_finProj (h : Bound s M tl ω ω' K) :
    (op h : _ →ₗ[𝕜] _) ∘ₗ finProj s n ω' = finProj s n ω ∘ₗ (op h : _ →ₗ[𝕜] _) := by
  refine LinearMap.ext fun x => ?_
  funext j
  ext m
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, finProj_apply, op_apply]
  split_ifs with hm
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by simp
  · simp

end Proj

/-- Injectivity: if the tail `λ` of `T` does not vanish, `D` is another finite-block-and-tail
operator and `‖I - T D‖ < 1`, then `T` is injective. -/
theorem injective_op {MD : Fin n → I → Fin n → I → 𝕜} {tlD : I → 𝕜} {KD : Fin n → Fin n → ℝ}
    (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD) (htl : ∀ m ∉ s, tl m ≠ 0)
    (hnorm : ‖ContinuousLinearMap.id 𝕜 _ - (op hA).comp (op hD)‖ < 1) :
    Function.Injective (op hA) := by
  refine injective_of_decomposition (op hA) (op hD) (finProj s n ω) (finProj s n ω')
    isIdempotentElem_finProj isIdempotentElem_finProj (op_comp_finProj hA) (op_comp_finProj hD)
    (by rw [finrank_range_finProj, finrank_range_finProj]) (fun y hy hAy => ?_) hnorm
  funext j; ext m
  by_cases hm : m ∈ s
  · have := congrArg (fun z : Fin n → WeightedL1 𝕜 ω' => z j m) hy
    simpa [finProj_apply, hm] using this
  · have := congrArg (fun z : Fin n → WeightedL1 𝕜 ω => z j m) hAy
    simp only [op_apply, hm, ↓reduceIte, Pi.zero_apply, WeightedLp.zero_apply] at this
    simpa [htl m hm] using this

/-! ### Composition -/

omit [DecidableEq I] in
theorem sum_sum_comm4 (f : Fin n → I → Fin n → I → 𝕜) :
    ∑ a, ∑ b ∈ s, ∑ c, ∑ d ∈ s, f a b c d = ∑ c, ∑ d ∈ s, ∑ a, ∑ b ∈ s, f a b c d := by
  calc ∑ a, ∑ b ∈ s, ∑ c, ∑ d ∈ s, f a b c d = ∑ a, ∑ c, ∑ b ∈ s, ∑ d ∈ s, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b ∈ s, ∑ d ∈ s, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d ∈ s, ∑ b ∈ s, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d ∈ s, ∑ a, ∑ b ∈ s, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- `I - T D` is again a finite-block-and-tail operator: its finite block is `δ - M M_D` and its
tail is `1 - λ λ_D`. -/
theorem id_sub_op_comp_op {MD : Fin n → I → Fin n → I → 𝕜} {tlD : I → 𝕜} {KD : Fin n → Fin n → ℝ}
    {E : Fin n → I → Fin n → I → 𝕜} {tlE : I → 𝕜} {KE : Fin n → Fin n → ℝ}
    (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD) (hE : Bound s E tlE ω ω KE)
    (hEfin : ∀ j m i l, m ∈ s → l ∈ s →
      E j m i l = (if j = i ∧ m = l then 1 else 0) - ∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l)
    (hEtail : ∀ m ∉ s, tlE m = 1 - tl m * tlD m) :
    ContinuousLinearMap.id 𝕜 _ - (op hA).comp (op hD) = op hE := by
  ext x j m
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, Pi.sub_apply, WeightedLp.sub_apply, op_apply]
  split_ifs with hm
  · have hL : ∑ i', ∑ l' ∈ s, M j m i' l' * ∑ i, ∑ l ∈ s, MD i' l' i l * x i l =
        ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l) * x i l := by
      calc ∑ i', ∑ l' ∈ s, M j m i' l' * ∑ i, ∑ l ∈ s, MD i' l' i l * x i l
          = ∑ i', ∑ l' ∈ s, ∑ i, ∑ l ∈ s, M j m i' l' * MD i' l' i l * x i l := by
            refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm
        _ = ∑ i, ∑ l ∈ s, ∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l * x i l :=
            sum_sum_comm4 fun i' l' i l => M j m i' l' * MD i' l' i l * x i l
        _ = ∑ i, ∑ l ∈ s, (∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l) * x i l := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i' _ => by rw [Finset.sum_mul]
    have hδ : ∑ i, ∑ l ∈ s, (if j = i ∧ m = l then (1 : 𝕜) else 0) * x i l = x j m := by
      rw [Finset.sum_eq_single j (fun i _ hij => Finset.sum_eq_zero fun l _ => by
        simp [Ne.symm hij]) (by simp)]
      rw [Finset.sum_eq_single m (fun l _ hlm => by simp [Ne.symm hlm]) (by simp [hm])]
      simp
    have hR : ∑ i, ∑ l ∈ s, E j m i l * x i l = ∑ i, ∑ l ∈ s,
        ((if j = i ∧ m = l then (1 : 𝕜) else 0) * x i l -
          (∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l) * x i l) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l hl => by
        rw [hEfin j m i l hm hl, sub_mul]
    rw [hL, hR]
    simp only [Finset.sum_sub_distrib, hδ]
  · rw [hEtail m hm]; ring

/-! ### A canonical bound, and the matrix of an operator -/

variable (s) in
/-- A crude but always valid bound: `K_{ji} = ∑_{l ∈ s} (∑_{m ∈ s} |M_{jmil}| ω_m) / ω'_l + κ`. -/
noncomputable def crudeK (M : Fin n → I → Fin n → I → 𝕜) (ω ω' : Weights I) (κ : ℝ)
    (j i : Fin n) : ℝ :=
  ∑ l ∈ s, (∑ m ∈ s, ‖M j m i l‖ * ω m) / ω' l + κ

omit [DecidableEq I] in
theorem crudeK_sum_nonneg (ω ω' : Weights I) (j i : Fin n) :
    0 ≤ ∑ l ∈ s, (∑ m ∈ s, ‖M j m i l‖ * ω m) / ω' l :=
  Finset.sum_nonneg fun l _ => div_nonneg
    (Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (ω.pos m).le) (ω'.pos l).le

omit [DecidableEq I] in
theorem crudeBound {κ : ℝ} (hκ : 0 ≤ κ) (htail : ∀ l ∉ s, ‖tl l‖ * ω l ≤ κ * ω' l) :
    Bound s M tl ω ω' (crudeK s M ω ω' κ) where
  nonneg j i := add_nonneg (crudeK_sum_nonneg ω ω' j i) hκ
  fin j i l hl := by
    have hterm : (∑ m ∈ s, ‖M j m i l‖ * ω m) / ω' l ≤
        ∑ l' ∈ s, (∑ m ∈ s, ‖M j m i l'‖ * ω m) / ω' l' :=
      Finset.single_le_sum (f := fun l' => (∑ m ∈ s, ‖M j m i l'‖ * ω m) / ω' l')
        (fun l' _ => div_nonneg (Finset.sum_nonneg fun m _ =>
          mul_nonneg (norm_nonneg _) (ω.pos m).le) (ω'.pos l').le) hl
    rw [div_le_iff₀ (ω'.pos l)] at hterm
    refine hterm.trans (mul_le_mul_of_nonneg_right ?_ (ω'.pos l).le)
    simp only [crudeK]
    linarith
  tail j l hl := (htail l hl).trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_left (crudeK_sum_nonneg ω ω' j j)) (ω'.pos l).le)

/-- The unit tuple `e_{i,k}`: the sequence `e_k` in component `i`, zero elsewhere. -/
noncomputable def unitVec (i : Fin n) (k : I) : Fin n → WeightedL1 𝕜 ω :=
  Pi.single i (WeightedL1.single k 1)

/-- A bounded operator on tuples acts through its matrix: `(T y)_{j,m} = ∑ᵢ ∑ₖ (T e_{i,k})_{j,m} y_{i,k}`
(the inner sums converge). -/
theorem hasSum_apply (T : (Fin n → WeightedL1 𝕜 ω') →L[𝕜] (Fin n → WeightedL1 𝕜 ω))
    (y : Fin n → WeightedL1 𝕜 ω') (i j : Fin n) (m : I) :
    HasSum (fun k => T (unitVec i k) j m * y i k) (T (Pi.single i (y i)) j m) := by
  let Φ : WeightedL1 𝕜 ω' →L[𝕜] 𝕜 :=
    (WeightedLp.evalCLM m).comp ((ContinuousLinearMap.proj j).comp
      (T.comp (ContinuousLinearMap.single 𝕜 (fun _ : Fin n => WeightedL1 𝕜 ω') i)))
  have h := (WeightedL1.hasSum_single (y i)).mapL Φ
  have h2 : (fun k => T (unitVec i k) j m * y i k) =
      fun k => Φ (WeightedL1.single k (y i k)) := by
    funext k
    rw [WeightedL1.single_eq_smul, map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [h2]
  exact h

theorem apply_eq_sum_tsum (T : (Fin n → WeightedL1 𝕜 ω') →L[𝕜] (Fin n → WeightedL1 𝕜 ω))
    (y : Fin n → WeightedL1 𝕜 ω') (j : Fin n) (m : I) :
    T y j m = ∑ i, ∑' k, T (unitVec i k) j m * y i k := by
  have hy : y = ∑ i, Pi.single i (y i) := (Finset.univ_sum_single y).symm
  conv_lhs => rw [hy, map_sum, Finset.sum_apply, WeightedLp.sum_apply]
  exact Finset.sum_congr rfl fun i _ => (hasSum_apply T y i j m).tsum_eq.symm

/-- A bounded operator on sequences acts through its matrix: `(T y)_m = ∑ₖ (T e_k)_m y_k`. -/
theorem hasSum_apply1 (T : WeightedL1 𝕜 ω' →L[𝕜] WeightedL1 𝕜 ω) (y : WeightedL1 𝕜 ω') (m : I) :
    HasSum (fun k => T (WeightedL1.single k 1) m * y k) (T y m) := by
  have h := (WeightedL1.hasSum_single y).mapL ((WeightedLp.evalCLM m).comp T)
  convert h using 1
  · funext k
    conv_rhs => rw [WeightedL1.single_eq_smul, map_smul, smul_eq_mul]
    rw [mul_comm]
    rfl
  · rfl

/-! ### Scalar operators (`n = 1`) -/

section Scalar

variable {M : Fin 1 → I → Fin 1 → I → 𝕜} {K : Fin 1 → Fin 1 → ℝ}

/-- The scalar operator `ℓ¹_{ω'} → ℓ¹_ω` with finite block `M` and diagonal tail `λ` (the case
`n = 1`): `x ↦ (T (x))₀`. -/
noncomputable def op1 (h : Bound s M tl ω ω' K) : WeightedL1 𝕜 ω' →L[𝕜] WeightedL1 𝕜 ω :=
  (ContinuousLinearMap.proj 0).comp
    ((op h).comp (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id 𝕜 (WeightedL1 𝕜 ω')))

theorem op1_apply' (h : Bound s M tl ω ω' K) (x : WeightedL1 𝕜 ω') :
    op1 h x = op h (fun _ => x) 0 := rfl

theorem op1_apply (h : Bound s M tl ω ω' K) (x : WeightedL1 𝕜 ω') (m : I) :
    op1 h x m = if m ∈ s then ∑ l ∈ s, M 0 m 0 l * x l else tl m * x m := by
  rw [op1_apply', op_apply, Fin.sum_univ_one]

theorem norm_op1_apply_le (h : Bound s M tl ω ω' K) (x : WeightedL1 𝕜 ω') :
    ‖op1 h x‖ ≤ K 0 0 * ‖x‖ := by
  rw [op1_apply']
  refine (norm_op_apply_le h _ 0).trans (le_of_eq ?_)
  rw [Fin.sum_univ_one]

theorem norm_op1_le (h : Bound s M tl ω ω' K) : ‖op1 h‖ ≤ K 0 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (h.nonneg 0 0) (norm_op1_apply_le h)

omit [DecidableEq I] in
/-- A tuple of length one is the constant tuple of its entry. -/
theorem fin_one_eq_const {E : Type*} (y : Fin 1 → E) : y = fun _ => y 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

/-- `I - T D` for scalar operators (`id_sub_op_comp_op` with `n = 1`). -/
theorem id_sub_op1_comp_op1 {MD : Fin 1 → I → Fin 1 → I → 𝕜} {tlD : I → 𝕜}
    {KD : Fin 1 → Fin 1 → ℝ} {E : Fin 1 → I → Fin 1 → I → 𝕜} {tlE : I → 𝕜}
    {KE : Fin 1 → Fin 1 → ℝ}
    (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD) (hE : Bound s E tlE ω ω KE)
    (hEfin : ∀ j m i l, m ∈ s → l ∈ s →
      E j m i l = (if j = i ∧ m = l then 1 else 0) - ∑ i', ∑ l' ∈ s, M j m i' l' * MD i' l' i l)
    (hEtail : ∀ m ∉ s, tlE m = 1 - tl m * tlD m) :
    ContinuousLinearMap.id 𝕜 _ - (op1 hA).comp (op1 hD) = op1 hE := by
  ext1 x
  have h := congrArg (fun T => T (fun _ : Fin 1 => x) 0) (id_sub_op_comp_op hA hD hE hEfin hEtail)
  simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    Pi.sub_apply] at h
  rw [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, op1_apply',
    op1_apply', op1_apply', ← fin_one_eq_const]
  exact h

/-- Injectivity of scalar operators (`injective_op` with `n = 1`). -/
theorem injective_op1 {MD : Fin 1 → I → Fin 1 → I → 𝕜} {tlD : I → 𝕜} {KD : Fin 1 → Fin 1 → ℝ}
    (hA : Bound s M tl ω ω' K) (hD : Bound s MD tlD ω' ω KD) (htl : ∀ m ∉ s, tl m ≠ 0)
    (hnorm : ‖ContinuousLinearMap.id 𝕜 _ - (op1 hA).comp (op1 hD)‖ < 1) :
    Function.Injective (op1 hA) := by
  set S := ContinuousLinearMap.id 𝕜 (WeightedL1 𝕜 ω) - (op1 hA).comp (op1 hD)
  set T := ContinuousLinearMap.id 𝕜 (Fin 1 → WeightedL1 𝕜 ω) - (op hA).comp (op hD)
  have hTS : ∀ y, T y = fun _ => S (y 0) := fun y => by
    rw [fin_one_eq_const (T y)]
    funext i
    simp only [T, S, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      Pi.sub_apply, op1_apply']
    rw [← fin_one_eq_const (op hD fun _ => y 0), ← fin_one_eq_const y]
  have hT : ‖T‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun y => ?_) hnorm
    rw [hTS, pi_norm_const]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm y 0) (norm_nonneg _))
  have hinj := injective_op hA hD htl hT
  intro x y hxy
  have : op hA (fun _ => x) = op hA (fun _ => y) := by
    rw [fin_one_eq_const (op hA fun _ => x), fin_one_eq_const (op hA fun _ => y)]
    exact funext fun _ => hxy
  exact congrFun (hinj this) 0

end Scalar

end FiniteTail

end RadiiPolynomial
