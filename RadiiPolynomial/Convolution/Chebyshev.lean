module

public import RadiiPolynomial.Convolution.Symmetric
public import RadiiPolynomial.WeightedLp.Operators
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Spaces of Chebyshev coefficients

Fix `ν ≥ 1`. The weights over `ℕ`

  `ω_0 = 1, ω_k = 2 ν^k`   and   `ω'_0 = 1, ω'_k = ν^k / k`   (`k ≥ 1`)

define the Banach spaces `X_ν = ℓ¹_{ω,ℕ}(ℝ)` (`Chebyshev.X`), with
`‖a‖ = |a_0| + 2 ∑_{k ≥ 1} |a_k| ν^k`, and `Y_ν = ℓ¹_{ω',ℕ}(ℝ)` (`Chebyshev.Y`). An element
`a ∈ X_ν` represents the Chebyshev series `a_0 + 2 ∑_{k ≥ 1} a_k T_k(t)`.

The Chebyshev product is `(a * b)_k = ∑_{j ∈ ℤ} a_{|j|} b_{|k - j|}`. It is defined through the
symmetric extension `a ↦ (a_{|k|})_{k ∈ ℤ}` (`symExt`), a linear isometry from `X_ν` onto the
symmetric sequences of `ℓ¹_{ν,ℤ}`: the product, the unit and the whole commutative Banach algebra
structure of `X_ν` are pulled back from that closed subalgebra (`instNormedCommRing`,
`instNormedAlgebra`; `mul_apply` gives the formula above).

The operators `diffOp`, `shiftUp`, `shiftDown : X_ν → Y_ν` (each with one entry per column) are
`(D a)_k = 2k a_k`, `(S₊ c)_k = c_{k+1}` and `(S₋ c)_k = c_{k-1}` for `k ≥ 1` (all three vanish
at `k = 0`), with `‖D‖ ≤ 1`, `‖S₊‖ ≤ 1/(2ν)`, `‖S₋‖ ≤ ν`; `shiftOp = S₊ - S₋`,
`‖shiftOp‖ ≤ ν + 1/(2ν)`. `e0` is the unit sequence `(1, 0, 0, …)` of `Y_ν`.

Supports: `SuppLe a N` (`a_k = 0` for `k > N`) is preserved by sums and scalar multiples and
`SuppLe a N₁ → SuppLe b N₂ → SuppLe (a * b) (N₁ + N₂)`; hence a polynomial of total degree `≤ M` in
sequences supported in `[0, N]` is supported in `[0, M N]` (`suppLe_aeval`). With the unit sequence
`e_k`, `(b * e_k)_p = b_{|p - k|} + b_{p + k}` for `k ≥ 1` (`mul_single_apply`).

`boundaryEval s` is the bounded functional `a ↦ a_0 + 2 ∑_{k ≥ 1} s^k a_k` for `|s| ≤ 1`, of norm at
most `1`; for `s = ±1` it is the value `u(±1)` of the Chebyshev series.
-/

@[expose] public section

namespace RadiiPolynomial

namespace Chebyshev

theorem nu_pos {ν : ℝ} (hν : 1 ≤ ν) : 0 < ν := lt_of_lt_of_le zero_lt_one hν

variable (ν : ℝ) (hν : 1 ≤ ν)

/-- The weights `ω_0 = 1`, `ω_k = 2 ν^k`. -/
def weights (ν : ℝ) (hν : 1 ≤ ν) : Weights ℕ :=
  ⟨fun k => if k = 0 then 1 else 2 * ν ^ k, fun k => by
    split_ifs
    · exact one_pos
    · exact mul_pos two_pos (pow_pos (nu_pos hν) k)⟩

/-- The weights `ω'_0 = 1`, `ω'_k = ν^k / k`. -/
noncomputable def weightsY (ν : ℝ) (hν : 1 ≤ ν) : Weights ℕ :=
  ⟨fun k => if k = 0 then 1 else ν ^ k / k, fun k => by
    split_ifs with hk
    · exact one_pos
    · exact div_pos (pow_pos (nu_pos hν) k) (by exact_mod_cast Nat.pos_of_ne_zero hk)⟩

theorem weights_apply (k : ℕ) : weights ν hν k = if k = 0 then 1 else 2 * ν ^ k := rfl

theorem weightsY_apply (k : ℕ) : weightsY ν hν k = if k = 0 then 1 else ν ^ k / k := rfl

@[simp] theorem weights_zero : weights ν hν 0 = 1 := rfl

@[simp] theorem weights_succ (k : ℕ) : weights ν hν (k + 1) = 2 * ν ^ (k + 1) := rfl

/-- `X_ν`, the Chebyshev coefficients with `|a_0| + 2 ∑_{k ≥ 1} |a_k| ν^k < ∞`. -/
abbrev X := WeightedL1 ℝ (weights ν hν)

/-- `Y_ν = ℓ¹_{ω',ℕ}(ℝ)`, `ω'_0 = 1`, `ω'_k = ν^k / k`. -/
abbrev Y := WeightedL1 ℝ (weightsY ν hν)

variable {ν hν}

/-! ### The symmetric extension -/

theorem summable_symExt (a : X ν hν) :
    Summable fun k : ℤ => (Weights.geomInt ν hν) k * ‖a k.natAbs‖ := by
  have hle : ∀ n : ℕ, ν ^ n * ‖a n‖ ≤ weights ν hν n * ‖a n‖ := fun n => by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [weights_apply]
    split_ifs with hn
    · simp [hn]
    · linarith [pow_pos (nu_pos hν) n]
  have h0 : Summable fun n : ℕ => ν ^ n * ‖a n‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_pos (nu_pos hν) n).le (norm_nonneg _))
      hle a.summable
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using h0
  · have := (summable_nat_add_iff 1).2 h0
    refine this.congr fun n => ?_
    simp only [Weights.geomInt_apply]
    congr 2

/-- The symmetric extension `(a_{|k|})_{k ∈ ℤ}` of `a ∈ X_ν`, an element of `ℓ¹_{ν,ℤ}`. -/
noncomputable def symExt (a : X ν hν) : WeightedL1 ℝ (Weights.geomInt ν hν) :=
  WeightedL1.ofSummable (fun k : ℤ => a k.natAbs) (summable_symExt a)

@[simp] theorem symExt_apply (a : X ν hν) (k : ℤ) : symExt a k = a k.natAbs := rfl

theorem symExt_mem (a : X ν hν) : symExt a ∈ WeightedL1.symmetricSubalgebra ℝ ν hν :=
  fun k => by simp

/-- The norm of `X_ν` is the norm of the symmetric extension in `ℓ¹_{ν,ℤ}`. -/
theorem norm_symExt (a : X ν hν) : ‖symExt a‖ = ‖a‖ := by
  let g : ℕ → ℝ := fun n => ν ^ n * ‖a n‖
  have hpos : (fun n : ℕ => (Weights.geomInt ν hν) n * ‖symExt a n‖) = g := by
    funext n; simp [g]
  have hneg : (fun n : ℕ => (Weights.geomInt ν hν) (-((n : ℤ) + 1)) * ‖symExt a (-((n : ℤ) + 1))‖) =
      fun n => g (n + 1) := by
    funext n
    simp only [g, Weights.geomInt_apply, symExt_apply]
    congr 2
  have h0 : Summable g := by
    have := (summable_symExt a).comp_injective Nat.cast_injective
    rw [← hpos]; exact this
  have h1 : Summable fun n => g (n + 1) := (summable_nat_add_iff 1).2 h0
  have hS : ∑' n : ℕ, weights ν hν (n + 1) * ‖a (n + 1)‖ = 2 * ∑' n : ℕ, g (n + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [weights_succ]; ring
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum,
    tsum_of_nat_of_neg_add_one (by rw [hpos]; exact h0) (by rw [hneg]; exact h1), hpos, hneg,
    h0.tsum_eq_zero_add, a.summable.tsum_eq_zero_add, hS]
  simp only [g, pow_zero, one_mul, weights_zero]
  ring

theorem symExt_injective : Function.Injective (symExt : X ν hν → _) := fun a b h => by
  ext n
  have := congrArg (fun s : WeightedL1 ℝ (Weights.geomInt ν hν) => s (n : ℤ)) h
  simpa using this

@[simp] theorem symExt_zero : symExt (0 : X ν hν) = 0 := by ext k; simp

theorem symExt_add (a b : X ν hν) : symExt (a + b) = symExt a + symExt b := by ext k; simp

theorem symExt_neg (a : X ν hν) : symExt (-a) = -symExt a := by ext k; simp

theorem symExt_sub (a b : X ν hν) : symExt (a - b) = symExt a - symExt b := by ext k; simp

theorem symExt_smul (c : ℝ) (a : X ν hν) : symExt (c • a) = c • symExt a := by ext k; simp

/-- The restriction `(s_n)_{n ∈ ℕ}` of `s ∈ ℓ¹_{ν,ℤ}`; for symmetric `s` it inverts `symExt`. -/
noncomputable def restrict (s : WeightedL1 ℝ (Weights.geomInt ν hν)) : X ν hν :=
  WeightedL1.ofSummable (fun n : ℕ => s n) (by
    have h0 : Summable fun n : ℕ => ν ^ n * ‖s n‖ :=
      (s.summable.comp_injective Nat.cast_injective).congr fun n => by simp
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg ((weights ν hν).pos n).le (norm_nonneg _))
      (fun n => ?_) (h0.mul_left 2)
    rw [weights_apply, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    split_ifs with hn
    · simp [hn]
    · exact le_rfl)

@[simp] theorem restrict_apply (s : WeightedL1 ℝ (Weights.geomInt ν hν)) (n : ℕ) :
    restrict s n = s n := rfl

theorem symExt_restrict (s : WeightedL1 ℝ (Weights.geomInt ν hν))
    (hs : s ∈ WeightedL1.symmetricSubalgebra ℝ ν hν) : symExt (restrict s) = s := by
  ext k
  rw [symExt_apply, restrict_apply]
  rcases Int.natAbs_eq k with h | h
  · rw [← h]
  · rw [h, hs]
    simp

/-! ### The Chebyshev product -/

/-- The symmetric sequences of `ℓ¹_{ν,ℤ}`. -/
local notation "Sym" => WeightedL1.symmetricSubalgebra ℝ ν hν

/-- The Chebyshev product `(a * b)_k = ∑_{j ∈ ℤ} a_{|j|} b_{|k - j|}`. -/
noncomputable instance : Mul (X ν hν) := ⟨fun a b => restrict (symExt a * symExt b)⟩

noncomputable instance : One (X ν hν) := ⟨restrict 1⟩

noncomputable instance : Pow (X ν hν) ℕ := ⟨fun a n => restrict (symExt a ^ n)⟩

noncomputable instance : NatCast (X ν hν) := ⟨fun n => restrict n⟩

noncomputable instance : IntCast (X ν hν) := ⟨fun n => restrict n⟩

theorem symExt_mul (a b : X ν hν) : symExt (a * b) = symExt a * symExt b :=
  symExt_restrict _ ((Sym).mul_mem (symExt_mem a) (symExt_mem b))

theorem symExt_one : symExt (1 : X ν hν) = 1 := symExt_restrict _ (Sym).one_mem

theorem symExt_pow (a : X ν hν) (n : ℕ) : symExt (a ^ n) = symExt a ^ n :=
  symExt_restrict _ ((Sym).pow_mem (symExt_mem a) n)

theorem symExt_natCast (n : ℕ) : symExt (n : X ν hν) = n := symExt_restrict _ ((Sym).natCast_mem n)

theorem symExt_intCast (n : ℤ) : symExt (n : X ν hν) = n := symExt_restrict _ ((Sym).intCast_mem n)

theorem symExt_nsmul (n : ℕ) (a : X ν hν) : symExt (n • a) = n • symExt a := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, symExt_smul, Nat.cast_smul_eq_nsmul]

theorem symExt_zsmul (n : ℤ) (a : X ν hν) : symExt (n • a) = n • symExt a := by
  rw [← Int.cast_smul_eq_zsmul ℝ, symExt_smul, Int.cast_smul_eq_zsmul]

/-- `(X_ν, *)` is a commutative ring, isomorphic to the symmetric sequences of `ℓ¹_{ν,ℤ}`. -/
noncomputable instance instCommRing : CommRing (X ν hν) :=
  symExt_injective.commRing symExt symExt_zero symExt_one symExt_add symExt_mul symExt_neg
    symExt_sub symExt_nsmul symExt_zsmul symExt_pow symExt_natCast symExt_intCast

/-- `(X_ν, *)` is a commutative Banach algebra with unit: `‖a * b‖ ≤ ‖a‖ ‖b‖`. -/
noncomputable instance instNormedCommRing : NormedCommRing (X ν hν) where
  __ := (inferInstance : NormedAddCommGroup (X ν hν))
  __ := instCommRing
  norm_mul_le a b := by
    rw [← norm_symExt, ← norm_symExt, ← norm_symExt, symExt_mul]
    exact norm_mul_le _ _

noncomputable instance instAlgebra : Algebra ℝ (X ν hν) :=
  Algebra.ofModule
    (fun r a b => symExt_injective (by rw [symExt_mul, symExt_smul, symExt_smul, symExt_mul,
      smul_mul_assoc]))
    (fun r a b => symExt_injective (by rw [symExt_mul, symExt_smul, symExt_smul, symExt_mul,
      mul_smul_comm]))

noncomputable instance instNormedAlgebra : NormedAlgebra ℝ (X ν hν) where
  norm_smul_le := norm_smul_le

/-- The Chebyshev product: `(a * b)_k = ∑_{j ∈ ℤ} a_{|j|} b_{|k - j|}`. -/
theorem mul_apply (a b : X ν hν) (k : ℕ) :
    (a * b) k = ∑' j : ℤ, a j.natAbs * b ((k : ℤ) - j).natAbs := by
  change (symExt a * symExt b) (k : ℤ) = _
  rw [WeightedL1.mul_apply, Convolution.conv_int]
  rfl

/-! ### Boundary values -/

/-- The coefficients `1, 2s, 2s², …` of the value `a_0 + 2 ∑_{k ≥ 1} s^k a_k`. -/
def evalWeight (s : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else 2 * s ^ k

theorem norm_evalWeight_le {s : ℝ} (hs : |s| ≤ 1) (k : ℕ) :
    ‖evalWeight s k‖ ≤ 1 * weights ν hν k := by
  rw [one_mul, weights_apply, evalWeight]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_two]
    have h1 : |s| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
    have h2 : 1 ≤ ν ^ k := one_le_pow₀ hν
    nlinarith

variable (ν hν) in
/-- The value `a_0 + 2 ∑_{k ≥ 1} s^k a_k` (for `s = ±1`, the value at `t = s` of the Chebyshev
series of `a`), a bounded functional of norm at most `1` when `|s| ≤ 1`. -/
noncomputable def boundaryEval (s : ℝ) (hs : |s| ≤ 1) : X ν hν →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' k, evalWeight s k * a k
      map_add' := fun a b => by
        simp only [WeightedLp.add_apply, mul_add]
        exact (WeightedL1.summable_mul a (norm_evalWeight_le hs)).of_norm.tsum_add
          (WeightedL1.summable_mul b (norm_evalWeight_le hs)).of_norm
      map_smul' := fun c a => by
        simp only [WeightedLp.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← tsum_mul_left]
        exact tsum_congr fun k => by ring }
    1 fun a => WeightedL1.norm_tsum_mul_le a (norm_evalWeight_le hs)

theorem boundaryEval_apply (s : ℝ) (hs : |s| ≤ 1) (a : X ν hν) :
    boundaryEval ν hν s hs a = ∑' k, evalWeight s k * a k := rfl

theorem norm_boundaryEval_le (s : ℝ) (hs : |s| ≤ 1) : ‖boundaryEval ν hν s hs‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### The operators `D`, `S₊`, `S₋` -/

theorem diff_bound (k : ℕ) : ‖(2 * k : ℝ)‖ * weightsY ν hν k ≤ 1 * weights ν hν k := by
  rw [weightsY_apply, weights_apply, one_mul]
  split_ifs with hk
  · simp [hk]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
    exact le_rfl

theorem shiftUp_bound (k : ℕ) :
    ‖(if 2 ≤ k then (1 : ℝ) else 0)‖ * weightsY ν hν (k - 1) ≤ (2 * ν)⁻¹ * weights ν hν k := by
  have hν0 := nu_pos hν
  split_ifs with hk
  · have hk1 : k - 1 ≠ 0 := by omega
    have hk0 : k ≠ 0 := by omega
    simp only [weightsY_apply, weights_apply, hk1, hk0, ↓reduceIte, norm_one, one_mul]
    have hc : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk1
    have hpow : ν ^ k = ν * ν ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    rw [div_le_iff₀ (by linarith), hpow]
    field_simp
    nlinarith [pow_pos hν0 (k - 1)]
  · rw [norm_zero, zero_mul]
    exact mul_nonneg (inv_nonneg.2 (by linarith)) ((weights ν hν).pos k).le

theorem shiftDown_bound (k : ℕ) : ‖(1 : ℝ)‖ * weightsY ν hν (k + 1) ≤ ν * weights ν hν k := by
  have hν0 := nu_pos hν
  simp only [norm_one, one_mul, weightsY_apply, Nat.succ_ne_zero, ↓reduceIte, weights_apply]
  rw [div_le_iff₀ (by positivity)]
  split_ifs with hk
  · subst hk; simp
  · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    rw [pow_succ]
    push_cast
    nlinarith [mul_pos hν0 (pow_pos hν0 k)]

variable (ν hν)

/-- `(D a)_k = 2k a_k`, `D : X_ν → Y_ν`, `‖D‖ ≤ 1`. -/
noncomputable def diffOp : X ν hν →L[ℝ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := weights ν hν) (fun k => k)
    (fun k => (2 * k : ℝ)) zero_le_one (diff_bound (ν := ν) (hν := hν))).toCLM

/-- `(S₊ c)_k = c_{k+1}` for `k ≥ 1`, `(S₊ c)_0 = 0`, `‖S₊‖ ≤ 1/(2ν)`. -/
noncomputable def shiftUp : X ν hν →L[ℝ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := weights ν hν) (fun k => k - 1)
    (fun k => if 2 ≤ k then (1 : ℝ) else 0)
    (inv_nonneg.2 (mul_nonneg zero_le_two (nu_pos hν).le))
    (shiftUp_bound (ν := ν) (hν := hν))).toCLM

/-- `(S₋ c)_k = c_{k-1}` for `k ≥ 1`, `(S₋ c)_0 = 0`, `‖S₋‖ ≤ ν`. -/
noncomputable def shiftDown : X ν hν →L[ℝ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := weights ν hν) (fun k => k + 1)
    (fun _ => (1 : ℝ)) (nu_pos hν).le (shiftDown_bound (ν := ν) (hν := hν))).toCLM

/-- `(S c)_k = c_{k+1} - c_{k-1}` for `k ≥ 1`, `(S c)_0 = 0`. -/
noncomputable def shiftOp : X ν hν →L[ℝ] Y ν hν := shiftUp ν hν - shiftDown ν hν

/-- The unit sequence `(1, 0, 0, …)` of `Y_ν`. -/
noncomputable def e0 : Y ν hν := WeightedL1.single 0 1

variable {ν hν}

theorem diffOp_apply (a : X ν hν) (k : ℕ) : diffOp ν hν a k = 2 * k * a k := by
  rw [diffOp, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

theorem shiftUp_apply (c : X ν hν) (k : ℕ) :
    shiftUp ν hν c k = if k = 0 then 0 else c (k + 1) := by
  rw [shiftUp, ColNormBound.toCLM_apply, tsum_eq_single (k + 1) fun n hn => by
    by_cases h : k = n - 1
    · have : n = 0 := by omega
      simp [h, this]
    · simp [h]]
  by_cases hk : k = 0
  · simp [hk]
  · have : 2 ≤ k + 1 := by omega
    simp [hk, this]

theorem shiftDown_apply (c : X ν hν) (k : ℕ) :
    shiftDown ν hν c k = if k = 0 then 0 else c (k - 1) := by
  rw [shiftDown, ColNormBound.toCLM_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [tsum_eq_single (k - 1) fun n hn => by
      have : k ≠ n + 1 := by omega
      simp [this]]
    have : k = k - 1 + 1 := by omega
    simp [hk, ← this]

theorem shiftOp_apply (c : X ν hν) (k : ℕ) :
    shiftOp ν hν c k = if k = 0 then 0 else c (k + 1) - c (k - 1) := by
  rw [shiftOp, sub_apply, WeightedLp.sub_apply, shiftUp_apply, shiftDown_apply]
  split_ifs <;> simp

theorem norm_diffOp_le : ‖diffOp ν hν‖ ≤ 1 := ColNormBound.norm_toCLM_le _

theorem norm_shiftUp_le : ‖shiftUp ν hν‖ ≤ (2 * ν)⁻¹ := ColNormBound.norm_toCLM_le _

theorem norm_shiftDown_le : ‖shiftDown ν hν‖ ≤ ν := ColNormBound.norm_toCLM_le _

/-- `‖S‖ ≤ ν + 1/(2ν)`. -/
theorem norm_shiftOp_le : ‖shiftOp ν hν‖ ≤ ν + (2 * ν)⁻¹ := by
  rw [shiftOp, add_comm]
  exact (norm_sub_le _ _).trans (add_le_add norm_shiftUp_le norm_shiftDown_le)

@[simp] theorem e0_apply (k : ℕ) : (e0 ν hν) k = if k = 0 then 1 else 0 := by
  simp [e0, WeightedL1.single_apply]

theorem norm_e0 : ‖e0 ν hν‖ = 1 := by
  rw [e0, WeightedL1.norm_single]; simp [weightsY_apply]

/-! ### The unit, supports, and products with unit sequences -/

theorem one_apply (k : ℕ) : (1 : X ν hν) k = if k = 0 then 1 else 0 := by
  change (1 : WeightedL1 ℝ (Weights.geomInt ν hν)) (k : ℤ) = _
  rw [WeightedL1.one_def, WeightedL1.single_apply]
  simp

instance : NormOneClass (X ν hν) :=
  ⟨by rw [← norm_symExt, symExt_one, WeightedL1.one_def, WeightedL1.norm_single]; simp⟩

/-- `a_k = 0` for all `k > N`. -/
def SuppLe (a : X ν hν) (N : ℕ) : Prop := ∀ k, N < k → a k = 0

theorem SuppLe.mono {a : X ν hν} {N N' : ℕ} (h : SuppLe a N) (hN : N ≤ N') : SuppLe a N' :=
  fun k hk => h k (lt_of_le_of_lt hN hk)

theorem suppLe_zero (N : ℕ) : SuppLe (0 : X ν hν) N := fun _ _ => rfl

theorem suppLe_one : SuppLe (1 : X ν hν) 0 := fun k hk => by
  simp [one_apply, Nat.pos_iff_ne_zero.1 hk]

theorem SuppLe.add {a b : X ν hν} {N : ℕ} (ha : SuppLe a N) (hb : SuppLe b N) :
    SuppLe (a + b) N := fun k hk => by
  rw [WeightedLp.add_apply, ha k hk, hb k hk, add_zero]

theorem SuppLe.smul {a : X ν hν} {N : ℕ} (c : ℝ) (ha : SuppLe a N) : SuppLe (c • a) N :=
  fun k hk => by rw [WeightedLp.smul_apply, ha k hk, mul_zero]

theorem SuppLe.mul {a b : X ν hν} {N₁ N₂ : ℕ} (ha : SuppLe a N₁) (hb : SuppLe b N₂) :
    SuppLe (a * b) (N₁ + N₂) := fun k hk => by
  rw [mul_apply]
  refine (tsum_congr fun j => ?_).trans tsum_zero
  by_cases h1 : N₁ < j.natAbs
  · rw [ha _ h1, zero_mul]
  · have : k ≤ j.natAbs + ((k : ℤ) - j).natAbs := by
      have := Int.natAbs_add_le j ((k : ℤ) - j)
      rwa [add_sub_cancel, Int.natAbs_natCast] at this
    rw [hb _ (by omega), mul_zero]

theorem SuppLe.pow {a : X ν hν} {N : ℕ} (ha : SuppLe a N) (d : ℕ) : SuppLe (a ^ d) (d * N) := by
  induction d with
  | zero => simpa using suppLe_one
  | succ d ih => rw [pow_succ, add_mul, one_mul]; exact ih.mul ha

theorem SuppLe.finset_sum {ι : Type*} {S : Finset ι} {f : ι → X ν hν} {N : ℕ}
    (h : ∀ i ∈ S, SuppLe (f i) N) : SuppLe (∑ i ∈ S, f i) N := fun k hk => by
  rw [WeightedLp.sum_apply]
  exact Finset.sum_eq_zero fun i hi => h i hi k hk

theorem SuppLe.finset_prod {ι : Type*} {S : Finset ι} {f : ι → X ν hν} {N : ι → ℕ}
    (h : ∀ i ∈ S, SuppLe (f i) (N i)) : SuppLe (∏ i ∈ S, f i) (∑ i ∈ S, N i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using suppLe_one
  | insert x S hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self x S)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem suppLe_algebraMap (c : ℝ) : SuppLe (algebraMap ℝ (X ν hν) c) 0 := by
  rw [Algebra.algebraMap_eq_smul_one]; exact suppLe_one.smul c

/-- A polynomial of total degree `≤ M` in sequences supported in `[0, N]` is supported in
`[0, M N]`. -/
theorem suppLe_aeval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (a : Fin n → X ν hν) {N M : ℕ}
    (ha : ∀ i, SuppLe (a i) N) (hP : P.totalDegree ≤ M) :
    SuppLe (MvPolynomial.aeval a P) (M * N) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine SuppLe.finset_sum fun d hd => ?_
  have hdeg : ∑ i, d i ≤ M := by
    have := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    omega
  have := (suppLe_algebraMap (ν := ν) (hν := hν) (P.coeff d)).mul
    (SuppLe.finset_prod (S := Finset.univ) fun i _ => (ha i).pow (d i))
  refine this.mono ?_
  rw [zero_add, ← Finset.sum_mul]
  exact Nat.mul_le_mul_right N hdeg

/-- The product with the unit sequence `e_k`, `k ≥ 1`: `(b * e_k)_p = b_{|p - k|} + b_{p + k}`. -/
theorem mul_single_apply (b : X ν hν) {k : ℕ} (hk : k ≠ 0) (p : ℕ) :
    (b * (WeightedL1.single k 1 : X ν hν)) p = b ((p : ℤ) - k).natAbs + b (p + k) := by
  rw [mul_apply]
  have hne : (p : ℤ) - k ≠ (p : ℤ) + k := by omega
  rw [tsum_eq_sum (s := {(p : ℤ) - k, (p : ℤ) + k}) fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have : ((p : ℤ) - j).natAbs ≠ k := by omega
    simp [WeightedL1.single_apply, this],
    Finset.sum_pair hne]
  have h1 : ((p : ℤ) - ((p : ℤ) - k)).natAbs = k := by omega
  have h2 : ((p : ℤ) - ((p : ℤ) + k)).natAbs = k := by omega
  have h3 : ((p : ℤ) + k).natAbs = p + k := by omega
  simp [h3]

end Chebyshev

end RadiiPolynomial
