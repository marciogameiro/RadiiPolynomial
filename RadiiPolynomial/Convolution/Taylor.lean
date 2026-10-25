module

public import RadiiPolynomial.Convolution.Instances
public import RadiiPolynomial.WeightedLp.Operators
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Spaces of Taylor coefficients

Fix `ν > 0`. The space `ℓ¹_ν = ℓ¹_{ν,ℕ}(ℝ)` (`Taylor.X`), with `‖a‖ = ∑_k |a_k| ν^k`, is a
commutative Banach algebra under the Cauchy product `(a * b)_k = ∑_{i + j = k} a_i b_j`
(`Weights.geom`, `Convolution.conv_nat`). An element `a ∈ ℓ¹_ν` represents the power series
`∑_k a_k t^k`, which converges absolutely for `|t| ≤ ν`.

Derivatives of power series do not lie in `ℓ¹_ν` in general; they lie in `ℓ¹_ω` (`Taylor.Y`) with
the weights `ω_k = ν^{k+1} / (k+1)`. The operators

* `diffOp : ℓ¹_ν → ℓ¹_ω`, `(D a)_0 = a_0`, `(D a)_k = k a_k` (`k ≥ 1`), `‖D‖ ≤ ν`;
* `shift : ℓ¹_ν → ℓ¹_ν`, `(S a)_0 = 0`, `(S a)_k = a_{k-1}` (`k ≥ 1`), `‖S‖ ≤ ν`;
* `incl : ℓ¹_ν → ℓ¹_ω`, the inclusion, `‖incl‖ ≤ ν`,

each have one entry per column. `e0` is the unit sequence `(1, 0, 0, …)` of `ℓ¹_ω`.

Supports: `SuppLe a N` (`a_k = 0` for `k > N`) is preserved by sums and scalar multiples and
`SuppLe a N₁ → SuppLe b N₂ → SuppLe (a * b) (N₁ + N₂)`; hence a polynomial of total degree `≤ M` in
sequences supported in `[0, N]` is supported in `[0, M N]` (`suppLe_aeval`). With the unit sequence
`e_m`, `(b * e_m)_p = b_{p - m}` for `m ≤ p` and `0` otherwise (`mul_single_apply`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace Taylor

variable (ν : ℝ) (hν : 0 < ν)

/-- The weights `ω_k = ν^{k+1} / (k+1)`. -/
noncomputable def weightsY (ν : ℝ) (hν : 0 < ν) : Weights ℕ :=
  ⟨fun k => ν ^ (k + 1) / (k + 1), fun k => by positivity⟩

theorem weightsY_apply (k : ℕ) : weightsY ν hν k = ν ^ (k + 1) / (k + 1) := rfl

/-- `ℓ¹_ν`, the Taylor coefficients with `∑_k |a_k| ν^k < ∞`, with the Cauchy product. -/
abbrev X := WeightedL1 ℝ (Weights.geom ν hν)

/-- `ℓ¹_ω`, `ω_k = ν^{k+1} / (k+1)`. -/
abbrev Y := WeightedL1 ℝ (weightsY ν hν)

variable {ν hν}

/-! ### The operators `D`, `S` and the inclusion -/

theorem diff_bound (k : ℕ) :
    ‖(if k = 0 then (1 : ℝ) else k)‖ * weightsY ν hν k ≤ ν * Weights.geom ν hν k := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  rw [weightsY_apply, Weights.geom_apply, pow_succ, mul_div_assoc', div_le_iff₀ hk1]
  split_ifs with hk
  · subst hk; simp
  · rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
    nlinarith [mul_pos (pow_pos hν k) hν]

theorem shift_bound (k : ℕ) :
    ‖(1 : ℝ)‖ * Weights.geom ν hν (k + 1) ≤ ν * Weights.geom ν hν k := by
  rw [norm_one, one_mul, Weights.geom_apply, Weights.geom_apply, pow_succ, mul_comm]

theorem incl_bound (k : ℕ) : ‖(1 : ℝ)‖ * weightsY ν hν k ≤ ν * Weights.geom ν hν k := by
  have hk1 : (1 : ℝ) ≤ k + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  rw [norm_one, one_mul, weightsY_apply, Weights.geom_apply, pow_succ, mul_comm (ν ^ k)]
  exact div_le_self (by positivity) hk1

variable (ν hν)

/-- `(D a)_0 = a_0`, `(D a)_k = k a_k` (`k ≥ 1`), `D : ℓ¹_ν → ℓ¹_ω`, `‖D‖ ≤ ν`. -/
noncomputable def diffOp : X ν hν →L[ℝ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := Weights.geom ν hν) (fun k => k)
    (fun k => if k = 0 then (1 : ℝ) else k) hν.le (diff_bound (ν := ν) (hν := hν))).toCLM

/-- `(S a)_0 = 0`, `(S a)_k = a_{k-1}` (`k ≥ 1`), `S : ℓ¹_ν → ℓ¹_ν`, `‖S‖ ≤ ν`. -/
noncomputable def shift : X ν hν →L[ℝ] X ν hν :=
  (ColNormBound.single (ω := Weights.geom ν hν) (ω' := Weights.geom ν hν) (fun k => k + 1)
    (fun _ => (1 : ℝ)) hν.le (shift_bound (ν := ν) (hν := hν))).toCLM

/-- The inclusion `ℓ¹_ν → ℓ¹_ω`, of norm at most `ν`. -/
noncomputable def incl : X ν hν →L[ℝ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := Weights.geom ν hν) (fun k => k)
    (fun _ => (1 : ℝ)) hν.le (incl_bound (ν := ν) (hν := hν))).toCLM

/-- The unit sequence `(1, 0, 0, …)` of `ℓ¹_ω`. -/
noncomputable def e0 : Y ν hν := WeightedL1.single 0 1

variable {ν hν}

theorem diffOp_apply (a : X ν hν) (k : ℕ) :
    diffOp ν hν a k = (if k = 0 then 1 else k) * a k := by
  rw [diffOp, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

theorem shift_apply (a : X ν hν) (k : ℕ) :
    shift ν hν a k = if k = 0 then 0 else a (k - 1) := by
  rw [shift, ColNormBound.toCLM_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [tsum_eq_single (k - 1) fun n hn => by
      have : k ≠ n + 1 := by omega
      simp [this]]
    have : k = k - 1 + 1 := by omega
    simp [hk, ← this]

@[simp] theorem incl_apply (a : X ν hν) (k : ℕ) : incl ν hν a k = a k := by
  rw [incl, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

theorem norm_diffOp_le : ‖diffOp ν hν‖ ≤ ν := ColNormBound.norm_toCLM_le _

theorem norm_shift_le : ‖shift ν hν‖ ≤ ν := ColNormBound.norm_toCLM_le _

theorem norm_incl_le : ‖incl ν hν‖ ≤ ν := ColNormBound.norm_toCLM_le _

@[simp] theorem e0_apply (k : ℕ) : (e0 ν hν) k = if k = 0 then 1 else 0 := by
  simp [e0, WeightedL1.single_apply]

/-! ### The unit, supports, and products with unit sequences -/

theorem mul_apply (a b : X ν hν) (k : ℕ) :
    (a * b) k = ∑ p ∈ Finset.antidiagonal k, a p.1 * b p.2 := by
  rw [WeightedL1.mul_apply, Convolution.conv_nat]

theorem one_apply (k : ℕ) : (1 : X ν hν) k = if k = 0 then 1 else 0 := by
  rw [WeightedL1.one_def, WeightedL1.single_apply]

instance : NormOneClass (X ν hν) :=
  ⟨by rw [WeightedL1.one_def, WeightedL1.norm_single]; simp⟩

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
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  by_cases h1 : N₁ < p.1
  · rw [ha _ h1, zero_mul]
  · rw [hb _ (by omega), mul_zero]

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

/-- The product with the unit sequence `e_m`: `(b * e_m)_p = b_{p - m}` if `m ≤ p`, else `0`. -/
theorem mul_single_apply (b : X ν hν) (m p : ℕ) :
    (b * (WeightedL1.single m 1 : X ν hν)) p = if m ≤ p then b (p - m) else 0 := by
  rw [mul_apply]
  split_ifs with hm
  · rw [Finset.sum_eq_single (p - m, m)]
    · simp
    · intro q hq hne
      rw [Finset.mem_antidiagonal] at hq
      have : q.2 ≠ m := fun h => hne (Prod.ext (by omega) h)
      simp [WeightedL1.single_apply, this]
    · intro h
      exact absurd (Finset.mem_antidiagonal.2 (by omega)) h
  · refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_antidiagonal] at hq
    have : q.2 ≠ m := by omega
    simp [WeightedL1.single_apply, this]

end Taylor

end RadiiPolynomial
