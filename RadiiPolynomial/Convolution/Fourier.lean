module

public import RadiiPolynomial.Convolution.Instances
public import RadiiPolynomial.WeightedLp.Operators
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Spaces of Fourier coefficients

Fix `ν ≥ 1`. The space `ℓ¹_ν = ℓ¹_{ν,ℤ}(ℂ)` (`Fourier.X`), with `‖a‖ = ∑_{n ∈ ℤ} |a_n| ν^{|n|}`, is a
commutative Banach algebra under the discrete convolution `(a * b)_n = ∑_{j ∈ ℤ} a_j b_{n-j}`
(`Weights.geomInt`, `Convolution.conv_int`). An element `a ∈ ℓ¹_ν` represents the Fourier series
`∑_n a_n e^{int}`, which converges absolutely and uniformly in `t ∈ ℝ`.

Derivatives of Fourier series lie in `ℓ¹_ω` (`Fourier.Y`), `ω_k = ν^{|k|} / (1 + |k|)`; the derivative
`diffOp : ℓ¹_ν → ℓ¹_ω`, `(D a)_k = i k a_k`, and the inclusion `incl : ℓ¹_ν → ℓ¹_ω` have norm at most
`1`.

* `center N = {-N, …, N}` (`mem_center`: `n ∈ center N ↔ |n| ≤ N`);
* `finPart N h = ∑_{|l| ≤ N} h_l e_l`, the projection onto the modes `|n| ≤ N`;
* supports: `SuppLe a N` (`a_n = 0` for `|n| > N`) is preserved by sums and scalar multiples, and
  `SuppLe a N₁ → SuppLe b N₂ → SuppLe (a * b) (N₁ + N₂)`; hence a polynomial of total degree `≤ M`
  in sequences supported in `{-N, …, N}` is supported in `{-MN, …, MN}` (`suppLe_aeval`);
* `mul_single_apply`: the product with a unit sequence, `(b * e_m)_n = b_{n - m}`;
* `sum_center_mul_le`: if `h_n = 0` for `|n| ≤ N`, then
  `∑_{|n| ≤ N} |(a * h)_n| ν^{-|n|} ≤ ν^{-2N-2} ‖a‖ ‖h‖`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace Fourier

theorem nu_pos {ν : ℝ} (hν : 1 ≤ ν) : 0 < ν := lt_of_lt_of_le zero_lt_one hν

variable (ν : ℝ) (hν : 1 ≤ ν)

/-- `ℓ¹_ν`, the Fourier coefficients with `∑_n |a_n| ν^{|n|} < ∞`, with the discrete
convolution. -/
abbrev X := WeightedL1 ℂ (Weights.geomInt ν hν)

/-- The weights `ω_k = ν^{|k|} / (1 + |k|)`. -/
noncomputable def weightsY : Weights ℤ :=
  ⟨fun k => ν ^ k.natAbs / (1 + k.natAbs), fun k => div_pos (pow_pos (nu_pos hν) _) (by positivity)⟩

/-- `ℓ¹_ω`, `ω_k = ν^{|k|} / (1 + |k|)`. -/
abbrev Y := WeightedL1 ℂ (weightsY ν hν)

variable {ν hν}

theorem weightsY_apply (k : ℤ) : weightsY ν hν k = ν ^ k.natAbs / (1 + k.natAbs) := rfl

theorem diff_bound (k : ℤ) :
    ‖Complex.I * k‖ * weightsY ν hν k ≤ 1 * Weights.geomInt ν hν k := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, weightsY_apply,
    Weights.geomInt_apply, one_mul, mul_div_assoc', div_le_iff₀ (by positivity), Nat.cast_natAbs,
    Int.cast_abs]
  nlinarith [pow_pos (nu_pos hν) k.natAbs, abs_nonneg (k : ℝ)]

theorem incl_bound (k : ℤ) : ‖(1 : ℂ)‖ * weightsY ν hν k ≤ 1 * Weights.geomInt ν hν k := by
  rw [norm_one, one_mul, one_mul, weightsY_apply, Weights.geomInt_apply]
  exact div_le_self (pow_pos (nu_pos hν) _).le (by linarith [(Nat.cast_nonneg k.natAbs : (0 : ℝ) ≤ _)])

variable (ν hν)

/-- `(D a)_k = i k a_k`, `D : ℓ¹_ν → ℓ¹_ω`, `‖D‖ ≤ 1`. -/
noncomputable def diffOp : X ν hν →L[ℂ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := Weights.geomInt ν hν) (fun k => k)
    (fun k => Complex.I * k) zero_le_one diff_bound).toCLM

/-- The inclusion `ℓ¹_ν → ℓ¹_ω`, of norm at most `1`. -/
noncomputable def incl : X ν hν →L[ℂ] Y ν hν :=
  (ColNormBound.single (ω := weightsY ν hν) (ω' := Weights.geomInt ν hν) (fun k => k)
    (fun _ => (1 : ℂ)) zero_le_one incl_bound).toCLM

variable {ν hν}

@[simp] theorem diffOp_apply (a : X ν hν) (k : ℤ) : diffOp ν hν a k = Complex.I * k * a k := by
  rw [diffOp, ColNormBound.toCLM_apply, tsum_eq_single k fun m hm => by simp [Ne.symm hm]]
  simp

@[simp] theorem incl_apply (a : X ν hν) (k : ℤ) : incl ν hν a k = a k := by
  rw [incl, ColNormBound.toCLM_apply, tsum_eq_single k fun m hm => by simp [Ne.symm hm]]
  simp

theorem norm_incl_le : ‖incl ν hν‖ ≤ 1 := ColNormBound.norm_toCLM_le _

/-- The modes `{-N, …, N}`. -/
def center (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem mem_center {N : ℕ} {n : ℤ} : n ∈ center N ↔ n.natAbs ≤ N := by
  rw [center, Finset.mem_Icc]; omega

theorem center_mono {N M : ℕ} (h : N ≤ M) : center N ⊆ center M := fun n hn => by
  rw [mem_center] at hn ⊢; omega

theorem zero_mem_center (N : ℕ) : (0 : ℤ) ∈ center N := by rw [mem_center]; simp

theorem mul_apply (a b : X ν hν) (n : ℤ) : (a * b) n = ∑' j, a j * b (n - j) := by
  rw [WeightedL1.mul_apply, Convolution.conv_int]

theorem one_apply (n : ℤ) : (1 : X ν hν) n = if n = 0 then 1 else 0 := by
  rw [WeightedL1.one_def, WeightedL1.single_apply]

instance : NormOneClass (X ν hν) :=
  ⟨by rw [WeightedL1.one_def, WeightedL1.norm_single]; simp⟩

/-- The product with the unit sequence `e_m`: `(b * e_m)_n = b_{n - m}`. -/
theorem mul_single_apply (b : X ν hν) (m n : ℤ) :
    (b * (WeightedL1.single m 1 : X ν hν)) n = b (n - m) := by
  rw [mul_apply, tsum_eq_single (n - m) fun j hj => by
    rw [WeightedL1.single_apply, ite_eq_right (by omega), mul_zero]]
  simp

/-! ### The finite part -/

variable (N : ℕ)

/-- The projection `∑_{|l| ≤ N} h_l e_l` onto the modes `|n| ≤ N`. -/
noncomputable def finPart (h : X ν hν) : X ν hν := ∑ l ∈ center N, h l • WeightedL1.single l 1

variable {N}

theorem finPart_apply (h : X ν hν) (n : ℤ) :
    finPart N h n = if n ∈ center N then h n else 0 := by
  rw [finPart, WeightedLp.sum_apply]
  simp only [WeightedLp.smul_apply, WeightedL1.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]

theorem sub_finPart_apply (h : X ν hν) (n : ℤ) :
    (h - finPart N h) n = if n ∈ center N then 0 else h n := by
  rw [WeightedLp.sub_apply, finPart_apply]
  split_ifs <;> simp

theorem norm_sub_finPart_le (h : X ν hν) : ‖h - finPart N h‖ ≤ ‖h‖ := by
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum]
  have hle : ∀ n, Weights.geomInt ν hν n * ‖(h - finPart N h) n‖ ≤
      Weights.geomInt ν hν n * ‖h n‖ := fun n => by
    rw [sub_finPart_apply]
    split_ifs
    · rw [norm_zero, mul_zero]
      exact mul_nonneg ((Weights.geomInt ν hν).pos n).le (norm_nonneg _)
    · exact le_rfl
  exact Summable.tsum_le_tsum hle (WeightedL1.summable _) (WeightedL1.summable _)

/-! ### Supports -/

/-- `a_n = 0` for all `|n| > N`. -/
def SuppLe (a : X ν hν) (N : ℕ) : Prop := ∀ n : ℤ, N < n.natAbs → a n = 0

theorem SuppLe.mono {a : X ν hν} {N N' : ℕ} (h : SuppLe a N) (hN : N ≤ N') : SuppLe a N' :=
  fun n hn => h n (lt_of_le_of_lt hN hn)

theorem suppLe_zero (N : ℕ) : SuppLe (0 : X ν hν) N := fun _ _ => rfl

theorem SuppLe.add {a b : X ν hν} {N : ℕ} (ha : SuppLe a N) (hb : SuppLe b N) :
    SuppLe (a + b) N := fun n hn => by
  rw [WeightedLp.add_apply, ha n hn, hb n hn, add_zero]

theorem SuppLe.sub {a b : X ν hν} {N : ℕ} (ha : SuppLe a N) (hb : SuppLe b N) :
    SuppLe (a - b) N := fun n hn => by
  rw [WeightedLp.sub_apply, ha n hn, hb n hn, sub_zero]

theorem SuppLe.smul {a : X ν hν} {N : ℕ} (c : ℂ) (ha : SuppLe a N) : SuppLe (c • a) N :=
  fun n hn => by rw [WeightedLp.smul_apply, ha n hn, mul_zero]

theorem SuppLe.mul {a b : X ν hν} {N₁ N₂ : ℕ} (ha : SuppLe a N₁) (hb : SuppLe b N₂) :
    SuppLe (a * b) (N₁ + N₂) := fun n hn => by
  rw [mul_apply]
  have h0 : ∀ j, a j * b (n - j) = 0 := fun j => by
    by_cases h1 : N₁ < j.natAbs
    · rw [ha j h1, zero_mul]
    · rw [hb (n - j) (by omega), mul_zero]
  simp [h0]

theorem suppLe_one : SuppLe (1 : X ν hν) 0 := fun n hn => by
  rw [one_apply, ite_eq_right (by omega)]

theorem SuppLe.pow {a : X ν hν} {N : ℕ} (ha : SuppLe a N) (d : ℕ) : SuppLe (a ^ d) (d * N) := by
  induction d with
  | zero => simpa using suppLe_one
  | succ d ih => rw [pow_succ, add_mul, one_mul]; exact ih.mul ha

theorem SuppLe.finset_sum {ι : Type*} {S : Finset ι} {f : ι → X ν hν} {N : ℕ}
    (h : ∀ i ∈ S, SuppLe (f i) N) : SuppLe (∑ i ∈ S, f i) N := fun n hn => by
  rw [WeightedLp.sum_apply]
  exact Finset.sum_eq_zero fun i hi => h i hi n hn

theorem SuppLe.finset_prod {ι : Type*} {S : Finset ι} {f : ι → X ν hν} {N : ι → ℕ}
    (h : ∀ i ∈ S, SuppLe (f i) (N i)) : SuppLe (∏ i ∈ S, f i) (∑ i ∈ S, N i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using suppLe_one
  | insert x S hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self x S)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem suppLe_algebraMap (c : ℂ) : SuppLe (algebraMap ℂ (X ν hν) c) 0 := by
  rw [Algebra.algebraMap_eq_smul_one]; exact suppLe_one.smul c

/-- A polynomial of total degree `≤ M` in sequences supported in `{-N, …, N}` is supported in
`{-MN, …, MN}`. -/
theorem suppLe_aeval {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (a : Fin n → X ν hν) {N M : ℕ}
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

/-! ### Products with sequences vanishing on the center -/

/-- If `h_n = 0` for `|n| ≤ N`, then `∑_{|n| ≤ N} |(a * h)_n| ν^{-|n|} ≤ ν^{-2N-2} ‖a‖ ‖h‖`. -/
theorem sum_center_mul_le (a h : X ν hν) {N : ℕ} (hh : ∀ n ∈ center N, h n = 0) :
    ∑ n ∈ center N, ‖(a * h) n‖ / ν ^ n.natAbs ≤ ‖a‖ * ‖h‖ / ν ^ (2 * N + 2) := by
  have hν0 := nu_pos hν
  set wa : ℤ → ℝ := fun i => ν ^ i.natAbs * ‖a i‖ with hwa
  set wh : ℤ → ℝ := fun j => ν ^ j.natAbs * ‖h j‖ with hwh
  have hwa0 : ∀ i, 0 ≤ wa i := fun i => by positivity
  have hwh0 : ∀ j, 0 ≤ wh j := fun j => by positivity
  have hsa : Summable wa := by simpa only [Weights.geomInt_apply] using a.summable
  have hsh : Summable wh := by simpa only [Weights.geomInt_apply] using h.summable
  have hwa_le : ∀ i, wa i ≤ ‖a‖ := fun i => by
    simpa only [Weights.geomInt_apply] using WeightedLp.norm_apply_le a i
  have hna : ‖a‖ = ∑' i, wa i := by
    rw [WeightedL1.norm_eq_tsum]; simp only [Weights.geomInt_apply, hwa]
  have hnh : ‖h‖ = ∑' j, wh j := by
    rw [WeightedL1.norm_eq_tsum]; simp only [Weights.geomInt_apply, hwh]
  set P : ℤ → ℤ → ℝ := fun n j => wa (n - j) * wh j with hP
  have hsP : ∀ n, Summable (P n) := fun n =>
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hwa0 _) (hwh0 j))
      (fun j => mul_le_mul_of_nonneg_right (hwa_le _) (hwh0 j)) (hsh.mul_left ‖a‖)
  have hνN : 0 < ν ^ (2 * N + 2) := pow_pos hν0 _
  -- each coefficient of the product
  have hterm : ∀ n ∈ center N, ‖(a * h) n‖ / ν ^ n.natAbs ≤ (∑' j, P n j) / ν ^ (2 * N + 2) := by
    intro n hn
    have hνn : 0 < ν ^ n.natAbs := pow_pos hν0 _
    -- `|h_j| |a_{n-j}| ν^{2N+2} ≤ ν^{|n|} P n j`
    have hpt : ∀ j, ‖h j * a (n - j)‖ ≤ ν ^ n.natAbs / ν ^ (2 * N + 2) * P n j := fun j => by
      rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hνN]
      by_cases hj : j ∈ center N
      · rw [hh j hj, norm_zero, zero_mul, zero_mul]
        exact mul_nonneg hνn.le (mul_nonneg (hwa0 _) (hwh0 j))
      · rw [mem_center, not_le] at hj
        have hexp : 2 * N + 2 ≤ n.natAbs + ((n - j).natAbs + j.natAbs) := by omega
        have hpow : ν ^ (2 * N + 2) ≤ ν ^ n.natAbs * (ν ^ (n - j).natAbs * ν ^ j.natAbs) := by
          rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hν hexp
        simp only [hP, hwa, hwh]
        calc ‖h j‖ * ‖a (n - j)‖ * ν ^ (2 * N + 2)
            ≤ ‖h j‖ * ‖a (n - j)‖ * (ν ^ n.natAbs * (ν ^ (n - j).natAbs * ν ^ j.natAbs)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = ν ^ n.natAbs * (ν ^ (n - j).natAbs * ‖a (n - j)‖ * (ν ^ j.natAbs * ‖h j‖)) := by
              ring
    have hsn : Summable fun j => ‖h j * a (n - j)‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) hpt ((hsP n).mul_left _)
    rw [mul_comm a h, mul_apply, div_le_div_iff₀ hνn hνN]
    calc ‖∑' j, h j * a (n - j)‖ * ν ^ (2 * N + 2)
        ≤ (∑' j, ν ^ n.natAbs / ν ^ (2 * N + 2) * P n j) * ν ^ (2 * N + 2) :=
          mul_le_mul_of_nonneg_right ((norm_tsum_le_tsum_norm hsn).trans
            (Summable.tsum_le_tsum hpt hsn ((hsP n).mul_left _))) hνN.le
      _ = (∑' j, P n j) * ν ^ n.natAbs := by
          rw [tsum_mul_left]; field_simp
  -- exchange the finite sum and the series
  have hcol : ∀ j, ∑ n ∈ center N, P n j ≤ ‖a‖ * wh j := fun j => by
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hwh0 j)
    have hinj : Set.InjOn (fun n : ℤ => n - j) (center N : Set ℤ) := fun x _ y _ hxy => by
      simpa using hxy
    rw [← Finset.sum_image (f := wa) hinj, hna]
    exact hsa.sum_le_tsum _ fun i _ => hwa0 i
  calc ∑ n ∈ center N, ‖(a * h) n‖ / ν ^ n.natAbs
      ≤ ∑ n ∈ center N, (∑' j, P n j) / ν ^ (2 * N + 2) := Finset.sum_le_sum hterm
    _ = (∑' j, ∑ n ∈ center N, P n j) / ν ^ (2 * N + 2) := by
        rw [← Finset.sum_div, Summable.tsum_finsetSum fun n _ => hsP n]
    _ ≤ (∑' j, ‖a‖ * wh j) / ν ^ (2 * N + 2) := by
        exact div_le_div_of_nonneg_right
          (Summable.tsum_le_tsum hcol (summable_sum fun n _ => hsP n) (hsh.mul_left _)) hνN.le
    _ = ‖a‖ * ‖h‖ / ν ^ (2 * N + 2) := by rw [tsum_mul_left, ← hnh]

end Fourier

end RadiiPolynomial
