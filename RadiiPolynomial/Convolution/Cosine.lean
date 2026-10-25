module

public import RadiiPolynomial.Convolution.Chebyshev
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Cosine series: one-sided sequences with the symmetric product

Fix `ν ≥ 1`. The space `ℓ¹_ν` of one-sided sequences (`Cosine.X`), with `‖a‖ = ∑_{k ≥ 0} |a_k| ν^k`,
carries the symmetric (extended) convolution
`(a * b)_k = ∑_{k₁ + k₂ = k, kᵢ ∈ ℤ} a_{|k₁|} b_{|k₂|}`: the coefficients of the product of the
cosine series `a_0 + 2 ∑ a_k cos(k L y)`. For this norm the product only satisfies
`‖a * b‖ ≤ 4 ‖a‖ ‖b‖`, so `ℓ¹_ν` is not a normed algebra; the product is computed in the Chebyshev
algebra `X_ν` (`Chebyshev.X`, the same product with the equivalent norm
`|a_0| + 2 ∑_{k ≥ 1} |a_k| ν^k`), through the coefficientwise identities
`toCheb : ℓ¹_ν → X_ν` (`‖toCheb‖ ≤ 2`) and `ofCheb : X_ν → ℓ¹_ν` (`‖ofCheb‖ ≤ 1`).

* `mul2 a b`, `mul3 a b c`, `cube a = mul3 a a a`, with `‖mul2 a b‖ ≤ 4 ‖a‖ ‖b‖` and
  `‖mul3 a b c‖ ≤ 8 ‖a‖ ‖b‖ ‖c‖` (`norm_mul2_le`, `norm_mul3_le`);
* for finitely supported sequences: the product as a finite sum (`mul2_apply_of_supp`),
  `|(a * a)_i| ≤ (|a| * |a|)_i` (`abs_mul2_le`, `absX`), supports (`mul2_eq_zero`), and the product
  with a unit sequence (`mul3_single_apply`);
* `cube` is Fréchet differentiable with derivative `h ↦ 3 mul3 a a h` (`hasFDerivAt_cube`);
* for `ν' ≤ ν` the inclusion `ℓ¹_ν ⊂ ℓ¹_ν'` (`embed`, same coefficients) does not increase norms and
  commutes with the product (`norm_embed_le`, `cube_embed`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace Cosine

/-- The weights `ν^k`, `ν ≥ 1` (a separate definition from `Weights.geom`, whose `ℓ¹` space carries
the Cauchy product). -/
def weights (ν : ℝ) (hν : 1 ≤ ν) : Weights ℕ :=
  ⟨fun k => ν ^ k, fun k => pow_pos (Chebyshev.nu_pos hν) k⟩

variable (ν : ℝ) (hν : 1 ≤ ν)

theorem weights_apply (k : ℕ) : weights ν hν k = ν ^ k := rfl

/-- `ℓ¹_ν`, the one-sided sequences with `∑_k |a_k| ν^k < ∞`. -/
abbrev X := WeightedL1 ℝ (weights ν hν)

variable {ν hν}

theorem toCheb_bound (k : ℕ) :
    ‖(1 : ℝ)‖ * Chebyshev.weights ν hν k ≤ 2 * weights ν hν k := by
  rw [norm_one, one_mul, Chebyshev.weights_apply, weights_apply]
  split_ifs with hk
  · subst hk; norm_num
  · exact le_rfl

theorem ofCheb_bound (k : ℕ) : ‖(1 : ℝ)‖ * weights ν hν k ≤ 1 * Chebyshev.weights ν hν k := by
  rw [norm_one, one_mul, one_mul, Chebyshev.weights_apply, weights_apply]
  split_ifs with hk
  · subst hk; simp
  · nlinarith [pow_pos (Chebyshev.nu_pos hν) k]

variable (ν hν)

/-- The identity on coefficients `ℓ¹_ν → X_ν`, of norm at most `2`. -/
noncomputable def toCheb : X ν hν →L[ℝ] Chebyshev.X ν hν :=
  (ColNormBound.single (ω := Chebyshev.weights ν hν) (ω' := weights ν hν) (fun k => k)
    (fun _ => (1 : ℝ)) zero_le_two (toCheb_bound (ν := ν) (hν := hν))).toCLM

/-- The identity on coefficients `X_ν → ℓ¹_ν`, of norm at most `1`. -/
noncomputable def ofCheb : Chebyshev.X ν hν →L[ℝ] X ν hν :=
  (ColNormBound.single (ω := weights ν hν) (ω' := Chebyshev.weights ν hν) (fun k => k)
    (fun _ => (1 : ℝ)) zero_le_one (ofCheb_bound (ν := ν) (hν := hν))).toCLM

variable {ν hν}

@[simp] theorem toCheb_apply (a : X ν hν) (k : ℕ) : toCheb ν hν a k = a k := by
  rw [toCheb, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

@[simp] theorem ofCheb_apply (c : Chebyshev.X ν hν) (k : ℕ) : ofCheb ν hν c k = c k := by
  rw [ofCheb, ColNormBound.toCLM_apply, tsum_eq_single k fun n hn => by simp [Ne.symm hn]]
  simp

theorem norm_toCheb_le : ‖toCheb ν hν‖ ≤ 2 := ColNormBound.norm_toCLM_le _

theorem norm_ofCheb_le : ‖ofCheb ν hν‖ ≤ 1 := ColNormBound.norm_toCLM_le _

theorem norm_toCheb_apply_le (a : X ν hν) : ‖toCheb ν hν a‖ ≤ 2 * ‖a‖ :=
  ((toCheb ν hν).le_opNorm a).trans (mul_le_mul_of_nonneg_right norm_toCheb_le (norm_nonneg _))

theorem norm_ofCheb_apply_le (c : Chebyshev.X ν hν) : ‖ofCheb ν hν c‖ ≤ ‖c‖ :=
  ((ofCheb ν hν).le_opNorm c).trans (by
    simpa using mul_le_mul_of_nonneg_right norm_ofCheb_le (norm_nonneg c))

@[simp] theorem ofCheb_toCheb (a : X ν hν) : ofCheb ν hν (toCheb ν hν a) = a := by
  ext k; simp

@[simp] theorem toCheb_ofCheb (c : Chebyshev.X ν hν) : toCheb ν hν (ofCheb ν hν c) = c := by
  ext k; simp

/-! ### The symmetric product -/

variable (ν hν)

/-- The symmetric product `a * b * c` of three sequences. -/
noncomputable def mul3 (a b c : X ν hν) : X ν hν :=
  ofCheb ν hν (toCheb ν hν a * toCheb ν hν b * toCheb ν hν c)

/-- The cube `a³ = a * a * a`. -/
noncomputable def cube (a : X ν hν) : X ν hν := mul3 ν hν a a a

/-- The derivative of the cube at `a`: `h ↦ 3 a * a * h`. -/
noncomputable def cubeDeriv (a : X ν hν) : X ν hν →L[ℝ] X ν hν :=
  (ofCheb ν hν).comp (((3 : ℕ) • toCheb ν hν a ^ (3 - 1)) • toCheb ν hν)

variable {ν hν}

theorem cubeDeriv_apply (a h : X ν hν) : cubeDeriv ν hν a h = (3 : ℝ) • mul3 ν hν a a h := by
  rw [← ofCheb_toCheb ((3 : ℝ) • mul3 ν hν a a h), cubeDeriv, ContinuousLinearMap.comp_apply]
  congr 1
  simp only [smul_apply, mul3, map_smul, toCheb_ofCheb, smul_eq_mul,
    Algebra.smul_def, map_ofNat]
  ring

theorem norm_mul3_le (a b c : X ν hν) : ‖mul3 ν hν a b c‖ ≤ 8 * ‖a‖ * ‖b‖ * ‖c‖ := by
  refine (norm_ofCheb_apply_le _).trans ?_
  refine (norm_mul_le _ _).trans ?_
  have hab := (norm_mul_le (toCheb ν hν a) (toCheb ν hν b)).trans
    (mul_le_mul (norm_toCheb_apply_le a) (norm_toCheb_apply_le b) (norm_nonneg _)
      (by positivity))
  calc ‖toCheb ν hν a * toCheb ν hν b‖ * ‖toCheb ν hν c‖
      ≤ (2 * ‖a‖ * (2 * ‖b‖)) * (2 * ‖c‖) :=
        mul_le_mul hab (norm_toCheb_apply_le c) (norm_nonneg _) (by positivity)
    _ = 8 * ‖a‖ * ‖b‖ * ‖c‖ := by ring

/-- `‖c * c * h - a * a * h‖ ≤ 8 ‖c - a‖ ‖c + a‖ ‖h‖`. -/
theorem norm_mul3_sub_le (c a h : X ν hν) :
    ‖mul3 ν hν c c h - mul3 ν hν a a h‖ ≤ 8 * ‖c - a‖ * ‖c + a‖ * ‖h‖ := by
  have heq : mul3 ν hν c c h - mul3 ν hν a a h =
      ofCheb ν hν (toCheb ν hν (c - a) * toCheb ν hν (c + a) * toCheb ν hν h) := by
    have hsub : ∀ x y : Chebyshev.X ν hν, ofCheb ν hν x - ofCheb ν hν y = ofCheb ν hν (x - y) :=
      fun x y => (map_sub _ x y).symm
    rw [mul3, mul3, hsub, map_sub (toCheb ν hν) c a, map_add (toCheb ν hν) c a]
    congr 1
    ring
  rw [heq]
  refine (norm_ofCheb_apply_le _).trans ((norm_mul_le _ _).trans ?_)
  have h1 := (norm_mul_le (toCheb ν hν (c - a)) (toCheb ν hν (c + a))).trans
    (mul_le_mul (norm_toCheb_apply_le (c - a)) (norm_toCheb_apply_le (c + a)) (norm_nonneg _)
      (by positivity))
  calc ‖toCheb ν hν (c - a) * toCheb ν hν (c + a)‖ * ‖toCheb ν hν h‖
      ≤ (2 * ‖c - a‖ * (2 * ‖c + a‖)) * (2 * ‖h‖) :=
        mul_le_mul h1 (norm_toCheb_apply_le h) (norm_nonneg _) (by positivity)
    _ = 8 * ‖c - a‖ * ‖c + a‖ * ‖h‖ := by ring

theorem cube_eq (a : X ν hν) : cube ν hν a = ofCheb ν hν (toCheb ν hν a ^ 3) := by
  rw [cube, mul3, pow_three, mul_assoc]

/-- The cube is Fréchet differentiable, with derivative `h ↦ 3 a * a * h`. -/
theorem hasFDerivAt_cube (a : X ν hν) : HasFDerivAt (cube ν hν) (cubeDeriv ν hν a) a := by
  have h := ((toCheb ν hν).hasFDerivAt.pow 3 (x := a))
  have h2 := (ofCheb ν hν).hasFDerivAt.comp a h
  have hfun : cube ν hν = fun x => ofCheb ν hν (toCheb ν hν x ^ 3) := funext cube_eq
  rw [hfun]
  exact h2

theorem mul3_comm_left (a b c : X ν hν) : mul3 ν hν a b c = mul3 ν hν b a c := by
  rw [mul3, mul3, mul_comm (toCheb ν hν a)]

/-- `(a + b)³ - a³ - 3 a² b = 3 a b² + b³`. -/
theorem cube_add (a b : X ν hν) :
    cube ν hν (a + b) = cube ν hν a + (3 : ℝ) • mul3 ν hν a a b + (3 : ℝ) • mul3 ν hν a b b +
      cube ν hν b := by
  set A := toCheb ν hν a
  set B := toCheb ν hν b
  have hsum : toCheb ν hν (a + b) * toCheb ν hν (a + b) * toCheb ν hν (a + b) =
      A * A * A + 3 * (A * A * B) + 3 * (A * B * B) + B * B * B := by
    rw [map_add]; ring
  have h3 : ∀ x : Chebyshev.X ν hν, ofCheb ν hν (3 * x) = (3 : ℝ) • ofCheb ν hν x := fun x => by
    rw [← map_smul, Algebra.smul_def, map_ofNat]
  rw [cube, mul3, hsum, map_add, map_add, map_add, h3, h3]
  rfl

/-! ### Products of finitely supported sequences -/

variable (ν hν)

/-- The symmetric product `a * b`. -/
noncomputable def mul2 (a b : X ν hν) : X ν hν := ofCheb ν hν (toCheb ν hν a * toCheb ν hν b)

/-- The sequence `|a| = (|a_k|)_k`. -/
noncomputable def absX (a : X ν hν) : X ν hν :=
  WeightedL1.ofSummable (fun k => |a k|) (by simpa [Real.norm_eq_abs] using a.summable)

variable {ν hν}

@[simp] theorem absX_apply (a : X ν hν) (k : ℕ) : absX ν hν a k = |a k| := rfl

theorem norm_absX (a : X ν hν) : ‖absX ν hν a‖ = ‖a‖ := by
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum]
  simp [Real.norm_eq_abs]

theorem mul3_eq_mul2 (a b c : X ν hν) : mul3 ν hν a b c = mul2 ν hν (mul2 ν hν a b) c := by
  rw [mul3, mul2, mul2, toCheb_ofCheb]

theorem norm_mul2_le (a b : X ν hν) : ‖mul2 ν hν a b‖ ≤ 4 * ‖a‖ * ‖b‖ := by
  refine (norm_ofCheb_apply_le _).trans ((norm_mul_le _ _).trans ?_)
  calc ‖toCheb ν hν a‖ * ‖toCheb ν hν b‖ ≤ (2 * ‖a‖) * (2 * ‖b‖) :=
        mul_le_mul (norm_toCheb_apply_le a) (norm_toCheb_apply_le b) (norm_nonneg _)
          (by positivity)
    _ = 4 * ‖a‖ * ‖b‖ := by ring

/-- If `a_k = 0` for `k ≥ m`, the product is a finite sum:
`(a * b)_i = ∑_{|j| < m} a_{|j|} b_{|i - j|}`. -/
theorem mul2_apply_of_supp {m : ℕ} (a b : X ν hν) (ha : ∀ k, m ≤ k → a k = 0) (i : ℕ) :
    mul2 ν hν a b i = ∑ j ∈ Finset.Icc (1 - (m : ℤ)) (m - 1), a j.natAbs * b ((i : ℤ) - j).natAbs := by
  rw [mul2, ofCheb_apply, Chebyshev.mul_apply]
  rw [tsum_eq_sum (s := Finset.Icc (1 - (m : ℤ)) (m - 1)) fun j hj => by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    simp [ha j.natAbs (by omega)]]
  simp

/-- `|(a * a)_i| ≤ (|a| * |a|)_i` for finitely supported `a`. -/
theorem abs_mul2_le {m : ℕ} (a : X ν hν) (ha : ∀ k, m ≤ k → a k = 0) (i : ℕ) :
    |mul2 ν hν a a i| ≤ mul2 ν hν (absX ν hν a) (absX ν hν a) i := by
  have ha' : ∀ k, m ≤ k → absX ν hν a k = 0 := fun k hk => by simp [ha k hk]
  rw [mul2_apply_of_supp a a ha, mul2_apply_of_supp _ _ ha']
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => by rw [abs_mul]; rfl

theorem mul2_nonneg {a b : X ν hν} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (i : ℕ) :
    0 ≤ mul2 ν hν a b i := by
  rw [mul2, ofCheb_apply, Chebyshev.mul_apply]
  exact tsum_nonneg fun j => mul_nonneg (by simpa using ha _) (by simpa using hb _)

/-- If `a_k = 0` for `k ≥ m` and `b_k = 0` for `k ≥ m'`, then `(a * b)_i = 0` for
`i ≥ m + m' - 1`. -/
theorem mul2_eq_zero {m m' : ℕ} (a b : X ν hν) (ha : ∀ k, m ≤ k → a k = 0)
    (hb : ∀ k, m' ≤ k → b k = 0) {i : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (hi : m + m' - 1 ≤ i) :
    mul2 ν hν a b i = 0 := by
  have h1 : Chebyshev.SuppLe (toCheb ν hν a) (m - 1) := fun k hk => by
    rw [toCheb_apply, ha k (by omega)]
  have h2 : Chebyshev.SuppLe (toCheb ν hν b) (m' - 1) := fun k hk => by
    rw [toCheb_apply, hb k (by omega)]
  rw [mul2, ofCheb_apply, h1.mul h2 i (by omega)]

theorem toCheb_single (l : ℕ) :
    toCheb ν hν (WeightedL1.single l 1) = (WeightedL1.single l 1 : Chebyshev.X ν hν) := by
  ext k; simp [WeightedL1.single_apply]

/-- The product with the unit sequence `e_l`, `l ≥ 1`:
`(a * b * e_l)_p = (a * b)_{|p - l|} + (a * b)_{p + l}`. -/
theorem mul3_single_apply (a b : X ν hν) {l : ℕ} (hl : l ≠ 0) (p : ℕ) :
    mul3 ν hν a b (WeightedL1.single l 1) p =
      mul2 ν hν a b ((p : ℤ) - l).natAbs + mul2 ν hν a b (p + l) := by
  rw [mul3, ofCheb_apply, toCheb_single, Chebyshev.mul_single_apply _ hl]
  simp [mul2]

/-! ### Changing the weight -/

section Embed

variable {ν' : ℝ} {hν' : 1 ≤ ν'}

theorem summable_embed (hle : ν' ≤ ν) (a : X ν hν) :
    Summable fun k => weights ν' hν' k * ‖a k‖ :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by rw [weights_apply]; exact pow_nonneg (by linarith) k) (norm_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right
      (by rw [weights_apply, weights_apply]; exact pow_le_pow_left₀ (by linarith) hle k)
      (norm_nonneg _))
    a.summable

variable (hν') in
/-- For `ν' ≤ ν`, the inclusion `ℓ¹_ν ⊂ ℓ¹_ν'` (same coefficients). -/
noncomputable def embed (hle : ν' ≤ ν) (a : X ν hν) : X ν' hν' :=
  WeightedL1.ofSummable (fun k => a k) (summable_embed hle a)

@[simp] theorem embed_apply (hle : ν' ≤ ν) (a : X ν hν) (k : ℕ) : embed hν' hle a k = a k :=
  WeightedL1.ofSummable_apply _ _ k

theorem norm_embed_le (hle : ν' ≤ ν) (a : X ν hν) : ‖embed hν' hle a‖ ≤ ‖a‖ := by
  rw [embed, WeightedL1.norm_ofSummable, WeightedL1.norm_eq_tsum a]
  exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right
      (by rw [weights_apply, weights_apply]; exact pow_le_pow_left₀ (by linarith) hle k)
      (norm_nonneg _))
    (summable_embed hle a) a.summable

theorem embed_sub (hle : ν' ≤ ν) (a b : X ν hν) :
    embed hν' hle (a - b) = embed hν' hle a - embed hν' hle b := by
  ext k
  rw [WeightedLp.sub_apply, embed_apply, embed_apply, embed_apply, WeightedLp.sub_apply]

theorem cube_embed (hle : ν' ≤ ν) (a : X ν hν) :
    cube ν' hν' (embed hν' hle a) = embed hν' hle (cube ν hν a) := by
  ext k
  simp only [cube_eq, ofCheb_apply, embed_apply, pow_three', Chebyshev.mul_apply, toCheb_apply]

end Embed

end Cosine

end RadiiPolynomial
