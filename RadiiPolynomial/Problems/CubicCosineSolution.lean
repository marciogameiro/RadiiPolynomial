module

public import RadiiPolynomial.Problems.CubicCosine
public import RadiiPolynomial.Convolution.FourierSeries
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# Equilibria from zeros of cubic cosine problems

For `a ∈ ℓ¹_ν` (`Cosine.X`, `ν ≥ 1`) let `u(y) = a_0 + 2 ∑_{k ≥ 1} a_k cos(k L y)` (`cosSeries`). It is
the Fourier series `∑_{k ∈ ℤ} a_{|k|} e^{ikLy}` of the symmetric extension `(a_{|k|})_{k ∈ ℤ}`
(`symSeq`, `cosSeries_eq`), and the symmetric product becomes the product of functions:
`symSeq (a³) = (symSeq a)³` (`symSeq_cube`).

For eigenvalues `μ_k = λ - (1 - k² L²)²` and `F(a) = 0`, `μ_k a_k = (a³)_k` and
`k⁴ L⁴ / 2 ≤ |μ_k| + |λ| + 1` give `∑_k k⁴ |a_k| < ∞` (`summable_pow_four`). Hence `u` is `C⁴`, with
derivatives computed term by term, and `(λ - 1) u - 2 u'' - u'''' - u³ = 0`: `u` is an even,
`2π/L`-periodic equilibrium of the Swift–Hohenberg equation `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³`.
`exists_equilibrium` collects these facts for an isolated zero of `F` near `ā`, with
`sup_y |u(y) - ū(y)| < 2 r₀` for the cosine series `ū` of `ā`.

Different weights: a zero of `F` in `ℓ¹_ν` is a zero in `ℓ¹_ν'` for `ν' ≤ ν` (`F_embed`), so the
isolated zeros obtained with two weights have the same coefficients as soon as `r₀(ν) ≤ r₁(ν')`
(`coeff_eq_of_isolatedZero`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace CubicCosine

open Fourier Cosine Metric

variable {ν : ℝ} {hν : 1 ≤ ν}

/-- The cosine series `u(y) = a_0 + 2 ∑_{k ≥ 1} a_k cos(k L y)`. -/
noncomputable def cosSeries (L : ℝ) (a : Cosine.X ν hν) (y : ℝ) : ℝ :=
  a 0 + 2 * ∑' k : ℕ, a (k + 1) * Real.cos ((k + 1 : ℕ) * L * y)

/-- The symmetric extension `(a_{|k|})_{k ∈ ℤ}`, as a complex two-sided sequence. -/
noncomputable def symSeq (a : Cosine.X ν hν) : Fourier.X ν hν :=
  ofRealX ν hν (Chebyshev.symExt (toCheb ν hν a))

@[simp] theorem symSeq_apply (a : Cosine.X ν hν) (k : ℤ) : symSeq a k = (a k.natAbs : ℂ) := by
  simp [symSeq]

theorem symSeq_sub (a b : Cosine.X ν hν) : symSeq (a - b) = symSeq a - symSeq b := by
  ext k; simp

theorem symSeq_cube (a : Cosine.X ν hν) : symSeq (cube ν hν a) = symSeq a ^ 3 := by
  rw [symSeq, cube_eq, toCheb_ofCheb, Chebyshev.symExt_pow, ofRealX_pow]; rfl

theorem norm_symSeq_le (a : Cosine.X ν hν) : ‖symSeq a‖ ≤ 2 * ‖a‖ := by
  have h : ‖symSeq a‖ = ‖Chebyshev.symExt (toCheb ν hν a)‖ := by
    rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum]
    simp [symSeq, Complex.norm_real]
  rw [h, Chebyshev.norm_symExt]
  exact norm_toCheb_apply_le a

theorem summable_abs (a : Cosine.X ν hν) : Summable fun n : ℕ => |a n| :=
  Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => by
    rw [← Real.norm_eq_abs]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hν)) a.summable

theorem cosSeries_eq (L : ℝ) (a : Cosine.X ν hν) (y : ℝ) :
    (cosSeries L a y : ℂ) = fourierEval ν hν (L * y) (symSeq a) := by
  set f : ℤ → ℂ := fun k => symSeq a k * expI (L * y) k with hf
  have hs : Summable f := (WeightedL1.summable_charEval (norm_expI_le (L * y)) (symSeq a)).of_norm
  have hi1 : Function.Injective fun n : ℕ => (n : ℤ) + 1 := fun m n h => by simpa using h
  have hi2 : Function.Injective fun n : ℕ => -((n : ℤ) + 1) := fun m n h => by simpa using h
  have h1 : Summable fun n : ℕ => f (n + 1) := hs.comp_injective hi1
  have h2 : Summable fun n : ℕ => f (-(n + 1)) := hs.comp_injective hi2
  have hterm : ∀ n : ℕ, f (n + 1) + f (-(n + 1)) =
      ((2 * (a (n + 1) * Real.cos ((n + 1 : ℕ) * L * y)) : ℝ) : ℂ) := fun n => by
    have hx : (((n : ℤ) + 1 : ℤ) : ℂ) * ((L * y : ℝ) : ℂ) =
        ((((n + 1 : ℕ) : ℝ) * L * y : ℝ) : ℂ) := by push_cast; ring
    simp only [hf, symSeq_apply, expI]
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, show ((n : ℤ) + 1).natAbs = n + 1 by omega,
      Int.cast_neg, neg_mul, hx, ← mul_add, ← Complex.two_cos]
    push_cast
    ring
  rw [fourierEval_apply, show (fun k => symSeq a k * expI (L * y) k) = f from rfl,
    tsum_of_add_one_of_neg_add_one h1 h2, add_assoc, add_comm (f 0), ← add_assoc,
    ← h1.tsum_add h2, tsum_congr hterm, ← Complex.ofReal_tsum]
  simp only [hf, symSeq_apply, Int.natAbs_zero, expI_zero, mul_one, cosSeries]
  push_cast
  rw [tsum_mul_left]
  ring

/-! ### Regularity -/

/-- `∑_k k⁴ |a_k| < ∞` for a zero of `F` with `μ_k = λ - (1 - k² L²)²`. -/
theorem summable_pow_four (P : CubicCosine) {lam L : ℝ} (hL : 0 < L)
    (hμ : ∀ k : ℕ, P.μ k = lam - (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2) {a : Cosine.X ν hν}
    (hF : P.F ν hν a = 0) : Summable fun k : ℕ => (k : ℝ) ^ 4 * |a k| := by
  have hc : Summable fun k : ℕ => |cube ν hν a k| := summable_abs _
  have hL4 : 0 < L ^ 4 := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hc.add ((summable_abs a).mul_left (|lam| + 1))).mul_left (2 / L ^ 4))
  have hk := congrArg (fun z : P.Y ν hν => z k) hF
  simp only [F_apply, WeightedLp.zero_apply, sub_eq_zero] at hk
  have hsq : (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2 ≤ |lam| + |P.μ k| := by
    have : (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2 = lam - P.μ k := by rw [hμ]; ring
    rw [this]; linarith [le_abs_self lam, neg_abs_le (P.μ k)]
  have hb : (k : ℝ) ^ 4 * L ^ 4 / 2 ≤ |P.μ k| + |lam| + 1 := by
    nlinarith [sq_nonneg ((k : ℝ) ^ 2 * L ^ 2 - 2)]
  have hka : |P.μ k| * |a k| = |cube ν hν a k| := by rw [← abs_mul, hk]
  calc (k : ℝ) ^ 4 * |a k| = 2 / L ^ 4 * ((k : ℝ) ^ 4 * L ^ 4 / 2 * |a k|) := by
        field_simp
    _ ≤ 2 / L ^ 4 * ((|P.μ k| + |lam| + 1) * |a k|) := by gcongr
    _ = 2 / L ^ 4 * (|cube ν hν a k| + (|lam| + 1) * |a k|) := by rw [← hka]; ring

/-- The `j`-th derivative coefficients `(i k)^j a_{|k|}`. -/
noncomputable def derivSeq (a : Cosine.X ν hν) (j : ℕ) (k : ℤ) : ℂ :=
  (Complex.I * k) ^ j * (a k.natAbs : ℂ)

theorem norm_derivSeq (a : Cosine.X ν hν) (j : ℕ) (k : ℤ) :
    ‖derivSeq a j k‖ = (k.natAbs : ℝ) ^ j * |a k.natAbs| := by
  rw [derivSeq, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
    Complex.norm_real, Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

theorem summable_derivSeq {a : Cosine.X ν hν} (h4 : Summable fun k : ℕ => (k : ℝ) ^ 4 * |a k|)
    {j : ℕ} (hj : j ≤ 4) : Summable fun k => ‖derivSeq a j k‖ := by
  simp only [norm_derivSeq]
  refine summable_int_natAbs (g := fun n => (n : ℝ) ^ j * |a n|) ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h4.add (summable_abs a))
  have : (n : ℝ) ^ j ≤ (n : ℝ) ^ 4 + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rcases j with _ | j <;> simp
    · exact (pow_le_pow_right₀ (by exact_mod_cast h) hj).trans (le_add_of_nonneg_right zero_le_one)
  nlinarith [abs_nonneg (a n)]

/-- The term by term derivative series `V_j(y) = L^j ∑_k (ik)^j a_{|k|} e^{ikLy}`. -/
noncomputable def derivFun (L : ℝ) (a : Cosine.X ν hν) (j : ℕ) (y : ℝ) : ℂ :=
  (L : ℂ) ^ j * ∑' k, derivSeq a j k * expI (L * y) k

theorem hasDerivAt_derivFun {L : ℝ} {a : Cosine.X ν hν}
    (h4 : Summable fun k : ℕ => (k : ℝ) ^ 4 * |a k|) {j : ℕ} (hj : j < 4) (y : ℝ) :
    HasDerivAt (derivFun L a j) (derivFun L a (j + 1) y) y := by
  have h1 : Summable fun k : ℤ => (k.natAbs : ℝ) * ‖derivSeq a j k‖ := by
    have := summable_derivSeq h4 (j := j + 1) hj
    refine this.congr fun k => ?_
    rw [norm_derivSeq, norm_derivSeq]; ring
  have hU := hasDerivAt_tsum_expI (derivSeq a j) (summable_derivSeq h4 hj.le) h1 (L * y)
  have hcomp := (hU.scomp y ((hasDerivAt_id y).const_mul L)).const_mul ((L : ℂ) ^ j)
  convert hcomp using 1
  · funext z; rfl
  show (L : ℂ) ^ (j + 1) * ∑' k, derivSeq a (j + 1) k * expI (L * y) k =
    (L : ℂ) ^ j * ((L * 1) • ∑' k, Complex.I * k * derivSeq a j k * expI (L * y) k)
  rw [Complex.real_smul, mul_one, pow_succ, mul_assoc]
  congr 2
  exact tsum_congr fun k => by simp only [derivSeq]; ring

/-! ### The equilibrium -/

/-- A zero of `F` with `μ_k = λ - (1 - k² L²)²` gives an even, `2π/L`-periodic `C⁴` equilibrium
`u = cosSeries L a` of `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³`. -/
theorem equilibrium_of_F_eq_zero (P : CubicCosine) {lam L : ℝ} (hL : 0 < L)
    (hμ : ∀ k : ℕ, P.μ k = lam - (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2) {a : Cosine.X ν hν}
    (hF : P.F ν hν a = 0) :
    ∃ u₁ u₂ u₃ u₄ : ℝ → ℝ, ∀ y, HasDerivAt (cosSeries L a) (u₁ y) y ∧ HasDerivAt u₁ (u₂ y) y ∧
      HasDerivAt u₂ (u₃ y) y ∧ HasDerivAt u₃ (u₄ y) y ∧
      (lam - 1) * cosSeries L a y - 2 * u₂ y - u₄ y - cosSeries L a y ^ 3 = 0 := by
  have h4 := summable_pow_four P hL hμ hF
  have hV0 : ∀ y, derivFun L a 0 y = (cosSeries L a y : ℂ) := fun y => by
    rw [cosSeries_eq, derivFun, pow_zero, one_mul, fourierEval_apply]
    exact tsum_congr fun k => by simp [derivSeq]
  have hre : ∀ (j : ℕ) (hj : j < 4) (y : ℝ),
      HasDerivAt (fun z => (derivFun L a j z).re) (derivFun L a (j + 1) y).re y := fun j hj y =>
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_derivFun h4 hj y)
  refine ⟨fun y => (derivFun L a 1 y).re, fun y => (derivFun L a 2 y).re,
    fun y => (derivFun L a 3 y).re, fun y => (derivFun L a 4 y).re, fun y => ⟨?_, hre 1 (by norm_num) y,
      hre 2 (by norm_num) y, hre 3 (by norm_num) y, ?_⟩⟩
  · have := hre 0 (by norm_num) y
    simp only [hV0, Complex.ofReal_re] at this
    exact this
  · -- the equation, coefficientwise: `(λ - 1) - 2 L² (ik)² - L⁴ (ik)⁴ = μ_{|k|}`
    have hsum : ∀ j, j ≤ 4 → Summable fun k => derivSeq a j k * expI (L * y) k := fun j hj =>
      Summable.of_norm (by simpa [norm_mul, norm_expI] using summable_derivSeq h4 hj)
    set T : ℕ → ℂ := fun j => ∑' k, derivSeq a j k * expI (L * y) k with hT
    have hD : ∀ j, derivFun L a j y = (L : ℂ) ^ j * T j := fun j => rfl
    have hser : ((lam : ℂ) - 1) * T 0 - 2 * (L : ℂ) ^ 2 * T 2 - (L : ℂ) ^ 4 * T 4 =
        fourierEval ν hν (L * y) (symSeq (cube ν hν a)) := by
      have e : ∑' k, (((lam : ℂ) - 1) * (derivSeq a 0 k * expI (L * y) k) -
          2 * (L : ℂ) ^ 2 * (derivSeq a 2 k * expI (L * y) k) -
          (L : ℂ) ^ 4 * (derivSeq a 4 k * expI (L * y) k)) =
          ((lam : ℂ) - 1) * T 0 - 2 * (L : ℂ) ^ 2 * T 2 - (L : ℂ) ^ 4 * T 4 := by
        rw [Summable.tsum_sub (((hsum 0 (by norm_num)).mul_left _).sub
            ((hsum 2 (by norm_num)).mul_left _)) ((hsum 4 (by norm_num)).mul_left _),
          Summable.tsum_sub ((hsum 0 (by norm_num)).mul_left _) ((hsum 2 (by norm_num)).mul_left _),
          tsum_mul_left, tsum_mul_left, tsum_mul_left]
      rw [← e, fourierEval_apply]
      refine tsum_congr fun k => ?_
      have hk := congrArg (fun z : P.Y ν hν => z k.natAbs) hF
      simp only [F_apply, WeightedLp.zero_apply, sub_eq_zero] at hk
      have hNK : ((k.natAbs : ℕ) : ℂ) ^ 2 = (k : ℂ) ^ 2 := by
        rw [Nat.cast_natAbs, ← Int.cast_pow, sq_abs, Int.cast_pow]
      have hI4 : Complex.I ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
      rw [symSeq_apply, ← hk, hμ]
      simp only [derivSeq, mul_pow, Complex.I_sq, hI4, pow_zero, one_mul]
      push_cast
      rw [show (1 - ((k.natAbs : ℕ) : ℂ) ^ 2 * (L : ℂ) ^ 2) ^ 2 =
        (1 - (k : ℂ) ^ 2 * (L : ℂ) ^ 2) ^ 2 by rw [hNK]]
      ring
    have hcomb : (((lam - 1) * cosSeries L a y : ℝ) : ℂ) - 2 * derivFun L a 2 y -
        derivFun L a 4 y = ((cosSeries L a y ^ 3 : ℝ) : ℂ) := by
      rw [hD, hD, Complex.ofReal_mul, ← hV0, hD, pow_zero, one_mul, Complex.ofReal_pow, ← hV0, hD,
        pow_zero, one_mul]
      push_cast
      rw [show ((lam : ℂ) - 1) * T 0 - 2 * ((L : ℂ) ^ 2 * T 2) - (L : ℂ) ^ 4 * T 4 =
        ((lam : ℂ) - 1) * T 0 - 2 * (L : ℂ) ^ 2 * T 2 - (L : ℂ) ^ 4 * T 4 by ring, hser,
        symSeq_cube, map_pow]
      congr 1
      rw [← cosSeries_eq, ← hV0, hD, pow_zero, one_mul]
    have := congrArg Complex.re hcomb
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num] at this
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul] at this
    linarith

theorem cosSeries_neg (L : ℝ) (a : Cosine.X ν hν) (y : ℝ) : cosSeries L a (-y) = cosSeries L a y := by
  simp only [cosSeries, mul_neg, Real.cos_neg]

theorem cosSeries_add_period (L : ℝ) (hL : L ≠ 0) (a : Cosine.X ν hν) (y : ℝ) :
    cosSeries L a (y + 2 * Real.pi / L) = cosSeries L a y := by
  simp only [cosSeries]
  congr 2
  refine tsum_congr fun k => ?_
  rw [show ((k + 1 : ℕ) : ℝ) * L * (y + 2 * Real.pi / L) =
    ((k + 1 : ℕ) : ℝ) * L * y + ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) by field_simp,
    Real.cos_add_nat_mul_two_pi]

theorem abs_cosSeries_sub_le (L : ℝ) (a b : Cosine.X ν hν) (y : ℝ) :
    |cosSeries L a y - cosSeries L b y| ≤ 2 * ‖a - b‖ := by
  have h : ((cosSeries L a y - cosSeries L b y : ℝ) : ℂ) =
      fourierEval ν hν (L * y) (symSeq (a - b)) := by
    push_cast; rw [cosSeries_eq, cosSeries_eq, symSeq_sub, map_sub]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h]
  exact (norm_fourierEval_le _ _).trans (norm_symSeq_le _)

/-- An isolated zero of `F` near `ā` (with `μ_k = λ - (1 - k² L²)²`) gives an even, `2π/L`-periodic
`C⁴` equilibrium `u` of `u_t = (λ - 1) u - 2 u_yy - u_yyyy - u³` with `|u(y) - ū(y)| < 2 r₀`; its
cosine coefficients form the unique zero of `F` within `r₁` of `ā`. -/
theorem exists_equilibrium (P : CubicCosine) {lam L : ℝ} (hL : 0 < L)
    (hμ : ∀ k : ℕ, P.μ k = lam - (1 - (k : ℝ) ^ 2 * L ^ 2) ^ 2) {abar : Cosine.X ν hν}
    {r₀ r₁ : ℝ} (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) :
    ∃ a : Cosine.X ν hν, P.F ν hν a = 0 ∧ (∀ b ∈ closedBall abar r₁, P.F ν hν b = 0 → b = a) ∧
      ∃ u₁ u₂ u₃ u₄ : ℝ → ℝ, ∀ y, HasDerivAt (cosSeries L a) (u₁ y) y ∧
        HasDerivAt u₁ (u₂ y) y ∧ HasDerivAt u₂ (u₃ y) y ∧ HasDerivAt u₃ (u₄ y) y ∧
        (lam - 1) * cosSeries L a y - 2 * u₂ y - u₄ y - cosSeries L a y ^ 3 = 0 ∧
        cosSeries L a (-y) = cosSeries L a y ∧
        cosSeries L a (y + 2 * Real.pi / L) = cosSeries L a y ∧
        |cosSeries L a y - cosSeries L abar y| < 2 * r₀ := by
  obtain ⟨a, ha, hFa, huniq⟩ := h
  obtain ⟨u₁, u₂, u₃, u₄, hu⟩ := equilibrium_of_F_eq_zero P hL hμ hFa
  refine ⟨a, hFa, huniq, u₁, u₂, u₃, u₄, fun y => ⟨(hu y).1, (hu y).2.1, (hu y).2.2.1,
    (hu y).2.2.2.1, (hu y).2.2.2.2, cosSeries_neg L a y, cosSeries_add_period L hL.ne' a y, ?_⟩⟩
  rw [mem_ball, dist_eq_norm] at ha
  linarith [abs_cosSeries_sub_le L a abar y]

/-! ### Different weights -/

section Embed

variable {ν' : ℝ} {hν' : 1 ≤ ν'}

/-- A zero of `F` in `ℓ¹_ν` is a zero of `F` in `ℓ¹_ν'`, `ν' ≤ ν`. -/
theorem F_embed (P : CubicCosine) (hle : ν' ≤ ν) {a : Cosine.X ν hν} (hF : P.F ν hν a = 0) :
    P.F ν' hν' (embed hν' hle a) = 0 := by
  ext k
  have h := congrArg (fun y : P.Y ν hν => y k) hF
  simp only [F_apply, WeightedLp.zero_apply] at h ⊢
  rw [cube_embed, embed_apply, embed_apply]
  exact h

/-- Zeros for different weights coincide: let the zeros of `F` near `ā` in `ℓ¹_ν` and in `ℓ¹_ν'`
(`ν' ≤ ν`, the same coefficients `ā`) be isolated, with `r₀ ≤ r₁'`. Then every zero within `r₁` of
`ā` in `ℓ¹_ν` and every zero within `r₁'` of `ā` in `ℓ¹_ν'` have the same coefficients. -/
theorem coeff_eq_of_isolatedZero (P : CubicCosine) (hle : ν' ≤ ν) {abar : Cosine.X ν hν}
    {abar' : Cosine.X ν' hν'} (hab : ∀ k, abar' k = abar k) {r₀ r₁ r₀' r₁' : ℝ}
    (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) (h' : HasIsolatedZero (P.F ν' hν') abar' r₀' r₁')
    (hr : r₀ ≤ r₁') {b : Cosine.X ν hν} (hb : b ∈ closedBall abar r₁) (hFb : P.F ν hν b = 0)
    {c : Cosine.X ν' hν'} (hc : c ∈ closedBall abar' r₁') (hFc : P.F ν' hν' c = 0) (k : ℕ) :
    b k = c k := by
  obtain ⟨a, ha, hFa, hu⟩ := h
  obtain ⟨a', -, -, hu'⟩ := h'
  have hab' : abar' = embed hν' hle abar := by
    ext k
    rw [embed_apply, hab]
  have hmem : embed hν' hle a ∈ closedBall abar' r₁' := by
    rw [mem_ball, dist_eq_norm] at ha
    rw [mem_closedBall, dist_eq_norm, hab', ← embed_sub]
    exact (norm_embed_le _ _).trans (ha.le.trans hr)
  rw [hu b hb hFb, hu' c hc hFc, ← hu' _ hmem (P.F_embed hle hFa), embed_apply]

end Embed

end CubicCosine

end RadiiPolynomial
