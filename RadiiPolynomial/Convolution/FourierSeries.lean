module

public import RadiiPolynomial.Convolution.Fourier
public import RadiiPolynomial.Convolution.Character
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fourier series

For `a ∈ ℓ¹_ν(ℤ)` (`ν ≥ 1`) the Fourier series `u(t) = ∑_k a_k e^{ikt}` converges absolutely for
all `t ∈ ℝ`, and evaluation at `t` is an algebra homomorphism `ℓ¹_ν → ℂ` (`fourierEval`, via
`WeightedL1.charEval` with the character `k ↦ e^{ikt}`, `expI`): the convolution becomes the product
of Fourier series. Moreover `|u(t)| ≤ ‖a‖` (`norm_fourierEval_le`) and `u` is `2π`-periodic
(`fourierEval_add_two_pi`).

Derivatives: for `1 ≤ ν' < ν`, `D a = (i k a_k)_k ∈ ℓ¹_{ν'}` (`derivX`), and for `ν > 1` the series
can be differentiated term by term, `u'(t) = ∑_k i k a_k e^{ikt}` (`hasDerivAt_fourierEval`).

Symmetry: `(a^*)_k = (a_{-k})^*` (`conjX`) is an isometric, additive involution, compatible with the
convolution, `a^* * b^* = (a * b)^*` (`conjX_mul`), and `∑_k (a^*)_k e^{ikt}` is the complex conjugate
of `∑_k a_k e^{ikt}` (`fourierEval_conjX`); in particular the Fourier series of a symmetric sequence
(`a^* = a`) is real (`im_fourierEval_eq_zero`). For a polynomial `p` with real coefficients,
`p(a)^* = p(a^*)` (`conjX_aeval`).

Coefficients: `∫_0^{2π} u(θ) e^{-imθ} dθ = 2π a_m` (`integral_fourierEval_mul_expI`), so `u` determines
`a` (`eq_of_fourierEval_eq`). If `u(θ + φ) = u(θ)` for all `θ`, then `a_k e^{ikφ} = a_k`
(`coeff_mul_expI_eq_of_periodic`); in particular, if `a_1 ≠ 0`, no `φ ∈ (0, 2π)` is a period of `u`
(`exists_ne_of_coeff_one_ne_zero`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace Fourier

/-- `e^{ikt}`. -/
noncomputable def expI (t : ℝ) (k : ℤ) : ℂ := Complex.exp (k * t * Complex.I)

theorem norm_expI (t : ℝ) (k : ℤ) : ‖expI t k‖ = 1 := by
  rw [expI, show ((k : ℂ) * t * Complex.I) = (((k : ℝ) * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem expI_zero (t : ℝ) : expI t 0 = 1 := by simp [expI]

theorem expI_add (t : ℝ) (k l : ℤ) : expI t (k + l) = expI t k * expI t l := by
  rw [expI, expI, expI, ← Complex.exp_add]
  push_cast
  ring_nf

theorem expI_add_two_pi (t : ℝ) (k : ℤ) : expI (t + 2 * Real.pi) k = expI t k := by
  rw [expI, expI, show (k : ℂ) * ((t + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
    k * t * Complex.I + k * (2 * Real.pi * Complex.I) by push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

variable {ν : ℝ} {hν : 1 ≤ ν}

theorem norm_expI_le (t : ℝ) (k : ℤ) : ‖expI t k‖ ≤ Weights.geomInt ν hν k := by
  rw [norm_expI, Weights.geomInt_apply]; exact one_le_pow₀ hν

variable (ν hν) in
/-- The Fourier series `∑_k a_k e^{ikt}`, an algebra homomorphism `ℓ¹_ν → ℂ`. -/
noncomputable def fourierEval (t : ℝ) : X ν hν →ₐ[ℂ] ℂ :=
  WeightedL1.charEval (expI t) (expI_zero t) (expI_add t) (norm_expI_le t)

theorem fourierEval_apply (t : ℝ) (a : X ν hν) : fourierEval ν hν t a = ∑' k, a k * expI t k := rfl

theorem norm_fourierEval_le (t : ℝ) (a : X ν hν) : ‖fourierEval ν hν t a‖ ≤ ‖a‖ :=
  WeightedL1.norm_charEval_le _ _ _ a

theorem fourierEval_add_two_pi (t : ℝ) (a : X ν hν) :
    fourierEval ν hν (t + 2 * Real.pi) a = fourierEval ν hν t a := by
  simp only [fourierEval_apply, expI_add_two_pi]

/-! ### Derivatives -/

include hν in
/-- `|k| ν'^{|k|} ≤ B ν^{|k|}` for `0 ≤ ν' < ν`, with `B = ∑_n n (ν'/ν)^n`. -/
theorem exists_natAbs_mul_pow_le {ν' : ℝ} (hν'0 : 0 ≤ ν') (hνν : ν' < ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℤ, (k.natAbs : ℝ) * ν' ^ k.natAbs ≤ B * ν ^ k.natAbs := by
  have hν0 : 0 < ν := lt_of_lt_of_le zero_lt_one hν
  set q := ν' / ν with hq
  have hq0 : 0 ≤ q := div_nonneg hν'0 hν0.le
  have hq1 : q < 1 := by rw [hq, div_lt_one hν0]; exact hνν
  have hsum : Summable fun n : ℕ => (n : ℝ) * q ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0] : ‖q‖ < 1)
  refine ⟨∑' n : ℕ, (n : ℝ) * q ^ n, tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n)
    (pow_nonneg hq0 n), fun k => ?_⟩
  have hB := hsum.le_tsum k.natAbs fun m _ => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hq0 m)
  have hpow : ν' ^ k.natAbs = q ^ k.natAbs * ν ^ k.natAbs := by
    rw [hq, div_pow, div_mul_cancel₀ _ (pow_pos hν0 _).ne']
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hB (pow_pos hν0 _).le

variable (ν hν) in
/-- `D a = (i k a_k)_k`, `ℓ¹_ν → ℓ¹_{ν'}` for `1 ≤ ν' < ν`. -/
noncomputable def derivX {ν' : ℝ} (hν' : 1 ≤ ν') (hνν : ν' < ν) : X ν hν →L[ℂ] X ν' hν' :=
  (ColNormBound.single (ω := Weights.geomInt ν' hν') (ω' := Weights.geomInt ν hν) (fun k => k)
    (fun k => Complex.I * k) (exists_natAbs_mul_pow_le (hν := hν) (by linarith) hνν).choose_spec.1 fun k => by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Weights.geomInt_apply,
        Weights.geomInt_apply, ← Int.cast_abs, ← Nat.cast_natAbs]
      exact (exists_natAbs_mul_pow_le (hν := hν) (by linarith) hνν).choose_spec.2 k).toCLM

theorem derivX_apply {ν' : ℝ} (hν' : 1 ≤ ν') (hνν : ν' < ν) (a : X ν hν) (k : ℤ) :
    derivX ν hν hν' hνν a k = Complex.I * k * a k := by
  rw [derivX, ColNormBound.toCLM_apply, tsum_eq_single k fun m hm => by simp [Ne.symm hm]]
  simp

theorem hasDerivAt_expI (k : ℤ) (t : ℝ) :
    HasDerivAt (fun s => expI s k) (Complex.I * k * expI t k) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 := ((h1.const_mul (k : ℂ)).mul_const Complex.I).cexp
  have hf : (fun s => expI s k) = fun s : ℝ => Complex.exp (k * s * Complex.I) := rfl
  rw [hf]
  convert h2 using 1
  rw [expI]; ring

/-- Term by term differentiation of Fourier series, `ν > 1`: `u'(t) = ∑_k i k a_k e^{ikt}`. -/
theorem hasDerivAt_fourierEval (hν1 : 1 < ν) (a : X ν hν) (t : ℝ) :
    HasDerivAt (fun s => fourierEval ν hν s a) (∑' k, Complex.I * k * a k * expI t k) t := by
  have hs : Summable fun k => ‖derivX ν hν le_rfl hν1 a k‖ := by
    simpa only [Weights.geomInt_apply, one_pow, one_mul] using (derivX ν hν le_rfl hν1 a).summable
  have h := hasDerivAt_tsum (u := fun k => ‖derivX ν hν le_rfl hν1 a k‖) hs
    (g := fun k s => a k * expI s k) (g' := fun k s => a k * (Complex.I * k * expI s k))
    (fun k s => (hasDerivAt_expI k s).const_mul (a k)) (fun k s => by
      rw [derivX_apply]
      simp only [norm_mul, norm_expI, mul_one]
      exact le_of_eq (by ring))
    (y₀ := 0) ((WeightedL1.summable_charEval (norm_expI_le 0) a).of_norm) t
  convert h using 1
  · funext s; rfl
  · exact tsum_congr fun k => by ring

/-- Term by term differentiation of `θ ↦ ∑_k s_k e^{ikθ}` when `∑_k |k| |s_k| < ∞`. -/
theorem hasDerivAt_tsum_expI (s : ℤ → ℂ) (hs0 : Summable fun k => ‖s k‖)
    (hs1 : Summable fun k => (k.natAbs : ℝ) * ‖s k‖) (θ : ℝ) :
    HasDerivAt (fun φ => ∑' k, s k * expI φ k) (∑' k, Complex.I * k * s k * expI θ k) θ := by
  have h := hasDerivAt_tsum (u := fun k => (k.natAbs : ℝ) * ‖s k‖) hs1
    (g := fun k φ => s k * expI φ k) (g' := fun k φ => s k * (Complex.I * k * expI φ k))
    (fun k φ => (hasDerivAt_expI k φ).const_mul (s k)) (fun k φ => by
      simp only [norm_mul, norm_expI, mul_one, Complex.norm_I, one_mul, Complex.norm_intCast,
        Nat.cast_natAbs, Int.cast_abs]
      exact le_of_eq (by ring))
    (y₀ := 0) (Summable.of_norm (by simpa [norm_mul, norm_expI] using hs0)) θ
  convert h using 1
  exact tsum_congr fun k => by ring

/-! ### Real sequences -/

variable (ν hν) in
/-- A real two-sided sequence as a complex one, an algebra homomorphism over `ℝ` on products. -/
noncomputable def ofRealX (s : WeightedL1 ℝ (Weights.geomInt ν hν)) : X ν hν :=
  WeightedL1.ofSummable (fun k => (s k : ℂ)) (by simpa [Complex.norm_real] using s.summable)

@[simp] theorem ofRealX_apply (s : WeightedL1 ℝ (Weights.geomInt ν hν)) (k : ℤ) :
    ofRealX ν hν s k = (s k : ℂ) := rfl

theorem ofRealX_mul (s t : WeightedL1 ℝ (Weights.geomInt ν hν)) :
    ofRealX ν hν (s * t) = ofRealX ν hν s * ofRealX ν hν t := by
  ext k
  rw [ofRealX_apply, WeightedL1.mul_apply, WeightedL1.mul_apply, Convolution.conv,
    Convolution.conv, Complex.ofReal_tsum]
  push_cast
  rfl

theorem ofRealX_one : ofRealX ν hν (1 : WeightedL1 ℝ (Weights.geomInt ν hν)) = 1 := by
  ext k
  rw [ofRealX_apply, WeightedL1.one_def, WeightedL1.one_def, WeightedL1.single_apply,
    WeightedL1.single_apply]
  split_ifs <;> simp

theorem ofRealX_add (s t : WeightedL1 ℝ (Weights.geomInt ν hν)) :
    ofRealX ν hν (s + t) = ofRealX ν hν s + ofRealX ν hν t := by ext k; simp

theorem ofRealX_smul (c : ℝ) (s : WeightedL1 ℝ (Weights.geomInt ν hν)) :
    ofRealX ν hν (c • s) = (c : ℂ) • ofRealX ν hν s := by
  ext k; simp only [ofRealX_apply, WeightedLp.smul_apply, Complex.ofReal_mul]

theorem norm_ofRealX (s : WeightedL1 ℝ (Weights.geomInt ν hν)) : ‖ofRealX ν hν s‖ = ‖s‖ := by
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum]
  simp [Complex.norm_real]

theorem summable_int_natAbs {g : ℕ → ℝ} (hg : Summable g) : Summable fun k : ℤ => g k.natAbs := by
  refine Summable.of_nat_of_neg_add_one (by simpa using hg) ?_
  refine ((summable_nat_add_iff 1).2 hg).congr fun n => ?_
  congr 1

/-- For a real sequence `b` with `∑ |b_n| < ∞`,
`∑_{k ∈ ℤ} b_{|k|} e^{ikθ} = b_0 + 2 ∑_{n ≥ 1} b_n cos(nθ)`. -/
theorem tsum_natAbs_mul_expI (b : ℕ → ℝ) (hb : Summable fun n => |b n|) (θ : ℝ) :
    ∑' k : ℤ, (b k.natAbs : ℂ) * expI θ k =
      ((b 0 + 2 * ∑' n : ℕ, b (n + 1) * Real.cos ((n + 1 : ℕ) * θ) : ℝ) : ℂ) := by
  set f : ℤ → ℂ := fun k => (b k.natAbs : ℂ) * expI θ k with hf
  have hsum : Summable f := Summable.of_norm (by
    simpa [hf, norm_mul, norm_expI, Complex.norm_real] using summable_int_natAbs hb)
  have hi1 : Function.Injective fun n : ℕ => (n : ℤ) + 1 := fun m n h => by simpa using h
  have hi2 : Function.Injective fun n : ℕ => -((n : ℤ) + 1) := fun m n h => by simpa using h
  have h1 : Summable fun n : ℕ => f (n + 1) := hsum.comp_injective hi1
  have h2 : Summable fun n : ℕ => f (-(n + 1)) := hsum.comp_injective hi2
  have hterm : ∀ n : ℕ, f (n + 1) + f (-(n + 1)) =
      ((2 * (b (n + 1) * Real.cos ((n + 1 : ℕ) * θ)) : ℝ) : ℂ) := fun n => by
    have hx : (((n : ℤ) + 1 : ℤ) : ℂ) * (θ : ℂ) = ((((n + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) := by
      push_cast; ring
    simp only [hf, expI]
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, show ((n : ℤ) + 1).natAbs = n + 1 by omega,
      Int.cast_neg, neg_mul, hx, ← mul_add, ← Complex.two_cos]
    push_cast
    ring
  rw [tsum_of_add_one_of_neg_add_one h1 h2, add_assoc, add_comm (f 0), ← add_assoc,
    ← h1.tsum_add h2, tsum_congr hterm, ← Complex.ofReal_tsum]
  simp only [hf, Int.natAbs_zero, expI_zero, mul_one]
  push_cast
  rw [tsum_mul_left]
  ring

theorem ofRealX_pow (s : WeightedL1 ℝ (Weights.geomInt ν hν)) (e : ℕ) :
    ofRealX ν hν (s ^ e) = ofRealX ν hν s ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, ofRealX_one]
  | succ e ih => rw [pow_succ, pow_succ, ofRealX_mul, ih]

/-! ### Symmetry -/

/-- `(a^*)_k = (a_{-k})^*`. -/
noncomputable def conjX (a : X ν hν) : X ν hν :=
  WeightedL1.ofSummable (fun k => star (a (-k))) (by
    have := (Equiv.neg ℤ).summable_iff.2 a.summable
    simpa [Function.comp_def, Weights.geomInt_apply, Int.natAbs_neg] using this)

@[simp] theorem conjX_apply (a : X ν hν) (k : ℤ) : conjX a k = star (a (-k)) := rfl

theorem conjX_conjX (a : X ν hν) : conjX (conjX a) = a := by ext k; simp

theorem conjX_add (a b : X ν hν) : conjX (a + b) = conjX a + conjX b := by ext k; simp

theorem conjX_sub (a b : X ν hν) : conjX (a - b) = conjX a - conjX b := by ext k; simp

theorem conjX_smul (c : ℂ) (a : X ν hν) : conjX (c • a) = star c • conjX a := by ext k; simp

theorem norm_conjX (a : X ν hν) : ‖conjX a‖ = ‖a‖ := by
  rw [WeightedL1.norm_eq_tsum, WeightedL1.norm_eq_tsum,
    ← (Equiv.neg ℤ).tsum_eq (fun k => Weights.geomInt ν hν k * ‖a k‖)]
  simp [Weights.geomInt_apply, Int.natAbs_neg]

/-- `a^* * b^* = (a * b)^*`. -/
theorem conjX_mul (a b : X ν hν) : conjX (a * b) = conjX a * conjX b := by
  ext k
  rw [conjX_apply, mul_apply, mul_apply, tsum_star, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Equiv.neg_apply, conjX_apply, star_mul']
  rw [show -k - -j = -(k - j) by ring]

theorem conjX_one : conjX (1 : X ν hν) = 1 := by
  ext k
  rw [conjX_apply, one_apply, one_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

theorem conjX_zero : conjX (0 : X ν hν) = 0 := by ext k; simp

theorem conjX_sum {ι : Type*} (S : Finset ι) (f : ι → X ν hν) :
    conjX (∑ i ∈ S, f i) = ∑ i ∈ S, conjX (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [conjX_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, conjX_add, ih]

theorem conjX_prod {ι : Type*} (S : Finset ι) (f : ι → X ν hν) :
    conjX (∏ i ∈ S, f i) = ∏ i ∈ S, conjX (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [conjX_one]
  | insert x S hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, conjX_mul, ih]

theorem conjX_pow (a : X ν hν) (e : ℕ) : conjX (a ^ e) = conjX a ^ e := by
  induction e with
  | zero => simp [conjX_one]
  | succ e ih => rw [pow_succ, pow_succ, conjX_mul, ih]

theorem conjX_algebraMap {c : ℂ} (hc : star c = c) :
    conjX (algebraMap ℂ (X ν hν) c) = algebraMap ℂ (X ν hν) c := by
  rw [Algebra.algebraMap_eq_smul_one, conjX_smul, conjX_one, hc]

/-- For a polynomial `p` with real coefficients, `p(a)^* = p(a^*)`. -/
theorem conjX_aeval {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ)
    (hp : ∀ d, star (p.coeff d) = p.coeff d) (a : σ → X ν hν) :
    conjX (MvPolynomial.aeval a p) = MvPolynomial.aeval (fun i => conjX (a i)) p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.aeval_def,
    MvPolynomial.eval₂_eq', conjX_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [conjX_mul, conjX_algebraMap (hp d), conjX_prod]
  simp only [conjX_pow]

theorem star_expI (t : ℝ) (k : ℤ) : star (expI t k) = expI t (-k) := by
  rw [expI, expI, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
  ring

/-- `(∑_k a_k e^{ikt})^* = ∑_k (a^*)_k e^{ikt}`. -/
theorem fourierEval_conjX (t : ℝ) (a : X ν hν) :
    star (fourierEval ν hν t a) = fourierEval ν hν t (conjX a) := by
  rw [fourierEval_apply, fourierEval_apply, ← (Equiv.neg ℤ).tsum_eq (fun k => conjX a k * expI t k)]
  rw [tsum_star]
  refine tsum_congr fun k => ?_
  simp only [Equiv.neg_apply, conjX_apply, neg_neg, star_mul', star_expI]

/-- The Fourier series of a symmetric sequence is real. -/
theorem im_fourierEval_eq_zero {a : X ν hν} (ha : conjX a = a) (t : ℝ) :
    (fourierEval ν hν t a).im = 0 := by
  have h := fourierEval_conjX (ν := ν) (hν := hν) t a
  rw [ha] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

theorem ofReal_re_fourierEval {a : X ν hν} (ha : conjX a = a) (t : ℝ) :
    (((fourierEval ν hν t a).re : ℝ) : ℂ) = fourierEval ν hν t a :=
  Complex.ext rfl (by rw [Complex.ofReal_im, im_fourierEval_eq_zero ha])

/-! ### Fourier coefficients -/

theorem expI_add_left (s t : ℝ) (k : ℤ) : expI (s + t) k = expI s k * expI t k := by
  simp only [expI, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_expI (k : ℤ) : Continuous fun t => expI t k :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_expI k t).continuousAt

/-- `∫_0^{2π} e^{ikθ} dθ = 2π` if `k = 0`, and `0` otherwise. -/
theorem integral_expI (k : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, expI θ k = if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp [expI]
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) Complex.I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
    have hfun : (fun θ : ℝ => expI θ k) = fun θ : ℝ => Complex.exp (k * Complex.I * θ) := by
      funext θ
      rw [expI]
      ring_nf
    have h2 : Complex.exp (k * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨k, by push_cast; ring⟩
    rw [hfun, h, h2]
    simp

theorem summable_norm_coeff (a : X ν hν) : Summable fun k => ‖a k‖ := by
  simpa [norm_mul, norm_expI] using WeightedL1.summable_charEval (norm_expI_le 0) a

/-- The Fourier coefficients: `∫_0^{2π} u(θ) e^{-imθ} dθ = 2π a_m`. -/
theorem integral_fourierEval_mul_expI (a : X ν hν) (m : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, fourierEval ν hν θ a * expI θ (-m) =
      ((2 * Real.pi : ℝ) : ℂ) * a m := by
  set f : ℤ → C(ℝ, ℂ) := fun k =>
    ⟨fun θ => a k * expI θ (k - m), continuous_const.mul (continuous_expI _)⟩ with hf
  have hint : (fun θ => fourierEval ν hν θ a * expI θ (-m)) = fun θ => ∑' k, f k θ := by
    funext θ
    rw [fourierEval_apply, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [hf, ContinuousMap.coe_mk]
    rw [mul_assoc, ← expI_add, sub_eq_add_neg]
  have hk : ∀ k, ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ =
      if k = m then ((2 * Real.pi : ℝ) : ℂ) * a m else 0 := fun k => by
    simp only [hf, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_const_mul, integral_expI]
    by_cases hkm : k = m
    · subst hkm; simp [mul_comm]
    · simp [sub_eq_zero, hkm]
  rw [hint, ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm ?_, tsum_congr hk,
    tsum_ite_eq]
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (summable_norm_coeff a)
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun θ => ?_
  simp [hf, norm_expI]

/-- A Fourier series determines its coefficients. -/
theorem eq_of_fourierEval_eq {a b : X ν hν}
    (h : ∀ θ, fourierEval ν hν θ a = fourierEval ν hν θ b) : a = b := by
  ext m
  have h0 := integral_fourierEval_mul_expI (a - b) m
  simp only [map_sub, h, sub_self, zero_mul, intervalIntegral.integral_zero] at h0
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have := (mul_eq_zero.1 h0.symm).resolve_left hpi
  rwa [WeightedLp.sub_apply, sub_eq_zero] at this

variable (ν hν) in
/-- The modulated sequence `(a_k e^{ikφ})_k`, the coefficients of `θ ↦ u(θ + φ)`. -/
noncomputable def modX (φ : ℝ) (a : X ν hν) : X ν hν :=
  WeightedL1.ofSummable (fun k => a k * expI φ k) (by simpa [norm_mul, norm_expI] using a.summable)

theorem modX_apply (φ : ℝ) (a : X ν hν) (k : ℤ) : modX ν hν φ a k = a k * expI φ k :=
  WeightedL1.ofSummable_apply _ _ k

theorem fourierEval_modX (φ θ : ℝ) (a : X ν hν) :
    fourierEval ν hν θ (modX ν hν φ a) = fourierEval ν hν (θ + φ) a := by
  rw [fourierEval_apply, fourierEval_apply]
  refine tsum_congr fun k => ?_
  rw [modX_apply, expI_add_left]
  ring

/-- If `u(θ + φ) = u(θ)` for all `θ`, then `a_k e^{ikφ} = a_k` for all `k`. -/
theorem coeff_mul_expI_eq_of_periodic {a : X ν hν} {φ : ℝ}
    (h : ∀ θ, fourierEval ν hν (θ + φ) a = fourierEval ν hν θ a) (k : ℤ) :
    a k * expI φ k = a k := by
  have he := eq_of_fourierEval_eq (a := modX ν hν φ a) (b := a) fun θ => by rw [fourierEval_modX, h]
  have := congrArg (fun c : X ν hν => c k) he
  simpa [modX_apply] using this

/-- If `a_1 ≠ 0`, then no `φ ∈ (0, 2π)` is a period of `u`. -/
theorem exists_ne_of_coeff_one_ne_zero {a : X ν hν} (ha : a 1 ≠ 0) {φ : ℝ} (h0 : 0 < φ)
    (h1 : φ < 2 * Real.pi) : ∃ θ, fourierEval ν hν (θ + φ) a ≠ fourierEval ν hν θ a := by
  by_contra hcon
  push Not at hcon
  have he : expI φ 1 = 1 := by
    have := coeff_mul_expI_eq_of_periodic hcon 1
    exact mul_left_cancel₀ ha (by rw [this, mul_one])
  rw [expI, Complex.exp_eq_one_iff] at he
  obtain ⟨n, hn⟩ := he
  have hφ : φ = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have h0' : (0 : ℤ) < n := by exact_mod_cast hn0
  have h1' : n < (1 : ℤ) := by exact_mod_cast hn1
  omega

end Fourier

end RadiiPolynomial
