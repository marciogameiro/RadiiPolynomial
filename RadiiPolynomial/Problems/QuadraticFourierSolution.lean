module

public import RadiiPolynomial.Problems.QuadraticFourier
public import RadiiPolynomial.Convolution.FourierSeries
public import RadiiPolynomial.Abstract.RadiiPoly

/-!
# Solutions of forced quadratic problems in Fourier series

For eigenvalues `λ_n = -n² + i c₁ n + c₂` (`c₁, c₂ ∈ ℝ`) a zero `a` of `F(a) = Λ a - ι(a * a + g)` in
`ℓ¹_ν` (`ν > 1`) gives a `2π`-periodic `C²` solution `u(t) = ∑_n a_n e^{int}` of
`u'' + c₁ u' + c₂ u - u² = ∑_n g_n e^{int}` (`solves_of_F_eq_zero`).

Symmetry: if `g_{-n} = g_n^*` and `ā^* = ā`, then the zero of `F` near `ā` is symmetric
(`conjX_eq_of_isolatedZero`), so that `u` is real. `exists_solution` collects these facts: an isolated
zero of `F` near a symmetric `ā` gives a real `2π`-periodic `C²` solution `u` within `r₀` of
`∑_n ā_n e^{int}`, whose Fourier coefficients form the unique zero of `F` within `r₁` of `ā`.
-/

@[expose] public section

namespace RadiiPolynomial

namespace QuadraticFourier

open Fourier Metric

variable (P : QuadraticFourier) {ν : ℝ} {hν : 1 ≤ ν}

theorem summable_fourier (a : X ν hν) (t : ℝ) : Summable fun k => a k * expI t k :=
  (WeightedL1.summable_charEval (norm_expI_le t) a).of_norm

/-- A zero of `F` with `λ_n = -n² + i c₁ n + c₂` solves `u'' + c₁ u' + c₂ u - u² = ∑_n g_n e^{int}`,
`u(t) = ∑_n a_n e^{int}` (with `u'`, `u''` the term by term derivatives). -/
theorem solves_of_F_eq_zero (hν1 : 1 < ν) {c₁ c₂ : ℂ}
    (hlam : ∀ n : ℤ, P.lam n = -(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂) {a : X ν hν}
    (hF : P.F ν hν a = 0) :
    ∃ u' u'' : ℝ → ℂ, ∀ t, HasDerivAt (fun s => fourierEval ν hν s a) (u' t) t ∧
      HasDerivAt u' (u'' t) t ∧
      u'' t + c₁ * u' t + c₂ * fourierEval ν hν t a - fourierEval ν hν t a ^ 2 =
        fourierEval ν hν t (P.forcing ν hν) := by
  set ν' := (1 + ν) / 2 with hν'def
  have hν' : 1 ≤ ν' := by rw [hν'def]; linarith
  have hν'1 : 1 < ν' := by rw [hν'def]; linarith
  have hνν : ν' < ν := by rw [hν'def]; linarith
  set b := derivX ν hν hν' hνν a with hb
  set c := derivX ν' hν' le_rfl hν'1 b with hc
  refine ⟨fun t => fourierEval ν' hν' t b, fun t => fourierEval 1 le_rfl t c, fun t => ⟨?_, ?_, ?_⟩⟩
  · convert hasDerivAt_fourierEval hν1 a t using 1
    beta_reduce
    rw [fourierEval_apply]
    exact tsum_congr fun k => by rw [hb, derivX_apply]
  · convert hasDerivAt_fourierEval hν'1 b t using 1
    beta_reduce
    rw [fourierEval_apply]
    exact tsum_congr fun k => by rw [hc, derivX_apply]
  · have hcoef : ∀ k : ℤ, c k + c₁ * b k + c₂ * a k = P.lam k * a k := fun k => by
      rw [hc, derivX_apply, hb, derivX_apply, hlam]
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (k : ℂ) ^ 2 * a k * hI
    have hF' : ∀ k : ℤ, P.lam k * a k - (a * a) k - P.g k = 0 := fun k => by
      have := congrArg (fun y : P.Y ν hν => y k) hF
      simpa [F_apply] using this
    have key : ∑' k, ((c k + c₁ * b k + c₂ * a k) - (a * a) k - P.g k) * expI t k = 0 := by
      simp [hcoef, hF']
    have e1 : (fun k => ((c k + c₁ * b k + c₂ * a k) - (a * a) k - P.g k) * expI t k) =
        fun k => c k * expI t k + c₁ * (b k * expI t k) + c₂ * (a k * expI t k) -
          (a * a) k * expI t k - P.forcing ν hν k * expI t k := by
      funext k; rw [forcing_apply]; ring
    have sc := summable_fourier c t
    have sb := summable_fourier b t
    have sa := summable_fourier a t
    have saa := summable_fourier (a * a) t
    have sg := summable_fourier (P.forcing ν hν) t
    rw [e1, Summable.tsum_sub (((sc.add (sb.mul_left c₁)).add (sa.mul_left c₂)).sub saa) sg,
      Summable.tsum_sub ((sc.add (sb.mul_left c₁)).add (sa.mul_left c₂)) saa,
      Summable.tsum_add (sc.add (sb.mul_left c₁)) (sa.mul_left c₂), Summable.tsum_add sc
        (sb.mul_left c₁), tsum_mul_left, tsum_mul_left] at key
    have hsq : fourierEval ν hν t a ^ 2 = ∑' k, (a * a) k * expI t k := by
      rw [sq, ← map_mul, fourierEval_apply]
    beta_reduce
    rw [hsq]
    simp only [fourierEval_apply]
    linear_combination key

/-- Symmetry: if `λ_{-n} = λ_n^*`, `g_{-n} = g_n^*` and `ā^* = ā`, then the zero of `F` near `ā` is
symmetric, `ã^* = ã`. -/
theorem conjX_eq_of_isolatedZero (hlam : ∀ n : ℤ, P.lam (-n) = star (P.lam n))
    (hg : ∀ n : ℤ, P.g (-n) = star (P.g n)) {abar : X ν hν} (habar : conjX abar = abar)
    {r₀ r₁ : ℝ} (hr : r₀ ≤ r₁) {a : X ν hν} (ha : a ∈ ball abar r₀) (hFa : P.F ν hν a = 0)
    (huniq : ∀ b ∈ closedBall abar r₁, P.F ν hν b = 0 → b = a) : conjX a = a := by
  refine huniq _ ?_ ?_
  · rw [mem_closedBall, dist_eq_norm, ← habar, ← conjX_sub, norm_conjX, ← dist_eq_norm]
    exact (mem_ball.1 ha).le.trans hr
  · ext k
    have h0 := congrArg (fun y : P.Y ν hν => y (-k)) hFa
    simp only [F_apply, WeightedLp.zero_apply] at h0
    rw [F_apply, WeightedLp.zero_apply, ← conjX_mul, conjX_apply, conjX_apply]
    have hl : P.lam k = star (P.lam (-k)) := by rw [hlam, star_star]
    have hgk : P.g k = star (P.g (-k)) := by rw [hg, star_star]
    rw [hl, hgk, ← star_mul', ← star_sub, ← star_sub, h0, star_zero]

/-- An isolated zero of `F` near a symmetric `ā` gives a real `2π`-periodic `C²` solution `u` of
`u'' + c₁ u' + c₂ u - u² = Re ∑_n g_n e^{int}` within `r₀` of `∑_n ā_n e^{int}`; its Fourier
coefficients form the unique zero of `F` within `r₁` of `ā`. -/
theorem exists_solution (hν1 : 1 < ν) {c₁ c₂ : ℝ}
    (hlam : ∀ n : ℤ, P.lam n = -(n : ℂ) ^ 2 + Complex.I * c₁ * n + c₂)
    (hg : ∀ n : ℤ, P.g (-n) = star (P.g n)) {abar : X ν hν} (habar : conjX abar = abar)
    {r₀ r₁ : ℝ} (hr : r₀ ≤ r₁) (h : HasIsolatedZero (P.F ν hν) abar r₀ r₁) :
    ∃ a : X ν hν, P.F ν hν a = 0 ∧ (∀ b ∈ closedBall abar r₁, P.F ν hν b = 0 → b = a) ∧
      ∃ u u' u'' : ℝ → ℝ, ∀ t, (u t : ℂ) = ∑' n, a n * expI t n ∧
        HasDerivAt u (u' t) t ∧ HasDerivAt u' (u'' t) t ∧
        u'' t + c₁ * u' t + c₂ * u t - u t ^ 2 = (∑' n, P.g n * expI t n).re ∧
        u (t + 2 * Real.pi) = u t ∧ ‖(u t : ℂ) - fourierEval ν hν t abar‖ < r₀ := by
  obtain ⟨a, ha, hFa, huniq⟩ := h
  have hlam' : ∀ n : ℤ, P.lam (-n) = star (P.lam n) := fun n => by
    rw [hlam, hlam]
    simp only [Int.cast_neg, star_add, star_neg, star_mul', Complex.star_def, map_pow,
      Complex.conj_I, Complex.conj_ofReal, map_intCast]
    ring
  have hsym := P.conjX_eq_of_isolatedZero hlam' hg habar hr ha hFa huniq
  obtain ⟨U', U'', hU⟩ := P.solves_of_F_eq_zero hν1 (c₁ := c₁) (c₂ := c₂) hlam hFa
  have hre : ∀ t, (((fourierEval ν hν t a).re : ℝ) : ℂ) = fourierEval ν hν t a :=
    ofReal_re_fourierEval hsym
  refine ⟨a, hFa, huniq, fun t => (fourierEval ν hν t a).re, fun t => (U' t).re,
    fun t => (U'' t).re, fun t => ⟨by rw [hre]; rfl, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hU t).1
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hU t).2.1
  · have h3 := congrArg Complex.re (hU t).2.2
    rw [← hre t] at h3
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, ← Complex.ofReal_pow,
      Complex.ofReal_re] at h3
    rw [h3, fourierEval_apply]
    rfl
  · simp only [fourierEval_add_two_pi]
  · rw [hre, ← map_sub]
    exact lt_of_le_of_lt (norm_fourierEval_le t _) (by rwa [mem_ball, dist_eq_norm] at ha)

end QuadraticFourier

end RadiiPolynomial
