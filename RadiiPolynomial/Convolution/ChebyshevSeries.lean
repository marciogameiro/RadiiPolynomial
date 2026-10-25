module

public import RadiiPolynomial.Convolution.Chebyshev
public import RadiiPolynomial.Convolution.FourierSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chebyshev series as functions on `[-1, 1]`

For a real sequence `a` with `∑ |a_k| < ∞`, `u(t) = a_0 + 2 ∑_{k ≥ 1} a_k T_k(t)` (`chebSeries`)
converges on `[-1, 1]`. With `t = cos θ` and `T_k(cos θ) = cos(kθ)` it becomes the Fourier series
`U(θ) = ∑_{k ∈ ℤ} a_{|k|} e^{ikθ}` (`cosFun`, `chebSeries_cos`), so that `u(t) = Re U(arccos t)`.

Differentiation: if `2k b_k = L (c_{k-1} - c_{k+1})` for `k ≥ 1` and `∑ |c_k| < ∞`, then
`∑ k |b_k| < ∞` (`summable_of_rel`) and

  `U_b'(θ) = ∑_k i k b_{|k|} e^{ikθ} = -L sin θ · U_c(θ)`   (`hasDerivAt_cosFun`),

since `i k b_{|k|} = -(i L / 2) (c_{|k+1|} - c_{|k-1|})` for every `k ∈ ℤ` and the shifts
`k ↦ k ± 1` multiply `U_c` by `e^{∓iθ}`. By the chain rule (`d/dt arccos t = -1/sin θ`) the function
`u_b` is differentiable on `(-1, 1)` with `u_b' = L u_c` (`hasDerivAt_chebSeries`), and, since
`u_b`, `u_c` are continuous on `[-1, 1]`, also at the endpoints within `[-1, 1]`
(`hasDerivWithinAt_chebSeries`). Integrating gives the Chebyshev coefficients of a primitive
(`integral_chebSeries`).

On `X_ν` the map `a ↦ U_a(θ)` is an algebra homomorphism (`thetaEval`), so the Chebyshev product
becomes the product of functions: `u_{a * b} = u_a u_b` (`chebSeries_mul`) and
`u_{P(a)}(t) = P(u_a(t))` for a polynomial `P` (`chebSeries_aeval`). The values at `t = ±1` are `a_0 + 2 ∑_{k ≥ 1} (±1)^k a_k`
(`chebSeries_neg_one`, `chebSeries_one`), and `|u_a(t)| ≤ ‖a‖_ν` (`abs_chebSeries_le_norm`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace Chebyshev

open Set Filter Topology
open Fourier (expI expI_add norm_expI)

/-- The Chebyshev series `u(t) = a_0 + 2 ∑_{k ≥ 1} a_k T_k(t)`. -/
noncomputable def chebSeries (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  a 0 + 2 * ∑' k : ℕ, a (k + 1) * (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t

/-- The series in the variable `θ`, `t = cos θ`: `U(θ) = ∑_{k ∈ ℤ} a_{|k|} e^{ikθ}`. -/
noncomputable def cosFun (a : ℕ → ℝ) (θ : ℝ) : ℂ := ∑' k : ℤ, (a k.natAbs : ℂ) * expI θ k

theorem abs_T_le {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ k).eval t| ≤ 1 := by
  rw [← Real.cos_arccos ht.1 ht.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem summable_term {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    Summable fun k : ℕ => a (k + 1) * (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_T_le ht _))
    ((summable_nat_add_iff 1).2 ha))

theorem chebSeries_cos {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (θ : ℝ) :
    (chebSeries a (Real.cos θ) : ℂ) = cosFun a θ := by
  rw [cosFun, Fourier.tsum_natAbs_mul_expI a ha, chebSeries]
  simp only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]

theorem chebSeries_eq_re {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : chebSeries a t = (cosFun a (Real.arccos t)).re := by
  rw [← chebSeries_cos ha, Real.cos_arccos ht.1 ht.2, Complex.ofReal_re]

theorem continuous_cosFun {a : ℕ → ℝ} (ha : Summable fun n => |a n|) : Continuous (cosFun a) :=
  continuous_tsum (u := fun k : ℤ => |a k.natAbs|)
    (fun k => continuous_const.mul
      (continuous_iff_continuousAt.2 fun θ => (Fourier.hasDerivAt_expI k θ).continuousAt))
    (Fourier.summable_int_natAbs ha)
    (fun k θ => le_of_eq (by rw [norm_mul, norm_expI, mul_one, Complex.norm_real, Real.norm_eq_abs]))

theorem continuousOn_chebSeries {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    ContinuousOn (chebSeries a) (Icc (-1) 1) :=
  (Complex.continuous_re.comp ((continuous_cosFun ha).comp Real.continuous_arccos)).continuousOn.congr
    fun _ ht => chebSeries_eq_re ha ht

/-- `u(-1) = a_0 + 2 ∑_{k ≥ 1} (-1)^k a_k`. -/
theorem chebSeries_neg_one (a : ℕ → ℝ) :
    chebSeries a (-1) = a 0 + 2 * ∑' k : ℕ, (-1) ^ (k + 1) * a (k + 1) := by
  have h : ∀ k : ℕ, (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval (-1) = (-1) ^ (k + 1) := fun k => by
    have := Polynomial.Chebyshev.T_real_cos Real.pi (k + 1 : ℕ)
    rwa [Real.cos_pi, Int.cast_natCast, Real.cos_nat_mul_pi] at this
  rw [chebSeries]
  congr 2
  exact tsum_congr fun k => by rw [h, mul_comm]

/-- `u(1) = a_0 + 2 ∑_{k ≥ 1} a_k`. -/
theorem chebSeries_one (a : ℕ → ℝ) : chebSeries a 1 = a 0 + 2 * ∑' k : ℕ, a (k + 1) := by
  simp [chebSeries, Polynomial.Chebyshev.T_eval_one]

theorem abs_chebSeries_le {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : |chebSeries a t| ≤ |a 0| + 2 * ∑' k : ℕ, |a (k + 1)| := by
  have hs : Summable fun k : ℕ => |a (k + 1)| := (summable_nat_add_iff 1).2 ha
  have hle : ∀ k : ℕ, |a (k + 1) * (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t| ≤ |a (k + 1)| :=
    fun k => by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_T_le ht _)
  have hn : Summable fun k : ℕ => ‖a (k + 1) * (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  rw [chebSeries]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hn).trans ?_) zero_le_two
  exact Summable.tsum_le_tsum hle hn hs

theorem chebSeries_sub {a b : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (hb : Summable fun n => |b n|) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    chebSeries (a - b) t = chebSeries a t - chebSeries b t := by
  simp only [chebSeries, Pi.sub_apply, sub_mul]
  rw [Summable.tsum_sub (summable_term ha ht) (summable_term hb ht)]
  ring

/-! ### Differentiation -/

section Deriv

variable {b c : ℕ → ℝ} {L : ℝ}

/-- If `2k b_k = L (c_{k-1} - c_{k+1})` (`k ≥ 1`) and `∑ |c_k| < ∞`, then `∑ k |b_k| < ∞`. -/
theorem summable_of_rel (hc : Summable fun n => |c n|)
    (hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = L * (c (k - 1) - c (k + 1))) :
    Summable fun n : ℕ => (n : ℝ) * |b n| := by
  have h1 : Summable fun n => |c (n - 1)| := (summable_nat_add_iff 1).1 (by simpa using hc)
  have h2 : Summable fun n => |c (n + 1)| := (summable_nat_add_iff 1).2 hc
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h1.add h2).mul_left (|L| / 2))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, zero_mul]; positivity
  · have h := hbc n hn.ne'
    calc (n : ℝ) * |b n| = |2 * n * b n| / 2 := by
          rw [abs_mul, abs_mul, abs_two, Nat.abs_cast]; ring
      _ = |L| * |c (n - 1) - c (n + 1)| / 2 := by rw [h, abs_mul]
      _ ≤ |L| / 2 * (|c (n - 1)| + |c (n + 1)|) := by
          have := abs_sub (c (n - 1)) (c (n + 1))
          have hL := abs_nonneg L
          nlinarith

theorem summable_abs_of_rel (hc : Summable fun n => |c n|)
    (hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = L * (c (k - 1) - c (k + 1))) :
    Summable fun n => |b n| := by
  refine (summable_nat_add_iff 1).1 (Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((summable_nat_add_iff 1).2 (summable_of_rel hc hbc)))
  have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  nlinarith [abs_nonneg (b (n + 1))]

/-- `U_b'(θ) = -L sin θ · U_c(θ)` when `2k b_k = L (c_{k-1} - c_{k+1})` for `k ≥ 1`. -/
theorem hasDerivAt_cosFun (hc : Summable fun n => |c n|)
    (hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = L * (c (k - 1) - c (k + 1))) (θ : ℝ) :
    HasDerivAt (cosFun b) (-((L : ℂ) * (Real.sin θ : ℂ)) * cosFun c θ) θ := by
  set s : ℤ → ℂ := fun k => (b k.natAbs : ℂ) with hs
  set σ : ℤ → ℂ := fun k => (c k.natAbs : ℂ) with hσ
  have hs0 : Summable fun k => ‖s k‖ := by
    simpa [hs, Complex.norm_real] using Fourier.summable_int_natAbs (summable_abs_of_rel hc hbc)
  have hs1 : Summable fun k : ℤ => (k.natAbs : ℝ) * ‖s k‖ := by
    simpa [hs, Complex.norm_real] using Fourier.summable_int_natAbs (summable_of_rel hc hbc)
  have hd := Fourier.hasDerivAt_tsum_expI s hs0 hs1 θ
  -- the relation `i k b_{|k|} = -(i L / 2) (c_{|k+1|} - c_{|k-1|})` for all `k ∈ ℤ`
  have hrel : ∀ k : ℤ, Complex.I * k * s k = -(Complex.I * L / 2) * (σ (k + 1) - σ (k - 1)) := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩ <;> rcases m with _ | m
    · simp [hσ]
    · have h := hbc (m + 1) (by omega)
      rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega] at h
      have h' : 2 * ((m + 1 : ℕ) : ℂ) * (b (m + 1) : ℂ) = (L : ℂ) * ((c m : ℂ) - (c (m + 2) : ℂ)) := by
        exact_mod_cast h
      simp only [hs, hσ]
      rw [show (((m + 1 : ℕ) : ℤ) + 1).natAbs = m + 2 by omega,
        show (((m + 1 : ℕ) : ℤ) - 1).natAbs = m by omega, Int.natAbs_natCast]
      push_cast at h' ⊢
      linear_combination (Complex.I / 2) * h'
    · simp [hσ]
    · have h := hbc (m + 1) (by omega)
      rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega] at h
      have h' : 2 * ((m + 1 : ℕ) : ℂ) * (b (m + 1) : ℂ) = (L : ℂ) * ((c m : ℂ) - (c (m + 2) : ℂ)) := by
        exact_mod_cast h
      simp only [hs, hσ]
      rw [show (-((m + 1 : ℕ) : ℤ) + 1).natAbs = m by omega,
        show (-((m + 1 : ℕ) : ℤ) - 1).natAbs = m + 2 by omega,
        show (-((m + 1 : ℕ) : ℤ)).natAbs = m + 1 by omega]
      push_cast at h' ⊢
      linear_combination (-(Complex.I / 2)) * h'
  -- the shifts `k ↦ k ± 1` multiply `U_c` by `e^{∓iθ}`
  set g : ℤ → ℂ := fun k => σ k * expI θ k with hg
  have hgs : Summable g := Summable.of_norm (by
    simpa [hg, hσ, norm_mul, norm_expI, Complex.norm_real] using Fourier.summable_int_natAbs hc)
  have hA' : ∀ k : ℤ, σ (k + 1) * expI θ k = expI θ (-1) * g (k + 1) := fun k => by
    rw [hg, show expI θ k = expI θ (-1) * expI θ (k + 1) by rw [← expI_add]; congr 1; ring]
    ring
  have hB' : ∀ k : ℤ, σ (k - 1) * expI θ k = expI θ 1 * g (k - 1) := fun k => by
    rw [hg, show expI θ k = expI θ 1 * expI θ (k - 1) by rw [← expI_add]; congr 1; ring]
    ring
  have hAs : Summable fun k : ℤ => σ (k + 1) * expI θ k := by
    simp only [hA']
    exact (hgs.comp_injective (add_left_injective 1)).mul_left _
  have hBs : Summable fun k : ℤ => σ (k - 1) * expI θ k := by
    simp only [hB']
    exact (hgs.comp_injective (sub_left_injective (b := 1))).mul_left _
  have hA : ∑' k : ℤ, σ (k + 1) * expI θ k = expI θ (-1) * cosFun c θ := by
    have he : ∑' k : ℤ, g (k + 1) = ∑' k : ℤ, g k := (Equiv.addRight (1 : ℤ)).tsum_eq g
    rw [tsum_congr hA', tsum_mul_left, he]
    rfl
  have hB : ∑' k : ℤ, σ (k - 1) * expI θ k = expI θ 1 * cosFun c θ := by
    have he : ∑' k : ℤ, g (k - 1) = ∑' k : ℤ, g k := (Equiv.subRight (1 : ℤ)).tsum_eq g
    rw [tsum_congr hB', tsum_mul_left, he]
    rfl
  have hsin : (expI θ (-1) - expI θ 1) * Complex.I = 2 * (Real.sin θ : ℂ) := by
    rw [Complex.ofReal_sin, Complex.two_sin]
    simp [expI]
  have hsum : ∑' k : ℤ, Complex.I * k * s k * expI θ k =
      -(Complex.I * L / 2) * (expI θ (-1) - expI θ 1) * cosFun c θ := by
    calc ∑' k : ℤ, Complex.I * k * s k * expI θ k
        = ∑' k : ℤ, -(Complex.I * L / 2) * (σ (k + 1) * expI θ k - σ (k - 1) * expI θ k) :=
          tsum_congr fun k => by rw [hrel]; ring
      _ = -(Complex.I * L / 2) * (expI θ (-1) * cosFun c θ - expI θ 1 * cosFun c θ) := by
          rw [tsum_mul_left, hAs.tsum_sub hBs, hA, hB]
      _ = _ := by ring
  refine hd.congr_deriv ?_
  rw [hsum]
  linear_combination (-(L : ℂ) / 2 * cosFun c θ) * hsin

/-- `u_b' = L u_c` on `(-1, 1)` when `2k b_k = L (c_{k-1} - c_{k+1})` for `k ≥ 1`. -/
theorem hasDerivAt_chebSeries (hc : Summable fun n => |c n|)
    (hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = L * (c (k - 1) - c (k + 1))) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) : HasDerivAt (chebSeries b) (L * chebSeries c t) t := by
  have hb := summable_abs_of_rel hc hbc
  have h1 := (hasDerivAt_cosFun hc hbc (Real.arccos t)).scomp t
    (Real.hasDerivAt_arccos ht.1.ne' ht.2.ne)
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have heq : chebSeries b =ᶠ[𝓝 t] (Complex.reCLM ∘ (cosFun b ∘ Real.arccos)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    simp only [Function.comp, Complex.reCLM_apply]
    exact chebSeries_eq_re hb (Ioo_subset_Icc_self hx)
  refine (h2.congr_of_eventuallyEq heq).congr_deriv ?_
  have hr : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])
  have hr' : (√(1 - t ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Real.sin_arccos, chebSeries_eq_re hc (Ioo_subset_Icc_self ht), Complex.reCLM_apply,
    Complex.smul_re, show -((L : ℂ) * (√(1 - t ^ 2) : ℂ)) = ((-(L * √(1 - t ^ 2)) : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul, smul_eq_mul]
  field_simp

/-- `u_b' = L u_c` on `[-1, 1]` (one-sided at the endpoints) when `2k b_k = L (c_{k-1} - c_{k+1})`
for `k ≥ 1`. -/
theorem hasDerivWithinAt_chebSeries (hc : Summable fun n => |c n|)
    (hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = L * (c (k - 1) - c (k + 1))) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasDerivWithinAt (chebSeries b) (L * chebSeries c t) (Icc (-1) 1) t := by
  have hb := summable_abs_of_rel hc hbc
  have hd : DifferentiableOn ℝ (chebSeries b) (Ioo (-1) 1) := fun x hx =>
    (hasDerivAt_chebSeries hc hbc hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1, L * chebSeries c x = deriv (chebSeries b) x := fun x hx =>
    (hasDerivAt_chebSeries hc hbc hx).deriv.symm
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h
    have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝[>] (-1) := Ioo_mem_nhdsGT (by norm_num)
    have hcont : ContinuousWithinAt (chebSeries b) (Ioo (-1) 1) (-1) :=
      (continuousOn_chebSeries hb (-1) hm1).mono Ioo_subset_Icc_self
    have hc' : ContinuousWithinAt (chebSeries c) (Ioi (-1)) (-1) :=
      (((continuousOn_chebSeries hc) (-1) hm1).mono Ioo_subset_Icc_self).mono_of_mem_nhdsWithin hs
    have hlim : Tendsto (deriv (chebSeries b)) (𝓝[>] (-1)) (𝓝 (L * chebSeries c (-1))) :=
      (hc'.tendsto.const_mul L).congr' (eventually_of_mem hs hderiv)
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hd hcont hs hlim).mono Icc_subset_Ici_self
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · subst h'
    have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT (by norm_num)
    have hcont : ContinuousWithinAt (chebSeries b) (Ioo (-1) 1) 1 :=
      (continuousOn_chebSeries hb 1 hp1).mono Ioo_subset_Icc_self
    have hc' : ContinuousWithinAt (chebSeries c) (Iio 1) 1 :=
      (((continuousOn_chebSeries hc) 1 hp1).mono Ioo_subset_Icc_self).mono_of_mem_nhdsWithin hs
    have hlim : Tendsto (deriv (chebSeries b)) (𝓝[<] 1) (𝓝 (L * chebSeries c 1)) :=
      (hc'.tendsto.const_mul L).congr' (eventually_of_mem hs hderiv)
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hd hcont hs hlim).mono Icc_subset_Iic_self
  · exact (hasDerivAt_chebSeries hc hbc ⟨h, h'⟩).hasDerivWithinAt

end Deriv

/-- Integration of a Chebyshev series: `∫_{-1}^t u_c = γ + 2 ∑_{k ≥ 1} (c_{k-1} - c_{k+1})/(2k) T_k(t)`
on `[-1, 1]`. -/
theorem integral_chebSeries {c : ℕ → ℝ} (hc : Summable fun n => |c n|) :
    ∃ γ : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1, ∫ s in (-1)..t, chebSeries c s =
      γ + 2 * ∑' k : ℕ, (c k - c (k + 2)) / (2 * (k + 1)) *
        (Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval t := by
  set b : ℕ → ℝ := fun k => if k = 0 then 0 else (c (k - 1) - c (k + 1)) / (2 * k) with hbdef
  have hbc : ∀ k : ℕ, k ≠ 0 → 2 * k * b k = 1 * (c (k - 1) - c (k + 1)) := fun k hk => by
    have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
    simp only [hbdef, hk, ↓reduceIte]
    field_simp
  have hb' : ∀ k : ℕ, b (k + 1) = (c k - c (k + 2)) / (2 * (k + 1)) := fun k => by
    simp only [hbdef, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    push_cast
    ring_nf
  refine ⟨-chebSeries b (-1), fun t ht => ?_⟩
  have hsub : Icc (-1 : ℝ) t ⊆ Icc (-1) 1 := Icc_subset_Icc_right ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((continuousOn_chebSeries (summable_abs_of_rel hc hbc)).mono hsub)
    (fun x hx => by simpa using hasDerivAt_chebSeries hc hbc ⟨hx.1, hx.2.trans_le ht.2⟩)
    ((continuousOn_chebSeries hc).mono (by rw [uIcc_of_le ht.1]; exact hsub)).intervalIntegrable]
  rw [chebSeries, show b 0 = 0 by simp [hbdef]]
  simp only [hb']
  ring

/-! ### Chebyshev sequences -/

variable {ν : ℝ} {hν : 1 ≤ ν}

theorem one_le_weights (k : ℕ) : 1 ≤ weights ν hν k := by
  rw [weights_apply]
  split_ifs
  · exact le_rfl
  · nlinarith [one_le_pow₀ (n := k) hν]

theorem summable_abs (a : X ν hν) : Summable fun n => |a n| :=
  Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => by
    rw [← Real.norm_eq_abs]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_weights n)) a.summable

/-- `|u_a(t)| ≤ ‖a‖_ν` on `[-1, 1]`. -/
theorem abs_chebSeries_le_norm (a : X ν hν) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |chebSeries a t| ≤ ‖a‖ := by
  refine (abs_chebSeries_le (summable_abs a) ht).trans ?_
  rw [WeightedL1.norm_eq_tsum, a.summable.tsum_eq_zero_add, weights_zero, one_mul,
    Real.norm_eq_abs, ← tsum_mul_left]
  refine add_le_add le_rfl (Summable.tsum_le_tsum (fun k => ?_)
    (((summable_nat_add_iff 1).2 (summable_abs a)).mul_left 2)
    ((summable_nat_add_iff 1).2 a.summable))
  show 2 * |a (k + 1)| ≤ weights ν hν (k + 1) * ‖a (k + 1)‖
  rw [weights_succ, Real.norm_eq_abs]
  nlinarith [one_le_pow₀ (n := k + 1) hν, abs_nonneg (a (k + 1))]

theorem chebSeries_sub_X (a b : X ν hν) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    chebSeries (a - b : X ν hν) t = chebSeries a t - chebSeries b t := by
  rw [show ⇑(a - b) = ⇑a - ⇑b from funext fun k => WeightedLp.sub_apply a b k]
  exact chebSeries_sub (summable_abs a) (summable_abs b) ht

variable (ν hν) in
/-- Evaluation at `θ` of the Fourier series of the symmetric extension, `a ↦ U_a(θ)`: an algebra
homomorphism `X_ν → ℂ`. -/
noncomputable def thetaEval (θ : ℝ) : X ν hν →ₐ[ℝ] ℂ where
  toFun a := Fourier.fourierEval ν hν θ (Fourier.ofRealX ν hν (symExt a))
  map_one' := by simp only [symExt_one, Fourier.ofRealX_one, map_one]
  map_mul' a b := by simp only [symExt_mul, Fourier.ofRealX_mul, map_mul]
  map_zero' := by rw [symExt_zero]; simp [Fourier.fourierEval_apply]
  map_add' a b := by simp only [symExt_add, Fourier.ofRealX_add, map_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, symExt_smul, symExt_one, Fourier.ofRealX_smul,
      Fourier.ofRealX_one, map_smul, map_one]
    simp

theorem thetaEval_apply (θ : ℝ) (a : X ν hν) : thetaEval ν hν θ a = cosFun a θ := rfl

/-- The Chebyshev product is the product of functions: `u_{a * b}(t) = u_a(t) u_b(t)`. -/
theorem chebSeries_mul (a b : X ν hν) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    chebSeries (a * b : X ν hν) t = chebSeries a t * chebSeries b t := by
  apply Complex.ofReal_injective
  rw [← Real.cos_arccos ht.1 ht.2, Complex.ofReal_mul]
  simp only [chebSeries_cos (summable_abs _)]
  exact map_mul (thetaEval ν hν (Real.arccos t)) a b

/-- The Chebyshev product is the product of functions: `u_{P(a)}(t) = P(u_{a_1}(t), …)`. -/
theorem chebSeries_aeval {n : ℕ} (a : Fin n → X ν hν) (p : MvPolynomial (Fin n) ℝ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    chebSeries (MvPolynomial.aeval a p) t = MvPolynomial.eval (fun i => chebSeries (a i) t) p := by
  apply Complex.ofReal_injective
  rw [← Real.cos_arccos ht.1 ht.2]
  set θ := Real.arccos t
  have hi : (fun i => thetaEval ν hν θ (a i)) =
      (algebraMap ℝ ℂ ∘ fun i => chebSeries (a i) (Real.cos θ)) :=
    funext fun i => (chebSeries_cos (summable_abs (a i)) θ).symm
  calc (chebSeries (MvPolynomial.aeval a p) (Real.cos θ) : ℂ)
      = thetaEval ν hν θ (MvPolynomial.aeval a p) := chebSeries_cos (summable_abs _) θ
    _ = MvPolynomial.aeval (fun i => thetaEval ν hν θ (a i)) p :=
        MvPolynomial.comp_aeval_apply a (thetaEval ν hν θ) p
    _ = _ := by
        have h := MvPolynomial.comp_aeval_apply (fun i => chebSeries (a i) (Real.cos θ))
          (Algebra.ofId ℝ ℂ) p
        simp only [Algebra.ofId_apply] at h
        rw [hi]
        exact h.symm

end Chebyshev

end RadiiPolynomial
