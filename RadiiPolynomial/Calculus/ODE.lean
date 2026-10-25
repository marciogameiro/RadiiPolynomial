module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Uniqueness of solutions of autonomous ODEs

`eqOn_Ioo_of_lipschitzOnWith_closedBall`: if the vector field `v` is Lipschitz on every closed ball
about `0` (for instance a polynomial vector field), then two solutions of `x' = v(x)` on an open
interval that agree at one time agree on the whole interval. Between the two times both
trajectories stay in a closed ball (they are continuous on a compact interval), where `v` is
Lipschitz, and Grönwall's inequality (Mathlib's `ODE_solution_unique_of_mem_Icc_right` and
`ODE_solution_unique_of_mem_Icc_left`) applies forward and backward in time.

`eqOn_Icc_of_lipschitzOnWith_closedBall`: the same on a closed interval `[a, b]`, for solutions with
one-sided derivatives at the endpoints that agree at `t = a`.
-/

@[expose] public section

namespace RadiiPolynomial

open Set Metric Filter Topology

/-- Uniqueness of solutions of `x' = v(x)` on an open interval, for `v` Lipschitz on every closed
ball about `0`. -/
theorem eqOn_Ioo_of_lipschitzOnWith_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ∀ R, ∃ K, LipschitzOnWith K v (closedBall 0 R))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {f g : ℝ → E}
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t) (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v (g t)) t)
    (heq : f t₀ = g t₀) : EqOn f g (Ioo a b) := by
  intro t ht
  set I := Icc (min t₀ t) (max t₀ t) with hIdef
  have hI : I ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le (lt_min ht₀.1 ht.1) hs.1, lt_of_le_of_lt hs.2 (max_lt ht₀.2 ht.2)⟩
  have hfc : ContinuousOn f I := fun s hs => (hf s (hI hs)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g I := fun s hs => (hg s (hI hs)).continuousAt.continuousWithinAt
  obtain ⟨Rf, hRf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Rg, hRg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK⟩ := hv (max Rf Rg)
  have hfs : ∀ s ∈ I, f s ∈ closedBall 0 (max Rf Rg) := fun s hs =>
    mem_closedBall_zero_iff.2 ((hRf s hs).trans (le_max_left _ _))
  have hgs : ∀ s ∈ I, g s ∈ closedBall 0 (max Rf Rg) := fun s hs =>
    mem_closedBall_zero_iff.2 ((hRg s hs).trans (le_max_right _ _))
  rcases le_total t₀ t with h | h
  · have hsub : Icc t₀ t ⊆ I := by
      rw [hIdef, min_eq_left h, max_eq_right h]
    have hsub' : Ico t₀ t ⊆ I := Ico_subset_Icc_self.trans hsub
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v)
      (s := fun _ => closedBall 0 (max Rf Rg)) (fun _ _ => hK) (hfc.mono hsub)
      (fun s hs => (hf s (hI (hsub' hs))).hasDerivWithinAt) (fun s hs => hfs s (hsub' hs))
      (hgc.mono hsub) (fun s hs => (hg s (hI (hsub' hs))).hasDerivWithinAt)
      (fun s hs => hgs s (hsub' hs)) heq ⟨h, le_rfl⟩
  · have hsub : Icc t t₀ ⊆ I := by
      rw [hIdef, min_eq_right h, max_eq_left h]
    have hsub' : Ioc t t₀ ⊆ I := Ioc_subset_Icc_self.trans hsub
    exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => v)
      (s := fun _ => closedBall 0 (max Rf Rg)) (fun _ _ => hK) (hfc.mono hsub)
      (fun s hs => (hf s (hI (hsub' hs))).hasDerivWithinAt) (fun s hs => hfs s (hsub' hs))
      (hgc.mono hsub) (fun s hs => (hg s (hI (hsub' hs))).hasDerivWithinAt)
      (fun s hs => hgs s (hsub' hs)) heq ⟨le_rfl, h⟩

/-- Uniqueness of solutions of `x' = v(x)` on a closed interval `[a, b]` with the same value at `a`
(derivatives within `[a, b]`), for `v` Lipschitz on every closed ball about `0`. -/
theorem eqOn_Icc_of_lipschitzOnWith_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : ∀ R, ∃ K, LipschitzOnWith K v (closedBall 0 R))
    {a b : ℝ} {f g : ℝ → E} (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (v (f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (v (g t)) (Icc a b) t) (heq : f a = g a) :
    EqOn f g (Icc a b) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousWithinAt
  obtain ⟨Rf, hRf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Rg, hRg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK⟩ := hv (max Rf Rg)
  have hI : ∀ t ∈ Ico a b, Icc a b ∈ 𝓝[≥] t := fun t ht => Icc_mem_nhdsGE_of_mem ht
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v)
    (s := fun _ => closedBall 0 (max Rf Rg)) (fun _ _ => hK) hfc
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hI t ht))
    (fun t ht => mem_closedBall_zero_iff.2
      ((hRf t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)))
    hgc (fun t ht => (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hI t ht))
    (fun t ht => mem_closedBall_zero_iff.2
      ((hRg t (Ico_subset_Icc_self ht)).trans (le_max_right _ _))) heq

end RadiiPolynomial
