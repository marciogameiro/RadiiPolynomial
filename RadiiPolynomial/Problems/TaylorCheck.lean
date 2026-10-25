module

public import RadiiPolynomial.Problems.TaylorRadii
public import RadiiPolynomial.Certificate.TaylorSeq
public import RadiiPolynomial.Certificate.Exact

/-!
# A computable checker for Taylor initial value problems

`TaylorData n` holds rational data: the polynomial vector field, the time scale `τ`, the initial
value `x₀`, the truncation `N`, the weight `ν`, the approximate solution `ā` (finite Taylor
sequences), the matrix `A^{(N)}`, the radii `r₀ ≤ r₁` and a degree bound `M`. From these data the
checker computes exactly (in `ℚ`) all quantities of the bound theorem
`TaylorIVP.radii_poly_two_radii`: `F(ā)`, the entries of `DF^{(N)}(ā)`, `E = I - A^{(N)} DF^{(N)}(ā)`,
the column maxima `K`, `bʲⁱ = ∂ᵢφ_j(ā)`, `Θᵢ(r)`, and the bounds `Y₀`, `Z₀`, `Z₁`, `Z₂(r)`.
`TaylorData.check` then only compares numbers: `p(r₀) < 0`, `p(r₁) < 0` and a few structural
conditions.

`TaylorData.verify`: if `D.check` holds, the initial value problem has a zero of `F` in the open
ball of radius `r₀` about `ā`, unique in the closed ball of radius `r₁`. The check is decidable; it
can be evaluated by the kernel (`decide +kernel`) or, for large data, by compiled code
(`native_decide`).
-/

@[expose] public section

namespace RadiiPolynomial

open TaySeq
open FinSeq (get)

/-- Rational data for a Taylor initial value problem and its approximate solution. -/
structure TaylorData (n : ℕ) where
  /-- the polynomial vector field -/
  f : Fin n → PolyData n
  /-- the time scale -/
  τ : ℚ
  /-- the initial value -/
  x₀ : Fin n → ℚ
  /-- the truncation -/
  N : ℕ
  /-- the weight `ν > 0` -/
  ν : ℚ
  /-- a bound for the degree of `f` -/
  M : ℕ
  /-- the approximate solution: Taylor coefficients `0, …, N` of each component -/
  abar : Fin n → List ℚ
  /-- the approximate inverse `A^{(N)}`, indexed by `(j, m), (i, l)` with `m, l ≤ N` -/
  A : Fin n → ℕ → Fin n → ℕ → ℚ
  /-- the radius `r₀` (existence) -/
  r0 : ℚ
  /-- the radius `r₁` (uniqueness) -/
  r1 : ℚ

namespace TaylorData

variable {n : ℕ} (D : TaylorData n)

/-- The weights `ν^k`. -/
def wX (k : ℕ) : ℚ := D.ν ^ k

/-- The finite part `{0, …, N}`. -/
def fin : Finset ℕ := Finset.range (D.N + 1)

/-- `c_j = φ_j(ā)`. -/
def phi (j : Fin n) : List ℚ := evalPoly (D.f j) D.abar

/-- `bʲⁱ = ∂ᵢφ_j(ā)`. -/
def bseq (j i : Fin n) : List ℚ := evalPoly ((D.f j).pderiv i) D.abar

/-- `F(ā)_{j,k}`, from `φ(ā)`. -/
def FvalWith (phi : Fin n → List ℚ) (j : Fin n) (k : ℕ) : ℚ :=
  if k = 0 then get (D.abar j) 0 - D.x₀ j
  else k * get (D.abar j) k - D.τ * get (phi j) (k - 1)

/-- The entries `(DF(ā) e_{i,l})_{j,m}`, from the `bʲⁱ`. -/
def DFWith (bs : Fin n → Fin n → List ℚ) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℚ :=
  (if m = 0 then 1 else (m : ℚ)) * (if j = i ∧ m = l then 1 else 0) -
    D.τ * (if m = 0 then 0 else mulUnit (bs j i) l (m - 1))

/-- The quantities from which the bounds are computed: `φ(ā)`, the `bʲⁱ`, `F(ā)` and the entries of
`DF(ā)`. They are computed either directly (`direct`, used in the proofs) or from precomputed
tables (`fast`, used by the checker); `fast_eq` shows that both agree. -/
structure Impl (n : ℕ) where
  /-- `φ(ā)` -/
  phi : Fin n → List ℚ
  /-- `bʲⁱ` -/
  bs : Fin n → Fin n → List ℚ
  /-- `F(ā)` -/
  Fv : Fin n → ℕ → ℚ
  /-- the entries of `DF(ā)` -/
  DF : Fin n → ℕ → Fin n → ℕ → ℚ

/-- The direct definitions. -/
def direct : Impl n :=
  ⟨D.phi, D.bseq, D.FvalWith D.phi, D.DFWith D.bseq⟩

/-- The largest index of `F(ā)` that the bounds use. -/
def Kmax : ℕ := D.M * D.N + 1

/-- Precomputed tables: each quantity is computed once. -/
def fast : Impl n :=
  let phiT : Array (List ℚ) := Array.ofFn fun j : Fin n => D.phi j
  let bsT : Array (List ℚ) := Array.ofFn fun ji : Fin (n * n) =>
    D.bseq (finProdFinEquiv.symm ji).1 (finProdFinEquiv.symm ji).2
  let phiF : Fin n → List ℚ := fun j => phiT.getD j.val []
  let bsF : Fin n → Fin n → List ℚ := fun j i => bsT.getD (finProdFinEquiv (j, i)).val []
  let FvT : Array ℚ := Array.ofFn fun jk : Fin (n * (D.Kmax + 1)) =>
    D.FvalWith phiF (finProdFinEquiv.symm jk).1 (finProdFinEquiv.symm jk).2
  let DFT : Array ℚ := Array.ofFn fun x : Fin ((n * (D.N + 1)) * (n * (D.N + 1))) =>
    let jm := finProdFinEquiv.symm (finProdFinEquiv.symm x).1
    let il := finProdFinEquiv.symm (finProdFinEquiv.symm x).2
    D.DFWith bsF jm.1 jm.2 il.1 il.2
  ⟨phiF, bsF,
    fun j k => if hk : k < D.Kmax + 1 then FvT.getD (finProdFinEquiv (j, ⟨k, hk⟩)).val 0
      else D.FvalWith phiF j k,
    fun j m i l => if h : m < D.N + 1 ∧ l < D.N + 1 then
      DFT.getD (finProdFinEquiv (finProdFinEquiv (j, ⟨m, h.1⟩), finProdFinEquiv (i, ⟨l, h.2⟩))).val 0
      else D.DFWith bsF j m i l⟩

/-- `E = I - A^{(N)} DF^{(N)}(ā)`. -/
def Eq (I : Impl n) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℚ :=
  (if j = i ∧ m = l then 1 else 0) - ∑ i', ∑ l' ∈ D.fin, D.A j m i' l' * I.DF i' l' i l

/-- `K^E_{ji} = max_{l ≤ N} ν^{-l} ∑_{m ≤ N} |E_{(j,m),(i,l)}| ν^m`. -/
def KE (I : Impl n) (j i : Fin n) : ℚ :=
  maxOver D.fin fun l => (∑ m ∈ D.fin, |D.Eq I j m i l| * D.wX m) / D.wX l

/-- `K_{ji} = max {max_{l ≤ N} ν^{-l} ∑_{m ≤ N} |A^{(N)}_{(j,m),(i,l)}| ν^m, δ_{ji} / (N + 1)}`. -/
def KA (j i : Fin n) : ℚ :=
  max (maxOver D.fin fun l => (∑ m ∈ D.fin, |D.A j m i l| * D.wX m) / D.wX l)
    (if j = i then ((D.N : ℚ) + 1)⁻¹ else 0)

/-- `Θᵢ(r) = ∑_{l,m} |∂_l ∂_m fᵢ|(‖ā₁‖ + r, …, ‖āₙ‖ + r)`. -/
def Theta (i : Fin n) (r : ℚ) : ℚ :=
  ∑ l, ∑ m, PolyData.absEval (((D.f i).pderiv m).pderiv l) fun k => normX D.ν (D.abar k) + r

/-- The bound `Y₀`. -/
def Y0 (I : Impl n) : ℚ :=
  finMax fun j =>
    ∑ k ∈ D.fin, |∑ i, ∑ l ∈ D.fin, D.A j k i l * I.Fv i l| * D.wX k +
      ∑ k ∈ Finset.Ico (D.N + 1) (D.M * D.N + 2), |I.Fv j k| * (D.ν ^ k / k)

/-- The bound `Z₀`. -/
def Z0 (I : Impl n) : ℚ := finMax fun j => ∑ i, D.KE I j i

/-- The bound `Z₁`. -/
def Z1 (I : Impl n) : ℚ :=
  finMax fun j => |D.τ| * D.ν / (D.N + 1) * ∑ i, normX D.ν (I.bs j i)

/-- The bound `Z₂(r)`. -/
def Z2 (r : ℚ) : ℚ :=
  finMax fun j => |D.τ| * D.ν * ∑ i, D.KA j i * D.Theta i r

/-- The conditions on the computed bounds. -/
def checkWith (I : Impl n) : Prop :=
  0 < D.ν ∧ 1 ≤ D.M ∧ (∀ j, (D.f j).degree ≤ D.M) ∧
    (∀ i, (D.abar i).length ≤ D.N + 1) ∧ 0 < D.r0 ∧ D.r0 ≤ D.r1 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0

instance (I : Impl n) : Decidable (D.checkWith I) := by unfold checkWith; infer_instance

/-- The check, with the precomputed tables. -/
def check : Prop := D.checkWith D.fast

instance : Decidable D.check := by unfold check; infer_instance

/-- The exact inverse of `DF^{(N)}(ā)`. With the indices ordered by `(m, j) ↦ m n + j`, the
matrix `DF^{(N)}(ā)` is lower triangular with diagonal `1, …, 1, 1, …, 1, 2, …, N`
(`TaylorIVP.DFN_eq_zero`), so it is inverted by forward substitution (`lowerTriInv`). -/
def exactInverse : Array (Array ℚ) :=
  let I := D.fast
  lowerTriInv (n * (D.N + 1) - 1) fun u v =>
    if h : u % n < n ∧ v % n < n then I.DF ⟨u % n, h.1⟩ (u / n) ⟨v % n, h.2⟩ (v / n) else 0

/-- The data with `A^{(N)}` replaced by the exact inverse of `DF^{(N)}(ā)` (then `Z₀ = 0`). -/
def withExactInverse : TaylorData n :=
  let Ainv := D.exactInverse
  { D with A := fun j m i l => (Ainv.getD (m * n + j) #[]).getD (l * n + i) 0 }


/-! ### Soundness: tables -/

/-- The precomputed tables agree with the direct definitions. -/
theorem fast_eq : D.fast = D.direct := by
  have hphi : (fun j : Fin n => (Array.ofFn fun j : Fin n => D.phi j).getD j.val []) = D.phi :=
    funext fun j => getD_ofFn _ j []
  have hbs : (fun j i : Fin n => (Array.ofFn fun ji : Fin (n * n) =>
      D.bseq (finProdFinEquiv.symm ji).1 (finProdFinEquiv.symm ji).2).getD
        (finProdFinEquiv (j, i)).val []) = D.bseq :=
    funext fun j => funext fun i => by rw [getD_ofFn]; simp
  simp only [fast, direct, hphi, hbs]
  congr 1
  · funext j k
    split_ifs with hk
    · rw [getD_ofFn]; simp
    · rfl
  · funext j m i l
    split_ifs with h
    · rw [getD_ofFn]; simp
    · rfl

/-! ### Soundness: the real problem -/

/-- The initial value problem with the data cast to `ℝ`. -/
noncomputable def toIVP : TaylorIVP n :=
  ⟨fun j => (D.f j).toMv, D.τ, fun j => D.x₀ j⟩

theorem toIVP_withExactInverse : D.withExactInverse.toIVP = D.toIVP := rfl

variable (hν : 0 < (D.ν : ℝ))

theorem phi_sound (j : Fin n) :
    MvPolynomial.aeval (toXVec D.abar : Fin n → Taylor.X (D.ν : ℝ) hν) (D.toIVP.f j) =
      toX (D.phi j) :=
  (toX_evalPoly _ _).symm

theorem bseq_sound (j i : Fin n) :
    D.toIVP.bmat (D.ν : ℝ) hν (toXVec D.abar) j i = toX (D.bseq j i) := by
  rw [TaylorIVP.bmat, bseq, toX_evalPoly]
  simp only [toIVP, PolyData.toMv_pderiv]
  rfl

theorem norm_bseq (j i : Fin n) :
    ‖D.toIVP.bmat (D.ν : ℝ) hν (toXVec D.abar) j i‖ = (normX D.ν (D.bseq j i) : ℝ) := by
  rw [bseq_sound, norm_toX D.ν rfl]

theorem norm_abarX (k : Fin n) :
    ‖(toXVec D.abar : Fin n → Taylor.X (D.ν : ℝ) hν) k‖ = (normX D.ν (D.abar k) : ℝ) :=
  norm_toX D.ν rfl _

theorem F_sound (j : Fin n) (k : ℕ) :
    D.toIVP.F (D.ν : ℝ) hν (toXVec D.abar) j k = (D.FvalWith D.phi j k : ℝ) := by
  by_cases hk : k = 0
  · subst hk
    rw [TaylorIVP.F_apply_zero, FvalWith, ite_eq_left rfl]
    push_cast
    rfl
  · rw [TaylorIVP.F_apply_of_ne_zero _ _ _ _ _ hk, FvalWith, ite_eq_right hk]
    rw [show MvPolynomial.aeval (toXVec D.abar) (D.toIVP.f j) = toX (D.phi j) from
      D.phi_sound hν j]
    push_cast
    rfl

theorem DF_sound (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) :
    D.toIVP.DFN (D.ν : ℝ) hν (toXVec D.abar) j m i l = (D.DFWith D.bseq j m i l : ℝ) := by
  rw [TaylorIVP.DFN, TaylorIVP.DF_apply_coeff, TaylorIVP.unitVec_apply,
    TaylorIVP.polyDeriv_unitVec, bseq_sound, toX_mul_single, DFWith]
  simp only [toIVP]
  split_ifs <;> push_cast <;> ring

theorem normX_nonneg (hνq : 0 ≤ D.ν) (a : List ℚ) : 0 ≤ normX D.ν a :=
  Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hνq k) (abs_nonneg _)

theorem Theta_sound (hνq : 0 ≤ D.ν) (i : Fin n) {rq : ℚ} (hr : 0 ≤ rq) :
    D.toIVP.Theta (D.ν : ℝ) hν (toXVec D.abar) i rq ≤ (D.Theta i rq : ℝ) := by
  rw [TaylorIVP.Theta, Theta]
  push_cast
  refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => ?_
  have hx : (fun k => ‖(toXVec D.abar : Fin n → Taylor.X (D.ν : ℝ) hν) k‖ + (rq : ℝ)) =
      fun k => ((normX D.ν (D.abar k) + rq : ℚ) : ℝ) := by
    funext k; rw [norm_abarX]; push_cast; rfl
  simp only [toIVP]
  rw [hx, PolyData.toMv_pderiv, PolyData.toMv_pderiv]
  exact PolyData.absEval_toMv_le _ _ fun k => add_nonneg (D.normX_nonneg hνq _) hr

theorem matE_sound (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) :
    D.toIVP.matE (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (toXVec D.abar) j m i l =
      (D.Eq D.direct j m i l : ℝ) := by
  rw [TaylorIVP.matE, Eq]
  push_cast
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => by
      rw [DF_sound]; rfl

/-- **The checker is sound.** If `D.check` holds, then `F` has a zero in the open ball of radius
`r₀` about `ā`, and it is the unique zero in the closed ball of radius `r₁`. -/
theorem verify [NeZero n] (h : D.check) :
    HasIsolatedZero (D.toIVP.F (D.ν : ℝ) hν) (toXVec D.abar) D.r0 D.r1 := by
  rw [check, fast_eq] at h
  obtain ⟨hν0, hM, hdeg, hlen, hr0, hr01, hp0, hp1⟩ := h
  have hνq : 0 ≤ D.ν := hν0.le
  have hwX : ∀ k, 0 < D.wX k := fun k => pow_pos hν0 k
  have hwXeq : ∀ k, (D.ν : ℝ) ^ k = (D.wX k : ℝ) := fun k => by rw [wX]; push_cast; rfl
  set I := D.direct
  have habar : ∀ i, Taylor.SuppLe ((toXVec D.abar : Fin n → Taylor.X (D.ν : ℝ) hν) i) D.N :=
    fun i => (suppLe_toX _).mono (by have := hlen i; omega)
  have hdeg' : ∀ j, (D.toIVP.f j).totalDegree ≤ D.M := fun j =>
    (PolyData.totalDegree_toMv_le _).trans (hdeg j)
  -- `Y₀`
  have hY : ∀ j, ∑ k ∈ Finset.range (D.N + 1),
      |∑ i, ∑ l ∈ Finset.range (D.N + 1), (D.A j k i l : ℝ) *
        D.toIVP.F (D.ν : ℝ) hν (toXVec D.abar) i l| * (D.ν : ℝ) ^ k +
      ∑ k ∈ Finset.Ico (D.N + 1) (D.M * D.N + 2),
        |D.toIVP.F (D.ν : ℝ) hν (toXVec D.abar) j k| * ((D.ν : ℝ) ^ k / k) ≤ (D.Y0 I : ℝ) := by
    intro j
    simp only [F_sound, hwXeq]
    have := le_finMax (f := fun j => ∑ k ∈ D.fin, |∑ i, ∑ l ∈ D.fin, D.A j k i l * I.Fv i l| *
      D.wX k + ∑ k ∈ Finset.Ico (D.N + 1) (D.M * D.N + 2), |I.Fv j k| * (D.ν ^ k / k)) j
    simp only [wX] at this ⊢
    exact_mod_cast this
  -- `Z₀`
  have hKE0 : ∀ j i, (0 : ℝ) ≤ (D.KE I j i : ℝ) := fun j i => by
    exact_mod_cast maxOver_nonneg _ _
  have hKE : ∀ j i, ∀ l ∈ Finset.range (D.N + 1), ∑ m ∈ Finset.range (D.N + 1),
      |D.toIVP.matE (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (toXVec D.abar) j m i l| *
        (D.ν : ℝ) ^ m ≤ (D.KE I j i : ℝ) * (D.ν : ℝ) ^ l := by
    intro j i l hl
    simp only [matE_sound, hwXeq]
    have := le_mul_of_div_le (hwX l) (le_maxOver (g := fun l =>
      (∑ m ∈ D.fin, |D.Eq I j m i l| * D.wX m) / D.wX l) hl)
    exact_mod_cast this
  have hZ0 : ∀ j, ∑ i, (D.KE I j i : ℝ) ≤ (D.Z0 I : ℝ) := fun j => by
    exact_mod_cast le_finMax (f := fun j => ∑ i, D.KE I j i) j
  -- `Z₁`
  have hZ1 : ∀ j, |D.toIVP.τ| * (D.ν : ℝ) / (D.N + 1) *
      ∑ i, ‖D.toIVP.bmat (D.ν : ℝ) hν (toXVec D.abar) j i‖ ≤ (D.Z1 I : ℝ) := by
    intro j
    simp only [norm_bseq]
    have h' : |D.τ| * D.ν / (D.N + 1) * ∑ i, normX D.ν (D.bseq j i) ≤ D.Z1 I :=
      le_finMax (f := fun j => |D.τ| * D.ν / (D.N + 1) * ∑ i, normX D.ν (I.bs j i)) j
    simp only [toIVP]
    exact_mod_cast h'
  -- `Z₂`
  have hKA0 : ∀ j i, (0 : ℝ) ≤ (D.KA j i : ℝ) := fun j i => by
    exact_mod_cast le_max_of_le_left (maxOver_nonneg _ _)
  have hKAd : ∀ j, ((D.N : ℝ) + 1)⁻¹ ≤ (D.KA j j : ℝ) := fun j => by
    have h : ((D.N : ℚ) + 1)⁻¹ ≤ D.KA j j := le_max_of_le_right (by simp)
    have h' := (Rat.cast_le (K := ℝ)).2 h
    rwa [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one] at h'
  have hKA : ∀ j i, ∀ l ∈ Finset.range (D.N + 1), ∑ m ∈ Finset.range (D.N + 1),
      |(D.A j m i l : ℝ)| * (D.ν : ℝ) ^ m ≤ (D.KA j i : ℝ) * (D.ν : ℝ) ^ l := by
    intro j i l hl
    simp only [hwXeq]
    have := le_mul_of_div_le (K := D.KA j i) (hwX l) ((le_maxOver (g := fun l =>
      (∑ m ∈ D.fin, |D.A j m i l| * D.wX m) / D.wX l) hl).trans
        (le_max_left _ (if j = i then ((D.N : ℚ) + 1)⁻¹ else 0)))
    exact_mod_cast this
  have hZ2 : ∀ rq : ℚ, 0 ≤ rq → ∀ j, |D.toIVP.τ| * (D.ν : ℝ) *
      ∑ i, (D.KA j i : ℝ) * D.toIVP.Theta (D.ν : ℝ) hν (toXVec D.abar) i rq ≤ (D.Z2 rq : ℝ) := by
    intro rq hr j
    have hmax : ((|D.τ| * D.ν * ∑ i, D.KA j i * D.Theta i rq : ℚ) : ℝ) ≤ (D.Z2 rq : ℝ) := by
      exact_mod_cast le_finMax (f := fun j => |D.τ| * D.ν * ∑ i, D.KA j i * D.Theta i rq) j
    refine le_trans ?_ hmax
    push_cast
    simp only [toIVP]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (D.Theta_sound hν hνq i hr) (hKA0 j i))
      (mul_nonneg (abs_nonneg _) hν.le)
  have hp0' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp0
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  have hp1' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp1
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  exact D.toIVP.radii_poly_two_radii (toXVec D.abar) habar hM hdeg'
    (fun j m i l => (D.A j m i l : ℝ)) (by exact_mod_cast hr0) (by exact_mod_cast hr01) hY
    hKE0 hKE hZ0 hZ1 hKA0 hKAd hKA (hZ2 D.r0 hr0.le) (hZ2 D.r1 (hr0.le.trans hr01)) hp0' hp1'

end TaylorData

end RadiiPolynomial
