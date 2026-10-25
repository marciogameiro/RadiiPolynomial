module

public import RadiiPolynomial.Problems.ChebyshevRadii
public import RadiiPolynomial.Certificate.ChebyshevSeq
public import RadiiPolynomial.Certificate.Exact

/-!
# A computable checker for Chebyshev boundary value problems

`ChebData n` holds rational data: the polynomial vector field, `L`, `B₋`, `B₊`, `q`, the
truncation `N`, the weight `ν`, the approximate solution `ā` (finite Chebyshev sequences), the
matrix `A^{(N)}`, the radii `r₀ ≤ r₁` and a degree bound `M`. From these data the checker computes
exactly (in `ℚ`) all quantities of the bound theorem `ChebBVP.radii_poly_two_radii`: `F(ā)`, the
entries of `DF(ā)` (including the tail columns of `𝒞`), `E`, `A^{(N)} 𝒞`, the column maxima
`K`, `bʲⁱ = ∂ᵢφ_j(ā)`, `Θᵢ(r)`, and the bounds `Y₀`, `Z₀`, `Z₁`, `Z₂(r)`. `ChebData.check` then
only compares numbers: `p(r₀) < 0`, `p(r₁) < 0` and a few structural conditions.

`ChebData.verify`: if `D.check` holds, the boundary value problem has a zero of `F` in the open
ball of radius `r₀` about `ā`, unique in the closed ball of radius `r₁`. The check is decidable; it
can be evaluated by the kernel (`decide +kernel`) or, for large data, by compiled code
(`native_decide`).
-/

@[expose] public section

namespace RadiiPolynomial

open ChebSeq
open FinSeq (get)

/-- Rational data for a Chebyshev boundary value problem and its approximate solution. -/
structure ChebData (n : ℕ) where
  /-- the polynomial vector field -/
  f : Fin n → PolyData n
  /-- the time scaling -/
  L : ℚ
  /-- the boundary matrix at `t = -1` -/
  Bm : Fin n → Fin n → ℚ
  /-- the boundary matrix at `t = 1` -/
  Bp : Fin n → Fin n → ℚ
  /-- the boundary values -/
  q : Fin n → ℚ
  /-- the truncation -/
  N : ℕ
  /-- the weight `ν ≥ 1` -/
  ν : ℚ
  /-- a bound for the degree of `f` -/
  M : ℕ
  /-- the approximate solution: Chebyshev coefficients `0, …, N` of each component -/
  abar : Fin n → List ℚ
  /-- the approximate inverse `A^{(N)}`, indexed by `(j, m), (i, l)` with `m, l ≤ N` -/
  A : Fin n → ℕ → Fin n → ℕ → ℚ
  /-- the radius `r₀` (existence) -/
  r0 : ℚ
  /-- the radius `r₁` (uniqueness) -/
  r1 : ℚ

namespace ChebData

variable {n : ℕ} (D : ChebData n)

/-- The weights `ω_0 = 1`, `ω_k = 2 ν^k`. -/
def wX (k : ℕ) : ℚ := if k = 0 then 1 else 2 * D.ν ^ k

/-- The weights `ω'_0 = 1`, `ω'_k = ν^k / k`. -/
def wY (k : ℕ) : ℚ := if k = 0 then 1 else D.ν ^ k / k

/-- The finite part `{0, …, N}`. -/
def fin : Finset ℕ := Finset.range (D.N + 1)

/-- `c_j = φ_j(ā)`. -/
def phi (j : Fin n) : List ℚ := evalPoly (D.f j) D.abar

/-- `bʲⁱ = ∂ᵢφ_j(ā)`. -/
def bseq (j i : Fin n) : List ℚ := evalPoly ((D.f j).pderiv i) D.abar

/-- `F(ā)_{j,k}`, from `φ(ā)`. -/
def FvalWith (phi : Fin n → List ℚ) (j : Fin n) (k : ℕ) : ℚ :=
  if k = 0 then
    D.q j - ∑ i, (D.Bm j i * evalAt (-1) (D.abar i) + D.Bp j i * evalAt 1 (D.abar i))
  else 2 * k * get (D.abar j) k + D.L * (get (phi j) (k + 1) - get (phi j) (k - 1))

/-- The coefficients `1, 2s, 2s², …` of `a_0 + 2 ∑ s^k a_k`. -/
def ew (s : ℚ) (k : ℕ) : ℚ := if k = 0 then 1 else 2 * s ^ k

/-- The entries `(DF(ā) e_{i,l})_{j,m}`, from the `bʲⁱ`. -/
def DFWith (bs : Fin n → Fin n → List ℚ) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℚ :=
  (if m = 0 then -(D.Bm j i * ew (-1) l + D.Bp j i * ew 1 l) else 0) +
    2 * m * (if j = i ∧ m = l then 1 else 0) +
    D.L * (if m = 0 then 0 else mulUnit (bs j i) l (m + 1) - mulUnit (bs j i) l (m - 1))

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

/-- The largest column index of `DF(ā)` that the bounds use. -/
def Kmax : ℕ := D.M * D.N + 3

/-- Precomputed tables: each quantity is computed once. -/
def fast : Impl n :=
  let phiT : Array (List ℚ) := Array.ofFn fun j : Fin n => D.phi j
  let bsT : Array (List ℚ) := Array.ofFn fun ji : Fin (n * n) =>
    D.bseq (finProdFinEquiv.symm ji).1 (finProdFinEquiv.symm ji).2
  let phiF : Fin n → List ℚ := fun j => phiT.getD j.val []
  let bsF : Fin n → Fin n → List ℚ := fun j i => bsT.getD (finProdFinEquiv (j, i)).val []
  let FvT : Array ℚ := Array.ofFn fun jk : Fin (n * (D.Kmax + 1)) =>
    D.FvalWith phiF (finProdFinEquiv.symm jk).1 (finProdFinEquiv.symm jk).2
  let DFT : Array ℚ := Array.ofFn fun x : Fin ((n * (D.N + 1)) * (n * (D.Kmax + 1))) =>
    let jm := finProdFinEquiv.symm (finProdFinEquiv.symm x).1
    let il := finProdFinEquiv.symm (finProdFinEquiv.symm x).2
    D.DFWith bsF jm.1 jm.2 il.1 il.2
  ⟨phiF, bsF,
    fun j k => if hk : k < D.Kmax + 1 then FvT.getD (finProdFinEquiv (j, ⟨k, hk⟩)).val 0
      else D.FvalWith phiF j k,
    fun j m i l => if h : m < D.N + 1 ∧ l < D.Kmax + 1 then
      DFT.getD (finProdFinEquiv (finProdFinEquiv (j, ⟨m, h.1⟩), finProdFinEquiv (i, ⟨l, h.2⟩))).val 0
      else D.DFWith bsF j m i l⟩

/-- `E = I - A^{(N)} DF^{(N)}(ā)`. -/
def Eq (I : Impl n) (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) : ℚ :=
  (if j = i ∧ m = l then 1 else 0) - ∑ i', ∑ l' ∈ D.fin, D.A j m i' l' * I.DF i' l' i l

/-- `A^{(N)} 𝒞`. -/
def ACq (I : Impl n) (j : Fin n) (m : ℕ) (i : Fin n) (k : ℕ) : ℚ :=
  ∑ i', ∑ l' ∈ D.fin, D.A j m i' l' * I.DF i' l' i k

/-- `K^E_{ji} = max_{l ≤ N} (1/ω_l) ∑_{m ≤ N} |E_{(j,m),(i,l)}| ω_m`. -/
def KE (I : Impl n) (j i : Fin n) : ℚ :=
  maxOver D.fin fun l => (∑ m ∈ D.fin, |D.Eq I j m i l| * D.wX m) / D.wX l

/-- `K¹_{ji} = max_{N < k ≤ M N + 3} (1/ω_k) ∑_{m ≤ N} |(A^{(N)} 𝒞)_{(j,m),(i,k)}| ω_m`. -/
def K1 (I : Impl n) (j i : Fin n) : ℚ :=
  maxOver (Finset.Ioc D.N (D.M * D.N + 3)) fun k =>
    (∑ m ∈ D.fin, |D.ACq I j m i k| * D.wX m) / D.wX k

/-- `K_{ji} = max {max_{l ≤ N} (1/ω'_l) ∑_{m ≤ N} |A^{(N)}_{(j,m),(i,l)}| ω_m, δ_{ji}}`. -/
def KA (j i : Fin n) : ℚ :=
  max (maxOver D.fin fun l => (∑ m ∈ D.fin, |D.A j m i l| * D.wX m) / D.wY l)
    (if j = i then 1 else 0)

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
  finMax fun j => ∑ i, D.K1 I j i +
    |D.L| * (D.ν + D.ν⁻¹) / (2 * (D.N + 1)) * ∑ i, normX D.ν (I.bs j i)

/-- The bound `Z₂(r)`. -/
def Z2 (r : ℚ) : ℚ :=
  finMax fun j => |D.L| * (D.ν + (2 * D.ν)⁻¹) * ∑ i, D.KA j i * D.Theta i r

/-- The conditions on the computed bounds. -/
def checkWith (I : Impl n) : Prop :=
  1 ≤ D.ν ∧ 1 ≤ D.N ∧ 1 ≤ D.M ∧ (∀ j, (D.f j).degree ≤ D.M) ∧
    (∀ i, (D.abar i).length ≤ D.N + 1) ∧ 0 < D.r0 ∧ D.r0 ≤ D.r1 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 ∧
    radiiPoly (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0

instance (I : Impl n) : Decidable (D.checkWith I) := by unfold checkWith; infer_instance

/-- The check, with the precomputed tables. -/
def check : Prop := D.checkWith D.fast

instance : Decidable D.check := by unfold check; infer_instance

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

/-- The boundary value problem with the data cast to `ℝ`. -/
noncomputable def toBVP : ChebBVP n :=
  ⟨fun j => (D.f j).toMv, D.L, fun j i => D.Bm j i, fun j i => D.Bp j i, fun j => D.q j⟩

variable (hν : 1 ≤ (D.ν : ℝ))

/-- The approximate solution `ā ∈ X_ν^n` (`= toXVec D.abar`). -/
noncomputable def abarX : Fin n → Chebyshev.X (D.ν : ℝ) hν := fun i => toX (D.abar i)

theorem weights_eq (k : ℕ) : Chebyshev.weights (D.ν : ℝ) hν k = (D.wX k : ℝ) := by
  rw [Chebyshev.weights_apply, wX]; split_ifs <;> push_cast <;> rfl

theorem weightsY_eq (k : ℕ) : Chebyshev.weightsY (D.ν : ℝ) hν k = (D.wY k : ℝ) := by
  rw [Chebyshev.weightsY_apply, wY]; split_ifs <;> push_cast <;> rfl

theorem phi_sound (j : Fin n) :
    MvPolynomial.aeval (D.abarX hν) (D.toBVP.f j) = toX (D.phi j) :=
  (toX_evalPoly _ _).symm

theorem bseq_sound (j i : Fin n) :
    D.toBVP.bmat (D.ν : ℝ) hν (D.abarX hν) j i = toX (D.bseq j i) := by
  rw [ChebBVP.bmat, bseq, toX_evalPoly]
  simp only [toBVP, PolyData.toMv_pderiv]
  rfl

theorem norm_bseq (j i : Fin n) :
    ‖D.toBVP.bmat (D.ν : ℝ) hν (D.abarX hν) j i‖ = (normX D.ν (D.bseq j i) : ℝ) := by
  rw [bseq_sound, norm_toX D.ν rfl]

theorem norm_abarX (k : Fin n) : ‖D.abarX hν k‖ = (normX D.ν (D.abar k) : ℝ) :=
  norm_toX D.ν rfl _

theorem F_sound (j : Fin n) (k : ℕ) :
    D.toBVP.F (D.ν : ℝ) hν (D.abarX hν) j k = (D.FvalWith D.phi j k : ℝ) := by
  by_cases hk : k = 0
  · subst hk
    rw [ChebBVP.F_apply_zero, ChebBVP.bcLin_apply, FvalWith, ite_eq_left rfl]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ChebBVP.evalMinus, ChebBVP.evalPlus, abarX, toBVP]
    rw [boundaryEval_toX (-1) _ (-1) (by norm_num), boundaryEval_toX 1 _ 1 (by norm_num)]
  · rw [ChebBVP.F_apply_of_ne_zero _ _ _ _ _ hk, FvalWith, ite_eq_right hk]
    rw [show MvPolynomial.aeval (D.abarX hν) (D.toBVP.f j) = toX (D.phi j) from D.phi_sound hν j]
    push_cast
    rfl

theorem DF_sound (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) :
    D.toBVP.DFN (D.ν : ℝ) hν (D.abarX hν) j m i l = (D.DFWith D.bseq j m i l : ℝ) := by
  rw [ChebBVP.DFN, ChebBVP.DF_apply_coeff, ChebBVP.bcLin_unitVec, ChebBVP.unitVec_apply,
    ChebBVP.polyDeriv_unitVec, bseq_sound, toX_mul_single, toX_mul_single, DFWith]
  simp only [toBVP, Chebyshev.evalWeight, ew]
  split_ifs <;> push_cast <;> ring

theorem normX_nonneg (hνq : 0 ≤ D.ν) (a : List ℚ) : 0 ≤ normX D.ν a :=
  Finset.sum_nonneg fun k _ => mul_nonneg (by split_ifs <;> positivity) (abs_nonneg _)

theorem Theta_sound (hνq : 0 ≤ D.ν) (i : Fin n) {rq : ℚ} (hr : 0 ≤ rq) :
    D.toBVP.Theta (D.ν : ℝ) hν (D.abarX hν) i rq ≤ (D.Theta i rq : ℝ) := by
  rw [ChebBVP.Theta, Theta]
  push_cast
  refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => ?_
  have hx : (fun k => ‖D.abarX hν k‖ + (rq : ℝ)) = fun k => ((normX D.ν (D.abar k) + rq : ℚ) : ℝ) := by
    funext k; rw [norm_abarX]; push_cast; rfl
  simp only [toBVP]
  rw [hx, PolyData.toMv_pderiv, PolyData.toMv_pderiv]
  exact PolyData.absEval_toMv_le _ _ fun k => add_nonneg (D.normX_nonneg hνq _) hr

theorem matE_sound (j : Fin n) (m : ℕ) (i : Fin n) (l : ℕ) :
    D.toBVP.matE (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (D.abarX hν) j m i l =
      (D.Eq D.direct j m i l : ℝ) := by
  rw [ChebBVP.matE, Eq]
  push_cast
  congr 1
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => by
      rw [DF_sound]; rfl

theorem matAC_sound (j : Fin n) (m : ℕ) (i : Fin n) (k : ℕ) :
    D.toBVP.matAC (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (D.abarX hν) j m i k =
      (D.ACq D.direct j m i k : ℝ) := by
  rw [ChebBVP.matAC, ACq]
  push_cast
  exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun l' _ => by rw [DF_sound]; rfl

/-- **The checker is sound.** If `D.check` holds, then `F` has a zero in the open ball of radius
`r₀` about `ā`, and it is the unique zero in the closed ball of radius `r₁`. -/
theorem verify [NeZero n] (h : D.check) :
    HasIsolatedZero (D.toBVP.F (D.ν : ℝ) hν) (toXVec D.abar) D.r0 D.r1 := by
  rw [check, fast_eq] at h
  obtain ⟨hν1, hN, hM, hdeg, hlen, hr0, hr01, hp0, hp1⟩ := h
  have hνq : 0 ≤ D.ν := by linarith
  have hwX : ∀ k, 0 < D.wX k := fun k => by
    rw [wX]; split_ifs
    · exact one_pos
    · exact mul_pos two_pos (pow_pos (by linarith) k)
  have hwY : ∀ k, 0 < D.wY k := fun k => by
    rw [wY]; split_ifs with hk
    · exact one_pos
    · exact div_pos (pow_pos (by linarith) k) (by exact_mod_cast Nat.pos_of_ne_zero hk)
  set I := D.direct
  have habar : ∀ i, Chebyshev.SuppLe (D.abarX hν i) D.N := fun i =>
    (suppLe_toX _).mono (by have := hlen i; omega)
  have hdeg' : ∀ j, (D.toBVP.f j).totalDegree ≤ D.M := fun j =>
    (PolyData.totalDegree_toMv_le _).trans (hdeg j)
  -- `Y₀`
  have hY : ∀ j, ∑ k ∈ Finset.range (D.N + 1),
      |∑ i, ∑ l ∈ Finset.range (D.N + 1), (D.A j k i l : ℝ) *
        D.toBVP.F (D.ν : ℝ) hν (D.abarX hν) i l| * Chebyshev.weights (D.ν : ℝ) hν k +
      ∑ k ∈ Finset.Ico (D.N + 1) (D.M * D.N + 2),
        |D.toBVP.F (D.ν : ℝ) hν (D.abarX hν) j k| * ((D.ν : ℝ) ^ k / k) ≤ (D.Y0 I : ℝ) := by
    intro j
    simp only [F_sound, weights_eq]
    have := le_finMax (f := fun j => ∑ k ∈ D.fin, |∑ i, ∑ l ∈ D.fin, D.A j k i l * I.Fv i l| *
      D.wX k + ∑ k ∈ Finset.Ico (D.N + 1) (D.M * D.N + 2), |I.Fv j k| * (D.ν ^ k / k)) j
    exact_mod_cast this
  -- `Z₀`
  have hKE0 : ∀ j i, (0 : ℝ) ≤ (D.KE I j i : ℝ) := fun j i => by
    exact_mod_cast maxOver_nonneg _ _
  have hKE : ∀ j i, ∀ l ∈ Finset.range (D.N + 1), ∑ m ∈ Finset.range (D.N + 1),
      |D.toBVP.matE (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (D.abarX hν) j m i l| *
        Chebyshev.weights (D.ν : ℝ) hν m ≤ (D.KE I j i : ℝ) * Chebyshev.weights (D.ν : ℝ) hν l := by
    intro j i l hl
    simp only [matE_sound, weights_eq]
    have := le_mul_of_div_le (hwX l) (le_maxOver (g := fun l =>
      (∑ m ∈ D.fin, |D.Eq I j m i l| * D.wX m) / D.wX l) hl)
    exact_mod_cast this
  have hZ0 : ∀ j, ∑ i, (D.KE I j i : ℝ) ≤ (D.Z0 I : ℝ) := fun j => by
    exact_mod_cast le_finMax (f := fun j => ∑ i, D.KE I j i) j
  -- `Z₁`
  have hK10 : ∀ j i, (0 : ℝ) ≤ (D.K1 I j i : ℝ) := fun j i => by
    exact_mod_cast maxOver_nonneg _ _
  have hK1 : ∀ j i, ∀ k ∈ Finset.Ioc D.N (D.M * D.N + 3), ∑ m ∈ Finset.range (D.N + 1),
      |D.toBVP.matAC (D.ν : ℝ) hν D.N (fun j m i l => (D.A j m i l : ℝ)) (D.abarX hν) j m i k| *
        Chebyshev.weights (D.ν : ℝ) hν m ≤ (D.K1 I j i : ℝ) * Chebyshev.weights (D.ν : ℝ) hν k := by
    intro j i k hk
    simp only [matAC_sound, weights_eq]
    have := le_mul_of_div_le (hwX k) (le_maxOver (g := fun k =>
      (∑ m ∈ D.fin, |D.ACq I j m i k| * D.wX m) / D.wX k) hk)
    exact_mod_cast this
  have hZ1 : ∀ j, ∑ i, (D.K1 I j i : ℝ) + |D.toBVP.L| * ((D.ν : ℝ) + (D.ν : ℝ)⁻¹) /
      (2 * (D.N + 1)) * ∑ i, ‖D.toBVP.bmat (D.ν : ℝ) hν (D.abarX hν) j i‖ ≤ (D.Z1 I : ℝ) := by
    intro j
    simp only [norm_bseq]
    have := le_finMax (f := fun j => ∑ i, D.K1 I j i +
      |D.L| * (D.ν + D.ν⁻¹) / (2 * (D.N + 1)) * ∑ i, normX D.ν (I.bs j i)) j
    have h' : ∑ i, D.K1 I j i + |D.L| * (D.ν + D.ν⁻¹) / (2 * (D.N + 1)) *
        ∑ i, normX D.ν (D.bseq j i) ≤ D.Z1 I := this
    simp only [toBVP]
    exact_mod_cast h'
  -- `Z₂`
  have hKA0 : ∀ j i, (0 : ℝ) ≤ (D.KA j i : ℝ) := fun j i => by
    exact_mod_cast le_max_of_le_left (maxOver_nonneg _ _)
  have hKAd : ∀ j, (1 : ℝ) ≤ (D.KA j j : ℝ) := fun j => by
    exact_mod_cast le_max_of_le_right (by simp)
  have hKA : ∀ j i, ∀ l ∈ Finset.range (D.N + 1), ∑ m ∈ Finset.range (D.N + 1),
      |(D.A j m i l : ℝ)| * Chebyshev.weights (D.ν : ℝ) hν m ≤
        (D.KA j i : ℝ) * Chebyshev.weightsY (D.ν : ℝ) hν l := by
    intro j i l hl
    simp only [weights_eq, weightsY_eq]
    have := le_mul_of_div_le (K := D.KA j i) (hwY l) ((le_maxOver (g := fun l =>
      (∑ m ∈ D.fin, |D.A j m i l| * D.wX m) / D.wY l) hl).trans
        (le_max_left _ (if j = i then (1 : ℚ) else 0)))
    exact_mod_cast this
  have hZ2 : ∀ rq : ℚ, 0 ≤ rq → ∀ j, |D.toBVP.L| * ((D.ν : ℝ) + (2 * (D.ν : ℝ))⁻¹) *
      ∑ i, (D.KA j i : ℝ) * D.toBVP.Theta (D.ν : ℝ) hν (D.abarX hν) i rq ≤ (D.Z2 rq : ℝ) := by
    intro rq hr j
    have hmax : ((|D.L| * (D.ν + (2 * D.ν)⁻¹) * ∑ i, D.KA j i * D.Theta i rq : ℚ) : ℝ) ≤
        (D.Z2 rq : ℝ) := by
      exact_mod_cast le_finMax (f := fun j => |D.L| * (D.ν + (2 * D.ν)⁻¹) *
        ∑ i, D.KA j i * D.Theta i rq) j
    refine le_trans ?_ hmax
    push_cast
    simp only [toBVP]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (D.Theta_sound hν hνq i hr) (hKA0 j i))
      (mul_nonneg (abs_nonneg _) (by positivity))
  have hp0' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) D.r0 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp0
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  have hp1' : radiiPoly (D.Y0 I : ℝ) (D.Z0 I) (D.Z1 I) (D.Z2 D.r1) D.r1 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp1
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  exact D.toBVP.radii_poly_two_radii (D.abarX hν) hN habar hM hdeg'
    (fun j m i l => (D.A j m i l : ℝ)) (by exact_mod_cast hr0) (by exact_mod_cast hr01) hY
    hKE0 hKE hZ0 hK10 hK1 hZ1 hKA0 hKAd hKA (hZ2 D.r0 hr0.le) (hZ2 D.r1 (hr0.le.trans hr01))
    hp0' hp1'

end ChebData

end RadiiPolynomial
