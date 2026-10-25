module

public import RadiiPolynomial.Problems.FourierPeriodicRadii
public import RadiiPolynomial.Certificate.FourierSeq
public import RadiiPolynomial.Certificate.Exact

/-!
# A computable checker for periodic orbits in Fourier series

`FourierPeriodicData` holds exact data, with complex numbers as pairs of rationals (`QC`): the
vector field `f` (polynomials with rational coefficients, `PolyData`), the phase condition `ξ`,
`ξ̂`, the truncation dimension `N` (also used for the phase condition), the weight `ν`, the
approximate solution `x̄ = (τ̄, ā)` (`ā_{j,k}`, `|k| ≤ N`), the matrix `A^{(N)}` (unknowns ordered
`τ₀`, then `a_{j,k}` for `j = 0, …, n - 1` and `k = -N, …, N`, `idx`) and the radii `r₀ ≤ r₁`. From
these data the checker computes all quantities of `FourierPeriodic.radii_poly_two_radii`:
`φ_j(ā)` and `∂_{i'}φ_j(ā)` (`FS.evalPoly`), the matrix of `DF^{(N)}(x̄)` (`DMwith`),
`B = I - A^{(N)} DF^{(N)}(x̄)`, and the bounds `Y₀`, `Z₀`, `Z₁`, `Z₂(r₀)`, `Z₂(r₁)`; moduli are
replaced by rational upper bounds (`QC.absUp`). `FourierPeriodicData.check` then only compares
numbers: `p(r₀) < 0`, `p(r₁) < 0` and a few structural conditions.

`FourierPeriodicData.verify`: if `D.check` holds, then `F` has a zero in the open ball of radius
`r₀` about `x̄`, unique in the closed ball of radius `r₁`.
-/

@[expose] public section

namespace RadiiPolynomial

open Fourier FourierSeq ParamTail

/-- Exact data for a periodic orbit problem in Fourier series and its approximate solution. -/
structure FourierPeriodicData (n : ℕ) where
  /-- the vector field -/
  f : Fin n → PolyData n
  /-- the anchor point of the phase condition -/
  ξ : Fin n → QC
  /-- the normal vector of the phase condition -/
  ξhat : Fin n → QC
  /-- the truncation dimension (also of the phase condition) -/
  N : ℕ
  /-- the weight `ν ≥ 1` -/
  ν : ℚ
  /-- the approximate frequency `τ̄₀` -/
  tau : QC
  /-- the approximate solution: component `j`, coefficients `-N, …, N` -/
  abar : Fin n → List QC
  /-- the approximate inverse `A^{(N)}`, indexed by `0` (for `τ₀`) and `idx j k` -/
  A : ℕ → ℕ → QC
  /-- the radius `r₀` (existence) -/
  r0 : ℚ
  /-- the radius `r₁` (uniqueness) -/
  r1 : ℚ

namespace FourierPeriodicData

variable {n : ℕ} (D : FourierPeriodicData n)

/-- The index of the unknown `a_{j,k}`. -/
def idx (j : Fin n) (k : ℤ) : ℕ := 1 + j.val * (2 * D.N + 1) + (k + D.N).toNat

/-- The approximate solution `ā_j` as a sequence with support bound `N`. -/
def aS (j : Fin n) : FS := (D.N, D.abar j)

/-- The border of `A^{(N)}`. -/
def Ab : Border n ℤ QC := ⟨D.A 0 0, fun i l => D.A 0 (D.idx i l), fun j m => D.A (D.idx j m) 0⟩

/-- The block of `A^{(N)}`. -/
def AM (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : QC := D.A (D.idx j m) (D.idx i l)

/-- `i k`. -/
def iK (k : ℤ) : QC := (0, k)

/-- The entries `(DF(x̄) (0, e_{i,l}))_{j,m} = i m δ_{ji} δ_{ml} - τ̄ (∂ᵢφ_j(ā))_{m-l}`. -/
def DMwith (dphi : Fin n → Fin n → FS) (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : QC :=
  (if j = i ∧ m = l then iK m else 0) - QC.mul D.tau ((dphi i j).get (m - l))

/-- The quantities from which the bounds are computed: `φ_j(ā)`, `∂_{i'}φ_j(ā)` (`dphi i' j`) and
the block of `DF^{(N)}(x̄)`. They are computed either directly (`direct`, used in the proofs) or
once, in tables (`fast`, used by the checker); `fast_eq` shows that both agree. -/
structure Impl (n : ℕ) where
  /-- `φ_j(ā)` -/
  phi : Fin n → FS
  /-- `∂_{i'}φ_j(ā)` -/
  dphi : Fin n → Fin n → FS
  /-- the block of `DF^{(N)}(x̄)` -/
  DM : Fin n → ℤ → Fin n → ℤ → QC

/-- The direct definitions. -/
def direct : Impl n :=
  ⟨fun j => FS.evalPoly (D.f j) D.aS, fun i' j => FS.evalPoly (PolyData.pderiv i' (D.f j)) D.aS,
    D.DMwith fun i' j => FS.evalPoly (PolyData.pderiv i' (D.f j)) D.aS⟩

/-- Each quantity computed once. -/
def fast : Impl n :=
  let phiT : Array FS := Array.ofFn fun j : Fin n => FS.evalPoly (D.f j) D.aS
  let dphiT : Array (Array FS) := Array.ofFn fun i' : Fin n => Array.ofFn fun j : Fin n =>
    FS.evalPoly (PolyData.pderiv i' (D.f j)) D.aS
  let dphi : Fin n → Fin n → FS := fun i' j => (dphiT.getD i' #[]).getD j FS.zero
  let K := 2 * D.N + 1
  let DMT : Array (Array (Array (Array QC))) :=
    Array.ofFn fun j : Fin n => Array.ofFn fun m : Fin K => Array.ofFn fun i : Fin n =>
      Array.ofFn fun l : Fin K => D.DMwith dphi j ((m : ℤ) - D.N) i ((l : ℤ) - D.N)
  ⟨fun j => phiT.getD j FS.zero, dphi, fun j m i l =>
    if m.natAbs ≤ D.N ∧ l.natAbs ≤ D.N then
      (((DMT.getD j #[]).getD (m + D.N).toNat #[]).getD i #[]).getD (l + D.N).toNat 0
    else D.DMwith dphi j m i l⟩

/-- The border of `DF^{(N)}(x̄)`: corner `0`, row `ξ̂ᵢ`, column `-φ_j(ā)_m`. -/
def Drow (i : Fin n) : QC := D.ξhat i

/-- The column of `DF^{(N)}(x̄)`. -/
def Dcol (I : Impl n) (j : Fin n) (m : ℤ) : QC := -(I.phi j).get m

/-- `F₀(x̄) = ∑_j ξ̂_j (∑_{|k| ≤ N} ā_{j,k} - ξ_j)`. -/
def F0 : QC :=
  ∑ j, QC.mul (D.ξhat j) (∑ k ∈ center D.N, get D.N (D.abar j) k) - ∑ j, QC.mul (D.ξhat j) (D.ξ j)

/-- `F_j(x̄)_k = i k ā_{j,k} - τ̄ φ_j(ā)_k`. -/
def Fv (I : Impl n) (j : Fin n) (k : ℤ) : QC :=
  QC.mul (iK k) (get D.N (D.abar j) k) - QC.mul D.tau ((I.phi j).get k)

/-! ### `B = I - A^{(N)} DF^{(N)}(x̄)` -/

/-- The corner of `B`. -/
def E00 (I : Impl n) : QC :=
  (1, 0) - (QC.mul D.Ab.a00 0 + ∑ i, ∑ l ∈ center D.N, QC.mul (D.Ab.row i l) (Dcol I i l))

/-- The row of `B`. -/
def Erow (I : Impl n) (i : Fin n) (l : ℤ) : QC :=
  -(QC.mul D.Ab.a00 (D.Drow i) +
    ∑ i', ∑ l' ∈ center D.N, QC.mul (D.Ab.row i' l') (I.DM i' l' i l))

/-- The column of `B`. -/
def Ecol (I : Impl n) (j : Fin n) (m : ℤ) : QC :=
  -(QC.mul (D.Ab.col j m) 0 + ∑ i', ∑ l' ∈ center D.N, QC.mul (D.AM j m i' l') (Dcol I i' l'))

/-- The block of `B`. -/
def EM (I : Impl n) (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : QC :=
  (if j = i ∧ m = l then (1, 0) else 0) - (QC.mul (D.Ab.col j m) (D.Drow i) +
    ∑ i', ∑ l' ∈ center D.N, QC.mul (D.AM j m i' l') (I.DM i' l' i l))

/-! ### The bounds -/

/-- The largest degree of the components of `f`. -/
def Mdeg : ℕ := (List.finRange n).foldr (fun j acc => max (PolyData.degree (D.f j)) acc) 0

/-- The bound `Y₀`. -/
def Y0 (I : Impl n) : ℚ :=
  max (QC.absUp (QC.mul D.Ab.a00 D.F0 +
      ∑ i, ∑ l ∈ center D.N, QC.mul (D.Ab.row i l) (D.Fv I i l)))
    (finMax fun j => ∑ k ∈ center D.N, QC.absUp (QC.mul (D.Ab.col j k) D.F0 +
        ∑ i, ∑ l ∈ center D.N, QC.mul (D.AM j k i l) (D.Fv I i l)) * D.ν ^ k.natAbs +
      ∑ k ∈ center (D.Mdeg * D.N) \ center D.N,
        QC.absUp (D.Fv I j k) * D.ν ^ k.natAbs / (k.natAbs : ℚ))

/-- `ER_i ≥ ν^{-|l|} |B_{0,(i,l)}|`. -/
def ER (I : Impl n) (i : Fin n) : ℚ :=
  maxOver (center D.N) fun l => QC.absUp (D.Erow I i l) / D.ν ^ l.natAbs

/-- `EC_j ≥ ∑_m |B_{(j,m),0}| ν^{|m|}`. -/
def EC (I : Impl n) (j : Fin n) : ℚ :=
  ∑ m ∈ center D.N, QC.absUp (D.Ecol I j m) * D.ν ^ m.natAbs

/-- `EK_{ji} ≥` the column norm of the block `(j, i)` of `B`. -/
def EK (I : Impl n) (j i : Fin n) : ℚ :=
  maxOver (center D.N) fun l =>
    (∑ m ∈ center D.N, QC.absUp (D.EM I j m i l) * D.ν ^ m.natAbs) / D.ν ^ l.natAbs

/-- The bound `Z₀`. -/
def Z0 (I : Impl n) : ℚ :=
  max (QC.absUp (D.E00 I) + ∑ i, D.ER I i) (finMax fun j => D.EC I j + ∑ i, D.EK I j i)

/-- The weighted column sums of the block of `A^{(N)}` (upper bounds). -/
def colA (j i : Fin n) (l : ℤ) : ℚ :=
  ∑ m ∈ center D.N, QC.absUp (D.AM j m i l) * D.ν ^ m.natAbs

/-- `κ_{0i} ≥ ‖A_{0i} Γ‖`. -/
def kappa0 (i : Fin n) : ℚ :=
  maxOver (center D.N) fun l => QC.absUp (D.Ab.row i l) * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)

/-- `κ_{ji} ≥ ‖A_{ji} Γ‖`. -/
def kappa (j i : Fin n) : ℚ :=
  maxOver (center D.N) fun l => D.colA j i l * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)

/-- `Dφ_{i'i} ≥ ‖∂_{i'}φ_i(ā)‖`. -/
def Dphi (I : Impl n) (i' i : Fin n) : ℚ := normUp D.ν (I.dphi i' i).1 (I.dphi i' i).2

/-- `Φ_j ≥ ‖π_∞ φ_j(ā)‖`. -/
def Phi (I : Impl n) (j : Fin n) : ℚ :=
  ∑ k ∈ center (I.phi j).1 \ center D.N, QC.absUp ((I.phi j).get k) * D.ν ^ k.natAbs

/-- The bound `Z₁`. -/
def Z1 (I : Impl n) : ℚ :=
  max (QC.absUp D.tau * ∑ i, D.kappa0 i * ∑ i', D.Dphi I i' i)
    (finMax fun j => QC.absUp D.tau * ∑ i, D.kappa j i * ∑ i', D.Dphi I i' i +
      (D.Phi I j + QC.absUp D.tau * ∑ i', D.Dphi I i' j) / ((D.N : ℚ) + 1))

/-- `Rᵢ ≥ ν^{-|l|} |A_{0,(i,l)}|`. -/
def R (i : Fin n) : ℚ := maxOver (center D.N) fun l => QC.absUp (D.Ab.row i l) / D.ν ^ l.natAbs

/-- `K_{ji} ≥ ‖A_{ji}‖` on `ℓ¹_ν` (with the tail `1/(N+1)` on the diagonal). -/
def KA (j i : Fin n) : ℚ :=
  max (maxOver (center D.N) fun l => D.colA j i l / D.ν ^ l.natAbs)
    (if j = i then ((D.N : ℚ) + 1)⁻¹ else 0)

/-- `Θᵢ(r) = 2 ∑_l |∂_l f_i|(‖ā‖ + r) + |τ̄| ∑_{l,m} |∂_l ∂_m f_i|(‖ā‖ + r)`. -/
def Theta (i : Fin n) (r : ℚ) : ℚ :=
  2 * ∑ l, PolyData.absEval (PolyData.pderiv l (D.f i)) (fun k => normUp D.ν D.N (D.abar k) + r) +
    QC.absUp D.tau * ∑ l, ∑ m, PolyData.absEval (PolyData.pderiv l (PolyData.pderiv m (D.f i)))
      (fun k => normUp D.ν D.N (D.abar k) + r)

/-- The bound `Z₂(r)`. -/
def Z2 (r : ℚ) : ℚ :=
  max (∑ i, D.R i * D.Theta i r) (finMax fun j => ∑ i, D.KA j i * D.Theta i r)

/-- The conditions on the computed bounds. -/
def checkVals (y z0 z1 z2a z2b : ℚ) : Prop :=
  1 ≤ D.ν ∧ 1 ≤ D.Mdeg ∧ 0 < D.r0 ∧ D.r0 ≤ D.r1 ∧
    radiiPoly y z0 z1 z2a D.r0 < 0 ∧ radiiPoly y z0 z1 z2b D.r1 < 0

instance (y z0 z1 z2a z2b : ℚ) : Decidable (D.checkVals y z0 z1 z2a z2b) := by
  unfold checkVals; infer_instance

/-- The conditions, for the quantities `I`. -/
def checkWith (I : Impl n) : Prop :=
  D.checkVals (D.Y0 I) (D.Z0 I) (D.Z1 I) (D.Z2 D.r0) (D.Z2 D.r1)

instance (I : Impl n) : Decidable (D.checkWith I) := by unfold checkWith; infer_instance

/-- The check, with the quantities computed once. -/
def check : Prop := D.checkWith D.fast

instance : Decidable D.check := by unfold check; infer_instance

/-! ### The tables -/

theorem getD_ofFn' {α : Type*} {m : ℕ} (f : Fin m → α) (k : ℕ) (hk : k < m) (d : α) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ :=
  getD_ofFn f ⟨k, hk⟩ d

/-- The tables agree with the direct definitions. -/
theorem fast_eq : D.fast = D.direct := by
  have hdphi : (fun (i' j : Fin n) => ((Array.ofFn fun i' : Fin n => Array.ofFn fun j : Fin n =>
      FS.evalPoly (PolyData.pderiv i' (D.f j)) D.aS).getD i' #[]).getD j FS.zero) =
      fun i' j => FS.evalPoly (PolyData.pderiv i' (D.f j)) D.aS := by
    funext i' j; rw [getD_ofFn, getD_ofFn]
  simp only [fast, direct, hdphi, Impl.mk.injEq, true_and]
  constructor
  · funext j; rw [getD_ofFn]
  · funext j m i l
    split_ifs with h
    · have hm : (m + D.N).toNat < 2 * D.N + 1 := by omega
      have hl : (l + D.N).toNat < 2 * D.N + 1 := by omega
      rw [getD_ofFn, getD_ofFn' _ _ hm, getD_ofFn, getD_ofFn' _ _ hl]
      simp only
      congr 1 <;> omega
    · rfl

/-! ### Soundness -/

/-- The problem with complex coefficients (phase condition truncated at `N`). -/
noncomputable def toProblem : FourierPeriodic n :=
  ⟨fun j => (D.f j).toMvC, fun j => QC.toC (D.ξ j), fun j => QC.toC (D.ξhat j), D.N⟩

/-- The border of `A^{(N)}` over `ℂ`. -/
noncomputable def AbC : Border n ℤ ℂ :=
  ⟨QC.toC D.Ab.a00, fun i l => QC.toC (D.Ab.row i l), fun j m => QC.toC (D.Ab.col j m)⟩

/-- The block of `A^{(N)}` over `ℂ`. -/
noncomputable def AMC (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) : ℂ := QC.toC (D.AM j m i l)

variable (hν : 1 ≤ (D.ν : ℝ))

/-- The approximate solution `x̄ = (τ̄, ā)`. -/
noncomputable def xbar : FourierPeriodic.X n (D.ν : ℝ) hν :=
  (QC.toC D.tau, fun j => toX D.N (D.abar j))

theorem toC_iK (k : ℤ) : QC.toC (iK k) = Complex.I * k := by
  apply Complex.ext <;> simp [iK]

theorem aeval_sound (p : PolyData n) :
    MvPolynomial.aeval (D.xbar hν).2 p.toMvC = FS.toXF (FS.evalPoly p D.aS) := by
  rw [FS.toXF_evalPoly]; rfl

theorem phi_sound (j : Fin n) :
    MvPolynomial.aeval (D.xbar hν).2 (D.toProblem.f j) = FS.toXF (D.direct.phi j) :=
  D.aeval_sound hν _

theorem dphi_sound (i' j : Fin n) :
    MvPolynomial.aeval (D.xbar hν).2 (MvPolynomial.pderiv i' (D.toProblem.f j)) =
      FS.toXF (D.direct.dphi i' j) := by
  rw [toProblem, PolyData.toMvC_pderiv]; exact D.aeval_sound hν _

theorem F0_sound : (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).1 = QC.toC D.F0 := by
  rw [FourierPeriodic.F_fst, F0, map_sub, map_sum, map_sum]
  simp only [QC.toC_mul, map_sum]
  rfl

theorem Fv_sound (j : Fin n) (k : ℤ) :
    (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).2 j k = QC.toC (D.Fv D.direct j k) := by
  rw [FourierPeriodic.F_snd_apply, D.phi_sound hν, Fv, map_sub, QC.toC_mul, QC.toC_mul, toC_iK,
    FS.toXF_apply]
  rfl

theorem DFb_a00 : (D.toProblem.DFb (D.ν : ℝ) hν (D.xbar hν)).a00 = 0 := by
  simp [FourierPeriodic.DFb, FourierPeriodic.DF_fst]

theorem DFb_row (i : Fin n) {l : ℤ} (hl : l ∈ center D.N) :
    (D.toProblem.DFb (D.ν : ℝ) hν (D.xbar hν)).row i l = QC.toC (D.Drow i) := by
  have hN : D.toProblem.N₀ = D.N := rfl
  simp only [FourierPeriodic.DFb, FourierPeriodic.DF_fst, FiniteTail.unitVec, hN]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp only [Pi.single_eq_same, WeightedL1.single_apply, Finset.sum_ite_eq']
  rw [ite_eq_left hl, mul_one]
  rfl

theorem DFb_col (j : Fin n) (m : ℤ) :
    (D.toProblem.DFb (D.ν : ℝ) hν (D.xbar hν)).col j m = QC.toC (Dcol D.direct j m) := by
  simp only [FourierPeriodic.DFb, FourierPeriodic.DF_snd_apply, Dcol]
  rw [D.phi_sound hν, FS.toXF_apply, map_neg]
  simp

theorem DFM_sound (j : Fin n) (m : ℤ) (i : Fin n) (l : ℤ) :
    D.toProblem.DFM (D.ν : ℝ) hν (D.xbar hν) j m i l = QC.toC (D.direct.DM j m i l) := by
  simp only [FourierPeriodic.DFM, FourierPeriodic.DF_snd_apply, polyDeriv_apply,
    FiniteTail.unitVec, zero_mul, sub_zero]
  rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_eq_of_ne hi']) (by simp)]
  simp only [Pi.single_eq_same]
  rw [mul_single_apply, D.dphi_sound hν, FS.toXF_apply]
  simp only [direct, DMwith, map_sub, QC.toC_mul]
  by_cases hj : j = i
  · subst hj
    simp only [Pi.single_eq_same, WeightedL1.single_apply, true_and]
    split_ifs with hm
    · subst hm; rw [toC_iK, mul_one]; rfl
    · rw [mul_zero, map_zero]; rfl
  · simp only [Pi.single_eq_of_ne hj, WeightedLp.zero_apply, mul_zero, hj, false_and,
      ite_false, map_zero]
    rfl

theorem matEb_sound :
    (D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).a00 = QC.toC (D.E00 D.direct) ∧
    (∀ i, ∀ l ∈ center D.N,
      (D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).row i l =
        QC.toC (D.Erow D.direct i l)) ∧
    (∀ j m, (D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).col j m =
        QC.toC (D.Ecol D.direct j m)) := by
  refine ⟨?_, fun i l hl => ?_, fun j m => ?_⟩
  · simp only [FourierPeriodic.matEb, E00, D.DFb_a00 hν, D.DFb_col hν, map_sub, map_add, map_sum,
      QC.toC_mul, QC.toC_one, map_zero]
    rfl
  · simp only [FourierPeriodic.matEb, Erow, D.DFb_row hν i hl, D.DFM_sound hν, map_neg, map_add,
      map_sum, QC.toC_mul]
    rfl
  · simp only [FourierPeriodic.matEb, Ecol, D.DFb_a00 hν, D.DFb_col hν, map_neg, map_add,
      map_sum, QC.toC_mul, map_zero]
    rfl

theorem matEM_sound (j : Fin n) (m : ℤ) (i : Fin n) {l : ℤ} (hl : l ∈ center D.N) :
    D.toProblem.matEM (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν) j m i l =
      QC.toC (D.EM D.direct j m i l) := by
  simp only [FourierPeriodic.matEM, EM, D.DFb_row hν i hl, D.DFM_sound hν, map_sub, map_add,
    map_sum, QC.toC_mul]
  congr 1
  split_ifs <;> simp [QC.toC_one]

theorem degree_le_Mdeg (j : Fin n) : PolyData.degree (D.f j) ≤ D.Mdeg := by
  have h : ∀ l : List (Fin n), j ∈ l →
      PolyData.degree (D.f j) ≤ l.foldr (fun j acc => max (PolyData.degree (D.f j)) acc) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.1 hl with h | h
      · subst h; exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  exact h _ (List.mem_finRange j)

theorem norm_abar_le (k : Fin n) :
    ‖(D.xbar hν).2 k‖ ≤ (normUp D.ν D.N (D.abar k) : ℝ) := norm_toX_le D.ν rfl _ _

include hν in
theorem normUp_nonneg (N : ℕ) (a : List QC) : 0 ≤ normUp D.ν N a := by
  have hν0 : (0 : ℚ) ≤ D.ν := by exact_mod_cast (zero_le_one.trans hν)
  exact Finset.sum_nonneg fun k _ => mul_nonneg (QC.absUp_nonneg _) (pow_nonneg hν0 _)

theorem absEval_le (q : PolyData n) {r : ℚ} (hr : 0 ≤ r) :
    absEval (q.toMvC) (fun k => ‖(D.xbar hν).2 k‖ + (r : ℝ)) ≤
      (PolyData.absEval q (fun k => normUp D.ν D.N (D.abar k) + r) : ℝ) := by
  rw [PolyData.absEval_toMvC]
  have h1 : absEval (PolyData.toMv q) (fun k => ‖(D.xbar hν).2 k‖ + (r : ℝ)) ≤
      absEval (PolyData.toMv q) (fun k => ((normUp D.ν D.N (D.abar k) + r : ℚ) : ℝ)) :=
    absEval_mono _ (fun k => add_nonneg (norm_nonneg _) (by exact_mod_cast hr)) fun k => by
      rw [Rat.cast_add]; linarith [D.norm_abar_le hν k]
  exact h1.trans (PolyData.absEval_toMv_le q _ fun k => add_nonneg (D.normUp_nonneg hν _ _) hr)

theorem Theta_le {r : ℚ} (hr : 0 ≤ r) (i : Fin n) :
    D.toProblem.Theta (D.ν : ℝ) hν (D.xbar hν) i r ≤ (D.Theta i r : ℝ) := by
  rw [FourierPeriodic.Theta, Theta]
  push_cast
  have htau : ‖(D.xbar hν).1‖ ≤ (QC.absUp D.tau : ℝ) := QC.norm_toC_le_absUp _
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) zero_le_two)
    (mul_le_mul htau (Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => ?_)
      (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => absEval_nonneg _ fun k =>
        add_nonneg (norm_nonneg _) (by exact_mod_cast hr))
      (by exact_mod_cast QC.absUp_nonneg _))
  · rw [toProblem, PolyData.toMvC_pderiv]; exact D.absEval_le hν _ hr
  · rw [toProblem, PolyData.toMvC_pderiv, PolyData.toMvC_pderiv]; exact D.absEval_le hν _ hr

/-- **The checker is sound.** If `D.check` holds, then `F` has a zero in the open ball of radius
`r₀` about `x̄`, and it is the unique zero in the closed ball of radius `r₁`. -/
theorem verify (h : D.check) :
    HasIsolatedZero (D.toProblem.F (D.ν : ℝ) hν) (D.xbar hν) D.r0 D.r1 := by
  rw [check, fast_eq] at h
  obtain ⟨hν1, hM, hr0, hr01, hp0, hp1⟩ := h
  have hνpos : (0 : ℚ) < D.ν := by linarith
  have hw : ∀ k : ℤ, (0 : ℚ) < D.ν ^ k.natAbs := fun k => pow_pos hνpos _
  have hνR : (0 : ℝ) ≤ (D.ν : ℝ) := by exact_mod_cast hνpos.le
  have habs : ∀ z : QC, ‖QC.toC z‖ ≤ (QC.absUp z : ℝ) := QC.norm_toC_le_absUp
  -- bounds from maxima
  have hmax : ∀ {g : ℤ → ℚ} {l : ℤ}, l ∈ center D.N → ∀ {S w : ℚ}, 0 < w → S / w ≤ g l →
      ∀ {K : ℚ}, maxOver (center D.N) g ≤ K → S ≤ K * w := fun hl _ _ hw hS _ hK =>
    le_mul_of_div_le hw (hS.trans ((le_maxOver hl).trans hK))
  -- `Y₀`
  have hY0a : ‖D.AbC.a00 * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).1 +
      ∑ i, ∑ l ∈ center D.N, D.AbC.row i l * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).2 i l‖ ≤ (D.Y0 D.direct : ℝ) := by
    have : D.AbC.a00 * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).1 +
        ∑ i, ∑ l ∈ center D.N, D.AbC.row i l * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).2 i l =
        QC.toC (QC.mul D.Ab.a00 D.F0 + ∑ i, ∑ l ∈ center D.N, QC.mul (D.Ab.row i l) (D.Fv D.direct i l)) := by
      simp only [D.F0_sound hν, D.Fv_sound hν, map_add, map_sum, QC.toC_mul]
      rfl
    rw [this]
    exact (habs _).trans (by exact_mod_cast le_max_left _ _)
  have hY0b : ∀ j, ∑ k ∈ center D.N, ‖D.AbC.col j k * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).1 +
        ∑ i, ∑ l ∈ center D.N, D.AMC j k i l * (D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).2 i l‖ * (D.ν : ℝ) ^ k.natAbs +
      ∑ k ∈ center (D.Mdeg * D.N) \ center D.N,
        ‖(D.toProblem.F (D.ν : ℝ) hν (D.xbar hν)).2 j k‖ * (D.ν : ℝ) ^ k.natAbs / (k.natAbs : ℝ) ≤ (D.Y0 D.direct : ℝ) := by
    intro j
    have h1 : _ ≤ D.Y0 D.direct := (le_finMax (fun j => ∑ k ∈ center D.N, QC.absUp (QC.mul (D.Ab.col j k) D.F0 +
        ∑ i, ∑ l ∈ center D.N, QC.mul (D.AM j k i l) (D.Fv D.direct i l)) * D.ν ^ k.natAbs +
      ∑ k ∈ center (D.Mdeg * D.N) \ center D.N,
        QC.absUp (D.Fv D.direct j k) * D.ν ^ k.natAbs / (k.natAbs : ℚ)) j).trans (le_max_right _ _)
    refine le_trans ?_ (Rat.cast_le.2 h1)
    push_cast
    refine add_le_add (Finset.sum_le_sum fun k _ => ?_) (Finset.sum_le_sum fun k _ => ?_)
    · refine mul_le_mul_of_nonneg_right (le_of_eq_of_le ?_ (habs _)) (pow_nonneg hνR _)
      simp only [D.F0_sound hν, D.Fv_sound hν, map_add, map_sum, QC.toC_mul]
      rfl
    · rw [D.Fv_sound hν]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (habs _) (pow_nonneg hνR _))
        (Nat.cast_nonneg _)
  -- `Z₀`
  obtain ⟨hE00, hErow, hEcol⟩ := D.matEb_sound hν
  have hER : ∀ i, ∀ l ∈ center D.N, ‖(D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).row i l‖ ≤
      (D.ER D.direct i : ℝ) * (D.ν : ℝ) ^ l.natAbs := fun i l hl => by
    rw [hErow i l hl]
    exact (habs _).trans (by exact_mod_cast hmax hl (hw l) le_rfl le_rfl)
  have hEC : ∀ j, ∑ m ∈ center D.N, ‖(D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).col j m‖ *
      (D.ν : ℝ) ^ m.natAbs ≤ (D.EC D.direct j : ℝ) := fun j => by
    rw [EC]; push_cast
    exact Finset.sum_le_sum fun m _ => by
      rw [hEcol]; exact mul_le_mul_of_nonneg_right (habs _) (pow_nonneg hνR _)
  have hEK : ∀ j i, ∀ l ∈ center D.N, ∑ m ∈ center D.N,
      ‖D.toProblem.matEM (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν) j m i l‖ * (D.ν : ℝ) ^ m.natAbs ≤
        (D.EK D.direct j i : ℝ) * (D.ν : ℝ) ^ l.natAbs := fun j i l hl => by
    have h1 : ∑ m ∈ center D.N, QC.absUp (D.EM D.direct j m i l) * D.ν ^ m.natAbs ≤
        D.EK D.direct j i * D.ν ^ l.natAbs := hmax hl (hw l) le_rfl le_rfl
    calc ∑ m ∈ center D.N, ‖D.toProblem.matEM (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν) j m i l‖ *
          (D.ν : ℝ) ^ m.natAbs
        ≤ ((∑ m ∈ center D.N, QC.absUp (D.EM D.direct j m i l) * D.ν ^ m.natAbs : ℚ) : ℝ) := by
          push_cast
          exact Finset.sum_le_sum fun m _ => by
            rw [D.matEM_sound hν j m i hl]
            exact mul_le_mul_of_nonneg_right (habs _) (pow_nonneg hνR _)
      _ ≤ ((D.EK D.direct j i * D.ν ^ l.natAbs : ℚ) : ℝ) := Rat.cast_le.2 h1
      _ = (D.EK D.direct j i : ℝ) * (D.ν : ℝ) ^ l.natAbs := by push_cast; rfl
  have hZ00 : ‖(D.toProblem.matEb (D.ν : ℝ) hν D.N D.AbC D.AMC (D.xbar hν)).a00‖ + ∑ i, (D.ER D.direct i : ℝ) ≤
      (D.Z0 D.direct : ℝ) := by
    rw [hE00]
    have : QC.absUp (D.E00 D.direct) + ∑ i, D.ER D.direct i ≤ D.Z0 D.direct := le_max_left _ _
    refine le_trans (add_le_add (habs _) le_rfl) ?_
    exact_mod_cast this
  have hZ0 : ∀ j, (D.EC D.direct j : ℝ) + ∑ i, (D.EK D.direct j i : ℝ) ≤ (D.Z0 D.direct : ℝ) := fun j => by
    have : D.EC D.direct j + ∑ i, D.EK D.direct j i ≤ D.Z0 D.direct :=
      (le_finMax (fun j => D.EC D.direct j + ∑ i, D.EK D.direct j i) j).trans (le_max_right _ _)
    exact_mod_cast this
  -- `Z₁`
  have htau : ‖(D.xbar hν).1‖ ≤ (QC.absUp D.tau : ℝ) := habs _
  have hκ0 : ∀ i, ∀ l ∈ center D.N, ‖D.AbC.row i l‖ * (D.ν : ℝ) ^ l.natAbs ≤
      (D.kappa0 i : ℝ) * (D.ν : ℝ) ^ (2 * D.N + 2) := fun i l hl => by
    have h1 : QC.absUp (D.Ab.row i l) * D.ν ^ l.natAbs ≤ D.kappa0 i * D.ν ^ (2 * D.N + 2) :=
      le_mul_of_div_le (pow_pos hνpos _) (le_maxOver (g := fun l =>
        QC.absUp (D.Ab.row i l) * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)) hl)
    refine le_trans (mul_le_mul_of_nonneg_right (habs _) (pow_nonneg hνR _)) ?_
    exact_mod_cast h1
  have hcol : ∀ j i l, ∑ m ∈ center D.N, ‖D.AMC j m i l‖ * (D.ν : ℝ) ^ m.natAbs ≤
      (D.colA j i l : ℝ) := fun j i l => by
    rw [colA]; push_cast
    exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_right (habs _) (pow_nonneg hνR _)
  have hκ : ∀ j i, ∀ l ∈ center D.N,
      (∑ m ∈ center D.N, ‖D.AMC j m i l‖ * (D.ν : ℝ) ^ m.natAbs) * (D.ν : ℝ) ^ l.natAbs ≤
        (D.kappa j i : ℝ) * (D.ν : ℝ) ^ (2 * D.N + 2) := fun j i l hl => by
    have h1 : D.colA j i l * D.ν ^ l.natAbs ≤ D.kappa j i * D.ν ^ (2 * D.N + 2) :=
      le_mul_of_div_le (pow_pos hνpos _) (le_maxOver (g := fun l =>
        D.colA j i l * D.ν ^ l.natAbs / D.ν ^ (2 * D.N + 2)) hl)
    refine le_trans (mul_le_mul_of_nonneg_right (hcol j i l) (pow_nonneg hνR _)) ?_
    exact_mod_cast h1
  have hDphi : ∀ i' i, ‖MvPolynomial.aeval (D.xbar hν).2 (MvPolynomial.pderiv i' (D.toProblem.f i))‖ ≤
      (D.Dphi D.direct i' i : ℝ) := fun i' i => by
    rw [D.dphi_sound hν]; exact FS.norm_toXF_le D.ν rfl _
  have hΦ : ∀ j, ‖MvPolynomial.aeval (D.xbar hν).2 (D.toProblem.f j) - finPart D.N (MvPolynomial.aeval (D.xbar hν).2 (D.toProblem.f j))‖ ≤
      (D.Phi D.direct j : ℝ) := fun j => by
    rw [D.phi_sound hν]; exact FS.norm_sub_finPart_toXF_le D.ν rfl D.N _
  have hDphi0 : ∀ i' i, (0 : ℝ) ≤ D.Dphi D.direct i' i := fun i' i => (norm_nonneg _).trans (hDphi i' i)
  have hκ00 : ∀ i, (0 : ℝ) ≤ D.kappa0 i := fun i => by exact_mod_cast maxOver_nonneg _ _
  have hκ0' : ∀ j i, (0 : ℝ) ≤ D.kappa j i := fun j i => by exact_mod_cast maxOver_nonneg _ _
  have hZ10 : ‖(D.xbar hν).1‖ * ∑ i, (D.kappa0 i : ℝ) * ∑ i', (D.Dphi D.direct i' i : ℝ) ≤ (D.Z1 D.direct : ℝ) := by
    have : QC.absUp D.tau * ∑ i, D.kappa0 i * ∑ i', D.Dphi D.direct i' i ≤ D.Z1 D.direct := le_max_left _ _
    refine le_trans (mul_le_mul_of_nonneg_right htau (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hκ00 i) (Finset.sum_nonneg fun i' _ => hDphi0 i' i))) ?_
    exact_mod_cast this
  have hZ1 : ∀ j, ‖(D.xbar hν).1‖ * ∑ i, (D.kappa j i : ℝ) * ∑ i', (D.Dphi D.direct i' i : ℝ) +
      ((D.Phi D.direct j : ℝ) + ‖(D.xbar hν).1‖ * ∑ i', (D.Dphi D.direct i' j : ℝ)) / ((D.N : ℝ) + 1) ≤
        (D.Z1 D.direct : ℝ) := fun j => by
    have h1 : QC.absUp D.tau * ∑ i, D.kappa j i * ∑ i', D.Dphi D.direct i' i +
        (D.Phi D.direct j + QC.absUp D.tau * ∑ i', D.Dphi D.direct i' j) / ((D.N : ℚ) + 1) ≤ D.Z1 D.direct :=
      (le_finMax (fun j => QC.absUp D.tau * ∑ i, D.kappa j i * ∑ i', D.Dphi D.direct i' i +
        (D.Phi D.direct j + QC.absUp D.tau * ∑ i', D.Dphi D.direct i' j) / ((D.N : ℚ) + 1)) j).trans
        (le_max_right _ _)
    refine le_trans ?_ (Rat.cast_le.2 h1)
    push_cast
    have hs1 : (0 : ℝ) ≤ ∑ i, (D.kappa j i : ℝ) * ∑ i', (D.Dphi D.direct i' i : ℝ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hκ0' j i) (Finset.sum_nonneg fun i' _ => hDphi0 i' i)
    have hs2 : (0 : ℝ) ≤ ∑ i', (D.Dphi D.direct i' j : ℝ) := Finset.sum_nonneg fun i' _ => hDphi0 i' j
    gcongr
  -- `Z₂`
  have hR : ∀ i, ∀ l ∈ center D.N, ‖D.AbC.row i l‖ ≤ (D.R i : ℝ) * (D.ν : ℝ) ^ l.natAbs :=
    fun i l hl => (habs _).trans (by exact_mod_cast hmax hl (hw l) le_rfl le_rfl)
  have hR0 : ∀ i, (0 : ℝ) ≤ D.R i := fun i => by exact_mod_cast maxOver_nonneg _ _
  have hKA0 : ∀ j i, (0 : ℝ) ≤ D.KA j i := fun j i => by
    exact_mod_cast (maxOver_nonneg _ _).trans (le_max_left _ _)
  have hKAd : ∀ j, ((D.N : ℝ) + 1)⁻¹ ≤ D.KA j j := fun j => by
    have : ((D.N : ℚ) + 1)⁻¹ ≤ D.KA j j := by
      refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [ite_eq_left rfl]
    have h2 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h2
    exact h2
  have hKA : ∀ j i, ∀ l ∈ center D.N, ∑ m ∈ center D.N, ‖D.AMC j m i l‖ * (D.ν : ℝ) ^ m.natAbs ≤
      (D.KA j i : ℝ) * (D.ν : ℝ) ^ l.natAbs := fun j i l hl => by
    have h1 : D.colA j i l ≤ D.KA j i * D.ν ^ l.natAbs :=
      le_mul_of_div_le (hw l) ((le_maxOver (g := fun l => D.colA j i l / D.ν ^ l.natAbs) hl).trans
        (le_max_left _ _))
    exact (hcol j i l).trans (by exact_mod_cast h1)
  have hZ2 : ∀ r : ℚ, 0 ≤ r →
      (∑ i, (D.R i : ℝ) * D.toProblem.Theta (D.ν : ℝ) hν (D.xbar hν) i r ≤ (D.Z2 r : ℝ)) ∧
      ∀ j, ∑ i, (D.KA j i : ℝ) * D.toProblem.Theta (D.ν : ℝ) hν (D.xbar hν) i r ≤ (D.Z2 r : ℝ) := fun r hr => by
    refine ⟨?_, fun j => ?_⟩
    · have : ∑ i, D.R i * D.Theta i r ≤ D.Z2 r := le_max_left _ _
      refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (D.Theta_le hν hr i) (hR0 i)) ?_
      exact_mod_cast this
    · have : ∑ i, D.KA j i * D.Theta i r ≤ D.Z2 r :=
        (le_finMax (fun j => ∑ i, D.KA j i * D.Theta i r) j).trans (le_max_right _ _)
      refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (D.Theta_le hν hr i) (hKA0 j i)) ?_
      exact_mod_cast this
  obtain ⟨hZ2₀0, hZ2₀⟩ := hZ2 D.r0 hr0.le
  obtain ⟨hZ2₁0, hZ2₁⟩ := hZ2 D.r1 (hr0.le.trans hr01)
  have hp0' : radiiPoly (D.Y0 D.direct : ℝ) (D.Z0 D.direct) (D.Z1 D.direct) (D.Z2 D.r0) D.r0 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp0
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  have hp1' : radiiPoly (D.Y0 D.direct : ℝ) (D.Z0 D.direct) (D.Z1 D.direct) (D.Z2 D.r1) D.r1 < 0 := by
    have := (Rat.cast_lt (K := ℝ)).2 hp1
    rwa [RadiiPolynomial.Rat.cast_radiiPoly, Rat.cast_zero] at this
  exact D.toProblem.radii_poly_two_radii (D.xbar hν) (N := D.N) (M := D.Mdeg) le_rfl hM
    (fun j => (PolyData.totalDegree_toMvC_le _).trans (D.degree_le_Mdeg j))
    (fun j => suppLe_toX _ _) D.AbC D.AMC (by exact_mod_cast hr0) (by exact_mod_cast hr01)
    hY0a hY0b (fun i => by exact_mod_cast maxOver_nonneg _ _) hER hEC
    (fun j i => by exact_mod_cast maxOver_nonneg _ _) hEK hZ00 hZ0
    hκ00 hκ0 hκ0' hκ hDphi hΦ hZ10 hZ1 hR0 hR hKA0 hKAd hKA hZ2₀0 hZ2₀ hZ2₁0 hZ2₁ hp0' hp1'

end FourierPeriodicData

end RadiiPolynomial
