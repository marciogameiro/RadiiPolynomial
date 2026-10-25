module

public import RadiiPolynomial.Problems.ChebyshevRadii

/-!
# Initial value problems via Chebyshev series

The initial value problem `u' = L f(u)` on `[-1, 1]`, `u(-1) = x₀`, is the boundary value problem
with `B₋ = I`, `B₊ = 0`, `q = x₀` (`ChebBVP.ivp`). Its zero finding map, derivative and radii
polynomial theorem are those of `ChebBVP` (`ChebBVP.F`, `ChebBVP.hasFDerivAt_F`,
`ChebBVP.radii_poly_two_radii`); the row `k = 0` of `F` is the initial condition
`F_j(a)_0 = x₀,j - u_j(-1)` (`ChebBVP.ivp_F_apply_zero`).
-/

@[expose] public section

namespace RadiiPolynomial

namespace ChebBVP

open Chebyshev

variable {n : ℕ} (f : Fin n → MvPolynomial (Fin n) ℝ) (L : ℝ) (x₀ : Fin n → ℝ) (ν : ℝ)
  (hν : 1 ≤ ν)

/-- For the initial value problem, `F_j(a)_0 = x₀,j - u_j(-1)`. -/
theorem ivp_F_apply_zero (a : Fin n → X ν hν) (j : Fin n) :
    (ivp f L x₀).F ν hν a j 0 = x₀ j - evalMinus ν hν (a j) := by
  rw [F_apply_zero, bcLin, sum_apply,
    Finset.sum_eq_single j (fun i _ hij => by simp [ivp, Matrix.one_apply_ne' hij]) (by simp)]
  simp [ivp]

end ChebBVP

end RadiiPolynomial
