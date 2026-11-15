import Mathlib

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius

/-! Definitions for the Newton--Schulz error calculation in Section 6.3. -/

structure P17FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P17RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable def p17MatMul {n : ℕ}
    (A B : P17RealMatrix n) : P17RealMatrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p17Transpose {n : ℕ}
    (A : P17RealMatrix n) : P17RealMatrix n :=
  fun i j ↦ A j i

noncomputable def p17Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

def P17GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

noncomputable def p17RoundedDotProduct (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p17RoundedMatMul (fp : P17FPModel) {n : ℕ}
    (A B : P17RealMatrix n) : P17RealMatrix n :=
  fun i j ↦ p17RoundedDotProduct fp n (A i) (fun k ↦ B k j)

/-- The two rounded products used to form `XXᵀX` in equation (6.6). -/
noncomputable def p17RoundedGramTriple (fp : P17FPModel) {n : ℕ}
    (X : P17RealMatrix n) : P17RealMatrix n :=
  p17RoundedMatMul fp (p17RoundedMatMul fp X (p17Transpose X)) X

noncomputable def p17ExactGramTriple {n : ℕ}
    (X : P17RealMatrix n) : P17RealMatrix n :=
  p17MatMul (p17MatMul X (p17Transpose X)) X

/-- The componentwise majorant for the forward error `ε₁` in equation (6.6). -/
noncomputable def p17GramTripleErrorMajorant (fp : P17FPModel) {n : ℕ}
    (X : P17RealMatrix n) (i j : Fin n) : ℝ :=
  p17Gamma fp.u n *
      (∑ k : Fin n,
        |p17RoundedMatMul fp X (p17Transpose X) i k| * |X k j|) +
    p17Gamma fp.u n *
      (∑ k : Fin n,
        (∑ l : Fin n, |X i l| * |X k l|) * |X k j|)

/-! Definitions for the square-matrix error-transport core of Lemma 4.1. -/

abbrev P17ComplexMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

noncomputable def p17Sym {n : ℕ}
    (A : P17ComplexMatrix n) : P17ComplexMatrix n :=
  (2 : ℂ)⁻¹ • (A + star A)

noncomputable def p17HermitianEstimate {n : ℕ}
    (U X : P17ComplexMatrix n) : P17ComplexMatrix n :=
  p17Sym (star U * X)

noncomputable def p17CoreCoefficient (eps d : ℝ) : ℝ :=
  (2 * d + 1) * eps

/-- The identities and quantitative bounds established in the square-case proof
of Lemma 4.1 before the final residual and Hermitian-factor estimates. -/
structure P17Lemma41CoreData (n : ℕ) where
  X : P17ComplexMatrix n
  Xbar : P17ComplexMatrix n
  Yhat : P17ComplexMatrix n
  fXbar : P17ComplexMatrix n
  P : P17ComplexMatrix n
  Q : P17ComplexMatrix n
  Sigma : P17ComplexMatrix n
  fSigma : P17ComplexMatrix n
  recoveryDiagonal : P17ComplexMatrix n
  U : P17ComplexMatrix n
  HY : P17ComplexMatrix n
  Hbar : P17ComplexMatrix n
  H : P17ComplexMatrix n
  fHbar : P17ComplexMatrix n
  Z : P17ComplexMatrix n
  EX : P17ComplexMatrix n
  EY : P17ComplexMatrix n
  EH : P17ComplexMatrix n
  eps : ℝ
  d : ℝ
  xScale : ℝ
  fScale : ℝ
  eps_nonneg : 0 ≤ eps
  d_nonneg : 0 ≤ d
  xScale_nonneg : 0 ≤ xScale
  fScale_pos : 0 < fScale
  xbar_eq : Xbar = X + EX
  y_forward : Yhat = fXbar + EY
  y_polar : Yhat = U * HY
  hy_perturbed : HY = fHbar + EH
  xbar_svd : Xbar = P * Sigma * star Q
  fxbar_svd : fXbar = P * fSigma * star Q
  hbar_svd : Hbar = Q * Sigma * star Q
  fhbar_svd : fHbar = Q * fSigma * star Q
  z_svd : Z = Q * recoveryDiagonal * star Q
  q_unitary_left : star Q * Q = 1
  singular_recovery : fSigma * recoveryDiagonal = Sigma
  unitary_left : star U * U = 1
  U_left_isometry : ∀ W : P17ComplexMatrix n, ‖U * W‖ = ‖W‖
  Ustar_left_isometry : ∀ W : P17ComplexMatrix n, ‖star U * W‖ = ‖W‖
  hbar_selfadjoint : star Hbar = Hbar
  h_selfadjoint : star H = H
  ex_bound : ‖EX‖ ≤ eps * xScale
  ey_bound : ‖EY‖ ≤ eps * fScale
  eh_bound : ‖EH‖ ≤ eps * fScale
  z_scaled_bound : fScale * ‖Z‖ ≤ d * xScale
  hermitian_polar_bound : ‖Hbar - H‖ ≤ eps * xScale

end VSCLReuse
