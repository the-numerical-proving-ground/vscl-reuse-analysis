import Mathlib

namespace VSCLReuse

open scoped BigOperators Matrix
open Matrix

/-- The quadratic matrix polynomial `Q(λ) = λ² A + λ B + C`. -/
def p47Polynomial {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  z ^ 2 • A + z • B + C

/-- Eigenvector columns selected from a set of paper eigenpairs. -/
def p47SelectedVector {n p : ℕ} (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n) (j : Fin n) : Fin n → ℂ :=
  v (s.orderIsoOfFin hs j).val

/-- The ordered matrix `W` whose columns are the selected eigenvectors. -/
def p47EigenvectorMatrix {n p : ℕ} (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => p47SelectedVector v s hs j i

/-- Diagonal eigenvalue matrix for the same selected subset. -/
def p47EigenvalueMatrix {n p : ℕ} (lambda : Fin p → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun j => lambda (s.orderIsoOfFin hs j).val)

/-- The paper's formula (2.1) for a matrix solvent from selected eigenpairs. -/
noncomputable def p47Solvent {n p : ℕ} (lambda : Fin p → ℂ)
    (v : Fin p → Fin n → ℂ) (s : Finset (Fin p)) (hs : s.card = n) :
    Matrix (Fin n) (Fin n) ℂ :=
  p47EigenvectorMatrix v s hs * p47EigenvalueMatrix lambda s hs *
    (p47EigenvectorMatrix v s hs)⁻¹

end VSCLReuse
