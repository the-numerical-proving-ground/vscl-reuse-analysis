import VSCLReuse.P47.Definitions

namespace VSCLReuse

open Matrix Polynomial
open scoped BigOperators

private theorem p47_charpoly_solvent {n p : ℕ}
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (lambda (s.orderIsoOfFin hs j).val)) := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  have hWI : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  change (W * D * W⁻¹).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hWI, one_mul]
  exact Matrix.charpoly_diagonal _

private theorem p47_solvent_injective {n p : ℕ}
    (lambda : Fin p → ℂ) (hinj : Function.Injective lambda)
    (v : Fin p → Fin n → ℂ)
    (hHaar : ∀ (s : Finset (Fin p)) (hs : s.card = n),
      IsUnit (p47EigenvectorMatrix v s hs).det) :
    Function.Injective (fun s : {s : Finset (Fin p) // s.card = n} =>
      p47Solvent lambda v s.val s.property) := by
  intro s t heq
  change p47Solvent lambda v s.val s.property =
    p47Solvent lambda v t.val t.property at heq
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨j, hj⟩ := (s.val.orderIsoOfFin s.property).surjective ⟨a, ha⟩
    have hja : (s.val.orderIsoOfFin s.property j).val = a := congrArg Subtype.val hj
    have hpoly := p47_charpoly_solvent lambda v s.val s.property (hHaar _ _)
    have hpoly' := p47_charpoly_solvent lambda v t.val t.property (hHaar _ _)
    have hz : (∏ k : Fin n,
        (Polynomial.X - Polynomial.C (lambda (t.val.orderIsoOfFin t.property k).val))).eval
          (lambda a) = 0 := by
      rw [← hpoly', ← heq, hpoly, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hja]
    rw [Polynomial.eval_prod] at hz
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
    have hka : (t.val.orderIsoOfFin t.property k).val = a := by
      apply hinj
      exact (sub_eq_zero.mp (by simpa using hk)).symm
    rw [← hka]
    exact (t.val.orderIsoOfFin t.property k).property
  · simpa [s.property, t.property]

private theorem p47_solvent_equation {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    A * p47Solvent lambda v s hs * p47Solvent lambda v s hs +
      B * p47Solvent lambda v s hs + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  let X := p47Solvent lambda v s hs
  have hWI : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hW
  have hIW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hXW : X * W = W * D := by
    change (W * D * W⁻¹) * W = W * D
    rw [Matrix.mul_assoc, hIW, Matrix.mul_one]
  have hcore : A * W * D * D + B * W * D + C * W = 0 := by
    ext i j
    let a := (s.orderIsoOfFin hs j).val
    have hcol (M : Matrix (Fin n) (Fin n) ℂ) :
        (M * W) i j = (M.mulVec (v a)) i := by
      simp [W, a, p47EigenvectorMatrix, p47SelectedVector,
        Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have he := congrArg (fun w : Fin n → ℂ => w i) (hEig a)
    have he' : (lambda a)^2 * (A.mulVec (v a)) i +
        (lambda a) * (B.mulVec (v a)) i + (C.mulVec (v a)) i = 0 := by
      simpa [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec] using he
    simp only [Matrix.add_apply, Matrix.zero_apply, D, p47EigenvalueMatrix,
      Matrix.mul_diagonal, hcol]
    calc
      (A.mulVec (v a)) i * lambda a * lambda a +
          (B.mulVec (v a)) i * lambda a + (C.mulVec (v a)) i =
          lambda a ^ 2 * (A.mulVec (v a)) i +
          lambda a * (B.mulVec (v a)) i + (C.mulVec (v a)) i := by ring
      _ = 0 := he'
  have hXXW : X * X * W = W * D * D := by
    calc
      X * X * W = X * (X * W) := by rw [Matrix.mul_assoc]
      _ = X * (W * D) := by rw [hXW]
      _ = W * D * D := by rw [← Matrix.mul_assoc, hXW]
  have hresW : (A * X * X + B * X + C) * W = 0 := by
    calc
      (A * X * X + B * X + C) * W = A * (X * X * W) + B * (X * W) + C * W := by
        simp [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * W * D * D + B * W * D + C * W := by
        rw [hXXW, hXW]
        simp [Matrix.mul_assoc]
      _ = 0 := hcore
  have hres : (A * X * X + B * X + C) = 0 := by
    calc
      A * X * X + B * X + C = (A * X * X + B * X + C) * W * W⁻¹ := by
        simp [Matrix.mul_assoc, hWI]
      _ = 0 := by simp [hresW]
  exact hres

theorem p47_c1_theorem2_1_at_least {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (hinj : Function.Injective lambda)
    (v : Fin p → Fin n → ℂ)
    (hnp : n ≤ p) (hp2n : p ≤ 2 * n)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (hHaar : ∀ (s : Finset (Fin p)) (hs : s.card = n),
      IsUnit (p47EigenvectorMatrix v s hs).det) :
    let solvents :=
      (Finset.univ : Finset {s : Finset (Fin p) // s.card = n}).image
        (fun s => p47Solvent lambda v s.val s.property)
    solvents.card = Nat.choose p n ∧
      ∀ X ∈ solvents, A * X * X + B * X + C = 0 := by
  -- PROOF_START P47-C1-H001
  classical
  dsimp
  constructor
  · rw [Finset.card_image_of_injective _
      (p47_solvent_injective lambda hinj v hHaar)]
    rw [Finset.card_univ, Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter (fun s : Finset (Fin p) => s.card = n)) =
          Finset.powersetCard n Finset.univ := by
      ext s
      simp
    rw [hfilter, Finset.card_powersetCard]
    simp
  · intro X hX
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hX
    exact p47_solvent_equation A B C lambda v s.val s.property hEig (hHaar _ _)

end VSCLReuse
