import VSCLReuse.P47.Definitions

namespace VSCLReuse

private theorem p47_charpoly_solvent {n p : ℕ}
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hu : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (lambda (s.orderIsoOfFin hs j).val)) := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  have hWD : W⁻¹ * (W * D) = D := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul W hu, one_mul]
  calc
    (p47Solvent lambda v s hs).charpoly = (W * D * W⁻¹).charpoly := rfl
    _ = (W⁻¹ * (W * D)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = D.charpoly := by rw [hWD]
    _ = _ := Matrix.charpoly_diagonal _

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
    have hroot : Polynomial.IsRoot
        (∏ j : Fin n, (Polynomial.X - Polynomial.C
          (lambda (t.val.orderIsoOfFin t.property j).val))) (lambda a) := by
      rw [← p47_charpoly_solvent lambda v t.val t.property (hHaar t.val t.property),
        ← heq, p47_charpoly_solvent lambda v s.val s.property (hHaar s.val s.property)]
      apply (Polynomial.isRoot_prod _ _ _).2
      refine ⟨(s.val.orderIsoOfFin s.property).symm ⟨a, ha⟩, Finset.mem_univ _, ?_⟩
      simp [Polynomial.IsRoot]
    obtain ⟨j, _, hj⟩ := (Polynomial.isRoot_prod _ _ _).1 hroot
    have hval : lambda (t.val.orderIsoOfFin t.property j).val = lambda a := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hj
      exact (sub_eq_zero.mp hj).symm
    have heqa : (t.val.orderIsoOfFin t.property j).val = a := hinj hval
    rw [← heqa]
    exact (t.val.orderIsoOfFin t.property j).property
  · exact le_of_eq (t.property.trans s.property.symm)

private theorem p47_solvent_eq {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hu : IsUnit (p47EigenvectorMatrix v s hs).det) :
    let X := p47Solvent lambda v s hs
    A * X * X + B * X + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  have hcols : A * W * D * D + B * W * D + C * W = 0 := by
    ext i j
    let a := (s.orderIsoOfFin hs j).val
    have h := congrFun (hEig a) i
    have he : (lambda a)^2 * (A.mulVec (v a)) i +
        (lambda a) * (B.mulVec (v a)) i + (C.mulVec (v a)) i = 0 := by
      simpa [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    simp only [Matrix.add_apply, Matrix.zero_apply]
    simp only [D, p47EigenvalueMatrix, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, W, p47EigenvectorMatrix, p47SelectedVector]
    simpa only [Matrix.mulVec, pow_two, mul_assoc, mul_left_comm, mul_comm] using he
  let X := p47Solvent lambda v s hs
  change A * X * X + B * X + C = 0
  have hXW : X * W = W * D := by
    dsimp [X, p47Solvent]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul W hu, Matrix.mul_one]
  have hAX : A * X * X * W = A * W * D * D := by
    calc
      A * X * X * W = A * (X * (X * W)) := by simp only [Matrix.mul_assoc]
      _ = A * (X * (W * D)) := by rw [hXW]
      _ = A * (W * D * D) := by rw [← Matrix.mul_assoc X W D, hXW]
      _ = A * W * D * D := by simp only [Matrix.mul_assoc]
  have hBX : B * X * W = B * W * D := by
    rw [Matrix.mul_assoc, hXW]
    simp only [Matrix.mul_assoc]
  have hY : (A * X * X + B * X + C) * W = 0 := by
    calc
      (A * X * X + B * X + C) * W =
          A * W * D * D + B * W * D + C * W := by
        simp only [Matrix.add_mul, hAX, hBX]
      _ = 0 := hcols
  have hY' := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * W⁻¹) hY
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hu,
    Matrix.mul_one, zero_mul] using hY'

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
  constructor
  · rw [Finset.card_image_of_injective _
      (p47_solvent_injective lambda hinj v hHaar)]
    simpa using (Fintype.card_finset_len (α := Fin p) n)
  · intro X hX
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hX
    exact p47_solvent_eq A B C lambda v hEig s.val s.property (hHaar s.val s.property)

end VSCLReuse
