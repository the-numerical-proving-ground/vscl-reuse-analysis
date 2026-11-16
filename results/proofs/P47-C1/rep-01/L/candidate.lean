import VSCLReuse.P47.Definitions

namespace VSCLReuse

private theorem p47_charpoly_solvent {n p : ℕ}
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (lambda (s.orderIsoOfFin hs j).val)) := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  change (W * D * W⁻¹).charpoly = _
  rw [Matrix.charpoly_mul_comm (W * D) W⁻¹]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul W hW, one_mul]
  exact Matrix.charpoly_diagonal _

private theorem p47_solvent_injective {n p : ℕ}
    (lambda : Fin p → ℂ) (hinj : Function.Injective lambda)
    (v : Fin p → Fin n → ℂ)
    (hHaar : ∀ (s : Finset (Fin p)) (hs : s.card = n),
      IsUnit (p47EigenvectorMatrix v s hs).det) :
    Function.Injective (fun s : {s : Finset (Fin p) // s.card = n} =>
      p47Solvent lambda v s.val s.property) := by
  intro s t hst
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    let i : Fin n := (s.val.orderIsoOfFin s.property).symm ⟨a, ha⟩
    have hai : (s.val.orderIsoOfFin s.property i).val = a := by
      simp [i]
    have hpoly :
        (∏ j : Fin n, (Polynomial.X - Polynomial.C
          (lambda (s.val.orderIsoOfFin s.property j).val))) =
        ∏ j : Fin n, (Polynomial.X - Polynomial.C
          (lambda (t.val.orderIsoOfFin t.property j).val)) := by
      rw [← p47_charpoly_solvent lambda v s.val s.property (hHaar _ _),
        ← p47_charpoly_solvent lambda v t.val t.property (hHaar _ _)]
      exact congrArg Matrix.charpoly hst
    have heval :
        Polynomial.eval (lambda a)
          (∏ j : Fin n, (Polynomial.X - Polynomial.C
            (lambda (s.val.orderIsoOfFin s.property j).val))) = 0 := by
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hai])
    rw [hpoly] at heval
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp heval
    have haj : a = (t.val.orderIsoOfFin t.property j).val :=
      hinj (sub_eq_zero.mp hj)
    rw [haj]
    exact (t.val.orderIsoOfFin t.property j).property
  · simp [s.property, t.property]

private theorem p47_solvent_is_solvent {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    let X := p47Solvent lambda v s hs
    A * X * X + B * X + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  let X := p47Solvent lambda v s hs
  have hWD : A * W * D * D + B * W * D + C * W = 0 := by
    ext i j
    let a : Fin p := (s.orderIsoOfFin hs j).val
    have he : (lambda a) ^ 2 * (A.mulVec (v a)) i +
        (lambda a) * (B.mulVec (v a)) i + (C.mulVec (v a)) i = 0 := by
      have h := congrFun (hEig a) i
      simpa [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    have hA : (A * W) i j = (A.mulVec (v a)) i := rfl
    have hB : (B * W) i j = (B.mulVec (v a)) i := rfl
    have hC : (C * W) i j = (C.mulVec (v a)) i := rfl
    simp only [Matrix.add_apply, Matrix.zero_apply, D, p47EigenvalueMatrix,
      Matrix.mul_diagonal]
    rw [hA, hB, hC]
    dsimp [D, p47EigenvalueMatrix]
    simp only [a, Finset.coe_orderIsoOfFin_apply] at he
    simp only [a, Finset.coe_orderIsoOfFin_apply]
    linear_combination he
  have hXW : X * W = W * D := by
    change W * D * W⁻¹ * W = W * D
    rw [Matrix.mul_assoc (W * D) W⁻¹ W, Matrix.nonsing_inv_mul W hW,
      Matrix.mul_one]
  have hXXW : X * X * W = W * D * D := by
    calc
      X * X * W = X * (X * W) := by rw [Matrix.mul_assoc]
      _ = X * (W * D) := by rw [hXW]
      _ = W * D * D := by rw [← Matrix.mul_assoc, hXW]
  have hmul : (A * X * X + B * X + C) * W = 0 := by
    calc
      (A * X * X + B * X + C) * W = A * (X * X * W) + B * (X * W) + C * W := by
        simp [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * W * D * D + B * W * D + C * W := by
        rw [hXXW, hXW]
        simp only [Matrix.mul_assoc]
      _ = 0 := hWD
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M * W⁻¹) hmul
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hW] using h

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
  dsimp
  constructor
  · rw [Finset.card_image_of_injective _
      (p47_solvent_injective lambda hinj v hHaar)]
    rw [Finset.card_univ, Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter (fun s : Finset (Fin p) => s.card = n)) =
          Finset.powersetCard n (Finset.univ : Finset (Fin p)) := by
      ext s
      simp
    rw [hfilter, Finset.card_powersetCard]
    simp
  · intro X hX
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hX
    exact p47_solvent_is_solvent A B C lambda v hEig s.val s.property
      (hHaar s.val s.property)

end VSCLReuse
