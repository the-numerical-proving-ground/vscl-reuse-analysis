import VSCLReuse.P47.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix
open Matrix Polynomial

private theorem p47_charpoly_solvent {n p : ℕ}
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hunit : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (lambda (s.orderIsoOfFin hs j).val)) := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  calc
    (p47Solvent lambda v s hs).charpoly = (W * D * W⁻¹).charpoly := rfl
    _ = (W⁻¹ * (W * D)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = D.charpoly := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul W hunit, one_mul]
    _ = _ := Matrix.charpoly_diagonal _

private theorem p47_mem_iff {n p : ℕ} (s : Finset (Fin p)) (hs : s.card = n)
    (a : Fin p) : a ∈ s ↔ ∃ j : Fin n, (s.orderIsoOfFin hs j).val = a := by
  constructor
  · intro ha
    let j := (s.orderIsoOfFin hs).symm ⟨a, ha⟩
    exact ⟨j, congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨a, ha⟩)⟩
  · rintro ⟨j, rfl⟩
    exact (s.orderIsoOfFin hs j).property

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
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨j, hj⟩ := (p47_mem_iff s.val s.property a).mp ha
    have hroot :
        (∏ k : Fin n, (Polynomial.X - Polynomial.C (lambda (s.val.orderIsoOfFin s.property k).val))).eval
          (lambda a) = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
    have hroot' :
        (∏ k : Fin n, (Polynomial.X - Polynomial.C (lambda (t.val.orderIsoOfFin t.property k).val))).eval
          (lambda a) = 0 := by
      rw [← p47_charpoly_solvent lambda v s.val s.property (hHaar s.val s.property)] at hroot
      rw [← p47_charpoly_solvent lambda v t.val t.property (hHaar t.val t.property)]
      rwa [← heq]
    rw [Polynomial.eval_prod] at hroot'
    obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp hroot'
    have hval : (t.val.orderIsoOfFin t.property k).val = a := by
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
      exact hinj hk.symm
    exact (p47_mem_iff t.val t.property a).mpr ⟨k, hval⟩
  · intro ha
    obtain ⟨j, hj⟩ := (p47_mem_iff t.val t.property a).mp ha
    have hroot :
        (∏ k : Fin n, (Polynomial.X - Polynomial.C (lambda (t.val.orderIsoOfFin t.property k).val))).eval
          (lambda a) = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
    have hroot' :
        (∏ k : Fin n, (Polynomial.X - Polynomial.C (lambda (s.val.orderIsoOfFin s.property k).val))).eval
          (lambda a) = 0 := by
      rw [← p47_charpoly_solvent lambda v t.val t.property (hHaar t.val t.property)] at hroot
      rw [← p47_charpoly_solvent lambda v s.val s.property (hHaar s.val s.property)]
      rwa [heq]
    rw [Polynomial.eval_prod] at hroot'
    obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp hroot'
    have hval : (s.val.orderIsoOfFin s.property k).val = a := by
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
      exact hinj hk.symm
    exact (p47_mem_iff s.val s.property a).mpr ⟨k, hval⟩

private theorem p47_mul_W_apply {n p : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin p → Fin n → ℂ) (s : Finset (Fin p)) (hs : s.card = n)
    (i j : Fin n) :
    (M * p47EigenvectorMatrix v s hs) i j =
      (M.mulVec (v (s.orderIsoOfFin hs j).val)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    p47EigenvectorMatrix, p47SelectedVector]

private theorem p47_selected_equation {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p, (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n) :
    let W := p47EigenvectorMatrix v s hs
    let D := p47EigenvalueMatrix lambda s hs
    A * W * D * D + B * W * D + C * W = 0 := by
  dsimp
  ext i j
  have he := congrFun (hEig (s.orderIsoOfFin hs j).val) i
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_diagonal,
    p47EigenvalueMatrix, p47_mul_W_apply] 
  simp only [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at he
  simp only [smul_eq_mul] at he
  convert he using 1 <;> ring

private theorem p47_solvent_equation {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p, (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hunit : IsUnit (p47EigenvectorMatrix v s hs).det) :
    let X := p47Solvent lambda v s hs
    A * X * X + B * X + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  let X := p47Solvent lambda v s hs
  have hWinv : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hunit
  have hW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hunit
  have hXW : X * W = W * D := by
    calc
      X * W = W * D * (W⁻¹ * W) := by simp [X, p47Solvent, W, D, Matrix.mul_assoc]
      _ = W * D := by rw [hWinv, Matrix.mul_one]
  have hXXW : (X * X) * W = W * D * D := by
    calc
      (X * X) * W = X * (X * W) := by rw [Matrix.mul_assoc]
      _ = X * (W * D) := by rw [hXW]
      _ = (X * W) * D := by rw [Matrix.mul_assoc]
      _ = W * D * D := by rw [hXW]
  have hprod : (A * X * X + B * X + C) * W = 0 := by
    calc
      (A * X * X + B * X + C) * W = A * ((X * X) * W) + B * (X * W) + C * W := by
        simp [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * (W * D * D) + B * (W * D) + C * W := by rw [hXXW, hXW]
      _ = 0 := by simpa [W, D, Matrix.mul_assoc] using
        (p47_selected_equation A B C lambda v hEig s hs)
  have h := congrArg (fun Y : Matrix (Fin n) (Fin n) ℂ => Y * W⁻¹) hprod
  simpa only [Matrix.mul_assoc, hW, Matrix.mul_one, Matrix.zero_mul] using h

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
  have hcard : Fintype.card {s : Finset (Fin p) // s.card = n} = Nat.choose p n := by
    rw [Fintype.card_of_subtype (Finset.powersetCard n (Finset.univ : Finset (Fin p)))
      (by intro s; simp)]
    simp
  dsimp only
  constructor
  · rw [Finset.card_image_of_injective _ (p47_solvent_injective lambda hinj v hHaar)]
    simpa using hcard
  · intro X hX
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hX
    exact p47_solvent_equation A B C lambda v hEig s.val s.property (hHaar s.val s.property)

end VSCLReuse
