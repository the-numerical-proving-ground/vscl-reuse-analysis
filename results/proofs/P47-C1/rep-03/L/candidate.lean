import VSCLReuse.P47.Definitions

namespace VSCLReuse

private theorem p47_solvent_charpoly {n p : ℕ} (lambda : Fin p → ℂ)
    (v : Fin p → Fin n → ℂ) (s : Finset (Fin p)) (hs : s.card = n)
    (hunit : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (lambda (s.orderIsoOfFin hs j).val)) := by
  unfold p47Solvent
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp only [Matrix.nonsing_inv_mul _ hunit, one_mul]
  exact Matrix.charpoly_diagonal _

private theorem p47_solvent_root_iff {n p : ℕ} (lambda : Fin p → ℂ)
    (hinj : Function.Injective lambda) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hunit : IsUnit (p47EigenvectorMatrix v s hs).det) (a : Fin p) :
    Polynomial.IsRoot (p47Solvent lambda v s hs).charpoly (lambda a) ↔ a ∈ s := by
  rw [p47_solvent_charpoly lambda v s hs hunit]
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    sub_eq_zero, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact (hinj hj.symm) ▸ (s.orderIsoOfFin hs j).property
  · intro ha
    let j := (s.orderIsoOfFin hs).symm ⟨a, ha⟩
    refine ⟨j, ?_⟩
    simp [j]

private theorem p47_selected_matrix_eq {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n) :
    let W := p47EigenvectorMatrix v s hs
    let D := p47EigenvalueMatrix lambda s hs
    (A * W) * (D * D) + (B * W) * D + C * W = 0 := by
  dsimp
  ext i j
  let a : Fin p := (s.orderIsoOfFin hs j).val
  have he := congrFun (hEig a) i
  simp only [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at he
  simp only [Matrix.add_apply, Matrix.zero_apply,
    p47EigenvalueMatrix, Matrix.diagonal_mul_diagonal,
    Matrix.mul_diagonal]
  simpa [p47EigenvectorMatrix, p47SelectedVector, a,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, pow_two] using he

private theorem p47_solvent_eq {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hunit : IsUnit (p47EigenvectorMatrix v s hs).det) :
    let X := p47Solvent lambda v s hs
    A * X * X + B * X + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  let X := p47Solvent lambda v s hs
  have hW : IsUnit W.det := hunit
  have hWD : X * W = W * D := by
    change (W * D * W⁻¹) * W = W * D
    calc
      (W * D * W⁻¹) * W = W * D * (W⁻¹ * W) := by simp [mul_assoc]
      _ = W * D := by rw [Matrix.nonsing_inv_mul W hW, mul_one]
  have hX2W : X * X * W = W * (D * D) := by
    calc
      X * X * W = X * (X * W) := by simp [mul_assoc]
      _ = X * (W * D) := by rw [hWD]
      _ = (X * W) * D := by rw [mul_assoc]
      _ = (W * D) * D := by rw [hWD]
      _ = W * (D * D) := by rw [mul_assoc]
  have hselected : (A * W) * (D * D) + (B * W) * D + C * W = 0 :=
    p47_selected_matrix_eq A B C lambda v hEig s hs
  have hEW : (A * X * X + B * X + C) * W = 0 := by
    calc
      (A * X * X + B * X + C) * W =
          A * (X * X * W) + B * (X * W) + C * W := by
            simp [add_mul, mul_assoc]
      _ = A * (W * (D * D)) + B * (W * D) + C * W := by
        rw [hX2W, hWD]
      _ = (A * W) * (D * D) + (B * W) * D + C * W := by
        simp [mul_assoc]
      _ = 0 := hselected
  have hE : A * X * X + B * X + C = 0 := by
    calc
      A * X * X + B * X + C = (A * X * X + B * X + C) * W * W⁻¹ := by
        simp [mul_assoc, Matrix.mul_nonsing_inv _ hW]
      _ = 0 := by rw [hEW]; simp
  exact hE

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
  have hInjective : Function.Injective
      (fun s : {s : Finset (Fin p) // s.card = n} =>
        p47Solvent lambda v s.val s.property) := by
    intro s t heq
    change p47Solvent lambda v s.val s.property =
      p47Solvent lambda v t.val t.property at heq
    apply Subtype.ext
    apply Finset.ext
    intro a
    calc
      a ∈ s.val ↔
          Polynomial.IsRoot (p47Solvent lambda v s.val s.property).charpoly (lambda a) :=
        (p47_solvent_root_iff lambda hinj v s.val s.property
          (hHaar s.val s.property) a).symm
      _ ↔ Polynomial.IsRoot (p47Solvent lambda v t.val t.property).charpoly (lambda a) := by
        rw [heq]
      _ ↔ a ∈ t.val :=
        p47_solvent_root_iff lambda hinj v t.val t.property
          (hHaar t.val t.property) a
  constructor
  · simp only [Finset.card_image_of_injective _ hInjective,
      Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin]
  · intro X hX
    rcases Finset.mem_image.mp hX with ⟨s, _, rfl⟩
    exact p47_solvent_eq A B C lambda v hEig s.val s.property
      (hHaar s.val s.property)

end VSCLReuse
