import VSCLReuse.P47.Definitions

namespace VSCLReuse

private lemma p47_charpoly_solvent {n p : ℕ} (lambda : Fin p → ℂ)
    (v : Fin p → Fin n → ℂ) (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    (p47Solvent lambda v s hs).charpoly =
      (p47EigenvalueMatrix lambda s hs).charpoly := by
  unfold p47Solvent
  rw [Matrix.charpoly_mul_comm (p47EigenvectorMatrix v s hs *
    p47EigenvalueMatrix lambda s hs) (p47EigenvectorMatrix v s hs)⁻¹]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW, one_mul]

private lemma p47_solvent_root_iff {n p : ℕ} (lambda : Fin p → ℂ)
    (hinj : Function.Injective lambda) (v : Fin p → Fin n → ℂ)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) (a : Fin p) :
    Polynomial.eval (lambda a) (p47Solvent lambda v s hs).charpoly = 0 ↔ a ∈ s := by
  rw [p47_charpoly_solvent lambda v s hs hW]
  simp only [p47EigenvalueMatrix, Matrix.charpoly_diagonal, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    sub_eq_zero, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have ha : a = (s.orderIsoOfFin hs j).val := hinj hj
    rw [ha]
    exact (s.orderIsoOfFin hs j).property
  · intro ha
    obtain ⟨j, hj⟩ := (s.orderIsoOfFin hs).surjective ⟨a, ha⟩
    refine ⟨j, ?_⟩
    exact congrArg (fun x : s => lambda x.val) hj.symm

private lemma p47_solvent_equation {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ) (lambda : Fin p → ℂ)
    (v : Fin p → Fin n → ℂ)
    (hEig : ∀ a : Fin p, (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (s : Finset (Fin p)) (hs : s.card = n)
    (hW : IsUnit (p47EigenvectorMatrix v s hs).det) :
    A * p47Solvent lambda v s hs * p47Solvent lambda v s hs +
      B * p47Solvent lambda v s hs + C = 0 := by
  let W := p47EigenvectorMatrix v s hs
  let D := p47EigenvalueMatrix lambda s hs
  have hWD : A * W * D * D + B * W * D + C * W = 0 := by
    ext i j
    let a := (s.orderIsoOfFin hs j).val
    have he := congrFun (hEig a) i
    simp only [p47Polynomial, Matrix.add_mulVec, Matrix.smul_mulVec,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at he
    simp only [Matrix.add_apply, D, p47EigenvalueMatrix, Matrix.mul_diagonal]
    simpa [W, a, p47EigenvectorMatrix, p47SelectedVector,
      Matrix.mul_apply, Matrix.mulVec, dotProduct,
      mul_left_comm, mul_comm, pow_two, mul_assoc] using he
  unfold p47Solvent
  change A * (W * D * W⁻¹) * (W * D * W⁻¹) +
    B * (W * D * W⁻¹) + C = 0
  have hWi : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hWr : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hW
  have hXX : (W * D * W⁻¹) * (W * D * W⁻¹) = W * D * D * W⁻¹ := by
    calc
      _ = W * D * (W⁻¹ * W) * D * W⁻¹ := by noncomm_ring
      _ = W * D * D * W⁻¹ := by rw [hWi, Matrix.mul_one]
  calc
    A * (W * D * W⁻¹) * (W * D * W⁻¹) +
        B * (W * D * W⁻¹) + C
      = (A * W * D * D + B * W * D + C * W) * W⁻¹ := by
          rw [Matrix.mul_assoc A, hXX]
          have hC : C = C * W * W⁻¹ := by rw [Matrix.mul_assoc, hWr, Matrix.mul_one]
          conv_lhs => rw [hC]
          noncomm_ring
    _ = 0 := by rw [hWD, zero_mul]

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
  let f : {s : Finset (Fin p) // s.card = n} → Matrix (Fin n) (Fin n) ℂ :=
    fun s => p47Solvent lambda v s.val s.property
  have hf : Function.Injective f := by
    intro s t heq
    change p47Solvent lambda v s.val s.property =
      p47Solvent lambda v t.val t.property at heq
    apply Subtype.ext
    apply Finset.ext
    intro a
    have hS := p47_solvent_root_iff lambda hinj v s.val s.property
      (hHaar s.val s.property) a
    have hT := p47_solvent_root_iff lambda hinj v t.val t.property
      (hHaar t.val t.property) a
    constructor
    · intro ha
      apply hT.mp
      rw [← heq]
      exact hS.mpr ha
    · intro ha
      apply hS.mp
      rw [heq]
      exact hT.mpr ha
  have hcount : (Finset.univ : Finset {s : Finset (Fin p) // s.card = n}).card =
      Nat.choose p n := by
    calc
      _ = Fintype.card {s : Finset (Fin p) // s.card = n} := rfl
      _ = ((Finset.univ : Finset (Fin p)).powersetCard n).card :=
        Fintype.card_of_subtype _ (by intro s; simp)
      _ = Nat.choose p n := by simp
  change ((Finset.univ : Finset {s : Finset (Fin p) // s.card = n}).image f).card =
      Nat.choose p n ∧
    ∀ X ∈ (Finset.univ : Finset {s : Finset (Fin p) // s.card = n}).image f,
      A * X * X + B * X + C = 0
  constructor
  · rw [Finset.card_image_of_injective _ hf]
    exact hcount
  · intro X hX
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hX
    exact p47_solvent_equation A B C lambda v hEig s.val s.property
      (hHaar s.val s.property)

end VSCLReuse
