import VSCLReuse.P02.Definitions

namespace VSCLReuse

open Asymptotics

private lemma p02_bigO_matrix_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B s) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) s := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private lemma p02_bigO_matrix_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s t : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B t) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u * B u) (fun u ↦ s u * t u) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k hk
  exact (hA i k).mul (hB k j)

private lemma p02_bigO_matrix_const_mul {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ)
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ C * A u) s := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k hk
  exact (hA k j).const_mul_left (C i k)

private lemma p02_bigO_matrix_mul_const {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ)
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u * C) s := by
  intro i j
  simp only [Matrix.mul_apply]
  apply IsBigO.sum
  intro k hk
  simpa only [mul_comm] using (hA i k).const_mul_left (C k j)

private lemma p02_bigO_matrix_scale {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s t : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s) (hst : s =O[nhds 0] t) :
    p02MatrixFamilyIsBigOAtZero A t := by
  intro i j
  exact (hA i j).trans hst

private lemma p02_bigO_matrix_zero {m : ℕ} {s : ℝ → ℝ} :
    p02MatrixFamilyIsBigOAtZero (fun _ ↦ (0 : Matrix (Fin m) (Fin m) ℝ)) s := by
  intro i j
  simpa using (isBigO_zero s (nhds (0 : ℝ)))

private lemma p02_bigO_u_one :
    (fun u : ℝ ↦ u) =O[nhds 0] (fun _ ↦ (1 : ℝ)) := by
  exact (Filter.tendsto_id : Filter.Tendsto (fun u : ℝ ↦ u) (nhds 0) (nhds 0)).isBigO_one ℝ

private lemma p02_bigO_u_mul_u :
    (fun u : ℝ ↦ u * u) =O[nhds 0] (fun u ↦ u ^ 2) := by
  simpa only [pow_two] using
    (isBigO_refl (fun u : ℝ ↦ u * u) (nhds 0))

private lemma p02_bigO_u2_mul_one :
    (fun u : ℝ ↦ u ^ 2 * (1 : ℝ)) =O[nhds 0] (fun u ↦ u ^ 2) := by
  simpa only [mul_one] using
    (isBigO_refl (fun u : ℝ ↦ u ^ 2) (nhds 0))

private lemma p02_product_expansion {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) :
    p02PerturbedHouseholderProduct P D u omega k =
      p02HouseholderProduct P k +
        p02FirstOrderHouseholderProduct P D u omega k +
          p02HigherOrderHouseholderProduct P D u omega k := by
  induction k with
  | zero =>
      simp [p02PerturbedHouseholderProduct, p02HouseholderProduct,
        p02FirstOrderHouseholderProduct, p02HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p02PerturbedHouseholderProduct, p02HouseholderProduct,
        p02FirstOrderHouseholderProduct, p02HigherOrderHouseholderProduct]
      rw [ih]
      noncomm_ring

private lemma p02_matvec_add {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ) :
    p02MatVec (A + B) b = p02MatVec A b + p02MatVec B b := by
  funext i
  simp [p02MatVec, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply]

private lemma p02_product_orders {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hD : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero (fun u ↦ D u j omega) (fun u ↦ u)) :
    ∀ k, k ≤ r →
      p02MatrixFamilyIsBigOAtZero
          (fun u ↦ p02FirstOrderHouseholderProduct P D u omega k)
          (fun u ↦ u) ∧
        p02MatrixSecondOrderAtZero
          (fun u ↦ p02HigherOrderHouseholderProduct P D u omega k) := by
  intro k hk
  induction k with
  | zero =>
      constructor
      · simpa only [p02FirstOrderHouseholderProduct] using
          (p02_bigO_matrix_zero (s := fun u : ℝ ↦ u) (m := m))
      · simpa only [p02MatrixSecondOrderAtZero,
          p02HigherOrderHouseholderProduct] using
          (p02_bigO_matrix_zero (s := fun u : ℝ ↦ u ^ 2) (m := m))
  | succ k ih =>
      have hklt : k < r := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      have hDk := hD k hklt
      have hDk1 := p02_bigO_matrix_scale hDk p02_bigO_u_one
      have hfirst : p02MatrixFamilyIsBigOAtZero
          (fun u ↦ p02FirstOrderHouseholderProduct P D u omega (k + 1))
          (fun u ↦ u) := by
        simpa only [p02FirstOrderHouseholderProduct] using
          (p02_bigO_matrix_add
            (p02_bigO_matrix_const_mul (P k) hprev.1)
            (p02_bigO_matrix_mul_const (p02HouseholderProduct P k) hDk))
      have hcross : p02MatrixSecondOrderAtZero
          (fun u ↦ D u k omega *
            p02FirstOrderHouseholderProduct P D u omega k) := by
        exact p02_bigO_matrix_scale
          (p02_bigO_matrix_mul hDk hprev.1) p02_bigO_u_mul_u
      have htail : p02MatrixSecondOrderAtZero
          (fun u ↦ D u k omega *
            p02HigherOrderHouseholderProduct P D u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, one_mul] using
          (p02_bigO_matrix_mul hDk1 hprev.2)
      constructor
      · exact hfirst
      · simpa only [p02MatrixSecondOrderAtZero,
          p02HigherOrderHouseholderProduct] using
          (p02_bigO_matrix_add
            (p02_bigO_matrix_add
              (p02_bigO_matrix_const_mul (P k) hprev.2) hcross) htail)

private lemma p02_householder_symmetric {m : ℕ} (v : Fin m → ℝ) :
    Matrix.transpose (p02HouseholderMatrix v) = p02HouseholderMatrix v := by
  ext i j
  simp [Matrix.transpose_apply, p02HouseholderMatrix, p02FiniteId,
    eq_comm, mul_comm]

private lemma p02_product_mul_transpose {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (hInv : ∀ j, j < r →
      p02HouseholderSequenceMatrix v j *
        p02HouseholderSequenceMatrix v j = 1) :
    ∀ k, k ≤ r →
      p02HouseholderProduct (p02HouseholderSequenceMatrix v) k *
        Matrix.transpose
          (p02HouseholderProduct (p02HouseholderSequenceMatrix v) k) = 1 := by
  intro k hk
  induction k with
  | zero => simp [p02HouseholderProduct]
  | succ k ih =>
      have hklt : k < r := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      simp only [p02HouseholderProduct, Matrix.transpose_mul]
      calc
        (p02HouseholderSequenceMatrix v k *
            p02HouseholderProduct (p02HouseholderSequenceMatrix v) k) *
            (Matrix.transpose
              (p02HouseholderProduct (p02HouseholderSequenceMatrix v) k) *
              Matrix.transpose (p02HouseholderSequenceMatrix v k)) =
          p02HouseholderSequenceMatrix v k *
            (p02HouseholderProduct (p02HouseholderSequenceMatrix v) k *
              Matrix.transpose
                (p02HouseholderProduct (p02HouseholderSequenceMatrix v) k)) *
            Matrix.transpose (p02HouseholderSequenceMatrix v k) := by
              simp only [mul_assoc]
        _ = p02HouseholderSequenceMatrix v k *
              Matrix.transpose (p02HouseholderSequenceMatrix v k) := by
              rw [hprev, mul_one]
        _ = 1 := by
              rw [show Matrix.transpose (p02HouseholderSequenceMatrix v k) =
                p02HouseholderSequenceMatrix v k from
                p02_householder_symmetric (v k)]
              exact hInv k hklt

private lemma p02_factor_step {m : ℕ}
    (P X D S F : Matrix (Fin m) (Fin m) ℝ)
    (horth : (P * X) * Matrix.transpose (P * X) = 1)
    (hfirst : X * S = F) :
    (P * X) * (S + Matrix.transpose (P * X) * D * X) =
      P * F + D * X := by
  calc
    _ = P * (X * S) + ((P * X) * Matrix.transpose (P * X)) * D * X := by
      noncomm_ring
    _ = P * F + D * X := by rw [hfirst, horth, one_mul]

private lemma p02_first_order_factor {Omega : Type*} {m r : ℕ}
    (v : ℕ → Fin m → ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hInv : ∀ j, j < r →
      p02HouseholderSequenceMatrix v j *
        p02HouseholderSequenceMatrix v j = 1)
    (u : ℝ) (omega : Omega) :
    p02HouseholderProduct (p02HouseholderSequenceMatrix v) r *
      p02TransformedHouseholderInsertionSum
        (p02HouseholderSequenceMatrix v) D u omega r =
      p02FirstOrderHouseholderProduct
        (p02HouseholderSequenceMatrix v) D u omega r := by
  have h : ∀ k, k ≤ r →
      p02HouseholderProduct (p02HouseholderSequenceMatrix v) k *
        p02TransformedHouseholderInsertionSum
          (p02HouseholderSequenceMatrix v) D u omega k =
        p02FirstOrderHouseholderProduct
          (p02HouseholderSequenceMatrix v) D u omega k := by
    intro k hk
    induction k with
    | zero => simp [p02HouseholderProduct,
        p02TransformedHouseholderInsertionSum,
        p02FirstOrderHouseholderProduct]
    | succ k ih =>
        have hklt : k < r := Nat.lt_of_succ_le hk
        have hprev := ih (Nat.le_of_lt hklt)
        have horth := p02_product_mul_transpose v hInv (k + 1) hk
        simpa only [p02HouseholderProduct,
          p02TransformedHouseholderInsertionSum, Finset.sum_range_succ,
          p02TransformedHouseholderInsertion,
          p02FirstOrderHouseholderProduct] using
          (p02_factor_step
            (p02HouseholderSequenceMatrix v k)
            (p02HouseholderProduct (p02HouseholderSequenceMatrix v) k)
            (D u k omega)
            (p02TransformedHouseholderInsertionSum
              (p02HouseholderSequenceMatrix v) D u omega k)
            (p02FirstOrderHouseholderProduct
              (p02HouseholderSequenceMatrix v) D u omega k)
            (by simpa only [p02HouseholderProduct] using horth) hprev)
  exact h r le_rfl

theorem p02_c1_householder_product_first_order_expansion
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    (model : P02Model15 Omega)
    (run : P02HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) (_hc5 : 0 < c5) (_hlambda : 0 < lambda)
    (hlocal : P02Lemma42VectorAssumption run c5 lambda) :
    ∃ (unfactoredRemainder factoredRemainder :
        ℝ → Omega → Matrix (Fin m) (Fin m) ℝ),
      (∀ omega, omega ∈ hlocal.localEvent →
        p02MatrixSecondOrderAtZero
          (fun u ↦ unfactoredRemainder u omega)) ∧
      (∀ omega, omega ∈ hlocal.localEvent →
        p02MatrixSecondOrderAtZero
          (fun u ↦ factoredRemainder u omega)) ∧
      (∀ u omega,
        run.computed u omega =
          p02ApplicationExactState run +
            p02MatVec
              (p02ApplicationFirstOrderMatrix run u omega +
                unfactoredRemainder u omega)
              run.b) ∧
      (∀ u omega,
        run.computed u omega =
            p02ApplicationExactState run +
            p02MatVec
              (Matrix.transpose (p02ApplicationQ run) *
                (p02ApplicationFSum run u omega +
                  factoredRemainder u omega))
              run.b) ∧
      ∀ u omega (j : Fin r),
        p02ApplicationF run u omega j =
          Matrix.transpose
              (p02HouseholderProduct
                (p02HouseholderSequenceMatrix run.householderVector)
                (j.val + 1)) *
            run.localPerturbation u j.val omega *
              p02HouseholderProduct
                (p02HouseholderSequenceMatrix run.householderVector) j.val := by
  -- PROOF_START P02-C1-H001
  let P : ℕ → Matrix (Fin m) (Fin m) ℝ :=
    p02HouseholderSequenceMatrix run.householderVector
  let H : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦
      p02HigherOrderHouseholderProduct P run.localPerturbation u omega r
  let G : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ Matrix.transpose (p02HouseholderProduct P r) * H u omega
  have horth : p02HouseholderProduct P r *
      Matrix.transpose (p02HouseholderProduct P r) = 1 := by
    exact p02_product_mul_transpose run.householderVector
      run.householder_involutory r le_rfl
  have hfactor (u : ℝ) (omega : Omega) :
      p02HouseholderProduct P r *
        p02ApplicationFSum run u omega =
      p02ApplicationFirstOrderMatrix run u omega := by
    exact p02_first_order_factor run.householderVector
      run.localPerturbation run.householder_involutory u omega
  have hcomputed (u : ℝ) (omega : Omega) :
      run.computed u omega =
        p02ApplicationExactState run +
          p02MatVec (p02ApplicationFirstOrderMatrix run u omega + H u omega)
            run.b := by
    rw [run.computed_product, p02_product_expansion]
    simp only [p02ApplicationExactState, p02ApplicationFirstOrderMatrix,
      P, H, p02_matvec_add]
    abel
  refine ⟨H, G, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega homega
    exact (p02_product_orders P run.localPerturbation omega
      (hlocal.local_first_order omega homega) r le_rfl).2
  · intro omega homega
    exact p02_bigO_matrix_const_mul
      (Matrix.transpose (p02HouseholderProduct P r))
      ((p02_product_orders P run.localPerturbation omega
        (hlocal.local_first_order omega homega) r le_rfl).2)
  · exact hcomputed
  · intro u omega
    have hmatrix : p02ApplicationFirstOrderMatrix run u omega + H u omega =
        Matrix.transpose (p02ApplicationQ run) *
          (p02ApplicationFSum run u omega + G u omega) := by
      change p02ApplicationFirstOrderMatrix run u omega + H u omega =
        p02HouseholderProduct P r *
          (p02ApplicationFSum run u omega +
            Matrix.transpose (p02HouseholderProduct P r) * H u omega)
      rw [mul_add, hfactor, ← mul_assoc, horth, one_mul]
    rw [hcomputed, hmatrix]
  · intro u omega j
    rfl

end VSCLReuse
