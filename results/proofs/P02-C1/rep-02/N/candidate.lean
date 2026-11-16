import VSCLReuse.P02.Definitions

namespace VSCLReuse

open Asymptotics

private theorem p02_matrixO_zero {m : ℕ} (s : ℝ → ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ : ℝ => (0 : Matrix (Fin m) (Fin m) ℝ)) s := by
  intro i j
  simpa using (isBigO_zero s (nhds (0 : ℝ)))

private theorem p02_matrixO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B s) :
    p02MatrixFamilyIsBigOAtZero (fun u => A u + B u) s := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private theorem p02_matrixO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s t : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B t) :
    p02MatrixFamilyIsBigOAtZero (fun u => A u * B u)
      (fun u => s u * t u) := by
  intro i j
  have h : (fun u : ℝ => ∑ k : Fin m, A u i k * B u k j) =O[nhds 0]
      (fun u => s u * t u) := by
    apply IsBigO.sum
    intro k hk
    exact (hA i k).mul (hB k j)
  simpa only [Matrix.mul_apply] using h

private theorem p02_matrixO_const_mul_left {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ)
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s) :
    p02MatrixFamilyIsBigOAtZero (fun u => C * A u) s := by
  intro i j
  have h : (fun u : ℝ => ∑ k : Fin m, C i k * A u k j) =O[nhds 0] s := by
    apply IsBigO.sum
    intro k hk
    exact (hA k j).const_mul_left (C i k)
  simpa only [Matrix.mul_apply] using h

private theorem p02_matrixO_const_mul_right {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (C : Matrix (Fin m) (Fin m) ℝ)
    (hA : p02MatrixFamilyIsBigOAtZero A s) :
    p02MatrixFamilyIsBigOAtZero (fun u => A u * C) s := by
  intro i j
  have h : (fun u : ℝ => ∑ k : Fin m, A u i k * C k j) =O[nhds 0] s := by
    apply IsBigO.sum
    intro k hk
    convert (hA i k).const_mul_left (C k j) using 1
    ext u
    ring
  simpa only [Matrix.mul_apply] using h

private theorem p02_matrixO_first_bounded {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A (fun u => u)) :
    p02MatrixFamilyIsBigOAtZero A (fun _ => (1 : ℝ)) := by
  intro i j
  exact (hA i j).trans
    (isBigO_const_of_tendsto
      (show Filter.Tendsto (fun u : ℝ => u) (nhds 0) (nhds 0) from Filter.tendsto_id)
      (one_ne_zero : (1 : ℝ) ≠ 0))

private theorem p02_matrixO_first_sq {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A (fun u => u))
    (hB : p02MatrixFamilyIsBigOAtZero B (fun u => u)) :
    p02MatrixSecondOrderAtZero (fun u => A u * B u) := by
  intro i j
  simpa only [p02MatrixSecondOrderAtZero, pow_two] using
    (p02_matrixO_mul hA hB i j)

private theorem p02_matrixO_first_second {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A (fun u => u))
    (hB : p02MatrixSecondOrderAtZero B) :
    p02MatrixSecondOrderAtZero (fun u => A u * B u) := by
  intro i j
  simpa only [one_mul] using
    (p02_matrixO_mul (p02_matrixO_first_bounded hA) hB i j)

private theorem p02_perturbed_product_expansion
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) :
    p02PerturbedHouseholderProduct P D u omega k =
      p02HouseholderProduct P k +
        p02FirstOrderHouseholderProduct P D u omega k +
          p02HigherOrderHouseholderProduct P D u omega k := by
  induction k with
  | zero => simp [p02PerturbedHouseholderProduct,
      p02HouseholderProduct, p02FirstOrderHouseholderProduct,
      p02HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p02PerturbedHouseholderProduct,
        p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct]
      rw [ih]
      noncomm_ring

private theorem p02_first_order_product_O
    {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hD : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero (fun u => D u j omega) (fun u => u)) :
    ∀ k, k ≤ r →
      p02MatrixFamilyIsBigOAtZero
        (fun u => p02FirstOrderHouseholderProduct P D u omega k)
        (fun u => u) := by
  intro k hk
  induction k with
  | zero =>
      simpa only [p02FirstOrderHouseholderProduct] using
        (p02_matrixO_zero (m := m) (fun u => u))
  | succ k ih =>
      simp only [p02FirstOrderHouseholderProduct]
      apply p02_matrixO_add
      · exact p02_matrixO_const_mul_left (P k)
          (ih (Nat.le_of_succ_le hk))
      · exact p02_matrixO_const_mul_right
          (p02HouseholderProduct P k)
          (hD k (lt_of_lt_of_le (Nat.lt_succ_self k) hk))

private theorem p02_higher_order_product_O
    {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega)
    (hD : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero (fun u => D u j omega) (fun u => u)) :
    ∀ k, k ≤ r →
      p02MatrixSecondOrderAtZero
        (fun u => p02HigherOrderHouseholderProduct P D u omega k) := by
  intro k hk
  induction k with
  | zero =>
      simpa only [p02HigherOrderHouseholderProduct,
        p02MatrixSecondOrderAtZero] using
        (p02_matrixO_zero (m := m) (fun u => u ^ 2))
  | succ k ih =>
      simp only [p02HigherOrderHouseholderProduct]
      apply p02_matrixO_add
      · apply p02_matrixO_add
        · exact p02_matrixO_const_mul_left (P k)
            (ih (Nat.le_of_succ_le hk))
        · exact p02_matrixO_first_sq
            (hD k (lt_of_lt_of_le (Nat.lt_succ_self k) hk))
            (p02_first_order_product_O P D omega hD k
              (Nat.le_of_succ_le hk))
      · exact p02_matrixO_first_second
          (hD k (lt_of_lt_of_le (Nat.lt_succ_self k) hk))
          (ih (Nat.le_of_succ_le hk))

private theorem p02_householder_matrix_symmetric {m : ℕ}
    (v : Fin m → ℝ) :
    Matrix.transpose (p02HouseholderMatrix v) = p02HouseholderMatrix v := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [p02HouseholderMatrix]
  · have h' : j ≠ i := Ne.symm h
    simp [p02HouseholderMatrix, p02FiniteId, h, h']
    ring

private theorem p02_householder_product_mul_transpose
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model) :
    ∀ k, k ≤ r →
      p02HouseholderProduct
          (p02HouseholderSequenceMatrix run.householderVector) k *
        Matrix.transpose
          (p02HouseholderProduct
            (p02HouseholderSequenceMatrix run.householderVector) k) = 1 := by
  intro k hk
  induction k with
  | zero => simp [p02HouseholderProduct]
  | succ k ih =>
      let P := p02HouseholderSequenceMatrix run.householderVector
      have hsym : Matrix.transpose (P k) = P k := by
        exact p02_householder_matrix_symmetric (run.householderVector k)
      have hP : P k * P k = 1 :=
        run.householder_involutory k
          (lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      have hprod := ih (Nat.le_of_succ_le hk)
      change (P k * p02HouseholderProduct P k) *
          Matrix.transpose (P k * p02HouseholderProduct P k) = 1
      rw [Matrix.transpose_mul, hsym]
      calc
        (P k * p02HouseholderProduct P k) *
            (Matrix.transpose (p02HouseholderProduct P k) * P k) =
            P k * (p02HouseholderProduct P k *
              Matrix.transpose (p02HouseholderProduct P k)) * P k := by
              simp only [mul_assoc]
        _ = P k * P k := by rw [hprod, mul_one]
        _ = 1 := hP

private theorem p02_first_order_factorization
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r →
      p02FirstOrderHouseholderProduct
          (p02HouseholderSequenceMatrix run.householderVector)
          run.localPerturbation u omega k =
        p02HouseholderProduct
          (p02HouseholderSequenceMatrix run.householderVector) k *
          p02TransformedHouseholderInsertionSum
            (p02HouseholderSequenceMatrix run.householderVector)
            run.localPerturbation u omega k := by
  intro k hk
  induction k with
  | zero =>
      simp [p02FirstOrderHouseholderProduct,
        p02HouseholderProduct,
        p02TransformedHouseholderInsertionSum]
  | succ k ih =>
      let P := p02HouseholderSequenceMatrix run.householderVector
      let D := run.localPerturbation
      have horth := p02_householder_product_mul_transpose run (k + 1) hk
      change p02FirstOrderHouseholderProduct P D u omega (k + 1) =
        p02HouseholderProduct P (k + 1) *
          p02TransformedHouseholderInsertionSum P D u omega (k + 1)
      simp only [p02FirstOrderHouseholderProduct,
        p02TransformedHouseholderInsertionSum,
        Finset.sum_range_succ]
      rw [ih (Nat.le_of_succ_le hk)]
      simp only [p02TransformedHouseholderInsertion]
      change (P k * (p02HouseholderProduct P k *
          p02TransformedHouseholderInsertionSum P D u omega k)) +
          D u k omega * p02HouseholderProduct P k =
        (P k * p02HouseholderProduct P k) *
          (p02TransformedHouseholderInsertionSum P D u omega k +
            Matrix.transpose (p02HouseholderProduct P (k + 1)) *
              D u k omega * p02HouseholderProduct P k)
      change (P k * p02HouseholderProduct P k) *
          Matrix.transpose (P k * p02HouseholderProduct P k) = 1 at horth
      simp only [p02HouseholderProduct]
      calc
        P k * (p02HouseholderProduct P k *
            p02TransformedHouseholderInsertionSum P D u omega k) +
            D u k omega * p02HouseholderProduct P k =
          (P k * p02HouseholderProduct P k) *
              p02TransformedHouseholderInsertionSum P D u omega k +
            ((P k * p02HouseholderProduct P k) *
              Matrix.transpose (P k * p02HouseholderProduct P k)) *
              (D u k omega * p02HouseholderProduct P k) := by
                rw [horth, one_mul]
                noncomm_ring
        _ = (P k * p02HouseholderProduct P k) *
            (p02TransformedHouseholderInsertionSum P D u omega k +
              Matrix.transpose (P k * p02HouseholderProduct P k) *
                D u k omega * p02HouseholderProduct P k) := by
              noncomm_ring

private theorem p02_matvec_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    p02MatVec (A + B) x = p02MatVec A x + p02MatVec B x := by
  funext i
  simp only [p02MatVec, Pi.add_apply, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

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
  let P := p02HouseholderSequenceMatrix run.householderVector
  let H : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega =>
      p02HigherOrderHouseholderProduct P run.localPerturbation u omega r
  refine ⟨H, (fun u omega => p02ApplicationQ run * H u omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro omega homega
    exact p02_higher_order_product_O P run.localPerturbation omega
      (hlocal.local_first_order omega homega) r le_rfl
  · intro omega homega
    exact p02_matrixO_const_mul_left (p02ApplicationQ run)
      (p02_higher_order_product_O P run.localPerturbation omega
        (hlocal.local_first_order omega homega) r le_rfl)
  · intro u omega
    rw [run.computed_product]
    change p02MatVec
        (p02PerturbedHouseholderProduct P run.localPerturbation u omega r)
        run.b =
      p02ApplicationExactState run +
        p02MatVec (p02ApplicationFirstOrderMatrix run u omega + H u omega) run.b
    rw [p02_perturbed_product_expansion]
    change p02MatVec
        (p02HouseholderProduct P r +
          p02FirstOrderHouseholderProduct P run.localPerturbation u omega r +
            H u omega) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec
          (p02FirstOrderHouseholderProduct P run.localPerturbation u omega r +
            H u omega) run.b
    rw [add_assoc, p02_matvec_add]
  · intro u omega
    rw [run.computed_product]
    have hfactor := p02_first_order_factorization run u omega r le_rfl
    have horth := p02_householder_product_mul_transpose run r le_rfl
    change p02MatVec
        (p02PerturbedHouseholderProduct P run.localPerturbation u omega r)
        run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec
          (p02HouseholderProduct P r *
            (p02TransformedHouseholderInsertionSum P
              run.localPerturbation u omega r +
              Matrix.transpose (p02HouseholderProduct P r) * H u omega))
          run.b
    rw [p02_perturbed_product_expansion]
    change p02MatVec
        (p02HouseholderProduct P r +
          p02FirstOrderHouseholderProduct P run.localPerturbation u omega r +
            H u omega) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec
          (p02HouseholderProduct P r *
            (p02TransformedHouseholderInsertionSum P
              run.localPerturbation u omega r +
              Matrix.transpose (p02HouseholderProduct P r) * H u omega))
          run.b
    rw [add_assoc, p02_matvec_add]
    congr 1
    rw [hfactor, mul_add, ← mul_assoc, horth, one_mul]
  · intro u omega j
    rfl

end VSCLReuse
