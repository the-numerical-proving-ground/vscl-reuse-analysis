import VSCLReuse.P02.Definitions

namespace VSCLReuse

private lemma p02_matrix_bigO_zero {m : ℕ} (f : ℝ → ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ => (0 : Matrix (Fin m) (Fin m) ℝ)) f := by
  intro i j
  simpa using (Asymptotics.isBigO_zero (fun u : ℝ => f u) (nhds 0))

private lemma p02_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B f) :
    p02MatrixFamilyIsBigOAtZero (fun u => A u + B u) f := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private lemma p02_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B g) :
    p02MatrixFamilyIsBigOAtZero (fun u => A u * B u) (fun u => f u * g u) := by
  intro i j
  rw [show (fun u => (A u * B u) i j) =
      (fun u => ∑ k : Fin m, A u i k * B u k j) from funext fun u => Matrix.mul_apply ..]
  exact Asymptotics.IsBigO.sum (s := Finset.univ) (by
    intro k hk
    exact (hA i k).mul (hB k j))

private lemma p02_matrix_bigO_const {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ : ℝ => A) (fun _ => 1) := by
  intro i j
  exact Asymptotics.isBigO_const_one ℝ (A i j) (nhds 0)

private lemma p02_matrix_bigO_mono {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hfg : f =O[nhds (0 : ℝ)] g) :
    p02MatrixFamilyIsBigOAtZero A g := by
  intro i j
  exact (hA i j).trans hfg

private lemma p02_bigO_id_one :
    (fun u : ℝ => u) =O[nhds 0] (fun _ => (1 : ℝ)) := by
  exact (Filter.tendsto_id : Filter.Tendsto (fun u : ℝ => u) (nhds 0) (nhds 0)).isBigO_one ℝ

private lemma p02_bigO_cube_square :
    (fun u : ℝ => u * u ^ 2) =O[nhds 0] (fun u => u ^ 2) := by
  simpa only [one_mul] using
    p02_bigO_id_one.mul (Asymptotics.isBigO_refl (fun u : ℝ => u ^ 2) (nhds 0))

private lemma p02_first_order_bigO {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (r : ℕ)
    (hDelta : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero (fun u => DeltaP u j omega) (fun u => u)) :
    ∀ k, k ≤ r →
      p02MatrixFamilyIsBigOAtZero
        (fun u => p02FirstOrderHouseholderProduct P DeltaP u omega k)
        (fun u => u) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [p02FirstOrderHouseholderProduct] using
        (p02_matrix_bigO_zero (m := m) (fun u : ℝ => u))
  | succ k ih =>
      intro hk
      have hk' : k < r := Nat.lt_of_succ_le hk
      have hleft : p02MatrixFamilyIsBigOAtZero
          (fun u => P k * p02FirstOrderHouseholderProduct P DeltaP u omega k)
          (fun u => u) := by
        simpa only [one_mul] using
          (p02_matrix_bigO_mul (p02_matrix_bigO_const (P k))
            (ih (Nat.le_of_lt hk')))
      have hright : p02MatrixFamilyIsBigOAtZero
          (fun u => DeltaP u k omega * p02HouseholderProduct P k)
          (fun u => u) := by
        simpa only [mul_one] using
          (p02_matrix_bigO_mul (hDelta k hk')
            (p02_matrix_bigO_const (p02HouseholderProduct P k)))
      simpa only [p02FirstOrderHouseholderProduct] using
        p02_matrix_bigO_add hleft hright

private lemma p02_higher_order_bigO {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (r : ℕ)
    (hDelta : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero (fun u => DeltaP u j omega) (fun u => u)) :
    ∀ k, k ≤ r →
      p02MatrixSecondOrderAtZero
        (fun u => p02HigherOrderHouseholderProduct P DeltaP u omega k) := by
  have hfirst := p02_first_order_bigO P DeltaP omega r hDelta
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [p02MatrixSecondOrderAtZero,
        p02HigherOrderHouseholderProduct] using
        (p02_matrix_bigO_zero (m := m) (fun u : ℝ => u ^ 2))
  | succ k ih =>
      intro hk
      have hk' : k < r := Nat.lt_of_succ_le hk
      have hleft : p02MatrixSecondOrderAtZero
          (fun u => P k * p02HigherOrderHouseholderProduct P DeltaP u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, one_mul] using
          (p02_matrix_bigO_mul (p02_matrix_bigO_const (P k))
            (ih (Nat.le_of_lt hk')))
      have hmiddle : p02MatrixSecondOrderAtZero
          (fun u => DeltaP u k omega *
            p02FirstOrderHouseholderProduct P DeltaP u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, pow_two] using
          (p02_matrix_bigO_mul (hDelta k hk')
            (hfirst k (Nat.le_of_lt hk')))
      have hright : p02MatrixSecondOrderAtZero
          (fun u => DeltaP u k omega *
            p02HigherOrderHouseholderProduct P DeltaP u omega k) := by
        exact p02_matrix_bigO_mono
          (p02_matrix_bigO_mul (hDelta k hk') (ih (Nat.le_of_lt hk')))
          p02_bigO_cube_square
      simpa only [p02MatrixSecondOrderAtZero,
        p02HigherOrderHouseholderProduct] using
        p02_matrix_bigO_add (p02_matrix_bigO_add hleft hmiddle) hright

private lemma p02_perturbed_product_decomposition {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) :
    ∀ k,
      p02PerturbedHouseholderProduct P DeltaP u omega k =
        p02HouseholderProduct P k +
          p02FirstOrderHouseholderProduct P DeltaP u omega k +
          p02HigherOrderHouseholderProduct P DeltaP u omega k := by
  intro k
  induction k with
  | zero =>
      simp [p02PerturbedHouseholderProduct, p02HouseholderProduct,
        p02FirstOrderHouseholderProduct, p02HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p02PerturbedHouseholderProduct, p02HouseholderProduct,
        p02FirstOrderHouseholderProduct, p02HigherOrderHouseholderProduct, ih]
      simp only [mul_add, add_mul]
      abel

private lemma p02_sequence_matrix_symmetric {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) :
    (p02HouseholderSequenceMatrix v j).transpose =
      p02HouseholderSequenceMatrix v j := by
  ext i k
  simp only [Matrix.transpose_apply, p02HouseholderSequenceMatrix,
    p02HouseholderMatrix, p02FiniteId]
  rw [show (if k = i then (1 : ℝ) else 0) =
      (if i = k then (1 : ℝ) else 0) by simp [eq_comm]]
  rw [mul_comm (v j k) (v j i)]

private lemma p02_product_mul_transpose {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hsym : ∀ j, j < r → (P j).transpose = P j)
    (hsq : ∀ j, j < r → P j * P j = 1) :
    ∀ k, k ≤ r →
      p02HouseholderProduct P k * (p02HouseholderProduct P k).transpose = 1 := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [p02HouseholderProduct]
  | succ k ih =>
      intro hk
      have hk' : k < r := Nat.lt_of_succ_le hk
      rw [p02HouseholderProduct, Matrix.transpose_mul, hsym k hk']
      calc
        (P k * p02HouseholderProduct P k) *
            ((p02HouseholderProduct P k).transpose * P k) =
          P k * (p02HouseholderProduct P k *
            (p02HouseholderProduct P k).transpose) * P k := by
            simp only [mul_assoc]
        _ = 1 := by rw [ih (Nat.le_of_lt hk'), mul_one, hsq k hk']

private lemma p02_product_transpose_step {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hsym : ∀ j, j < r → (P j).transpose = P j)
    (hsq : ∀ j, j < r → P j * P j = 1)
    (k : ℕ) (hk : k < r) :
    (p02HouseholderProduct P (k + 1)).transpose * P k =
      (p02HouseholderProduct P k).transpose := by
  rw [p02HouseholderProduct, Matrix.transpose_mul, hsym k hk]
  rw [mul_assoc, hsq k hk, mul_one]

private lemma p02_first_order_factored {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hsym : ∀ j, j < r → (P j).transpose = P j)
    (hsq : ∀ j, j < r → P j * P j = 1)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r →
      (p02HouseholderProduct P k).transpose *
        p02FirstOrderHouseholderProduct P DeltaP u omega k =
          p02TransformedHouseholderInsertionSum P DeltaP u omega k := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02TransformedHouseholderInsertionSum]
  | succ k ih =>
      intro hk
      have hk' : k < r := Nat.lt_of_succ_le hk
      rw [p02FirstOrderHouseholderProduct, mul_add,
        ← mul_assoc, p02_product_transpose_step P hsym hsq k hk',
        ih (Nat.le_of_lt hk')]
      simp only [p02TransformedHouseholderInsertionSum,
        Finset.sum_range_succ, p02TransformedHouseholderInsertion, mul_assoc]

private lemma p02_matvec_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ) :
    p02MatVec (A + B) b = p02MatVec A b + p02MatVec B b := by
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
  let P : ℕ → Matrix (Fin m) (Fin m) ℝ :=
    p02HouseholderSequenceMatrix run.householderVector
  let E : Matrix (Fin m) (Fin m) ℝ := p02HouseholderProduct P r
  have hsym : ∀ j, j < r → (P j).transpose = P j := by
    intro j hj
    exact p02_sequence_matrix_symmetric run.householderVector j
  have hsq : ∀ j, j < r → P j * P j = 1 := by
    intro j hj
    exact run.householder_involutory j hj
  have horth : E * E.transpose = 1 :=
    p02_product_mul_transpose P hsym hsq r le_rfl
  have hfirst (u : ℝ) (omega : Omega) :
      E.transpose *
          p02FirstOrderHouseholderProduct P run.localPerturbation u omega r =
        p02TransformedHouseholderInsertionSum
          P run.localPerturbation u omega r :=
    p02_first_order_factored P run.localPerturbation hsym hsq u omega r le_rfl
  have hhigher (omega : Omega) (ho : omega ∈ hlocal.localEvent) :
      p02MatrixSecondOrderAtZero
        (fun u => p02HigherOrderHouseholderProduct
          P run.localPerturbation u omega r) :=
    p02_higher_order_bigO P run.localPerturbation omega r
      (hlocal.local_first_order omega ho) r le_rfl
  refine ⟨(fun u omega =>
      p02HigherOrderHouseholderProduct P run.localPerturbation u omega r),
    (fun u omega => E.transpose *
      p02HigherOrderHouseholderProduct P run.localPerturbation u omega r),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro omega ho
    exact hhigher omega ho
  · intro omega ho
    simpa only [p02MatrixSecondOrderAtZero, one_mul] using
      (p02_matrix_bigO_mul
        (p02_matrix_bigO_const E.transpose) (hhigher omega ho))
  · intro u omega
    rw [run.computed_product]
    change p02MatVec
      (p02PerturbedHouseholderProduct P run.localPerturbation u omega r) run.b =
        p02MatVec E run.b +
          p02MatVec
            (p02FirstOrderHouseholderProduct P run.localPerturbation u omega r +
              p02HigherOrderHouseholderProduct P run.localPerturbation u omega r)
            run.b
    rw [p02_perturbed_product_decomposition]
    rw [add_assoc, p02_matvec_add]
  · intro u omega
    rw [run.computed_product]
    change p02MatVec
      (p02PerturbedHouseholderProduct P run.localPerturbation u omega r) run.b =
        p02MatVec E run.b +
          p02MatVec
            (E *
              (p02TransformedHouseholderInsertionSum
                P run.localPerturbation u omega r +
                E.transpose *
                  p02HigherOrderHouseholderProduct
                    P run.localPerturbation u omega r)) run.b
    rw [p02_perturbed_product_decomposition, add_assoc, p02_matvec_add]
    congr 1
    rw [mul_add]
    have hF : E * p02TransformedHouseholderInsertionSum
        P run.localPerturbation u omega r =
          p02FirstOrderHouseholderProduct P run.localPerturbation u omega r := by
      rw [← hfirst u omega, ← mul_assoc, horth, one_mul]
    rw [hF, ← mul_assoc, horth, one_mul]
  · intro u omega j
    rfl

end VSCLReuse
