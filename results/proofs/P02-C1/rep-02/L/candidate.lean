import VSCLReuse.P02.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p02_bigO_id_one :
    (fun u : ℝ ↦ u) =O[nhds 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
  exact Asymptotics.isBigO_const_of_tendsto Filter.tendsto_id (one_ne_zero)

private theorem p02_matrix_bigO_const {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ : ℝ ↦ A) (fun _ ↦ (1 : ℝ)) := by
  intro i j
  exact Asymptotics.isBigO_const_of_tendsto tendsto_const_nhds (one_ne_zero)

private theorem p02_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B s) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) s := by
  intro i j
  simpa using (hA i j).add (hB i j)

private theorem p02_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {s t : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A s)
    (hB : p02MatrixFamilyIsBigOAtZero B t) :
    p02MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ s u * t u) := by
  intro i j
  have hsum :
      (fun u : ℝ ↦ ∑ k : Fin m, A u i k * B u k j) =O[nhds 0]
        (fun u ↦ s u * t u) := by
    apply Asymptotics.IsBigO.sum
    intro k hk
    exact (hA i k).mul (hB k j)
  simpa only [Matrix.mul_apply] using hsum

private theorem p02_matrix_bigO_zero {m : ℕ} (s : ℝ → ℝ) :
    p02MatrixFamilyIsBigOAtZero
      (fun _ : ℝ ↦ (0 : Matrix (Fin m) (Fin m) ℝ)) s := by
  intro i j
  simpa using (Asymptotics.isBigO_zero (l := nhds (0 : ℝ)) (g := s))

private theorem p02_matrix_bigO_of_linear {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (h : p02MatrixFamilyIsBigOAtZero A (fun u ↦ u)) :
    p02MatrixFamilyIsBigOAtZero A (fun _ ↦ (1 : ℝ)) := by
  intro i j
  exact (h i j).trans p02_bigO_id_one

private theorem p02_product_expansion {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (Delta : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) :
    p02PerturbedHouseholderProduct P Delta u omega k =
      p02HouseholderProduct P k +
        p02FirstOrderHouseholderProduct P Delta u omega k +
          p02HigherOrderHouseholderProduct P Delta u omega k := by
  induction k with
  | zero => simp [p02PerturbedHouseholderProduct,
      p02HouseholderProduct, p02FirstOrderHouseholderProduct,
      p02HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p02PerturbedHouseholderProduct,
        p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct]
      rw [ih]
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel

private theorem p02_product_order {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (Delta : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (omega : Omega) (r : ℕ)
    (hDelta : ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero
        (fun u ↦ Delta u j omega) (fun u ↦ u)) :
    ∀ k, k ≤ r →
      p02MatrixFamilyIsBigOAtZero
        (fun u ↦ p02FirstOrderHouseholderProduct P Delta u omega k)
        (fun u ↦ u) ∧
      p02MatrixSecondOrderAtZero
        (fun u ↦ p02HigherOrderHouseholderProduct P Delta u omega k) := by
  intro k
  induction k with
  | zero =>
      intro hk
      constructor
      · simpa only [p02FirstOrderHouseholderProduct] using
          (p02_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u))
      · simpa only [p02HigherOrderHouseholderProduct,
          p02MatrixSecondOrderAtZero] using
          (p02_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u ^ 2))
  | succ k ih =>
      intro hk
      have hklt : k < r := by omega
      have hprev := ih (by omega : k ≤ r)
      have hlocal := hDelta k hklt
      have hlocal_one := p02_matrix_bigO_of_linear hlocal
      have hF1 : p02MatrixFamilyIsBigOAtZero
          (fun u ↦ P k * p02FirstOrderHouseholderProduct P Delta u omega k)
          (fun u ↦ u) := by
        simpa only [one_mul] using
          (p02_matrix_bigO_mul (p02_matrix_bigO_const (P k)) hprev.1)
      have hF2 : p02MatrixFamilyIsBigOAtZero
          (fun u ↦ Delta u k omega * p02HouseholderProduct P k)
          (fun u ↦ u) := by
        simpa only [mul_one] using
          (p02_matrix_bigO_mul hlocal
            (p02_matrix_bigO_const (p02HouseholderProduct P k)))
      have hH1 : p02MatrixSecondOrderAtZero
          (fun u ↦ P k * p02HigherOrderHouseholderProduct P Delta u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, one_mul] using
          (p02_matrix_bigO_mul (p02_matrix_bigO_const (P k)) hprev.2)
      have hH2 : p02MatrixSecondOrderAtZero
          (fun u ↦ Delta u k omega *
            p02FirstOrderHouseholderProduct P Delta u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, ← pow_two] using
          (p02_matrix_bigO_mul hlocal hprev.1)
      have hH3 : p02MatrixSecondOrderAtZero
          (fun u ↦ Delta u k omega *
            p02HigherOrderHouseholderProduct P Delta u omega k) := by
        simpa only [p02MatrixSecondOrderAtZero, one_mul] using
          (p02_matrix_bigO_mul hlocal_one hprev.2)
      constructor
      · simpa only [p02FirstOrderHouseholderProduct] using
          (p02_matrix_bigO_add hF1 hF2)
      · simpa only [p02HigherOrderHouseholderProduct,
          p02MatrixSecondOrderAtZero] using
          (p02_matrix_bigO_add (p02_matrix_bigO_add hH1 hH2) hH3)

private theorem p02_householder_symm {m : ℕ}
    (v : Fin m → ℝ) :
    Matrix.transpose (p02HouseholderMatrix v) = p02HouseholderMatrix v := by
  ext i j
  simp only [Matrix.transpose_apply, p02HouseholderMatrix]
  simp [p02FiniteId, eq_comm, mul_comm]

private theorem p02_product_orthogonal {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hSymm : ∀ j, j < r → Matrix.transpose (P j) = P j)
    (hInv : ∀ j, j < r → P j * P j = 1) :
    ∀ k, k ≤ r →
      Matrix.transpose (p02HouseholderProduct P k) *
          p02HouseholderProduct P k = 1 ∧
        p02HouseholderProduct P k *
          Matrix.transpose (p02HouseholderProduct P k) = 1 := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [p02HouseholderProduct]
  | succ k ih =>
      intro hk
      have hklt : k < r := by omega
      have hprev := ih (by omega : k ≤ r)
      constructor
      · simp only [p02HouseholderProduct, Matrix.transpose_mul, hSymm k hklt]
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (Matrix.transpose (p02HouseholderProduct P k))]
        rw [hInv k hklt, Matrix.mul_one]
        exact hprev.1
      · simp only [p02HouseholderProduct, Matrix.transpose_mul, hSymm k hklt]
        rw [Matrix.mul_assoc (P k), ← Matrix.mul_assoc (p02HouseholderProduct P k)]
        rw [hprev.2, Matrix.one_mul, hInv k hklt]

private theorem p02_first_order_factorization {Omega : Type*} {m r : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (Delta : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (hOrth : ∀ k, k ≤ r →
      p02HouseholderProduct P k *
        Matrix.transpose (p02HouseholderProduct P k) = 1)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r →
      p02HouseholderProduct P k *
          p02TransformedHouseholderInsertionSum P Delta u omega k =
        p02FirstOrderHouseholderProduct P Delta u omega k := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [p02HouseholderProduct,
        p02TransformedHouseholderInsertionSum,
        p02FirstOrderHouseholderProduct]
  | succ k ih =>
      intro hk
      have hsum :
          p02TransformedHouseholderInsertionSum P Delta u omega (k + 1) =
            p02TransformedHouseholderInsertionSum P Delta u omega k +
              p02TransformedHouseholderInsertion P Delta u omega k := by
        simp [p02TransformedHouseholderInsertionSum, Finset.sum_range_succ]
      rw [hsum, Matrix.mul_add]
      have hstep := hOrth (k + 1) hk
      simp only [p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02TransformedHouseholderInsertion] at *
      rw [Matrix.mul_assoc (P k), ih (by omega : k ≤ r)]
      simp only [← Matrix.mul_assoc, hstep, Matrix.one_mul]

private theorem p02_matvec_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    p02MatVec (A + B) x = p02MatVec A x + p02MatVec B x := by
  funext i
  simp [p02MatVec, add_mul, Finset.sum_add_distrib]

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
  let D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    run.localPerturbation
  let H : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ p02HigherOrderHouseholderProduct P D u omega r
  let T : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ Matrix.transpose (p02HouseholderProduct P r) * H u omega
  have hSymm : ∀ j, j < r → Matrix.transpose (P j) = P j := by
    intro j hj
    exact p02_householder_symm (run.householderVector j)
  have hOrth := p02_product_orthogonal P hSymm run.householder_involutory
  have hFactor (u : ℝ) (omega : Omega) :
      p02HouseholderProduct P r *
          p02TransformedHouseholderInsertionSum P D u omega r =
        p02FirstOrderHouseholderProduct P D u omega r :=
    p02_first_order_factorization P D (fun k hk ↦ (hOrth k hk).2) u omega r le_rfl
  have hHO (omega : Omega) (hw : omega ∈ hlocal.localEvent) :
      p02MatrixSecondOrderAtZero (fun u ↦ H u omega) := by
    exact (p02_product_order P D omega r (hlocal.local_first_order omega hw) r le_rfl).2
  refine ⟨H, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega hw
    exact hHO omega hw
  · intro omega hw
    change p02MatrixSecondOrderAtZero
      (fun u ↦ Matrix.transpose (p02HouseholderProduct P r) * H u omega)
    simpa only [p02MatrixSecondOrderAtZero, one_mul] using
      (p02_matrix_bigO_mul
        (p02_matrix_bigO_const
          (Matrix.transpose (p02HouseholderProduct P r)))
        (hHO omega hw))
  · intro u omega
    have hexp := p02_product_expansion P D u omega r
    rw [run.computed_product, hexp]
    change p02MatVec
        (p02HouseholderProduct P r +
          p02FirstOrderHouseholderProduct P D u omega r + H u omega) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec
          (p02FirstOrderHouseholderProduct P D u omega r + H u omega)
          run.b
    rw [add_assoc, p02_matvec_add]
  · intro u omega
    have hexp := p02_product_expansion P D u omega r
    rw [run.computed_product, hexp]
    change p02MatVec
        (p02HouseholderProduct P r +
          p02FirstOrderHouseholderProduct P D u omega r + H u omega) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec
          (p02HouseholderProduct P r *
            (p02TransformedHouseholderInsertionSum P D u omega r + T u omega))
          run.b
    rw [← p02_matvec_add]
    congr 1
    rw [Matrix.mul_add, hFactor]
    change p02HouseholderProduct P r +
        p02FirstOrderHouseholderProduct P D u omega r + H u omega =
      p02HouseholderProduct P r +
        (p02FirstOrderHouseholderProduct P D u omega r +
          p02HouseholderProduct P r *
            (Matrix.transpose (p02HouseholderProduct P r) * H u omega))
    rw [← Matrix.mul_assoc, (hOrth r le_rfl).2, Matrix.one_mul]
    abel
  · intro u omega j
    rfl

end VSCLReuse
