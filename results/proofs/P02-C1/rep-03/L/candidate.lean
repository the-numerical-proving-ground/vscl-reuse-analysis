import VSCLReuse.P02.Definitions

namespace VSCLReuse

private theorem p02_householder_symmetric {m : ℕ} (v : Fin m → ℝ) :
    Matrix.transpose (p02HouseholderMatrix v) = p02HouseholderMatrix v := by
  ext i j
  simp only [Matrix.transpose_apply, p02HouseholderMatrix]
  have hid : p02FiniteId j i = p02FiniteId i j := by
    simp only [p02FiniteId]
    by_cases h : i = j <;> simp [h, eq_comm]
  rw [hid]
  ring

private theorem p02_product_mul_transpose
    {m r : ℕ} (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ j, j < r → P j * P j = 1)
    (hSym : ∀ j, Matrix.transpose (P j) = P j) :
    ∀ k, k ≤ r → p02HouseholderProduct P k *
      Matrix.transpose (p02HouseholderProduct P k) = 1 := by
  intro k
  induction k with
  | zero => simp [p02HouseholderProduct]
  | succ k ih =>
      intro hk
      simp only [p02HouseholderProduct, Matrix.transpose_mul]
      rw [hSym k]
      calc
        (P k * p02HouseholderProduct P k) *
            (Matrix.transpose (p02HouseholderProduct P k) * P k) =
            P k * (p02HouseholderProduct P k *
              Matrix.transpose (p02HouseholderProduct P k)) * P k := by
                simp only [mul_assoc]
        _ = 1 := by rw [ih (Nat.le_of_lt (Nat.lt_of_succ_le hk)), mul_one,
          hP k (Nat.lt_of_succ_le hk)]

private theorem p02_product_first_order_identity
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    {r : ℕ} (hP : ∀ j, j < r → P j * P j = 1)
    (hSym : ∀ j, Matrix.transpose (P j) = P j)
    (u : ℝ) (omega : Omega) :
    ∀ k, k ≤ r → p02HouseholderProduct P k *
        p02TransformedHouseholderInsertionSum P D u omega k =
      p02FirstOrderHouseholderProduct P D u omega k := by
  intro k
  induction k with
  | zero => simp [p02HouseholderProduct,
        p02TransformedHouseholderInsertionSum,
        p02FirstOrderHouseholderProduct]
  | succ k ih =>
      intro hk
      have horth := p02_product_mul_transpose P hP hSym (k + 1) hk
      simp only [p02TransformedHouseholderInsertionSum,
        Finset.sum_range_succ, p02TransformedHouseholderInsertion,
        p02FirstOrderHouseholderProduct, p02HouseholderProduct]
      calc
        (P k * p02HouseholderProduct P k) *
          ( (∑ j ∈ Finset.range k,
              Matrix.transpose (p02HouseholderProduct P (j + 1)) *
                D u j omega * p02HouseholderProduct P j) +
            Matrix.transpose (P k * p02HouseholderProduct P k) *
              D u k omega * p02HouseholderProduct P k) =
          P k * (p02HouseholderProduct P k *
            p02TransformedHouseholderInsertionSum P D u omega k) +
            ((P k * p02HouseholderProduct P k) *
              Matrix.transpose (P k * p02HouseholderProduct P k)) *
                D u k omega * p02HouseholderProduct P k := by
                  dsimp [p02TransformedHouseholderInsertionSum,
                    p02TransformedHouseholderInsertion]
                  simp only [mul_add, mul_assoc]
        _ = _ := by
          simp only [p02HouseholderProduct] at horth
          rw [ih (Nat.le_of_lt (Nat.lt_of_succ_le hk)), horth, one_mul]

private theorem p02_perturbed_decomposition
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) :
    ∀ k, p02PerturbedHouseholderProduct P D u omega k =
      p02HouseholderProduct P k +
      p02FirstOrderHouseholderProduct P D u omega k +
      p02HigherOrderHouseholderProduct P D u omega k := by
  intro k
  induction k with
  | zero => simp [p02PerturbedHouseholderProduct,
        p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct]
  | succ k ih =>
      simp only [p02PerturbedHouseholderProduct,
        p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct, ih]
      noncomm_ring

private theorem p02_matrix_bigO_const {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ : ℝ ↦ A) (fun _ ↦ (1 : ℝ)) := by
  intro i j
  exact Asymptotics.isBigO_const_one ℝ (A i j) (nhds 0)

private theorem p02_matrix_bigO_zero {m : ℕ} (f : ℝ → ℝ) :
    p02MatrixFamilyIsBigOAtZero
      (fun _ : ℝ ↦ (0 : Matrix (Fin m) (Fin m) ℝ)) f := by
  intro i j
  simpa using (Asymptotics.isBigO_zero (fun u : ℝ ↦ f u) (nhds 0))

private theorem p02_matrix_bigO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B f) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) f := by
  intro i j
  simpa using (hA i j).add (hB i j)

private theorem p02_matrix_bigO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B g) :
    p02MatrixFamilyIsBigOAtZero
      (fun u ↦ A u * B u) (fun u ↦ f u * g u) := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (Asymptotics.IsBigO.sum (s := (Finset.univ : Finset (Fin m)))
      (by intro k _; exact (hA i k).mul (hB k j)))

private theorem p02_matrix_bigO_congr {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hAB : ∀ u, A u = B u)
    (hfg : ∀ u, f u = g u) :
    p02MatrixFamilyIsBigOAtZero B g := by
  intro i j
  have eA : A = B := funext hAB
  have ef : f = g := funext hfg
  simpa only [← eA, ← ef] using hA i j

private theorem p02_higher_order_bigO
    {Omega : Type*} {m r : ℕ}
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
  intro k
  induction k with
  | zero =>
      intro _
      constructor
      · simpa [p02FirstOrderHouseholderProduct] using
          (p02_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u))
      · simpa [p02MatrixSecondOrderAtZero,
          p02HigherOrderHouseholderProduct] using
          (p02_matrix_bigO_zero (m := m) (fun u : ℝ ↦ u ^ 2))
  | succ k ih =>
      intro hk
      have hk' : k ≤ r := Nat.le_of_lt (Nat.lt_of_succ_le hk)
      have hDk := hD k (Nat.lt_of_succ_le hk)
      have hfirst := (ih hk').1
      have hhigher := (ih hk').2
      have hPconst := p02_matrix_bigO_const (P k)
      have hid : (fun u : ℝ ↦ u) =O[nhds 0] (fun _ ↦ (1 : ℝ)) :=
        (Asymptotics.isLittleO_id_const (by norm_num : (1 : ℝ) ≠ 0)).isBigO
      have hDone : p02MatrixFamilyIsBigOAtZero
          (fun u ↦ D u k omega) (fun _ ↦ (1 : ℝ)) := by
        intro i j
        exact (hDk i j).trans hid
      constructor
      · simp only [p02FirstOrderHouseholderProduct]
        apply p02_matrix_bigO_add
        · exact p02_matrix_bigO_congr
            (p02_matrix_bigO_mul hPconst hfirst)
            (by intro u; rfl) (by intro u; simp)
        · exact p02_matrix_bigO_congr
            (p02_matrix_bigO_mul hDk
              (p02_matrix_bigO_const (p02HouseholderProduct P k)))
            (by intro u; rfl) (by intro u; simp)
      · simp only [p02MatrixSecondOrderAtZero,
          p02HigherOrderHouseholderProduct]
        have ha : p02MatrixFamilyIsBigOAtZero
            (fun u ↦ P k * p02HigherOrderHouseholderProduct P D u omega k)
            (fun u ↦ u ^ 2) :=
          p02_matrix_bigO_congr
            (p02_matrix_bigO_mul hPconst hhigher)
            (by intro u; rfl) (by intro u; simp)
        have hb : p02MatrixFamilyIsBigOAtZero
            (fun u ↦ D u k omega * p02FirstOrderHouseholderProduct P D u omega k)
            (fun u ↦ u ^ 2) :=
          p02_matrix_bigO_congr
            (p02_matrix_bigO_mul hDk hfirst)
            (by intro u; rfl) (by intro u; simp [pow_two])
        have hc : p02MatrixFamilyIsBigOAtZero
            (fun u ↦ D u k omega * p02HigherOrderHouseholderProduct P D u omega k)
            (fun u ↦ u ^ 2) :=
          p02_matrix_bigO_congr
            (p02_matrix_bigO_mul hDone hhigher)
            (by intro u; rfl) (by intro u; simp)
        exact p02_matrix_bigO_add (p02_matrix_bigO_add ha hb) hc

private theorem p02_matvec_add {m n : ℕ}
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
  let D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    run.localPerturbation
  let R : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ p02HigherOrderHouseholderProduct P D u omega r
  let S : ℝ → Omega → Matrix (Fin m) (Fin m) ℝ :=
    fun u omega ↦ p02ApplicationQ run * R u omega
  have hP : ∀ j, j < r → P j * P j = 1 := by
    intro j hj
    exact run.householder_involutory j hj
  have hSym : ∀ j, Matrix.transpose (P j) = P j := by
    intro j
    exact p02_householder_symmetric (run.householderVector j)
  have hOrth : p02HouseholderProduct P r * p02ApplicationQ run = 1 := by
    change p02HouseholderProduct P r *
      Matrix.transpose (p02HouseholderProduct P r) = 1
    exact p02_product_mul_transpose P hP hSym r le_rfl
  have hFirst (u : ℝ) (omega : Omega) :
      p02HouseholderProduct P r * p02ApplicationFSum run u omega =
        p02ApplicationFirstOrderMatrix run u omega := by
    change p02HouseholderProduct P r *
      p02TransformedHouseholderInsertionSum P D u omega r =
      p02FirstOrderHouseholderProduct P D u omega r
    exact p02_product_first_order_identity P D hP hSym u omega r le_rfl
  have hDecomp (u : ℝ) (omega : Omega) :
      p02PerturbedHouseholderProduct P D u omega r =
        p02HouseholderProduct P r +
        p02ApplicationFirstOrderMatrix run u omega + R u omega := by
    exact p02_perturbed_decomposition P D u omega r
  have hFactored (u : ℝ) (omega : Omega) :
      p02PerturbedHouseholderProduct P D u omega r =
        p02HouseholderProduct P r +
          Matrix.transpose (p02ApplicationQ run) *
            (p02ApplicationFSum run u omega + S u omega) := by
    have hQ : Matrix.transpose (p02ApplicationQ run) =
        p02HouseholderProduct P r := by
      change Matrix.transpose (Matrix.transpose (p02HouseholderProduct P r)) = _
      simp
    rw [hQ]
    rw [hDecomp, mul_add, ← hFirst]
    change _ = _ + (_ + p02HouseholderProduct P r *
      (p02ApplicationQ run * R u omega))
    rw [← mul_assoc, hOrth, one_mul]
    abel
  refine ⟨R, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega hmem
    exact (p02_higher_order_bigO P D omega
      (by intro j hj; exact hlocal.local_first_order omega hmem j hj)
      r le_rfl).2
  · intro omega hmem
    have hR := (p02_higher_order_bigO P D omega
      (by intro j hj; exact hlocal.local_first_order omega hmem j hj)
      r le_rfl).2
    change p02MatrixFamilyIsBigOAtZero
      (fun u ↦ p02ApplicationQ run * R u omega) (fun u ↦ u ^ 2)
    exact p02_matrix_bigO_congr
      (p02_matrix_bigO_mul (p02_matrix_bigO_const (p02ApplicationQ run)) hR)
      (by intro u; rfl) (by intro u; simp)
  · intro u omega
    rw [run.computed_product]
    change p02MatVec (p02PerturbedHouseholderProduct P D u omega r) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec (p02ApplicationFirstOrderMatrix run u omega + R u omega) run.b
    rw [hDecomp]
    simp only [p02_matvec_add, add_assoc]
  · intro u omega
    rw [run.computed_product]
    change p02MatVec (p02PerturbedHouseholderProduct P D u omega r) run.b =
      p02MatVec (p02HouseholderProduct P r) run.b +
        p02MatVec (Matrix.transpose (p02ApplicationQ run) *
          (p02ApplicationFSum run u omega + S u omega)) run.b
    rw [hFactored, p02_matvec_add]
  · intro u omega j
    rfl

end VSCLReuse
