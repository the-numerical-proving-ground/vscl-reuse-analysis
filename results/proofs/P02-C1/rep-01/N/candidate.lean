import VSCLReuse.P02.Definitions

namespace VSCLReuse

open Filter Asymptotics

private theorem p02_matrixO_add {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B f) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u + B u) f := by
  intro i j
  simpa only [Matrix.add_apply] using (hA i j).add (hB i j)

private theorem p02_matrixO_mul {m : ℕ}
    {A B : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hB : p02MatrixFamilyIsBigOAtZero B g) :
    p02MatrixFamilyIsBigOAtZero (fun u ↦ A u * B u)
      (fun u ↦ f u * g u) := by
  intro i j
  simpa only [Matrix.mul_apply] using
    (IsBigO.sum (s := Finset.univ)
      (A := fun k u ↦ A u i k * B u k j)
      (fun k _ ↦ (hA i k).mul (hB k j)))

private theorem p02_matrixO_const {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) :
    p02MatrixFamilyIsBigOAtZero (fun _ : ℝ ↦ A) (fun _ ↦ (1 : ℝ)) := by
  intro i j
  exact isBigO_const_const _ one_ne_zero _

private theorem p02_matrixO_trans {m : ℕ}
    {A : ℝ → Matrix (Fin m) (Fin m) ℝ} {f g : ℝ → ℝ}
    (hA : p02MatrixFamilyIsBigOAtZero A f)
    (hfg : f =O[nhds 0] g) :
    p02MatrixFamilyIsBigOAtZero A g := by
  intro i j
  exact (hA i j).trans hfg

private theorem p02_u_bigO_one :
    (fun u : ℝ ↦ u) =O[nhds 0] (fun _ ↦ (1 : ℝ)) := by
  exact isBigO_const_of_tendsto tendsto_id one_ne_zero

private theorem p02_u_sq_bigO_u :
    (fun u : ℝ ↦ u ^ 2) =O[nhds 0] (fun u ↦ u) := by
  simpa only [pow_two, mul_one] using
    (isBigO_refl (fun u : ℝ ↦ u) (nhds 0)).mul p02_u_bigO_one

private theorem p02_product_orthogonal_right {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (r : ℕ)
    (hP_symm : ∀ k, Matrix.transpose (P k) = P k)
    (hP_inv : ∀ k, k < r → P k * P k = 1) :
    ∀ k, k ≤ r → p02HouseholderProduct P k *
      Matrix.transpose (p02HouseholderProduct P k) = 1 := by
  intro k
  induction k with
  | zero => intro _; simp [p02HouseholderProduct]
  | succ k ih =>
      intro hk
      have hk_lt : k < r := Nat.lt_of_succ_le hk
      have hk_le : k ≤ r := Nat.le_of_lt hk_lt
      simp only [p02HouseholderProduct, Matrix.transpose_mul]
      calc
        (P k * p02HouseholderProduct P k) *
            (Matrix.transpose (p02HouseholderProduct P k) *
              Matrix.transpose (P k)) =
            P k * (p02HouseholderProduct P k *
              Matrix.transpose (p02HouseholderProduct P k)) *
              Matrix.transpose (P k) := by simp only [mul_assoc]
        _ = 1 := by rw [ih hk_le, mul_one, hP_symm k, hP_inv k hk_lt]

private theorem p02_perturbed_expansion {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ∀ (k : ℕ) (u : ℝ) (omega : Omega),
      p02PerturbedHouseholderProduct P D u omega k =
        p02HouseholderProduct P k +
          p02FirstOrderHouseholderProduct P D u omega k +
          p02HigherOrderHouseholderProduct P D u omega k := by
  intro k
  induction k with
  | zero =>
      intro u omega
      simp [p02PerturbedHouseholderProduct,
        p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct]
  | succ k ih =>
      intro u omega
      rw [p02PerturbedHouseholderProduct, ih]
      simp only [p02HouseholderProduct, p02FirstOrderHouseholderProduct,
        p02HigherOrderHouseholderProduct]
      noncomm_ring

private theorem p02_first_order_factor {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (r : ℕ)
    (horth : ∀ k, k ≤ r → p02HouseholderProduct P k *
      Matrix.transpose (p02HouseholderProduct P k) = 1) :
    ∀ (k : ℕ), k ≤ r → ∀ (u : ℝ) (omega : Omega),
      p02HouseholderProduct P k *
        p02TransformedHouseholderInsertionSum P D u omega k =
      p02FirstOrderHouseholderProduct P D u omega k := by
  intro k
  induction k with
  | zero =>
      intro _ u omega
      simp [p02TransformedHouseholderInsertionSum,
        p02FirstOrderHouseholderProduct]
  | succ k ih =>
      intro hk
      have hk_le : k ≤ r := Nat.le_of_lt (Nat.lt_of_succ_le hk)
      intro u omega
      rw [show p02TransformedHouseholderInsertionSum P D u omega (k + 1) =
          p02TransformedHouseholderInsertionSum P D u omega k +
            p02TransformedHouseholderInsertion P D u omega k by
              simp [p02TransformedHouseholderInsertionSum,
                Finset.sum_range_succ]]
      change (P k * p02HouseholderProduct P k) *
          (p02TransformedHouseholderInsertionSum P D u omega k +
            Matrix.transpose (p02HouseholderProduct P (k + 1)) *
              D u k omega * p02HouseholderProduct P k) =
        P k * p02FirstOrderHouseholderProduct P D u omega k +
          D u k omega * p02HouseholderProduct P k
      rw [mul_add, mul_assoc (P k) (p02HouseholderProduct P k), ih hk_le u omega]
      rw [mul_assoc (Matrix.transpose (p02HouseholderProduct P (k + 1)))
        (D u k omega) (p02HouseholderProduct P k)]
      change P k * p02FirstOrderHouseholderProduct P D u omega k +
          p02HouseholderProduct P (k + 1) *
            (Matrix.transpose (p02HouseholderProduct P (k + 1)) *
              (D u k omega * p02HouseholderProduct P k)) =
        P k * p02FirstOrderHouseholderProduct P D u omega k +
          D u k omega * p02HouseholderProduct P k
      rw [← mul_assoc (p02HouseholderProduct P (k + 1)), horth (k + 1) hk, one_mul]

private theorem p02_order_bounds {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (D : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (r : ℕ) (omega : Omega)
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
      · intro i j
        simpa [p02FirstOrderHouseholderProduct] using
          (isBigO_zero (fun u : ℝ ↦ u) (nhds 0) :
            (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun u ↦ u))
      · intro i j
        simpa [p02MatrixSecondOrderAtZero,
          p02HigherOrderHouseholderProduct] using
          (isBigO_zero (fun u : ℝ ↦ u ^ 2) (nhds 0) :
            (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun u ↦ u ^ 2))
  | succ k ih =>
      intro hk
      have hk_le : k ≤ r := Nat.le_of_lt (Nat.lt_of_succ_le hk)
      have hk_lt : k < r := Nat.lt_of_succ_le hk
      obtain ⟨hL, hR⟩ := ih hk_le
      have hDk := hD k hk_lt
      constructor
      · change p02MatrixFamilyIsBigOAtZero
          (fun u ↦ P k * p02FirstOrderHouseholderProduct P D u omega k +
            D u k omega * p02HouseholderProduct P k) (fun u ↦ u)
        apply p02_matrixO_add
        · simpa only [one_mul] using
            (p02_matrixO_mul (p02_matrixO_const (P k)) hL)
        · simpa only [mul_one] using
            (p02_matrixO_mul hDk
              (p02_matrixO_const (p02HouseholderProduct P k)))
      · change p02MatrixFamilyIsBigOAtZero
          (fun u ↦ P k * p02HigherOrderHouseholderProduct P D u omega k +
            D u k omega * p02FirstOrderHouseholderProduct P D u omega k +
            D u k omega * p02HigherOrderHouseholderProduct P D u omega k)
          (fun u ↦ u ^ 2)
        apply p02_matrixO_add
        · apply p02_matrixO_add
          · simpa only [one_mul] using
              (p02_matrixO_mul (p02_matrixO_const (P k)) hR)
          · simpa only [pow_two] using (p02_matrixO_mul hDk hL)
        · have hRlin := p02_matrixO_trans hR p02_u_sq_bigO_u
          simpa only [pow_two] using (p02_matrixO_mul hDk hRlin)

private theorem p02_matvec_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    p02MatVec (A + B) x = p02MatVec A x + p02MatVec B x := by
  funext i
  simp [p02MatVec, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

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
  let D := run.localPerturbation
  let H := p02HouseholderProduct P r
  let L (u : ℝ) (omega : Omega) :=
    p02FirstOrderHouseholderProduct P D u omega r
  let R (u : ℝ) (omega : Omega) :=
    p02HigherOrderHouseholderProduct P D u omega r
  let S (u : ℝ) (omega : Omega) :=
    p02TransformedHouseholderInsertionSum P D u omega r
  have hsymm : ∀ k, Matrix.transpose (P k) = P k := by
    intro k
    ext i j
    simp only [P, p02HouseholderSequenceMatrix, p02HouseholderMatrix,
      Matrix.transpose_apply]
    have hid : p02FiniteId j i = p02FiniteId i j := by
      simp [p02FiniteId, eq_comm]
    rw [hid, mul_comm (run.householderVector k j) (run.householderVector k i)]
  have horth : ∀ k, k ≤ r →
      p02HouseholderProduct P k *
        Matrix.transpose (p02HouseholderProduct P k) = 1 := by
    apply p02_product_orthogonal_right P r hsymm
    intro k hk
    exact run.householder_involutory k hk
  have hfactor : ∀ u omega, H * S u omega = L u omega := by
    intro u omega
    exact p02_first_order_factor P D r horth r (le_refl r) u omega
  have hR : ∀ omega, omega ∈ hlocal.localEvent →
      p02MatrixSecondOrderAtZero (fun u ↦ R u omega) := by
    intro omega hω
    exact (p02_order_bounds P D r omega
      (hlocal.local_first_order omega hω) r (le_refl r)).2
  have hfirst : ∀ u omega,
      run.computed u omega =
        p02ApplicationExactState run +
          p02MatVec (p02ApplicationFirstOrderMatrix run u omega +
            R u omega) run.b := by
    intro u omega
    calc
      run.computed u omega =
          p02MatVec (p02PerturbedHouseholderProduct P D u omega r) run.b :=
        run.computed_product u omega
      _ = p02MatVec (H + (L u omega + R u omega)) run.b := by
        rw [p02_perturbed_expansion]
        rw [add_assoc]
      _ = p02ApplicationExactState run +
          p02MatVec (p02ApplicationFirstOrderMatrix run u omega +
            R u omega) run.b := by
        rw [p02_matvec_add]
        rfl
  have hmat : ∀ u omega,
      Matrix.transpose (p02ApplicationQ run) *
        (p02ApplicationFSum run u omega +
          p02ApplicationQ run * R u omega) =
      p02ApplicationFirstOrderMatrix run u omega + R u omega := by
    intro u omega
    change Matrix.transpose (Matrix.transpose H) *
        (S u omega + Matrix.transpose H * R u omega) =
      L u omega + R u omega
    rw [Matrix.transpose_transpose, mul_add, hfactor u omega,
      ← mul_assoc, horth r (le_refl r), one_mul]
  refine ⟨R, (fun u omega ↦ p02ApplicationQ run * R u omega), hR, ?_, hfirst, ?_, ?_⟩
  · intro omega hω
    simpa only [one_mul] using
      (p02_matrixO_mul (p02_matrixO_const (p02ApplicationQ run)) (hR omega hω))
  · intro u omega
    rw [hfirst u omega]
    rw [hmat u omega]
  · intro u omega j
    rfl

end VSCLReuse
