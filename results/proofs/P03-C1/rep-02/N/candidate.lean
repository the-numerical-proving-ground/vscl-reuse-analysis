import VSCLReuse.P03.Definitions

namespace VSCLReuse

private theorem mv_add {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatAdd A B) x =
      p03VecAdd (p03MatVec A x) (p03MatVec B x) := by
  funext i
  simp [p03MatVec, p03MatAdd, p03VecAdd, add_mul, Finset.sum_add_distrib]

private theorem mv_scale {n : ℕ} (a : ℝ) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatScale a A) x = p03VecScale a (p03MatVec A x) := by
  funext i
  simp [p03MatVec, p03MatScale, p03VecScale, mul_assoc, Finset.mul_sum]

private theorem mv_mul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatMul A B) x = p03MatVec A (p03MatVec B x) := by
  funext i
  simp only [p03MatVec, p03MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem mv_id {n : ℕ} (x : Fin n → ℝ) :
    p03MatVec (p03IdMatrix n) x = x := by
  funext i
  simp [p03MatVec, p03IdMatrix]

private theorem mv_vec_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    p03MatVec A (p03VecAdd x y) =
      p03VecAdd (p03MatVec A x) (p03MatVec A y) := by
  funext i
  simp [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private theorem mv_vec_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    p03MatVec A (p03VecScale a x) =
      p03VecScale a (p03MatVec A x) := by
  funext i
  simp [p03MatVec, p03VecScale, Finset.mul_sum, mul_left_comm]

private theorem mv_vec_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    p03MatVec A (p03VecSub x y) =
      p03VecSub (p03MatVec A x) (p03MatVec A y) := by
  funext i
  simp [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private theorem mv_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i : Fin n) :
    0 ≤ p03MatVec A x i := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hA i j) (hx j)

private theorem mv_mono {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (x y : Fin n → ℝ)
    (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p03MatVec A x i ≤ p03MatVec A y i := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private theorem matmul_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hA i k) (hB k j)

private theorem matscale_nonneg {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (ha : 0 ≤ a)
    (hA : p03MatNonnegative A) :
    p03MatNonnegative (p03MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private theorem abs_mv_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤
      p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  calc
    |p03MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
      simp [p03MatVec, p03AbsMatrix, p03AbsVec, abs_mul]

private theorem abs_mat_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private theorem abs_vec_nonneg {n : ℕ} (x : Fin n → ℝ)
    (i : Fin n) : 0 ≤ p03AbsVec x i := abs_nonneg _

private theorem mv_inverse_residual {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) :
    p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) =
      p03VecSub (p03VecSub (run.iterate m) (run.correction m))
        run.exactSolution := by
  have h : p03ExactResidualAfterCorrection run m =
      p03MatVec run.A
        (p03VecSub
          (p03VecSub (run.iterate m) (run.correction m)) run.exactSolution) := by
    rw [mv_vec_sub, run.exact_system]
    rfl
  rw [h, ← mv_mul, run.inverse_left, mv_id]

private theorem exact_residual_eq_errors {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    p03ExactResidualAfterCorrection run m i =
      -roundoff.residualError m i - roundoff.correctionError m i := by
  have hr := congrFun (roundoff.residual_equation m) i
  have hc := congrFun (roundoff.correction_equation m) i
  simp only [p03ExactResidualAfterCorrection, mv_vec_sub, p03VecSub] at ⊢
  dsimp [p03VecSub, p03VecAdd] at hr hc
  rw [hc, hr]
  ring

private theorem iterate_error_eq {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    run.iterate (m + 1) i - run.exactSolution i =
      p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i +
        run.updateError (m + 1) i := by
  have hi := congrFun (run.update_equation m) i
  have hv := congrFun (mv_inverse_residual run m) i
  dsimp [p03VecSub, p03VecAdd] at *
  linarith

private theorem preupdate_eq {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    run.iterate m i - run.correction m i =
      run.exactSolution i +
        p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i := by
  have hv := congrFun (mv_inverse_residual run m) i
  dsimp [p03VecSub] at hv
  linarith

private theorem iterate_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
        p03MatVec (p03AbsMatrix run.Ainv)
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * |run.exactSolution i| := by
  let q := p03ExactResidualAfterCorrection run m
  let v := p03MatVec (p03AbsMatrix run.Ainv) (p03AbsVec q) i
  have hv : |p03MatVec run.Ainv q i| ≤ v := abs_mv_le _ _ _
  have hpre : |run.iterate m i - run.correction m i| ≤
      |run.exactSolution i| + v := by
    rw [preupdate_eq]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) hv)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have he := run.update_error_bound m i
  have he' : |run.updateError (m + 1) i| ≤
      run.u * (|run.exactSolution i| + v) :=
    he.trans (mul_le_mul_of_nonneg_left hpre hu)
  calc
    |run.iterate (m + 1) i - run.exactSolution i| =
        |p03MatVec run.Ainv q i + run.updateError (m + 1) i| := by
          rw [iterate_error_eq]
    _ ≤ |p03MatVec run.Ainv q i| + |run.updateError (m + 1) i| :=
      abs_add_le _ _
    _ ≤ v + run.u * (|run.exactSolution i| + v) := add_le_add hv he'
    _ = (1 + run.u) * v + run.u * |run.exactSolution i| := by ring

private theorem residual_unit_pos {n : ℕ}
    (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp [p03ResidualUnitRoundoff, run.u_pos]

private theorem c6_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (y : Fin n → ℝ) (i : Fin n) :
    run.u * p03MatVec constants.C6 y i =
      run.u * p03MatVec constants.C2 y i +
      (run.u + constants.c5 *
        p03ResidualUnitRoundoff run.precision run.u) * y i +
      run.u * (run.u + constants.c5 *
        p03ResidualUnitRoundoff run.precision run.u) *
        p03MatVec constants.C2
          (p03MatVec (p03MatMul (p03AbsMatrix run.A)
            (p03AbsMatrix run.Ainv)) y) i := by
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  rw [constants.C6_definition, mv_add, mv_scale]
  simp only [p03VecAdd, p03VecScale, mv_add, mv_scale, mv_mul, mv_id]
  field_simp
  ring

private theorem c7_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (y : Fin n → ℝ) (i : Fin n) :
    p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7 y i =
      run.u *
        ((n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec constants.C2 y i := by
  have hubar : p03ResidualUnitRoundoff run.precision run.u ≠ 0 :=
    ne_of_gt (residual_unit_pos run)
  rw [constants.C7_definition, mv_scale]
  simp only [p03VecScale]
  field_simp

private theorem lemma41_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run m i| ≤
      run.u * p03MatVec constants.C6
        (p03MatVec (p03AbsMatrix run.A)
          (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution))) i +
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      run.u ^ 2 * p03Lemma43c3 run *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))
            (p03MatVec (p03AbsMatrix run.A)
              (p03AbsVec run.exactSolution))) i := by
  let W := p03AbsMatrix run.A
  let V := p03AbsMatrix run.Ainv
  let S := p03MatMul W V
  let X := p03AbsVec run.exactSolution
  let Z := p03AbsVec (p03VecSub (run.iterate m) run.exactSolution)
  let E := p03AbsVec (roundoff.residualError m)
  let alpha : ℝ := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  let beta : ℝ := run.u + constants.c5 *
    p03ResidualUnitRoundoff run.precision run.u
  let R := p03VecAdd (p03VecScale alpha (p03MatVec W X))
    (p03VecScale beta (p03MatVec W Z))
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hk : 0 ≤ p03KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hsmaller : constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
    calc
      constants.c1 * run.u * p03KappaInverse run norm =
          constants.c1 * (run.u * p03KappaInverse run norm) := by ring
      _ ≤ constants.c8 * (run.u * p03KappaInverse run norm) :=
        mul_le_mul_of_nonneg_right constants.c1_le_c8 (mul_nonneg hu hk)
      _ = constants.c8 * run.u * p03KappaInverse run norm := by ring
      _ ≤ 1 / 2 := hsmall
  have hE : ∀ j, E j ≤ R j := by
    intro j
    have hr := roundoff.residual_error_bound m j
    have ha := abs_mv_le run.A (p03VecSub (run.iterate m) run.exactSolution) j
    have ha' := mul_le_mul_of_nonneg_left ha hu
    dsimp [E, R, X, Z, W, alpha, beta, p03VecAdd, p03VecScale,
      p03AbsVec] at *
    linarith
  have hC := roundoff.correction_error_bound hsmaller m i
  have hq : |p03ExactResidualAfterCorrection run m i| ≤
      E i + |roundoff.correctionError m i| := by
    rw [exact_residual_eq_errors]
    simpa only [abs_neg] using
      (abs_add_le (-roundoff.residualError m i)
        (-roundoff.correctionError m i))
  have hM : p03MatNonnegative
      (p03MatMul (p03MatMul constants.C2 W) V) :=
    matmul_nonneg _ _
      (matmul_nonneg _ _ constants.C2_nonnegative (abs_mat_nonneg _))
      (abs_mat_nonneg _)
  have hmono := mv_mono _ hM E R hE i
  have hbound : |p03ExactResidualAfterCorrection run m i| ≤
      R i + run.u * p03MatVec constants.C2 (p03MatVec W Z) i +
        run.u * p03MatVec
          (p03MatMul (p03MatMul constants.C2 W) V) R i := by
    have hC' : |roundoff.correctionError m i| ≤
        run.u * p03MatVec constants.C2 (p03MatVec W Z) i +
        run.u * p03MatVec
          (p03MatMul (p03MatMul constants.C2 W) V) E i := by
      simpa only [mv_mul] using hC
    have hmono' := mul_le_mul_of_nonneg_left hmono hu
    have hi := hE i
    linarith
  have hMR : run.u * p03MatVec
      (p03MatMul (p03MatMul constants.C2 W) V) R i =
      run.u * alpha * p03MatVec constants.C2
        (p03MatVec S (p03MatVec W X)) i +
      run.u * beta * p03MatVec constants.C2
        (p03MatVec S (p03MatVec W Z)) i := by
    dsimp [R, S]
    simp only [mv_mul, mv_vec_add, mv_vec_scale, p03VecAdd, p03VecScale]
    ring
  have hc6 := c6_action run norm dimensionBounds constants (p03MatVec W Z) i
  have hc7 := c7_action run norm dimensionBounds constants
    (p03MatVec S (p03MatVec W X)) i
  dsimp [S] at hc6 hc7
  dsimp [R, p03VecAdd, p03VecScale] at hbound
  rw [hMR] at hbound
  change |p03ExactResidualAfterCorrection run m i| ≤
    run.u * p03MatVec constants.C6 (p03MatVec W Z) i +
    (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u *
      p03MatVec W X i +
    run.u ^ 2 * p03Lemma43c3 run * p03MatVec W X i +
    p03ResidualUnitRoundoff run.precision run.u * run.u *
      p03MatVec constants.C7
        (p03MatVec S (p03MatVec W X)) i
  dsimp [alpha, beta] at hbound
  nlinarith [hc6, hc7]

private theorem initial_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43InitialVector constants i =
      run.u * p03MatVec constants.C6
        (p03MatVec (p03AbsMatrix run.A)
          (p03AbsVec run.exactSolution)) i +
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      run.u ^ 2 * p03Lemma43c3 run *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))
            (p03MatVec (p03AbsMatrix run.A)
              (p03AbsVec run.exactSolution))) i := by
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  simp only [p03Lemma43InitialVector, p03VecScale, mv_mul]
  rw [constants.C10_definition, mv_add, mv_add, mv_scale, mv_scale]
  simp only [p03VecAdd, p03VecScale, mv_mul, mv_id]
  field_simp
  ring

private theorem initial_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i := by
  have hz : p03AbsVec
      (p03VecSub (run.iterate 0) run.exactSolution) =
        p03AbsVec run.exactSolution := by
    funext j
    simp [run.iterate_zero, p03AbsVec, p03VecSub]
  have h := lemma41_bound run norm dimensionBounds constants roundoff hsmall 0 i
  rw [hz] at h
  rw [initial_action]
  exact h

private theorem recurrence_algebra {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (q : Fin n → ℝ) (i : Fin n) :
    let W := p03AbsMatrix run.A
    let V := p03AbsMatrix run.Ainv
    let X := p03AbsVec run.exactSolution
    let T := p03VecAdd
      (p03VecScale (1 + run.u) (p03MatVec V q))
      (p03VecScale run.u X)
    run.u * p03MatVec constants.C6 (p03MatVec W T) i +
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec W X i +
      run.u ^ 2 * p03Lemma43c3 run * p03MatVec W X i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec (p03MatMul W V) (p03MatVec W X)) i =
      p03MatVec (p03Lemma43Propagation constants) q i +
        p03Lemma43RecurrenceForcing constants i := by
  dsimp [p03Lemma43Propagation, p03Lemma43RecurrenceForcing]
  rw [constants.C8_definition, constants.C9_definition]
  simp only [mv_mul, mv_scale, mv_add, mv_vec_add, mv_vec_scale,
    p03VecScale, p03VecAdd, mv_id]
  ring

private theorem recurrence_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      p03MatVec (p03Lemma43Propagation constants)
        (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      p03Lemma43RecurrenceForcing constants i := by
  let W := p03AbsMatrix run.A
  let V := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let Q := p03AbsVec (p03ExactResidualAfterCorrection run m)
  let Z := p03AbsVec
    (p03VecSub (run.iterate (m + 1)) run.exactSolution)
  let T := p03VecAdd
    (p03VecScale (1 + run.u) (p03MatVec V Q))
    (p03VecScale run.u X)
  have hZ : ∀ j, Z j ≤ T j := by
    intro j
    exact iterate_error_bound run m j
  have hW : ∀ j, p03MatVec W Z j ≤ p03MatVec W T j :=
    fun j ↦ mv_mono W (abs_mat_nonneg _) Z T hZ j
  have hC6 := mv_mono constants.C6 constants.C6_nonnegative
    (p03MatVec W Z) (p03MatVec W T) hW i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hC6' := mul_le_mul_of_nonneg_left hC6 hu
  have h41 := lemma41_bound run norm dimensionBounds constants
    roundoff hsmall (m + 1) i
  change |p03ExactResidualAfterCorrection run (m + 1) i| ≤
    run.u * p03MatVec constants.C6 (p03MatVec W Z) i +
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec W X i +
      run.u ^ 2 * p03Lemma43c3 run * p03MatVec W X i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec (p03MatMul W V) (p03MatVec W X)) i at h41
  have halg := recurrence_algebra run norm dimensionBounds constants Q i
  dsimp only at halg
  linarith

private theorem propagation_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    p03MatNonnegative (p03Lemma43Propagation constants) := by
  unfold p03Lemma43Propagation
  exact matscale_nonneg _ _ (le_of_lt run.u_pos)
    (matmul_nonneg _ _ constants.C8_nonnegative
      (matmul_nonneg _ _ (abs_mat_nonneg _) (abs_mat_nonneg _)))

private theorem stationary_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    0 ≤ p03Lemma43StationaryVector constants i := by
  let W := p03AbsMatrix run.A
  let V := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  have hX : ∀ j, 0 ≤ X j := abs_vec_nonneg _
  have hWX : ∀ j, 0 ≤ p03MatVec W X j :=
    fun j ↦ mv_nonneg W (abs_mat_nonneg _) X hX j
  have hS : ∀ j, 0 ≤ p03MatVec (p03MatMul W V)
      (p03MatVec W X) j := by
    intro j
    exact mv_nonneg _
      (matmul_nonneg _ _ (abs_mat_nonneg _) (abs_mat_nonneg _))
      _ hWX j
  have h1 := hWX i
  have h2 := mv_nonneg constants.C11 constants.C11_nonnegative
    (p03MatVec W X) hWX i
  have h3 := mv_nonneg constants.C12 constants.C12_nonnegative
    (p03MatVec (p03MatMul W V) (p03MatVec W X)) hS i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p03ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (residual_unit_pos run)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [p03Lemma43StationaryVector, p03VecAdd, p03VecScale,
    mv_mul]
  simp only [mv_mul] at h3
  dsimp only [W, V, X] at h1 h2 h3
  positivity

private theorem stationary_fixed {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43StationaryVector constants i =
      p03Lemma43RecurrenceForcing constants i +
        p03MatVec (p03Lemma43Propagation constants)
          (p03Lemma43StationaryVector constants) i := by
  conv_lhs =>
    dsimp [p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
    rw [constants.C11_fixed_point, constants.C12_fixed_point]
  dsimp [p03Lemma43StationaryVector, p03Lemma43RecurrenceForcing,
    p03Lemma43Propagation, p03VecAdd, p03VecScale]
  simp only [mv_add, mv_scale, mv_mul, mv_vec_add, mv_vec_scale,
    p03VecAdd, p03VecScale]
  ring

theorem p03_c1_lemma_4_3_exact_residual_bound
    {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff :
      P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall :
      constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2) :
    ∀ m i,
      |p03ExactResidualAfterCorrection run m i| ≤
        p03Lemma43Bound constants m i := by
  -- PROOF_START P03-C1-H001
  intro m
  induction m with
  | zero =>
      intro i
      have hi := initial_bound run norm dimensionBounds constants
        roundoff hsmall i
      have hs := stationary_nonneg run norm dimensionBounds constants i
      simp only [p03Lemma43Bound, p03MatPow, mv_id, p03VecAdd]
      exact hi.trans (le_add_of_nonneg_right hs)
  | succ m ih =>
      intro i
      let B := p03Lemma43Propagation constants
      let I := p03Lemma43InitialVector constants
      let S := p03Lemma43StationaryVector constants
      let F := p03Lemma43RecurrenceForcing constants
      let Q := p03AbsVec (p03ExactResidualAfterCorrection run m)
      have hQ : ∀ j, Q j ≤ p03Lemma43Bound constants m j := ih
      have hB : p03MatNonnegative B :=
        propagation_nonneg run norm dimensionBounds constants
      have hmono := mv_mono B hB Q (p03Lemma43Bound constants m) hQ i
      have hrec := recurrence_bound run norm dimensionBounds constants
        roundoff hsmall m i
      have hstep : |p03ExactResidualAfterCorrection run (m + 1) i| ≤
          p03MatVec B (p03Lemma43Bound constants m) i + F i := by
        exact hrec.trans (add_le_add_left hmono _)
      have hfix := stationary_fixed run norm dimensionBounds constants i
      have hbound : p03Lemma43Bound constants (m + 1) i =
          p03MatVec B (p03Lemma43Bound constants m) i + F i := by
        change p03MatVec (p03MatMul B (p03MatPow B m)) I i + S i =
          p03MatVec B
            (p03VecAdd (p03MatVec (p03MatPow B m) I) S) i + F i
        rw [mv_mul, mv_vec_add]
        dsimp only [p03VecAdd]
        change S i = F i + p03MatVec B S i at hfix
        linarith
      exact hstep.trans_eq hbound.symm

end VSCLReuse
