import VSCLReuse.P03.Definitions

namespace VSCLReuse

private theorem p03_mv_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    p03MatVec A (p03VecAdd x y) =
      p03VecAdd (p03MatVec A x) (p03MatVec A y) := by
  funext i
  simp [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private theorem p03_mv_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    p03MatVec A (p03VecSub x y) =
      p03VecSub (p03MatVec A x) (p03MatVec A y) := by
  funext i
  simp [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private theorem p03_mv_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    p03MatVec A (p03VecScale a x) =
      p03VecScale a (p03MatVec A x) := by
  funext i
  simp [p03MatVec, p03VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p03_mv_mat_add {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatAdd A B) x =
      p03VecAdd (p03MatVec A x) (p03MatVec B x) := by
  funext i
  simp [p03MatVec, p03MatAdd, p03VecAdd, add_mul, Finset.sum_add_distrib]

private theorem p03_mv_mat_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    p03MatVec (p03MatScale a A) x =
      p03VecScale a (p03MatVec A x) := by
  funext i
  simp [p03MatVec, p03MatScale, p03VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p03_mv_mat_mul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatMul A B) x = p03MatVec A (p03MatVec B x) := by
  funext i
  simp only [p03MatVec, p03MatMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem p03_mat_mul_assoc {n : ℕ}
    (A B C : Fin n → Fin n → ℝ) :
    p03MatMul (p03MatMul A B) C = p03MatMul A (p03MatMul B C) := by
  funext i j
  simp only [p03MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem p03_mv_id {n : ℕ} (x : Fin n → ℝ) :
    p03MatVec (p03IdMatrix n) x = x := by
  funext i
  simp [p03MatVec, p03IdMatrix]

private theorem p03_mv_nonneg {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ} (hA : p03MatNonnegative A)
    (hx : ∀ i, 0 ≤ x i) (i : Fin n) : 0 ≤ p03MatVec A x i := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hA i j) (hx j)

private theorem p03_mv_mono {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x y : Fin n → ℝ} (hA : p03MatNonnegative A)
    (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p03MatVec A x i ≤ p03MatVec A y i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private theorem p03_mv_abs_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤
      p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  calc
    |p03MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
      simp [p03MatVec, p03AbsMatrix, p03AbsVec, abs_mul]

private theorem p03_abs_mat_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private theorem p03_mat_mul_nonneg {n : ℕ}
    {A B : Fin n → Fin n → ℝ}
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hA i k) (hB k j)

private theorem p03_mat_scale_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hA : p03MatNonnegative A) :
    p03MatNonnegative (p03MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private theorem p03_mat_pow_nonneg {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : p03MatNonnegative A) :
    ∀ m, p03MatNonnegative (p03MatPow A m)
  | 0 => by
      intro i j
      simp [p03MatPow, p03IdMatrix]
      split_ifs <;> norm_num
  | m + 1 => p03_mat_mul_nonneg hA (p03_mat_pow_nonneg hA m)

private theorem p03_pow_succ_mv {n : ℕ} (A : Fin n → Fin n → ℝ)
    (m : ℕ) (x : Fin n → ℝ) :
    p03MatVec (p03MatPow A (m + 1)) x =
      p03MatVec A (p03MatVec (p03MatPow A m) x) := by
  rw [p03MatPow, p03_mv_mat_mul]

private theorem p03_c3_nonneg {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 ≤ p03Lemma43c3 run := by
  have hu : 0 < run.u := run.u_pos
  have hpow1 : 1 + (n : ℝ) * run.u ≤ (1 + run.u) ^ n := by
    simpa [mul_comm] using
      (one_add_mul_le_pow (a := run.u) (n := n) (by linarith))
  have hpow2 : 1 + (n : ℝ) * run.u ^ 2 ≤ (1 + run.u ^ 2) ^ n := by
    simpa [mul_comm] using
      (one_add_mul_le_pow (a := run.u ^ 2) (n := n) (by nlinarith [sq_nonneg run.u]))
  cases hp : run.precision with
  | single =>
      simp only [p03Lemma43c3, hp]
      have hu2 : 0 < run.u ^ 2 := pow_pos hu _
      have hid : (n : ℝ) / run.u =
          ((n : ℝ) * run.u) / run.u ^ 2 := by
        field_simp
      rw [hid, ← sub_div]
      apply div_nonneg
      · have hpow0 : 0 ≤ (1 + run.u) ^ n - 1 := by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (le_of_lt hu)]
        nlinarith [mul_nonneg (le_of_lt hu) hpow0]
      · exact le_of_lt hu2
  | double =>
      simp only [p03Lemma43c3, hp]
      have hu2 : 0 < run.u ^ 2 := pow_pos hu _
      have hpow0 : 0 ≤ (1 + run.u ^ 2) ^ n - 1 := by
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg run.u)]
      have hnum : 0 ≤ (1 + run.u) * (1 + run.u ^ 2) *
          ((1 + run.u ^ 2) ^ n - 1) - (n : ℝ) * run.u ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ run.u + run.u ^ 2 + run.u ^ 3 by positivity)
          hpow0]
      rw [show (n : ℝ) = (n : ℝ) * run.u ^ 2 / run.u ^ 2 by
        field_simp]
      rw [← sub_div]
      exact div_nonneg hnum (le_of_lt hu2)

private theorem p03_ubar_pos {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;> simp [p03ResidualUnitRoundoff, run.u_pos,
    pow_pos run.u_pos]

private theorem p03_c5_nonneg {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    0 ≤ constants.c5 := by
  rw [constants.c5_definition]
  have hc3 := p03_c3_nonneg run
  have hc4 : 0 ≤ p03Lemma43c4 run := by
    cases hp : run.precision <;>
      simp [p03Lemma43c4, hp] <;> linarith [run.u_pos]
  apply add_nonneg (Nat.cast_nonneg (α := ℝ) n)
  apply div_nonneg
  · exact mul_nonneg (add_nonneg hc3 hc4) (sq_nonneg run.u)
  · exact le_of_lt (p03_ubar_pos run)

private theorem p03_exact_residual_identity {n : ℕ}
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
  rw [p03ExactResidualAfterCorrection, p03_mv_sub]
  dsimp [p03ExactResidualAfterCorrection, p03VecSub, p03VecAdd] at *
  linarith

private theorem p03_inverse_residual_identity {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) :
    p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) =
      p03VecSub (p03VecSub (run.iterate m) (run.correction m))
        run.exactSolution := by
  rw [p03ExactResidualAfterCorrection, ← run.exact_system,
    ← p03_mv_sub, ← p03_mv_mat_mul, run.inverse_left, p03_mv_id]

private theorem p03_next_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
        p03MatVec (p03AbsMatrix run.Ainv)
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * |run.exactSolution i| := by
  have hid := congrFun (p03_inverse_residual_identity run m) i
  have hu := run.update_error_bound m i
  have heq := congrFun (run.update_equation m) i
  dsimp [p03VecSub, p03VecAdd] at hid heq
  have hq := p03_mv_abs_le run.Ainv
    (p03ExactResidualAfterCorrection run m) i
  have htri : |run.iterate (m + 1) i - run.exactSolution i| ≤
      |p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i| +
        |run.updateError (m + 1) i| := by
    have heq' : run.iterate (m + 1) i - run.exactSolution i =
        p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i +
          run.updateError (m + 1) i := by rw [heq, hid]; ring
    rw [heq']
    exact abs_add_le
      (p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i)
      (run.updateError (m + 1) i)
  have hxi : |run.iterate m i - run.correction m i| ≤
      |p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i| +
        |run.exactSolution i| := by
    have heq' : run.iterate m i - run.correction m i =
        p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i +
          run.exactSolution i := by rw [hid]; ring
    rw [heq']
    exact abs_add_le
      (p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i)
      (run.exactSolution i)
  have hu0 : 0 ≤ run.u := le_of_lt run.u_pos
  nlinarith [mul_le_mul_of_nonneg_left hxi hu0]

private theorem p03_c6_action {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    run.u * p03MatVec constants.C6 x i =
      run.u * p03MatVec constants.C2 x i +
      (run.u + constants.c5 *
        p03ResidualUnitRoundoff run.precision run.u) * x i +
      run.u * (run.u + constants.c5 *
        p03ResidualUnitRoundoff run.precision run.u) *
        p03MatVec
          (p03MatMul constants.C2
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))) x i := by
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  rw [constants.C6_definition, p03_mv_mat_add, p03_mv_mat_scale,
    p03_mv_mat_add, p03_mv_mat_scale, p03_mv_mat_mul]
  simp only [p03VecAdd, p03VecScale, p03_mv_id]
  field_simp
  ring

private theorem p03_c7_action {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7 x i =
      run.u * ((n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
        p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec constants.C2 x i := by
  have hu : p03ResidualUnitRoundoff run.precision run.u ≠ 0 :=
    ne_of_gt (p03_ubar_pos run)
  rw [constants.C7_definition, p03_mv_mat_scale]
  dsimp [p03VecScale]
  field_simp

private theorem p03_residual_coefficient_bound {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run m i| ≤
      run.u * p03MatVec constants.C6
        (p03MatVec (p03AbsMatrix run.A)
          (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution))) i +
      ((n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
        p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec (p03MatMul (p03AbsMatrix run.A)
            (p03AbsMatrix run.Ainv))
            (p03MatVec (p03AbsMatrix run.A)
              (p03AbsVec run.exactSolution))) i := by
  let B := p03AbsMatrix run.A
  let D := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let E := p03AbsVec (p03VecSub (run.iterate m) run.exactSolution)
  let R := p03AbsVec (roundoff.residualError m)
  let K := p03MatMul constants.C2 (p03MatMul B D)
  let α : ℝ := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  let β : ℝ := constants.c5 * p03ResidualUnitRoundoff run.precision run.u
  let T : Fin n → ℝ := fun j ↦ α * p03MatVec B X j + (β + run.u) * p03MatVec B E j
  have hu0 : 0 ≤ run.u := le_of_lt run.u_pos
  have hκ : 0 ≤ p03KappaInverse run norm := by
    exact norm.matrix_norm_nonnegative _
  have hsmall1 : constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right constants.c1_le_c8
      (mul_nonneg hu0 hκ)]
  have hK : p03MatNonnegative K :=
    p03_mat_mul_nonneg constants.C2_nonnegative
      (p03_mat_mul_nonneg (p03_abs_mat_nonneg run.A)
        (p03_abs_mat_nonneg run.Ainv))
  have hR : ∀ j, R j ≤ T j := by
    intro j
    have hr := roundoff.residual_error_bound m j
    have ha := p03_mv_abs_le run.A
      (p03VecSub (run.iterate m) run.exactSolution) j
    dsimp [R, T, α, β, B, X, E, p03AbsVec] at *
    nlinarith [mul_le_mul_of_nonneg_left ha hu0]
  have hKR := p03_mv_mono hK hR i
  have hc := roundoff.correction_error_bound hsmall1 m i
  have hq : |p03ExactResidualAfterCorrection run m i| ≤
      R i + |roundoff.correctionError m i| := by
    rw [p03_exact_residual_identity run norm dimensionBounds constants roundoff m i]
    simpa [R, abs_sub_comm] using
      (abs_add_le (-roundoff.residualError m i) (-roundoff.correctionError m i))
  have hc' : |roundoff.correctionError m i| ≤
      run.u * p03MatVec constants.C2 (p03MatVec B E) i +
      run.u * p03MatVec K R i := by
    dsimp [K, R, E, B, D]
    rw [← p03_mv_mat_mul constants.C2 (p03AbsMatrix run.A),
      ← p03_mat_mul_assoc]
    exact hc
  have hmajor : |p03ExactResidualAfterCorrection run m i| ≤
      T i + run.u * p03MatVec constants.C2 (p03MatVec B E) i +
        run.u * p03MatVec K T i := by
    have hKR' := mul_le_mul_of_nonneg_left hKR hu0
    linarith [hR i, hq, hc']
  have hTcalc :
      T i + run.u * p03MatVec constants.C2 (p03MatVec B E) i +
        run.u * p03MatVec K T i =
      run.u * p03MatVec constants.C6 (p03MatVec B E) i +
        α * p03MatVec B X i +
        p03ResidualUnitRoundoff run.precision run.u * run.u *
          p03MatVec constants.C7
            (p03MatVec (p03MatMul B D) (p03MatVec B X)) i := by
    have hc6 := p03_c6_action dimensionBounds run norm constants
      (p03MatVec B E) i
    have hc7 := p03_c7_action dimensionBounds run norm constants
      (p03MatVec (p03MatMul B D) (p03MatVec B X)) i
    have hKT : p03MatVec K T i =
        α * p03MatVec K (p03MatVec B X) i +
          (β + run.u) * p03MatVec K (p03MatVec B E) i := by
      have hT : T = p03VecAdd (p03VecScale α (p03MatVec B X))
          (p03VecScale (β + run.u) (p03MatVec B E)) := rfl
      rw [hT, p03_mv_add, p03_mv_scale, p03_mv_scale]
      rfl
    rw [hKT]
    rw [hc6, hc7]
    simp only [K, p03_mv_mat_mul]
    dsimp [α, β]
    ring
  dsimp [B, D, X, E, α] at hmajor hTcalc ⊢
  linarith

private theorem p03_one_step_recurrence {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      p03MatVec (p03Lemma43Propagation constants)
        (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      p03Lemma43RecurrenceForcing constants i := by
  let B := p03AbsMatrix run.A
  let D := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let Q := p03AbsVec (p03ExactResidualAfterCorrection run m)
  let E := p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)
  let S := p03VecAdd (p03VecScale (1 + run.u) (p03MatVec D Q))
    (p03VecScale run.u X)
  let α : ℝ := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  have hE : ∀ j, E j ≤ S j := by
    intro j
    simpa [E, S, D, Q, X, p03AbsVec, p03VecSub, p03VecAdd, p03VecScale]
      using p03_next_error_bound run m j
  have hBE : ∀ j, p03MatVec B E j ≤ p03MatVec B S j := by
    intro j
    exact p03_mv_mono (p03_abs_mat_nonneg run.A) hE j
  have hC6 := p03_mv_mono constants.C6_nonnegative hBE i
  have hu0 : 0 ≤ run.u := le_of_lt run.u_pos
  have hq := p03_residual_coefficient_bound
    dimensionBounds run norm constants roundoff hsmall (m + 1) i
  have hmajor : |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      run.u * p03MatVec constants.C6 (p03MatVec B S) i +
      α * p03MatVec B X i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec (p03MatMul B D) (p03MatVec B X)) i := by
    dsimp [B, D, X, E, α] at hq ⊢
    nlinarith [mul_le_mul_of_nonneg_left hC6 hu0]
  have hcalc :
      run.u * p03MatVec constants.C6 (p03MatVec B S) i +
      α * p03MatVec B X i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C7
          (p03MatVec (p03MatMul B D) (p03MatVec B X)) i =
      p03MatVec (p03Lemma43Propagation constants) Q i +
        p03Lemma43RecurrenceForcing constants i := by
    have hc8 := constants.C8_definition
    have hc9 := constants.C9_definition
    simp only [p03Lemma43Propagation, p03Lemma43RecurrenceForcing,
      p03_mv_mat_scale, p03_mv_mat_mul, p03_mv_mat_add,
      p03_mv_add, p03_mv_scale, p03VecScale, p03VecAdd]
    rw [hc8, hc9]
    simp only [p03_mv_mat_scale, p03_mv_mat_add, p03_mv_mat_mul,
      p03_mv_add, p03_mv_scale, p03VecScale, p03VecAdd, p03_mv_id]
    simp only [S, p03_mv_add, p03_mv_scale, p03VecAdd, p03VecScale]
    dsimp [α]
    ring
  dsimp [Q] at hcalc ⊢
  linarith

private theorem p03_initial_bound {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i := by
  let B := p03AbsMatrix run.A
  let D := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let Y := p03MatVec B X
  let Z := p03MatVec (p03MatMul B D) Y
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let α : ℝ := (n : ℝ) * ubar + p03Lemma43c3 run * run.u ^ 2
  have hE0 : p03AbsVec
      (p03VecSub (run.iterate 0) run.exactSolution) = X := by
    funext j
    simp [X, run.iterate_zero, p03AbsVec, p03VecSub]
  have hq := p03_residual_coefficient_bound
    dimensionBounds run norm constants roundoff hsmall 0 i
  rw [hE0] at hq
  change |p03ExactResidualAfterCorrection run 0 i| ≤
    run.u * p03MatVec constants.C6 Y i + α * Y i +
      ubar * run.u * p03MatVec constants.C7 Z i at hq
  have hinit : p03Lemma43InitialVector constants i =
      run.u * p03MatVec constants.C6 Y i + α * Y i +
        ubar * run.u * p03MatVec constants.C7 Z i := by
    have hu : run.u ≠ 0 := ne_of_gt run.u_pos
    unfold p03Lemma43InitialVector
    rw [p03_mv_mat_mul]
    rw [constants.C10_definition, p03_mv_mat_add, p03_mv_mat_add,
      p03_mv_mat_scale, p03_mv_mat_scale]
    rw [p03_mv_mat_mul constants.C7]
    simp only [p03VecAdd, p03VecScale, p03_mv_id]
    change run.u *
      (p03MatVec constants.C6 Y i +
        ((n : ℝ) * ubar / run.u + p03Lemma43c3 run * run.u) * Y i +
        ubar * p03MatVec constants.C7 Z i) = _
    field_simp
    ring
  linarith

private theorem p03_stationary_fixed_point {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    p03Lemma43StationaryVector constants =
      p03VecAdd (p03Lemma43RecurrenceForcing constants)
        (p03MatVec (p03Lemma43Propagation constants)
          (p03Lemma43StationaryVector constants)) := by
  let B := p03AbsMatrix run.A
  let D := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let Y := p03MatVec B X
  let Z := p03MatVec (p03MatMul B D) Y
  let P := p03Lemma43Propagation constants
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  have h11 (i : Fin n) :
      p03MatVec constants.C11 Y i =
        p03MatVec constants.C9 Y i +
          p03MatVec P (p03MatVec constants.C11 Y) i := by
    have hh := congrFun
      (congrArg (fun M => p03MatVec M Y) constants.C11_fixed_point) i
    change p03MatVec constants.C11 Y i =
      p03MatVec (p03MatAdd constants.C9
        (p03MatMul (p03Lemma43Propagation constants) constants.C11)) Y i at hh
    rw [p03_mv_mat_add, p03_mv_mat_mul] at hh
    exact hh
  have h12 (i : Fin n) :
      p03MatVec constants.C12 Z i =
        (n : ℝ) * p03MatVec constants.C8 Z i +
        p03MatVec constants.C7 Z i +
          p03MatVec P (p03MatVec constants.C12 Z) i := by
    have hh := congrFun
      (congrArg (fun M => p03MatVec M Z) constants.C12_fixed_point) i
    change p03MatVec constants.C12 Z i =
      p03MatVec (p03MatAdd
        (p03MatAdd (p03MatScale (n : ℝ) constants.C8) constants.C7)
        (p03MatMul (p03Lemma43Propagation constants) constants.C12)) Z i at hh
    rw [p03_mv_mat_add, p03_mv_mat_add, p03_mv_mat_scale,
      p03_mv_mat_mul] at hh
    dsimp [p03VecAdd, p03VecScale] at hh
    exact hh
  have hPY (i : Fin n) : p03MatVec P Y i =
      run.u * p03MatVec constants.C8 Z i := by
    unfold P p03Lemma43Propagation
    rw [p03_mv_mat_scale, p03_mv_mat_mul]
    rfl
  funext i
  have hS : p03Lemma43StationaryVector constants =
      p03VecAdd (p03VecScale ((n : ℝ) * ubar) Y)
        (p03VecAdd (p03VecScale (run.u ^ 2) (p03MatVec constants.C11 Y))
          (p03VecScale (ubar * run.u) (p03MatVec constants.C12 Z))) := by
    funext j
    simp only [p03Lemma43StationaryVector, p03VecAdd, p03VecScale,
      p03_mv_mat_mul, Z, Y, B, D, X, ubar]
  have hF : p03Lemma43RecurrenceForcing constants =
      p03VecAdd (p03VecScale ((n : ℝ) * ubar) Y)
        (p03VecAdd (p03VecScale (run.u ^ 2) (p03MatVec constants.C9 Y))
          (p03VecScale (ubar * run.u) (p03MatVec constants.C7 Z))) := by
    funext j
    simp only [p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale,
      p03_mv_mat_mul, Z, Y, B, D, X, ubar]
  rw [hS, hF]
  simp only [p03_mv_add, p03_mv_scale, p03VecAdd, p03VecScale]
  rw [hPY i]
  have ha := h11 i
  have hb := h12 i
  linear_combination (run.u ^ 2) * ha + (ubar * run.u) * hb

private theorem p03_stationary_nonnegative {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    0 ≤ p03Lemma43StationaryVector constants i := by
  let B := p03AbsMatrix run.A
  let D := p03AbsMatrix run.Ainv
  let X := p03AbsVec run.exactSolution
  let Y := p03MatVec B X
  let Z := p03MatVec (p03MatMul B D) Y
  have hX : ∀ j, 0 ≤ X j := fun j => abs_nonneg _
  have hY : ∀ j, 0 ≤ Y j :=
    fun j => p03_mv_nonneg (p03_abs_mat_nonneg run.A) hX j
  have hZ : ∀ j, 0 ≤ Z j :=
    fun j => p03_mv_nonneg
      (p03_mat_mul_nonneg (p03_abs_mat_nonneg run.A)
        (p03_abs_mat_nonneg run.Ainv)) hY j
  have hc11 := p03_mv_nonneg constants.C11_nonnegative hY i
  have hc12 := p03_mv_nonneg constants.C12_nonnegative hZ i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p03ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p03_ubar_pos run)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hval : p03Lemma43StationaryVector constants i =
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u * Y i +
        run.u ^ 2 * p03MatVec constants.C11 Y i +
        p03ResidualUnitRoundoff run.precision run.u * run.u *
          p03MatVec constants.C12 Z i := by
    simp only [p03Lemma43StationaryVector, p03VecAdd, p03VecScale,
      p03_mv_mat_mul, Z, Y, B, D, X]
    ring
  rw [hval]
  nlinarith [mul_nonneg (mul_nonneg hn hubar) (hY i),
    mul_nonneg (sq_nonneg run.u) hc11,
    mul_nonneg (mul_nonneg hubar hu) hc12]

private theorem p03_propagation_nonnegative {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    p03MatNonnegative (p03Lemma43Propagation constants) := by
  exact p03_mat_scale_nonneg (le_of_lt run.u_pos)
    (p03_mat_mul_nonneg constants.C8_nonnegative
      (p03_mat_mul_nonneg (p03_abs_mat_nonneg run.A)
        (p03_abs_mat_nonneg run.Ainv)))

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
  let P := p03Lemma43Propagation constants
  let S := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  let V := p03Lemma43InitialVector constants
  have hP : p03MatNonnegative P :=
    p03_propagation_nonnegative dimensionBounds run norm constants
  have hfixed := p03_stationary_fixed_point
    dimensionBounds run norm constants
  intro m
  induction m with
  | zero =>
      intro i
      have hbase := p03_initial_bound
        dimensionBounds run norm constants roundoff hsmall i
      have hS := p03_stationary_nonnegative
        dimensionBounds run norm constants i
      change 0 ≤ S i at hS
      change |p03ExactResidualAfterCorrection run 0 i| ≤ V i at hbase
      change |p03ExactResidualAfterCorrection run 0 i| ≤
        p03MatVec (p03MatPow P 0) V i + S i
      rw [p03MatPow, p03_mv_id]
      linarith
  | succ m ih =>
      intro i
      have hstep := p03_one_step_recurrence
        dimensionBounds run norm constants roundoff hsmall m i
      have hmono :
          p03MatVec P (p03AbsVec (p03ExactResidualAfterCorrection run m)) i ≤
            p03MatVec P (p03Lemma43Bound constants m) i := by
        apply p03_mv_mono hP
        intro j
        exact ih j
      have hcalc :
          p03MatVec P (p03Lemma43Bound constants m) i + F i =
            p03Lemma43Bound constants (m + 1) i := by
        have hsi := congrFun hfixed i
        change S i = F i + p03MatVec P S i at hsi
        simp only [p03Lemma43Bound, p03_pow_succ_mv,
          p03_mv_add, p03VecAdd] at *
        linarith
      change |p03ExactResidualAfterCorrection run (m + 1) i| ≤
        p03MatVec P (p03AbsVec (p03ExactResidualAfterCorrection run m)) i + F i
        at hstep
      linarith

end VSCLReuse
