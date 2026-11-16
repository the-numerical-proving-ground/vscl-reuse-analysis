import VSCLReuse.P03.Definitions

namespace VSCLReuse

private theorem p03_mv_mul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul A B) x i = p03MatVec A (p03MatVec B x) i := by
  simp only [p03MatVec, p03MatMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem p03_mv_mul_assoc {n : ℕ}
    (A B C : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul (p03MatMul A B) C) x i =
      p03MatVec (p03MatMul A (p03MatMul B C)) x i := by
  have hBC : p03MatVec B (p03MatVec C x) =
      p03MatVec (p03MatMul B C) x := by
    funext j
    exact (p03_mv_mul B C x j).symm
  rw [p03_mv_mul, p03_mv_mul, p03_mv_mul, hBC]

private theorem p03_mv_add {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatAdd A B) x i =
      p03MatVec A x i + p03MatVec B x i := by
  simp [p03MatVec, p03MatAdd, add_mul, Finset.sum_add_distrib]

private theorem p03_mv_scale {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatScale a A) x i =
      a * p03MatVec A x i := by
  simp [p03MatVec, p03MatScale, mul_assoc, ← Finset.mul_sum]

private theorem p03_mv_vec_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecAdd x y) i =
      p03MatVec A x i + p03MatVec A y i := by
  simp [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private theorem p03_mv_vec_scale {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecScale a x) i =
      a * p03MatVec A x i := by
  simp only [p03MatVec, p03VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p03_mv_id {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03IdMatrix n) x i = x i := by
  simp [p03MatVec, p03IdMatrix]

private theorem p03_mv_mono {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (x y : Fin n → ℝ)
    (hxy : ∀ j, x j ≤ y j) (i : Fin n) :
    p03MatVec A x i ≤ p03MatVec A y i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private theorem p03_mv_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (i : Fin n) :
    0 ≤ p03MatVec A x i := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hA i j) (hx j)

private theorem p03_mm_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  exact p03_mv_nonneg A hA (fun k => B k j) (fun k => hB k j) i

private theorem p03_abs_matrix_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private theorem p03_mv_vec_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecSub x y) i =
      p03MatVec A x i - p03MatVec A y i := by
  simp [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private theorem p03_abs_mv_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤
      p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  calc
    |∑ j : Fin n, A i j * x j| ≤ ∑ j : Fin n, |A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [p03MatVec, p03AbsMatrix, p03AbsVec, abs_mul]

private theorem p03_abs_mv_mono {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (hxy : ∀ j, |x j| ≤ y j) (i : Fin n) :
    |p03MatVec A x i| ≤ p03MatVec (p03AbsMatrix A) y i := by
  exact (p03_abs_mv_le A x i).trans
    (p03_mv_mono _ (p03_abs_matrix_nonneg A) _ _ hxy i)

private theorem p03_abs_sub_le {a b : ℝ} : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

private theorem p03_mv_propagate {n : ℕ} (P : Fin n → Fin n → ℝ)
    (hP : p03MatNonnegative P) (v s q : Fin n → ℝ)
    (h0 : ∀ i, q i ≤ v i + s i)
    (F : Fin n → ℝ) (hF : ∀ i, F i + p03MatVec P s i = s i)
    (qnext : ℕ → Fin n → ℝ)
    (hbase : qnext 0 = q)
    (hstep : ∀ m i, qnext (m + 1) i ≤ p03MatVec P (qnext m) i + F i) :
    ∀ m i, qnext m i ≤ p03MatVec (p03MatPow P m) v i + s i := by
  intro m
  induction m with
  | zero =>
      intro i
      simpa [hbase, p03MatPow, p03_mv_id] using h0 i
  | succ m ih =>
      intro i
      calc
        qnext (m + 1) i ≤ p03MatVec P (qnext m) i + F i := hstep m i
        _ ≤ p03MatVec P (fun j => p03MatVec (p03MatPow P m) v j + s j) i + F i := by
          simpa only [add_comm] using
            (add_le_add_right (p03_mv_mono P hP _ _ ih i) (F i))
        _ = p03MatVec (p03MatPow P (m + 1)) v i + s i := by
          change p03MatVec P (p03VecAdd (p03MatVec (p03MatPow P m) v) s) i + F i = _
          rw [p03_mv_vec_add, p03MatPow, p03_mv_mul]
          linarith [hF i]

private theorem p03_unit_roundoff_pos {n : ℕ}
    (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;>
    simp [p03ResidualUnitRoundoff, run.u_pos]

private theorem p03_q_inverse {n : ℕ} (run : P03IterativeRefinementRun n)
    (m : ℕ) (i : Fin n) :
    p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i =
      (run.iterate m i - run.correction m i) - run.exactSolution i := by
  let w := p03VecSub (run.iterate m) (run.correction m)
  have hq : p03ExactResidualAfterCorrection run m =
      p03VecSub (p03MatVec run.A w) (p03MatVec run.A run.exactSolution) := by
    funext j
    simp only [p03ExactResidualAfterCorrection, p03VecSub, w]
    rw [congrFun run.exact_system j]
  rw [hq, p03_mv_vec_sub, ← p03_mv_mul, ← p03_mv_mul,
    run.inverse_left, p03_mv_id, p03_mv_id]
  rfl

private theorem p03_q_error {n : ℕ} (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run m i| ≤
      |roundoff.residualError m i| + |roundoff.correctionError m i| := by
  have hr := congrFun (roundoff.residual_equation m) i
  have hc := congrFun (roundoff.correction_equation m) i
  dsimp [p03VecAdd, p03VecSub] at hr hc
  have hq : p03ExactResidualAfterCorrection run m i =
      -(roundoff.residualError m i + roundoff.correctionError m i) := by
    change p03MatVec run.A (p03VecSub (run.iterate m) (run.correction m)) i -
      run.b i = _
    rw [p03_mv_vec_sub]
    linarith
  rw [hq, abs_neg]
  exact abs_add_le _ _

private theorem p03_next_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
          p03MatVec (p03AbsMatrix run.Ainv)
            (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
        run.u * |run.exactSolution i| := by
  let q := p03ExactResidualAfterCorrection run m
  let z := p03MatVec run.Ainv q i
  let Z := p03MatVec (p03AbsMatrix run.Ainv) (p03AbsVec q) i
  have hz : |z| ≤ Z := p03_abs_mv_le _ _ _
  have hupdate := run.update_error_bound m i
  have heq := congrFun (run.update_equation m) i
  dsimp [p03VecAdd, p03VecSub] at heq
  have hinv := p03_q_inverse run m i
  change z = (run.iterate m i - run.correction m i) - run.exactSolution i at hinv
  have hsum : |run.iterate m i - run.correction m i| ≤
      |run.exactSolution i| + |z| := by
    have hident : run.iterate m i - run.correction m i =
        run.exactSolution i + z := by linarith
    rw [hident]
    exact abs_add_le _ _
  have he : |run.iterate (m + 1) i - run.exactSolution i| ≤
      |z| + |run.updateError (m + 1) i| := by
    have hident : run.iterate (m + 1) i - run.exactSolution i =
        z + run.updateError (m + 1) i := by linarith
    rw [hident]
    exact abs_add_le _ _
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hscaled := mul_le_mul_of_nonneg_left hsum hu
  have hscaledz := mul_le_mul_of_nonneg_left hz hu
  dsimp [Z] at hz ⊢
  nlinarith

private theorem p03_core_identity {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (X E : Fin n → ℝ)
    (i : Fin n) :
    let M := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
    let ν := p03ResidualUnitRoundoff run.precision run.u
    let α := n * ν + p03Lemma43c3 run * run.u ^ 2
    let β := constants.c5 * ν + run.u
    let D := p03VecAdd (p03VecScale α X) (p03VecScale β E)
    D i + run.u * p03MatVec constants.C2 E i +
        run.u * p03MatVec (p03MatMul constants.C2 M) D i =
      run.u * p03MatVec constants.C6 E i + α * X i +
        run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i := by
  dsimp only
  let M := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  let β := constants.c5 * ν + run.u
  let D := p03VecAdd (p03VecScale α X) (p03VecScale β E)
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  have hν : ν ≠ 0 := ne_of_gt (p03_unit_roundoff_pos run)
  have hD : p03MatVec (p03MatMul constants.C2 M) D i =
      α * p03MatVec (p03MatMul constants.C2 M) X i +
      β * p03MatVec (p03MatMul constants.C2 M) E i := by
    dsimp [D]
    rw [p03_mv_vec_add, p03_mv_vec_scale, p03_mv_vec_scale]
  have hC6 : p03MatVec constants.C6 E i =
      p03MatVec constants.C2 E i +
        (1 + constants.c5 * ν / run.u) *
          (E i + run.u * p03MatVec (p03MatMul constants.C2 M) E i) := by
    rw [constants.C6_definition, p03_mv_add, p03_mv_scale,
      p03_mv_add, p03_mv_id, p03_mv_scale]
  have hC7 : p03MatVec (p03MatMul constants.C7 M) X i =
      (n + p03Lemma43c3 run * run.u ^ 2 / ν) *
        p03MatVec (p03MatMul constants.C2 M) X i := by
    rw [p03_mv_mul, constants.C7_definition, p03_mv_scale,
      ← p03_mv_mul]
  change D i + run.u * p03MatVec constants.C2 E i +
      run.u * p03MatVec (p03MatMul constants.C2 M) D i =
    run.u * p03MatVec constants.C6 E i + α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i
  rw [hD, hC6, hC7]
  dsimp [D, p03VecAdd, p03VecScale, α, β]
  field_simp [hu, hν]
  ring

private theorem p03_core_bound {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    let absA := p03AbsMatrix run.A
    let absAinv := p03AbsMatrix run.Ainv
    let M := p03MatMul absA absAinv
    let X := p03MatVec absA (p03AbsVec run.exactSolution)
    let e := p03VecSub (run.iterate m) run.exactSolution
    let E := p03MatVec absA (p03AbsVec e)
    let ν := p03ResidualUnitRoundoff run.precision run.u
    let α := n * ν + p03Lemma43c3 run * run.u ^ 2
    |p03ExactResidualAfterCorrection run m i| ≤
      run.u * p03MatVec constants.C6 E i + α * X i +
        run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i := by
  dsimp only
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let M := p03MatMul absA absAinv
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let e := p03VecSub (run.iterate m) run.exactSolution
  let E := p03MatVec absA (p03AbsVec e)
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  let β := constants.c5 * ν + run.u
  let D := p03VecAdd (p03VecScale α X) (p03VecScale β E)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hk : 0 ≤ p03KappaInverse run norm :=
    norm.matrix_norm_nonnegative _
  have hc1 : constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right constants.c1_le_c8
      (mul_nonneg hu hk)
    nlinarith [h]
  have hres : ∀ j, |roundoff.residualError m j| ≤ D j := by
    intro j
    have h0 := roundoff.residual_error_bound m j
    change |roundoff.residualError m j| ≤
      α * X j + constants.c5 * ν * E j +
        run.u * |p03MatVec run.A e j| at h0
    have hAe := p03_abs_mv_le run.A e j
    have hscaled := mul_le_mul_of_nonneg_left hAe hu
    change |p03MatVec run.A e j| ≤ E j at hAe
    change |roundoff.residualError m j| ≤ D j
    dsimp [D, p03VecAdd, p03VecScale]
    nlinarith
  have hcorr0 := roundoff.correction_error_bound hc1 m i
  have hcorr1 : |roundoff.correctionError m i| ≤
      run.u * p03MatVec constants.C2 E i +
        run.u * p03MatVec (p03MatMul constants.C2 M)
          (p03AbsVec (roundoff.residualError m)) i := by
    have h1 := p03_mv_mul constants.C2 absA (p03AbsVec e) i
    have h2 := p03_mv_mul_assoc constants.C2 absA absAinv
      (p03AbsVec (roundoff.residualError m)) i
    rw [h1, h2] at hcorr0
    exact hcorr0
  have hCM : p03MatNonnegative (p03MatMul constants.C2 M) :=
    p03_mm_nonneg constants.C2 M constants.C2_nonnegative
      (p03_mm_nonneg absA absAinv
        (p03_abs_matrix_nonneg run.A)
        (p03_abs_matrix_nonneg run.Ainv))
  have hcorr : |roundoff.correctionError m i| ≤
      run.u * p03MatVec constants.C2 E i +
        run.u * p03MatVec (p03MatMul constants.C2 M) D i := by
    have hmono := p03_mv_mono _ hCM
      (p03AbsVec (roundoff.residualError m)) D hres i
    have hscaled := mul_le_mul_of_nonneg_left hmono hu
    linarith
  have hq := p03_q_error run norm dimensionBounds constants roundoff m i
  have hbound : |p03ExactResidualAfterCorrection run m i| ≤
      D i + run.u * p03MatVec constants.C2 E i +
        run.u * p03MatVec (p03MatMul constants.C2 M) D i := by
    linarith [hres i, hcorr]
  have hident := p03_core_identity dimensionBounds run norm constants X E i
  change D i + run.u * p03MatVec constants.C2 E i +
      run.u * p03MatVec (p03MatMul constants.C2 M) D i =
    run.u * p03MatVec constants.C6 E i + α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i at hident
  exact le_of_le_of_eq hbound hident

private theorem p03_initial_identity {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    let absA := p03AbsMatrix run.A
    let M := p03MatMul absA (p03AbsMatrix run.Ainv)
    let X := p03MatVec absA (p03AbsVec run.exactSolution)
    let ν := p03ResidualUnitRoundoff run.precision run.u
    let α := n * ν + p03Lemma43c3 run * run.u ^ 2
    p03Lemma43InitialVector constants i =
      run.u * p03MatVec constants.C6 X i + α * X i +
        run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i := by
  dsimp only
  let absA := p03AbsMatrix run.A
  let M := p03MatMul absA (p03AbsMatrix run.Ainv)
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  have hu : run.u ≠ 0 := ne_of_gt run.u_pos
  have hC10 : p03MatVec constants.C10 X i =
      p03MatVec constants.C6 X i +
        (n * ν / run.u + p03Lemma43c3 run * run.u) * X i +
        ν * p03MatVec (p03MatMul constants.C7 M) X i := by
    rw [constants.C10_definition, p03_mv_add, p03_mv_add,
      p03_mv_scale, p03_mv_id, p03_mv_scale]
  change run.u * p03MatVec (p03MatMul constants.C10 absA)
      (p03AbsVec run.exactSolution) i = _
  rw [p03_mv_mul, hC10]
  dsimp [α, ν]
  field_simp [hu]
  ring

private theorem p03_stationary_nonneg {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    0 ≤ p03Lemma43StationaryVector constants i := by
  let absA := p03AbsMatrix run.A
  let M := p03MatMul absA (p03AbsMatrix run.Ainv)
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let ν := p03ResidualUnitRoundoff run.precision run.u
  have hX : ∀ j, 0 ≤ X j :=
    fun j => p03_mv_nonneg absA (p03_abs_matrix_nonneg run.A)
      (p03AbsVec run.exactSolution) (fun k => abs_nonneg _) j
  have h1 : 0 ≤ p03MatVec constants.C11 X i :=
    p03_mv_nonneg constants.C11 constants.C11_nonnegative X hX i
  have h2 : 0 ≤ p03MatVec
      (p03MatMul constants.C12 M) X i :=
    p03_mv_nonneg _
      (p03_mm_nonneg constants.C12 M constants.C12_nonnegative
        (p03_mm_nonneg absA (p03AbsMatrix run.Ainv)
          (p03_abs_matrix_nonneg run.A)
          (p03_abs_matrix_nonneg run.Ainv))) X hX i
  have hν : 0 ≤ ν := le_of_lt (p03_unit_roundoff_pos run)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  dsimp only [p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
  rw [← add_assoc]
  change 0 ≤ n * ν * X i + run.u ^ 2 *
    p03MatVec (p03MatMul constants.C11 absA)
      (p03AbsVec run.exactSolution) i +
    ν * run.u *
      p03MatVec
        (p03MatMul (p03MatMul constants.C12 M) absA)
        (p03AbsVec run.exactSolution) i
  rw [p03_mv_mul, p03_mv_mul]
  nlinarith [hX i, h1, h2, sq_nonneg run.u,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hν) (hX i),
    mul_nonneg (sq_nonneg run.u) h1,
    mul_nonneg (mul_nonneg hν hu) h2]

private theorem p03_recurrence_identity {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (q : Fin n → ℝ) (i : Fin n) :
    let absA := p03AbsMatrix run.A
    let absAinv := p03AbsMatrix run.Ainv
    let M := p03MatMul absA absAinv
    let X := p03MatVec absA (p03AbsVec run.exactSolution)
    let V := p03VecAdd
      (p03VecScale (1 + run.u) (p03MatVec absAinv q))
      (p03VecScale run.u (p03AbsVec run.exactSolution))
    let ν := p03ResidualUnitRoundoff run.precision run.u
    let α := n * ν + p03Lemma43c3 run * run.u ^ 2
    run.u * p03MatVec constants.C6 (p03MatVec absA V) i +
        α * X i +
        run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i =
      p03MatVec (p03Lemma43Propagation constants) q i +
        p03Lemma43RecurrenceForcing constants i := by
  dsimp only
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let M := p03MatMul absA absAinv
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let V := p03VecAdd
    (p03VecScale (1 + run.u) (p03MatVec absAinv q))
    (p03VecScale run.u (p03AbsVec run.exactSolution))
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  have hAV : p03MatVec absA V =
      p03VecAdd
        (p03VecScale (1 + run.u) (p03MatVec M q))
        (p03VecScale run.u X) := by
    funext j
    dsimp [V, p03VecAdd, p03VecScale]
    rw [p03_mv_vec_add, p03_mv_vec_scale, p03_mv_vec_scale,
      p03_mv_mul]
  have hP : p03MatVec (p03Lemma43Propagation constants) q i =
      run.u * (1 + run.u) *
        p03MatVec constants.C6 (p03MatVec M q) i := by
    rw [p03Lemma43Propagation, p03_mv_scale, p03_mv_mul,
      constants.C8_definition, p03_mv_scale]
    ring
  have hC9 : p03MatVec constants.C9 X i =
      p03MatVec constants.C6 X i + p03Lemma43c3 run * X i := by
    rw [constants.C9_definition, p03_mv_add, p03_mv_scale, p03_mv_id]
  have hF : p03Lemma43RecurrenceForcing constants i =
      n * ν * X i +
        (run.u ^ 2 * p03MatVec constants.C9 X i +
          ν * run.u * p03MatVec (p03MatMul constants.C7 M) X i) := by
    dsimp only [p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale]
    rw [p03_mv_mul, p03_mv_mul]
  rw [hAV, p03_mv_vec_add, p03_mv_vec_scale, p03_mv_vec_scale,
    hP, hF, hC9]
  ring

private theorem p03_recurrence_bound {n : ℕ}
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
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let M := p03MatMul absA absAinv
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let e := p03VecSub (run.iterate (m + 1)) run.exactSolution
  let E := p03MatVec absA (p03AbsVec e)
  let q := p03AbsVec (p03ExactResidualAfterCorrection run m)
  let V := p03VecAdd
    (p03VecScale (1 + run.u) (p03MatVec absAinv q))
    (p03VecScale run.u (p03AbsVec run.exactSolution))
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  have hnext : ∀ j, |e j| ≤ V j := by
    intro j
    simpa only [e, V, q, absAinv, p03VecSub, p03VecAdd,
      p03VecScale, p03AbsVec] using p03_next_error_bound run m j
  have hE : ∀ j, E j ≤ p03MatVec absA V j := by
    intro j
    exact p03_mv_mono absA (p03_abs_matrix_nonneg run.A)
      (p03AbsVec e) V hnext j
  have hCE := p03_mv_mono constants.C6 constants.C6_nonnegative
    E (p03MatVec absA V) hE i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hscaled := mul_le_mul_of_nonneg_left hCE hu
  have hcore := p03_core_bound dimensionBounds run norm constants
    roundoff hsmall (m + 1) i
  change |p03ExactResidualAfterCorrection run (m + 1) i| ≤
    run.u * p03MatVec constants.C6 E i + α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i at hcore
  have hident := p03_recurrence_identity dimensionBounds run norm constants q i
  change run.u * p03MatVec constants.C6 (p03MatVec absA V) i +
      α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i =
    p03MatVec (p03Lemma43Propagation constants) q i +
      p03Lemma43RecurrenceForcing constants i at hident
  have hmid : |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      run.u * p03MatVec constants.C6 (p03MatVec absA V) i +
        α * X i +
        run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i := by
    linarith
  exact le_of_le_of_eq hmid hident

private theorem p03_stationary_fixed_point {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43RecurrenceForcing constants i +
      p03MatVec (p03Lemma43Propagation constants)
        (p03Lemma43StationaryVector constants) i =
      p03Lemma43StationaryVector constants i := by
  let absA := p03AbsMatrix run.A
  let M := p03MatMul absA (p03AbsMatrix run.Ainv)
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let Y := p03MatVec M X
  let P := p03Lemma43Propagation constants
  let S := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  let ν := p03ResidualUnitRoundoff run.precision run.u
  have h11 : ∀ j, p03MatVec constants.C11 X j =
      p03MatVec constants.C9 X j +
        p03MatVec P (p03MatVec constants.C11 X) j := by
    intro j
    have h := congrArg (fun A => p03MatVec A X j)
      constants.C11_fixed_point
    dsimp only at h
    rw [p03_mv_add, p03_mv_mul] at h
    exact h
  have h12 : ∀ j, p03MatVec constants.C12 Y j =
      n * p03MatVec constants.C8 Y j +
        p03MatVec constants.C7 Y j +
        p03MatVec P (p03MatVec constants.C12 Y) j := by
    intro j
    have h := congrArg (fun A => p03MatVec A Y j)
      constants.C12_fixed_point
    dsimp only at h
    rw [p03_mv_add, p03_mv_add, p03_mv_scale, p03_mv_mul] at h
    exact h
  have hPX : p03MatVec P X i =
      run.u * p03MatVec constants.C8 Y i := by
    change p03MatVec
      (p03MatScale run.u (p03MatMul constants.C8 M)) X i = _
    rw [p03_mv_scale, p03_mv_mul]
  have hS : ∀ j, S j =
      n * ν * X j +
        (run.u ^ 2 * p03MatVec constants.C11 X j +
          ν * run.u * p03MatVec constants.C12 Y j) := by
    intro j
    dsimp only [S, p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
    rw [p03_mv_mul, p03_mv_mul, p03_mv_mul]
  have hF : F i =
      n * ν * X i +
        (run.u ^ 2 * p03MatVec constants.C9 X i +
          ν * run.u * p03MatVec constants.C7 Y i) := by
    dsimp only [F, p03Lemma43RecurrenceForcing, p03VecAdd,
      p03VecScale]
    rw [p03_mv_mul, p03_mv_mul, p03_mv_mul]
  have hPS : p03MatVec P S i =
      n * ν * p03MatVec P X i +
        (run.u ^ 2 * p03MatVec P (p03MatVec constants.C11 X) i +
          ν * run.u * p03MatVec P (p03MatVec constants.C12 Y) i) := by
    have hsfun : S =
        p03VecAdd (p03VecScale (n * ν) X)
          (p03VecAdd
            (p03VecScale (run.u ^ 2) (p03MatVec constants.C11 X))
            (p03VecScale (ν * run.u) (p03MatVec constants.C12 Y))) := by
      funext j
      exact hS j
    rw [hsfun, p03_mv_vec_add, p03_mv_vec_scale,
      p03_mv_vec_add, p03_mv_vec_scale, p03_mv_vec_scale]
  change F i + p03MatVec P S i = S i
  rw [hF, hPS, hS i, hPX, h11 i, h12 i]
  ring

private theorem p03_initial_bound {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i +
        p03Lemma43StationaryVector constants i := by
  let absA := p03AbsMatrix run.A
  let M := p03MatMul absA (p03AbsMatrix run.Ainv)
  let X := p03MatVec absA (p03AbsVec run.exactSolution)
  let E0 := p03MatVec absA
    (p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution))
  let ν := p03ResidualUnitRoundoff run.precision run.u
  let α := n * ν + p03Lemma43c3 run * run.u ^ 2
  have he0 : E0 = X := by
    have hvec : p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution) =
        p03AbsVec run.exactSolution := by
      funext j
      simp [run.iterate_zero, p03AbsVec, p03VecSub]
    change p03MatVec absA
      (p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution)) = X
    rw [hvec]
  have hcore := p03_core_bound dimensionBounds run norm constants
    roundoff hsmall 0 i
  change |p03ExactResidualAfterCorrection run 0 i| ≤
    run.u * p03MatVec constants.C6 E0 i + α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i at hcore
  rw [he0] at hcore
  have hident := p03_initial_identity dimensionBounds run norm constants i
  change p03Lemma43InitialVector constants i =
    run.u * p03MatVec constants.C6 X i + α * X i +
      run.u * ν * p03MatVec (p03MatMul constants.C7 M) X i at hident
  have hS := p03_stationary_nonneg dimensionBounds run norm constants i
  linarith

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
  let v := p03Lemma43InitialVector constants
  let s := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  let q : ℕ → Fin n → ℝ := fun m =>
    p03AbsVec (p03ExactResidualAfterCorrection run m)
  have hP : p03MatNonnegative P := by
    change p03MatNonnegative
      (p03MatScale run.u
        (p03MatMul constants.C8
          (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))
    intro i j
    apply mul_nonneg (le_of_lt run.u_pos)
    exact p03_mm_nonneg constants.C8 _ constants.C8_nonnegative
      (p03_mm_nonneg _ _
        (p03_abs_matrix_nonneg run.A)
        (p03_abs_matrix_nonneg run.Ainv)) i j
  have h0 : ∀ i, q 0 i ≤ v i + s i := by
    intro i
    exact p03_initial_bound dimensionBounds run norm constants roundoff hsmall i
  have hF : ∀ i, F i + p03MatVec P s i = s i := by
    intro i
    exact p03_stationary_fixed_point dimensionBounds run norm constants i
  have hstep : ∀ m i, q (m + 1) i ≤ p03MatVec P (q m) i + F i := by
    intro m i
    exact p03_recurrence_bound dimensionBounds run norm constants roundoff hsmall m i
  intro m i
  exact p03_mv_propagate P hP v s (q 0) h0 F hF q rfl hstep m i

end VSCLReuse
