import VSCLReuse.P03.Definitions

namespace VSCLReuse

private lemma p03_mv_nonneg {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x : Fin n → ℝ} (hA : p03MatNonnegative A) (hx : ∀ i, 0 ≤ x i)
    (i : Fin n) : 0 ≤ p03MatVec A x i := by
  unfold p03MatVec
  exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA i j) (hx j)

private lemma p03_mv_mono {n : ℕ} {A : Fin n → Fin n → ℝ}
    {x y : Fin n → ℝ} (hA : p03MatNonnegative A)
    (hxy : ∀ i, x i ≤ y i) (i : Fin n) :
    p03MatVec A x i ≤ p03MatVec A y i := by
  unfold p03MatVec
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private lemma p03_abs_mv_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤ p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  unfold p03MatVec p03AbsMatrix p03AbsVec
  calc
    |∑ j : Fin n, A i j * x j| ≤ ∑ j : Fin n, |A i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |x j| := by simp [abs_mul]

private lemma p03_mv_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecAdd x y) i =
      p03MatVec A x i + p03MatVec A y i := by
  simp [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private lemma p03_mv_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecSub x y) i =
      p03MatVec A x i - p03MatVec A y i := by
  simp [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private lemma p03_mv_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecScale a x) i =
      a * p03MatVec A x i := by
  simp [p03MatVec, p03VecScale, Finset.mul_sum, mul_left_comm]

private lemma p03_mv_matmul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul A B) x i =
      p03MatVec A (p03MatVec B x) i := by
  simp only [p03MatVec, p03MatMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext j
  simp only [Finset.mul_sum]
  congr 1
  funext k
  ring

private lemma p03_mv_matmul_fun {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatMul A B) x = p03MatVec A (p03MatVec B x) := by
  funext i
  exact p03_mv_matmul A B x i

private lemma p03_mv_id {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03IdMatrix n) x i = x i := by
  simp [p03MatVec, p03IdMatrix]

private lemma p03_mv_matadd {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatAdd A B) x i =
      p03MatVec A x i + p03MatVec B x i := by
  simp [p03MatVec, p03MatAdd, add_mul, Finset.sum_add_distrib]

private lemma p03_mv_matscale {n : ℕ} (a : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatScale a A) x i =
      a * p03MatVec A x i := by
  simp [p03MatVec, p03MatScale, Finset.mul_sum, mul_assoc]

private lemma p03_matmul_nonneg {n : ℕ} {A B : Fin n → Fin n → ℝ}
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  unfold p03MatMul
  exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA i k) (hB k j)

private lemma p03_absmatrix_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private lemma p03_absvec_nonneg {n : ℕ} (x : Fin n → ℝ) :
    ∀ i, 0 ≤ p03AbsVec x i := fun _ ↦ abs_nonneg _

private lemma p03_mv_abs_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  apply p03_mv_nonneg
  · intro j k
    exact abs_nonneg _
  · intro j
    exact abs_nonneg _

private lemma p03_ubar_pos {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;> simp [p03ResidualUnitRoundoff, run.u_pos]

private lemma p03_c3_nonneg {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 ≤ p03Lemma43c3 run := by
  have hu : 0 < run.u := run.u_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  cases hp : run.precision with
  | single =>
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ run.u by linarith) n
      have hu2 : 0 < run.u ^ 2 := pow_pos hu _
      have hmul := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 + run.u by linarith)
      have hnum : 0 ≤
          (1 + run.u) * ((1 + run.u) ^ n - 1) - n * run.u := by
        nlinarith [hmul, mul_nonneg hn (sq_nonneg run.u)]
      have heq : p03Lemma43c3 run =
          ((1 + run.u) * ((1 + run.u) ^ n - 1) - n * run.u) / run.u ^ 2 := by
        simp only [p03Lemma43c3, hp]
        field_simp
      rw [heq]
      exact div_nonneg hnum (le_of_lt hu2)
  | double =>
      have hu2 : 0 < run.u ^ 2 := pow_pos hu _
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ run.u ^ 2 by nlinarith) n
      have hq : n * run.u ^ 2 ≤ (1 + run.u ^ 2) ^ n - 1 := by
        nlinarith
      have hq0 : 0 ≤ (1 + run.u ^ 2) ^ n - 1 := by
        nlinarith [mul_nonneg hn (le_of_lt hu2)]
      have hf : 1 ≤ (1 + run.u) * (1 + run.u ^ 2) := by
        nlinarith [mul_nonneg (le_of_lt hu) (le_of_lt hu2)]
      have hprod := mul_le_mul_of_nonneg_right hf hq0
      have hnum : 0 ≤
          (1 + run.u) * (1 + run.u ^ 2) *
            ((1 + run.u ^ 2) ^ n - 1) - n * run.u ^ 2 := by
        nlinarith
      have heq : p03Lemma43c3 run =
          ((1 + run.u) * (1 + run.u ^ 2) *
            ((1 + run.u ^ 2) ^ n - 1) - n * run.u ^ 2) / run.u ^ 2 := by
        simp only [p03Lemma43c3, hp]
        field_simp
      rw [heq]
      exact div_nonneg hnum (le_of_lt hu2)

private lemma p03_q_eq_errors {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    {constants : P03Lemma43Constants run norm dimensionBounds}
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    p03ExactResidualAfterCorrection run m i =
      -roundoff.residualError m i - roundoff.correctionError m i := by
  have hr := congrArg (fun x : Fin n → ℝ => x i) (roundoff.residual_equation m)
  have hc := congrArg (fun x : Fin n → ℝ => x i) (roundoff.correction_equation m)
  simp only [p03VecAdd, p03VecSub] at hr hc
  unfold p03ExactResidualAfterCorrection
  change p03MatVec run.A (p03VecSub (run.iterate m) (run.correction m)) i -
    run.b i = _
  rw [p03_mv_sub]
  linarith

private lemma p03_c1_small {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2) :
    constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
  have hk : 0 ≤ p03KappaInverse run norm := norm.matrix_norm_nonnegative _
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  nlinarith [constants.c1_le_c8, mul_nonneg hu hk]

private lemma p03_basic_residual_bound {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
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
      run.u * ((n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
        p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec
          (p03MatMul constants.C2
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)))
          (p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)) i := by
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let b := p03MatVec absA
    (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution))
  let K := p03MatMul constants.C2 (p03MatMul absA absAinv)
  let α := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  let β := constants.c5 * p03ResidualUnitRoundoff run.precision run.u
  have hK : p03MatNonnegative K :=
    p03_matmul_nonneg constants.C2_nonnegative
      (p03_matmul_nonneg (p03_absmatrix_nonneg _) (p03_absmatrix_nonneg _))
  have hr (j : Fin n) :
      |roundoff.residualError m j| ≤ α * a j + (β + run.u) * b j := by
    have h := roundoff.residual_error_bound m j
    have habs := p03_abs_mv_le run.A
      (p03VecSub (run.iterate m) run.exactSolution) j
    have hprod := mul_le_mul_of_nonneg_left habs (le_of_lt run.u_pos)
    dsimp [α, β, a, b, absA] at *
    nlinarith
  have hKr :
      p03MatVec K (p03AbsVec (roundoff.residualError m)) i ≤
        α * p03MatVec K a i + (β + run.u) * p03MatVec K b i := by
    calc
      _ ≤ p03MatVec K
          (p03VecAdd (p03VecScale α a) (p03VecScale (β + run.u) b)) i :=
        p03_mv_mono hK (by intro j; exact hr j) i
      _ = _ := by rw [p03_mv_add, p03_mv_scale, p03_mv_scale]
  have hs :
      |roundoff.correctionError m i| ≤
        run.u * p03MatVec constants.C2 b i +
        run.u * p03MatVec K (p03AbsVec (roundoff.residualError m)) i := by
    have h := roundoff.correction_error_bound
      (p03_c1_small constants hsmall) m i
    dsimp [K, b, absA, absAinv]
    simpa only [p03_mv_matmul_fun, K, b, absA, absAinv, p03_mv_matmul]
      using h
  have hq := p03_q_eq_errors roundoff m i
  have habs : |p03ExactResidualAfterCorrection run m i| ≤
      |roundoff.residualError m i| + |roundoff.correctionError m i| := by
    rw [hq]
    simpa [sub_eq_add_neg] using
      (abs_add_le (-roundoff.residualError m i) (-roundoff.correctionError m i))
  have hraw :
      |p03ExactResidualAfterCorrection run m i| ≤
        α * a i + (β + run.u) * b i +
          run.u * p03MatVec constants.C2 b i +
          run.u * (α * p03MatVec K a i +
            (β + run.u) * p03MatVec K b i) := by
    have hu : 0 ≤ run.u := le_of_lt run.u_pos
    nlinarith [hr i, hs, hKr, mul_le_mul_of_nonneg_left hKr hu]
  have hC6 (x : Fin n → ℝ) (j : Fin n) :
      run.u * p03MatVec constants.C6 x j =
        (β + run.u) * x j + run.u * p03MatVec constants.C2 x j +
          run.u * (β + run.u) * p03MatVec K x j := by
    rw [constants.C6_definition]
    simp only [p03_mv_matadd, p03_mv_matscale, p03_mv_id,
      p03_mv_matmul]
    dsimp [β, K, absA, absAinv]
    simp only [p03_mv_matmul]
    field_simp [ne_of_gt run.u_pos]
    ring
  change |p03ExactResidualAfterCorrection run m i| ≤
    run.u * p03MatVec constants.C6 b i + α * a i +
      run.u * α * p03MatVec K a i
  rw [hC6]
  linarith

private lemma p03_inverse_residual_identity {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i =
      run.iterate m i - run.correction m i - run.exactSolution i := by
  have hq : p03ExactResidualAfterCorrection run m =
      p03MatVec run.A
        (p03VecSub (p03VecSub (run.iterate m) (run.correction m))
          run.exactSolution) := by
    funext j
    have hb := congrArg (fun x : Fin n → ℝ => x j) run.exact_system
    change p03MatVec run.A (p03VecSub (run.iterate m) (run.correction m)) j -
      run.b j = _
    rw [p03_mv_sub, p03_mv_sub, p03_mv_sub]
    linarith
  rw [hq, ← p03_mv_matmul, run.inverse_left, p03_mv_id]
  rfl

private lemma p03_state_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
        p03MatVec (p03AbsMatrix run.Ainv)
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * |run.exactSolution i| := by
  let q := p03ExactResidualAfterCorrection run m
  let v := p03MatVec run.Ainv q
  have hident := p03_inverse_residual_identity run m i
  have hupdate := congrArg (fun x : Fin n → ℝ => x i) (run.update_equation m)
  simp only [p03VecAdd, p03VecSub] at hupdate
  have hstep : run.iterate (m + 1) i - run.exactSolution i =
      v i + run.updateError (m + 1) i := by
    dsimp [v, q]
    linarith
  have hpre : run.iterate m i - run.correction m i =
      run.exactSolution i + v i := by
    dsimp [v, q]
    linarith
  have hdelta := run.update_error_bound m i
  rw [hpre] at hdelta
  have htri := abs_add_le (run.exactSolution i) (v i)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hdelta' : |run.updateError (m + 1) i| ≤
      run.u * (|run.exactSolution i| + |v i|) :=
    le_trans hdelta (mul_le_mul_of_nonneg_left htri hu)
  have hv := p03_abs_mv_le run.Ainv q i
  have htri2 := abs_add_le (v i) (run.updateError (m + 1) i)
  rw [hstep]
  nlinarith [mul_le_mul_of_nonneg_left hv hu]

private lemma p03_C7_action_identity {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    p03ResidualUnitRoundoff run.precision run.u * run.u *
      p03MatVec
        (p03MatMul constants.C7
          (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))) x i =
      run.u * ((n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
        p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec
          (p03MatMul constants.C2
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))) x i := by
  rw [constants.C7_definition, p03_mv_matmul, p03_mv_matscale]
  rw [← p03_mv_matmul]
  have hubar : p03ResidualUnitRoundoff run.precision run.u ≠ 0 :=
    ne_of_gt (p03_ubar_pos run)
  field_simp

private lemma p03_initial_bound {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i := by
  let a := p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)
  let B := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let K := p03MatMul constants.C2 B
  let α := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  have hb : p03MatVec (p03AbsMatrix run.A)
      (p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution)) = a := by
    congr 1
    funext j
    simp [run.iterate_zero, p03AbsVec, p03VecSub]
  have h := p03_basic_residual_bound constants roundoff hsmall 0 i
  rw [hb] at h
  have hC10 : run.u * p03MatVec constants.C10 a i =
      run.u * p03MatVec constants.C6 a i + α * a i +
        p03ResidualUnitRoundoff run.precision run.u * run.u *
          p03MatVec (p03MatMul constants.C7 B) a i := by
    rw [constants.C10_definition]
    simp only [p03_mv_matadd, p03_mv_matscale, p03_mv_id]
    dsimp [α]
    field_simp [ne_of_gt run.u_pos]
    ring
  have hC7 := p03_C7_action_identity constants a i
  dsimp only [p03Lemma43InitialVector, p03VecScale]
  rw [p03_mv_matmul]
  change |p03ExactResidualAfterCorrection run 0 i| ≤
    run.u * p03MatVec constants.C10 a i
  rw [hC10]
  dsimp [α, B, K] at *
  linarith

private lemma p03_recurrence_bound {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      p03MatVec (p03Lemma43Propagation constants)
        (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      p03Lemma43RecurrenceForcing constants i := by
  let q := p03ExactResidualAfterCorrection run m
  let absq := p03AbsVec q
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let B := p03MatMul absA absAinv
  let K := p03MatMul constants.C2 B
  let b := p03MatVec absA
    (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution))
  let α := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  have hstate (j : Fin n) :
      p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution) j ≤
        p03VecAdd
          (p03VecScale (1 + run.u) (p03MatVec absAinv absq))
          (p03VecScale run.u (p03AbsVec run.exactSolution)) j := by
    simpa only [p03AbsVec, p03VecSub, p03VecAdd, p03VecScale, q, absq,
      absAinv] using p03_state_error_bound run m j
  have hB (j : Fin n) :
      b j ≤ p03VecAdd
        (p03VecScale (1 + run.u) (p03MatVec B absq))
        (p03VecScale run.u a) j := by
    calc
      b j ≤ p03MatVec absA
          (p03VecAdd
            (p03VecScale (1 + run.u) (p03MatVec absAinv absq))
            (p03VecScale run.u (p03AbsVec run.exactSolution))) j :=
        p03_mv_mono (p03_absmatrix_nonneg _) hstate j
      _ = _ := by
        rw [p03_mv_add, p03_mv_scale, p03_mv_scale]
        dsimp [p03VecAdd, p03VecScale, a, B]
        rw [p03_mv_matmul]
  have hC6 := p03_mv_mono constants.C6_nonnegative hB i
  have hC6' : p03MatVec constants.C6 b i ≤
      (1 + run.u) *
        p03MatVec constants.C6 (p03MatVec B absq) i +
      run.u * p03MatVec constants.C6 a i := by
    simpa only [p03_mv_add, p03_mv_scale, p03VecAdd, p03VecScale] using hC6
  have hbasic := p03_basic_residual_bound constants roundoff hsmall (m + 1) i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hraw : |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      run.u * (1 + run.u) *
        p03MatVec constants.C6 (p03MatVec B absq) i +
      run.u ^ 2 * p03MatVec constants.C6 a i +
      α * a i + run.u * α * p03MatVec K a i := by
    dsimp [b, a, K, B, absA, absAinv, α] at hbasic ⊢
    nlinarith [mul_le_mul_of_nonneg_left hC6' hu]
  have hC7 := p03_C7_action_identity constants a i
  have hC9 : p03MatVec constants.C9 a i =
      p03MatVec constants.C6 a i + p03Lemma43c3 run * a i := by
    rw [constants.C9_definition, p03_mv_matadd, p03_mv_matscale,
      p03_mv_id]
  have hP : p03MatVec (p03Lemma43Propagation constants) absq i =
      run.u * (1 + run.u) *
        p03MatVec constants.C6 (p03MatVec B absq) i := by
    dsimp only [p03Lemma43Propagation]
    rw [p03_mv_matscale, p03_mv_matmul, constants.C8_definition,
      p03_mv_matscale]
    dsimp [B, absA, absAinv]
    ring
  have hF : p03Lemma43RecurrenceForcing constants i =
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u * a i +
      run.u ^ 2 * p03MatVec constants.C9 a i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec (p03MatMul constants.C7 B) a i := by
    dsimp only [p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale]
    rw [p03_mv_matmul, p03_mv_matmul]
    dsimp [a, B, absA, absAinv]
    ring
  rw [hP, hF, hC9]
  dsimp [α, K, B, absA, absAinv] at *
  nlinarith

private lemma p03_stationary_fixed_point {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43StationaryVector constants i =
      p03Lemma43RecurrenceForcing constants i +
        p03MatVec (p03Lemma43Propagation constants)
          (p03Lemma43StationaryVector constants) i := by
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let B := p03MatMul absA absAinv
  let P := p03Lemma43Propagation constants
  let ub := p03ResidualUnitRoundoff run.precision run.u
  let c11a := p03MatVec constants.C11 a
  let c12ba := p03MatVec constants.C12 (p03MatVec B a)
  have hSform (j : Fin n) : p03Lemma43StationaryVector constants j =
      (n : ℝ) * ub * a j + run.u ^ 2 * c11a j +
        ub * run.u * c12ba j := by
    dsimp [p03Lemma43StationaryVector, p03VecAdd, p03VecScale,
      a, B, ub, c11a, c12ba, absA, absAinv]
    rw [p03_mv_matmul, p03_mv_matmul, p03_mv_matmul]
    ring
  have hFform : p03Lemma43RecurrenceForcing constants i =
      (n : ℝ) * ub * a i +
        run.u ^ 2 * p03MatVec constants.C9 a i +
        ub * run.u *
          p03MatVec constants.C7 (p03MatVec B a) i := by
    dsimp [p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale,
      a, B, ub, absA, absAinv]
    rw [p03_mv_matmul, p03_mv_matmul, p03_mv_matmul]
    ring
  have hSfun : p03Lemma43StationaryVector constants =
      p03VecAdd
        (p03VecScale ((n : ℝ) * ub) a)
        (p03VecAdd (p03VecScale (run.u ^ 2) c11a)
          (p03VecScale (ub * run.u) c12ba)) := by
    funext j
    simp only [p03VecAdd, p03VecScale]
    simpa only [add_assoc] using hSform j
  have hPS : p03MatVec P (p03Lemma43StationaryVector constants) i =
      (n : ℝ) * ub * p03MatVec P a i +
        run.u ^ 2 * p03MatVec P c11a i +
        ub * run.u * p03MatVec P c12ba i := by
    rw [hSfun, p03_mv_add, p03_mv_scale, p03_mv_add,
      p03_mv_scale, p03_mv_scale]
    ring
  have hPa : p03MatVec P a i =
      run.u * p03MatVec constants.C8 (p03MatVec B a) i := by
    dsimp [P, p03Lemma43Propagation]
    rw [p03_mv_matscale, p03_mv_matmul]
  have h11 : c11a i = p03MatVec constants.C9 a i +
      p03MatVec P c11a i := by
    have h := congrArg (fun M : Fin n → Fin n → ℝ => p03MatVec M a i)
      constants.C11_fixed_point
    dsimp [c11a, P, p03Lemma43Propagation]
    simpa only [p03_mv_matadd, p03_mv_matmul] using h
  have h12 : c12ba i =
      (n : ℝ) * p03MatVec constants.C8 (p03MatVec B a) i +
      p03MatVec constants.C7 (p03MatVec B a) i +
      p03MatVec P c12ba i := by
    have h := congrArg
      (fun M : Fin n → Fin n → ℝ => p03MatVec M (p03MatVec B a) i)
      constants.C12_fixed_point
    dsimp [c12ba, P, p03Lemma43Propagation]
    simpa only [p03_mv_matadd, p03_mv_matscale, p03_mv_matmul] using h
  have h11' := congrArg (fun t : ℝ => run.u ^ 2 * t) h11
  have h12' := congrArg (fun t : ℝ => ub * run.u * t) h12
  have hPa' := congrArg (fun t : ℝ => (n : ℝ) * ub * t) hPa
  rw [hSform, hFform, hPS]
  nlinarith [h11', h12', hPa']

private lemma p03_propagation_nonneg {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    p03MatNonnegative (p03Lemma43Propagation constants) := by
  intro i j
  dsimp [p03Lemma43Propagation, p03MatScale]
  apply mul_nonneg (le_of_lt run.u_pos)
  exact p03_matmul_nonneg constants.C8_nonnegative
    (p03_matmul_nonneg (p03_absmatrix_nonneg _)
      (p03_absmatrix_nonneg _)) i j

private lemma p03_stationary_nonneg {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) : 0 ≤ p03Lemma43StationaryVector constants i := by
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let B := p03MatMul absA absAinv
  have ha (j : Fin n) : 0 ≤ a j :=
    p03_mv_nonneg (p03_absmatrix_nonneg _) (p03_absvec_nonneg _) j
  have hBa (j : Fin n) : 0 ≤ p03MatVec B a j :=
    p03_mv_nonneg
      (p03_matmul_nonneg (p03_absmatrix_nonneg _) (p03_absmatrix_nonneg _))
      ha j
  have h11 : 0 ≤ p03MatVec constants.C11 a i :=
    p03_mv_nonneg constants.C11_nonnegative ha i
  have h12 : 0 ≤ p03MatVec constants.C12 (p03MatVec B a) i :=
    p03_mv_nonneg constants.C12_nonnegative hBa i
  have hubar : 0 ≤ p03ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p03_ubar_pos run)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have heq : p03Lemma43StationaryVector constants i =
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u * a i +
      run.u ^ 2 * p03MatVec constants.C11 a i +
      p03ResidualUnitRoundoff run.precision run.u * run.u *
        p03MatVec constants.C12 (p03MatVec B a) i := by
    dsimp [p03Lemma43StationaryVector, p03VecAdd, p03VecScale,
      a, B, absA, absAinv]
    rw [p03_mv_matmul, p03_mv_matmul, p03_mv_matmul]
    ring
  rw [heq]
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hn hubar) (ha i))
      (mul_nonneg (sq_nonneg _) h11))
    (mul_nonneg (mul_nonneg hubar hu) h12)

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
  let I := p03Lemma43InitialVector constants
  let S := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  have hP : p03MatNonnegative P := p03_propagation_nonneg constants
  intro m
  induction m with
  | zero =>
      intro i
      have hinit := p03_initial_bound constants roundoff hsmall i
      have hS := p03_stationary_nonneg constants i
      change |p03ExactResidualAfterCorrection run 0 i| ≤
        p03MatVec (p03MatPow P 0) I i + S i
      change |p03ExactResidualAfterCorrection run 0 i| ≤
        p03MatVec (p03IdMatrix n) I i + S i
      rw [p03_mv_id]
      exact le_trans hinit (le_add_of_nonneg_right hS)
  | succ m ih =>
      intro i
      have hrec := p03_recurrence_bound constants roundoff hsmall m i
      have hmono : p03MatVec P
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i ≤
          p03MatVec P (p03Lemma43Bound constants m) i :=
        p03_mv_mono hP (fun j ↦ ih j) i
      have hfix := p03_stationary_fixed_point constants i
      have hbound : p03Lemma43Bound constants (m + 1) i =
          p03MatVec P (p03Lemma43Bound constants m) i + F i := by
        change p03MatVec (p03MatMul P (p03MatPow P m)) I i + S i =
          p03MatVec P
            (p03VecAdd (p03MatVec (p03MatPow P m) I) S) i + F i
        rw [p03_mv_matmul, p03_mv_add]
        linarith
      rw [hbound]
      exact le_trans hrec (by linarith)

end VSCLReuse
