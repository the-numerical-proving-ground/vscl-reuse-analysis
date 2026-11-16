import VSCLReuse.P03.Definitions

namespace VSCLReuse

private theorem p03_mv_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecAdd x y) i =
      p03MatVec A x i + p03MatVec A y i := by
  simp [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private theorem p03_mv_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecSub x y) i =
      p03MatVec A x i - p03MatVec A y i := by
  simp [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private theorem p03_mv_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (c : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecScale c x) i = c * p03MatVec A x i := by
  simp only [p03MatVec, p03VecScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p03_mv_matrix_add {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatAdd A B) x i =
      p03MatVec A x i + p03MatVec B x i := by
  simp [p03MatVec, p03MatAdd, add_mul, Finset.sum_add_distrib]

private theorem p03_mv_matrix_scale {n : ℕ} (c : ℝ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatScale c A) x i = c * p03MatVec A x i := by
  simp only [p03MatVec, p03MatScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p03_mv_mul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul A B) x i =
      p03MatVec A (p03MatVec B x) i := by
  simp only [p03MatVec, p03MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
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

private theorem p03_abs_mv_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤
      p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  calc
    |p03MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| := by
      simpa [p03MatVec] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun j : Fin n => A i j * x j)
    _ = _ := by simp [p03MatVec, p03AbsMatrix, p03AbsVec, abs_mul]

private theorem p03_abs_action_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  exact p03_mv_nonneg _ (by intro j k; exact abs_nonneg _) _
    (by intro j; exact abs_nonneg _) _

private theorem p03_c3_nonneg {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 ≤ p03Lemma43c3 run := by
  have hu : 0 < run.u := run.u_pos
  have hn : (0 : ℝ) ≤ n := by positivity
  cases hprecision : run.precision with
  | single =>
      have hb : 1 + (n : ℝ) * run.u ≤ (1 + run.u) ^ n := by
        simpa [add_comm, mul_comm] using
          (one_add_mul_le_pow (a := run.u) (n := n) (by linarith))
      have hnum : 0 ≤
          (1 + run.u) * ((1 + run.u) ^ n - 1) - (n : ℝ) * run.u := by
        have h₁ : 0 ≤ (n : ℝ) * run.u := mul_nonneg hn (le_of_lt hu)
        nlinarith
      have hu2 : 0 < run.u ^ 2 := sq_pos_of_pos hu
      simp only [p03Lemma43c3, hprecision]
      apply (sub_nonneg).mpr
      apply (div_le_div_iff₀ hu hu2).mpr
      nlinarith [mul_nonneg hnum (le_of_lt hu)]
  | double =>
      have hb : 1 + (n : ℝ) * run.u ^ 2 ≤ (1 + run.u ^ 2) ^ n := by
        simpa [add_comm, mul_comm] using
          (one_add_mul_le_pow (a := run.u ^ 2) (n := n)
            (by nlinarith [sq_nonneg run.u]))
      have hu2 : 0 < run.u ^ 2 := sq_pos_of_pos hu
      have hfac : 1 ≤ (1 + run.u) * (1 + run.u ^ 2) := by
        nlinarith [sq_nonneg run.u]
      have hnum : (n : ℝ) * run.u ^ 2 ≤
          (1 + run.u) * (1 + run.u ^ 2) * ((1 + run.u ^ 2) ^ n - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (by nlinarith :
          0 ≤ (1 + run.u ^ 2) ^ n - 1)) (sub_nonneg.mpr hfac)]
      simp only [p03Lemma43c3, hprecision]
      apply (sub_nonneg).mpr
      exact (le_div_iff₀ hu2).mpr hnum

private theorem p03_ubar_pos {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision <;> simp [p03ResidualUnitRoundoff, run.u_pos]

private theorem p03_c4_nonneg {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 ≤ p03Lemma43c4 run := by
  cases h : run.precision <;> simp [p03Lemma43c4, h]; linarith [run.u_pos]

private theorem p03_c5_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    0 ≤ constants.c5 := by
  rw [constants.c5_definition]
  have hsum : 0 ≤ p03Lemma43c3 run + p03Lemma43c4 run :=
    add_nonneg (p03_c3_nonneg run) (p03_c4_nonneg run)
  have hratio : 0 ≤
      (p03Lemma43c3 run + p03Lemma43c4 run) * run.u ^ 2 /
        p03ResidualUnitRoundoff run.precision run.u :=
    div_nonneg (mul_nonneg hsum (sq_nonneg _))
      (le_of_lt (p03_ubar_pos run))
  positivity

private theorem p03_mm_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  exact p03_mv_nonneg A hA (fun k => B k j) (fun k => hB k j) i

private theorem p03_abs_matrix_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private theorem p03_vec_abs_bound {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x y : Fin n → ℝ)
    (hxy : ∀ j, |x j| ≤ y j) (i : Fin n) :
    |p03MatVec A x i| ≤ p03MatVec (p03AbsMatrix A) y i := by
  exact (p03_abs_mv_le A x i).trans
    (p03_mv_mono _ (p03_abs_matrix_nonneg A) _ _ hxy i)

private theorem p03_inverse_residual {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    p03MatVec run.Ainv (p03ExactResidualAfterCorrection run m) i =
      run.iterate m i - run.correction m i - run.exactSolution i := by
  let y := p03VecSub (run.iterate m) (run.correction m)
  have heq : p03ExactResidualAfterCorrection run m =
      p03VecSub (p03MatVec run.A y) (p03MatVec run.A run.exactSolution) := by
    simp [p03ExactResidualAfterCorrection, y, run.exact_system]
  rw [heq, p03_mv_sub, ← p03_mv_mul, ← p03_mv_mul,
    run.inverse_left, p03_mv_id, p03_mv_id]
  rfl

private theorem p03_residual_error_identity {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    p03ExactResidualAfterCorrection run m i =
      -roundoff.residualError m i - roundoff.correctionError m i := by
  have hr := congrArg (fun f : Fin n → ℝ => f i) (roundoff.residual_equation m)
  have hc := congrArg (fun f : Fin n → ℝ => f i) (roundoff.correction_equation m)
  simp only [p03VecAdd, p03VecSub] at hr hc
  simp only [p03ExactResidualAfterCorrection, p03VecSub]
  rw [p03_mv_sub]
  linarith

private theorem p03_residual_error_zero {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (i : Fin n) : roundoff.residualError 0 i = 0 := by
  have hr := congrArg (fun f : Fin n → ℝ => f i) (roundoff.residual_equation 0)
  simp [run.residual_zero, run.iterate_zero, p03MatVec, p03VecAdd,
    p03VecSub] at hr
  linarith

private theorem p03_iterate_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
        p03MatVec (p03AbsMatrix run.Ainv)
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * |run.exactSolution i| := by
  let q := p03ExactResidualAfterCorrection run m
  let B := p03MatVec (p03AbsMatrix run.Ainv) (p03AbsVec q) i
  have hq : p03MatVec run.Ainv q i =
      run.iterate m i - run.correction m i - run.exactSolution i :=
    p03_inverse_residual run m i
  have hupdate := congrArg (fun f : Fin n → ℝ => f i) (run.update_equation m)
  simp only [p03VecAdd, p03VecSub] at hupdate
  have hdecomp : run.iterate (m + 1) i - run.exactSolution i =
      p03MatVec run.Ainv q i + run.updateError (m + 1) i := by
    linarith
  have hcorr : |run.iterate m i - run.correction m i| ≤
      |run.exactSolution i| + B := by
    have heq : run.iterate m i - run.correction m i =
        run.exactSolution i + p03MatVec run.Ainv q i := by linarith
    rw [heq]
    exact (abs_add_le _ _).trans
      (add_le_add_right (p03_abs_mv_le run.Ainv q i) _)
  have hupd : |run.updateError (m + 1) i| ≤
      run.u * (|run.exactSolution i| + B) :=
    (run.update_error_bound m i).trans
      (mul_le_mul_of_nonneg_left hcorr (le_of_lt run.u_pos))
  calc
    |run.iterate (m + 1) i - run.exactSolution i| =
        |p03MatVec run.Ainv q i + run.updateError (m + 1) i| := by rw [hdecomp]
    _ ≤ |p03MatVec run.Ainv q i| + |run.updateError (m + 1) i| :=
      abs_add_le _ _
    _ ≤ B + run.u * (|run.exactSolution i| + B) :=
      add_le_add (p03_abs_mv_le run.Ainv q i) hupd
    _ = (1 + run.u) * B + run.u * |run.exactSolution i| := by ring

private theorem p03_residual_roundoff_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (m : ℕ) (i : Fin n) :
    |roundoff.residualError (m + 1) i| ≤
      (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) *
        ((1 + run.u) *
          p03MatVec
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))
            (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
          run.u * p03MatVec (p03AbsMatrix run.A)
            (p03AbsVec run.exactSolution) i) := by
  let xerr := p03VecSub (run.iterate (m + 1)) run.exactSolution
  let q := p03ExactResidualAfterCorrection run m
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let a := p03MatVec absA (p03AbsVec run.exactSolution) i
  let T := p03MatVec (p03MatMul absA absAinv) (p03AbsVec q) i
  let D := p03MatVec absA (p03AbsVec xerr) i
  have hD : D ≤ (1 + run.u) * T + run.u * a := by
    let major : Fin n → ℝ := p03VecAdd
      (p03VecScale (1 + run.u) (p03MatVec absAinv (p03AbsVec q)))
      (p03VecScale run.u (p03AbsVec run.exactSolution))
    have hm : ∀ j, p03AbsVec xerr j ≤ major j := by
      intro j
      exact p03_iterate_error_bound run m j
    calc
      D ≤ p03MatVec absA major i :=
        p03_mv_mono absA (p03_abs_matrix_nonneg _) _ _ hm i
      _ = (1 + run.u) * T + run.u * a := by
        dsimp only [major]
        rw [p03_mv_add, p03_mv_scale, p03_mv_scale, ← p03_mv_mul]
  have hAerr : |p03MatVec run.A xerr i| ≤ D :=
    p03_abs_mv_le run.A xerr i
  have hcoeff : 0 ≤ constants.c5 *
      p03ResidualUnitRoundoff run.precision run.u + run.u := by
    exact add_nonneg
      (mul_nonneg (p03_c5_nonneg run norm dimensionBounds constants)
        (le_of_lt (p03_ubar_pos run))) (le_of_lt run.u_pos)
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  calc
    |roundoff.residualError (m + 1) i| ≤
      (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) * a +
        constants.c5 * p03ResidualUnitRoundoff run.precision run.u * D +
        run.u * |p03MatVec run.A xerr i| :=
      roundoff.residual_error_bound (m + 1) i
    _ ≤ (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) * a +
        constants.c5 * p03ResidualUnitRoundoff run.precision run.u * D +
        run.u * D := by
      gcongr
    _ = (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) * a +
        (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) * D := by ring
    _ ≤ (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) * a +
        (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) *
          ((1 + run.u) * T + run.u * a) := by gcongr

private theorem p03_correction_small {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2) :
    constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
  have hk : 0 ≤ p03KappaInverse run norm := norm.matrix_norm_nonnegative _
  exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right constants.c1_le_c8 (le_of_lt run.u_pos)) hk).trans
    hsmall

private theorem p03_abs_iterate_action_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    p03MatVec (p03AbsMatrix run.A)
        (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)) i ≤
      (1 + run.u) *
        p03MatVec
          (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * p03MatVec (p03AbsMatrix run.A)
        (p03AbsVec run.exactSolution) i := by
  let q := p03ExactResidualAfterCorrection run m
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let major : Fin n → ℝ := p03VecAdd
    (p03VecScale (1 + run.u) (p03MatVec absAinv (p03AbsVec q)))
    (p03VecScale run.u (p03AbsVec run.exactSolution))
  have hm : ∀ j,
      p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution) j ≤
        major j := by
    intro j
    exact p03_iterate_error_bound run m j
  calc
    p03MatVec absA
        (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)) i ≤
      p03MatVec absA major i :=
      p03_mv_mono absA (p03_abs_matrix_nonneg _) _ _ hm i
    _ = _ := by
      dsimp only [major]
      rw [p03_mv_add, p03_mv_scale, p03_mv_scale, ← p03_mv_mul]

private theorem p03_one_step_major {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (m : ℕ) (i : Fin n) :
    let absA := p03AbsMatrix run.A
    let absAinv := p03AbsMatrix run.Ainv
    let q := p03ExactResidualAfterCorrection run m
    let a := p03MatVec absA (p03AbsVec run.exactSolution)
    let t := p03MatVec (p03MatMul absA absAinv) (p03AbsVec q)
    let v := p03VecAdd (p03VecScale (1 + run.u) t) (p03VecScale run.u a)
    let e := p03VecAdd
      (p03VecScale
        (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) a)
      (p03VecScale
        (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) v)
    |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      e i + run.u * p03MatVec constants.C2 v i +
        run.u * p03MatVec
          (p03MatMul (p03MatMul constants.C2 absA) absAinv) e i := by
  dsimp only
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let q := p03ExactResidualAfterCorrection run m
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let t := p03MatVec (p03MatMul absA absAinv) (p03AbsVec q)
  let v := p03VecAdd (p03VecScale (1 + run.u) t) (p03VecScale run.u a)
  let e := p03VecAdd
    (p03VecScale
      (n * p03ResidualUnitRoundoff run.precision run.u +
        p03Lemma43c3 run * run.u ^ 2) a)
    (p03VecScale
      (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) v)
  have hv : ∀ j,
      p03MatVec absA
        (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)) j ≤
        v j := p03_abs_iterate_action_bound run m
  have he : ∀ j, |roundoff.residualError (m + 1) j| ≤ e j :=
    p03_residual_roundoff_bound run norm dimensionBounds constants roundoff m
  have hfirst : p03MatVec
      (p03MatMul constants.C2 absA)
      (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)) i ≤
      p03MatVec constants.C2 v i := by
    rw [p03_mv_mul]
    exact p03_mv_mono constants.C2 constants.C2_nonnegative _ _ hv i
  have hsecond : p03MatVec
      (p03MatMul (p03MatMul constants.C2 absA) absAinv)
      (p03AbsVec (roundoff.residualError (m + 1))) i ≤
      p03MatVec (p03MatMul (p03MatMul constants.C2 absA) absAinv) e i := by
    exact p03_mv_mono _
      (p03_mm_nonneg _ _
        (p03_mm_nonneg _ _ constants.C2_nonnegative
          (p03_abs_matrix_nonneg _)) (p03_abs_matrix_nonneg _))
      _ _ he i
  have hc := roundoff.correction_error_bound
    (p03_correction_small run norm dimensionBounds constants hsmall) (m + 1) i
  have hq := p03_residual_error_identity run norm dimensionBounds constants
    roundoff (m + 1) i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  calc
    |p03ExactResidualAfterCorrection run (m + 1) i| =
        |roundoff.residualError (m + 1) i +
          roundoff.correctionError (m + 1) i| := by
      rw [hq]
      have hneg : -roundoff.residualError (m + 1) i -
          roundoff.correctionError (m + 1) i =
          -(roundoff.residualError (m + 1) i +
            roundoff.correctionError (m + 1) i) := by ring
      rw [hneg, abs_neg]
    _ ≤ |roundoff.residualError (m + 1) i| +
          |roundoff.correctionError (m + 1) i| := abs_add_le _ _
    _ ≤ e i +
        (run.u * p03MatVec (p03MatMul constants.C2 absA)
          (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution)) i +
        run.u * p03MatVec
          (p03MatMul (p03MatMul constants.C2 absA) absAinv)
          (p03AbsVec (roundoff.residualError (m + 1))) i) :=
      add_le_add (he i) hc
    _ ≤ e i + run.u * p03MatVec constants.C2 v i +
        run.u * p03MatVec
          (p03MatMul (p03MatMul constants.C2 absA) absAinv) e i := by
      have h₁ := mul_le_mul_of_nonneg_left hfirst hu
      have h₂ := mul_le_mul_of_nonneg_left hsecond hu
      linarith

private theorem p03_C6_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    let S := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
    p03MatVec constants.C6 x i =
      p03MatVec constants.C2 x i +
        (1 + constants.c5 *
          p03ResidualUnitRoundoff run.precision run.u / run.u) *
          (x i + run.u * p03MatVec constants.C2 (p03MatVec S x) i) := by
  dsimp only
  rw [constants.C6_definition, p03_mv_matrix_add, p03_mv_matrix_scale,
    p03_mv_matrix_add, p03_mv_id, p03_mv_matrix_scale, p03_mv_mul]

private theorem p03_C7_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec constants.C7 x i =
      (n + p03Lemma43c3 run * run.u ^ 2 /
        p03ResidualUnitRoundoff run.precision run.u) *
        p03MatVec constants.C2 x i := by
  rw [constants.C7_definition, p03_mv_matrix_scale]

private theorem p03_C8_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec constants.C8 x i =
      (1 + run.u) * p03MatVec constants.C6 x i := by
  rw [constants.C8_definition, p03_mv_matrix_scale]

private theorem p03_C9_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec constants.C9 x i =
      p03MatVec constants.C6 x i + p03Lemma43c3 run * x i := by
  rw [constants.C9_definition, p03_mv_matrix_add,
    p03_mv_matrix_scale, p03_mv_id]

private theorem p03_mv_assoc {n : ℕ}
    (A B C : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul (p03MatMul A B) C) x i =
      p03MatVec A (p03MatVec (p03MatMul B C) x) i := by
  have hfun : p03MatVec (p03MatMul B C) x =
      p03MatVec B (p03MatVec C x) := by
    funext j
    exact p03_mv_mul B C x j
  rw [hfun, p03_mv_mul, p03_mv_mul]

private theorem p03_mv_triple {n : ℕ}
    (A B C : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul (p03MatMul A B) C) x i =
      p03MatVec A (p03MatVec B (p03MatVec C x)) i := by
  rw [p03_mv_mul, p03_mv_mul]

private theorem p03_recurrence_identity {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (m : ℕ) (i : Fin n) :
    let absA := p03AbsMatrix run.A
    let absAinv := p03AbsMatrix run.Ainv
    let q := p03ExactResidualAfterCorrection run m
    let a := p03MatVec absA (p03AbsVec run.exactSolution)
    let t := p03MatVec (p03MatMul absA absAinv) (p03AbsVec q)
    let v := p03VecAdd (p03VecScale (1 + run.u) t) (p03VecScale run.u a)
    let e := p03VecAdd
      (p03VecScale
        (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) a)
      (p03VecScale
        (constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u) v)
    e i + run.u * p03MatVec constants.C2 v i +
      run.u * p03MatVec
        (p03MatMul (p03MatMul constants.C2 absA) absAinv) e i =
      p03MatVec (p03Lemma43Propagation constants) (p03AbsVec q) i +
        p03Lemma43RecurrenceForcing constants i := by
  dsimp only
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let S := p03MatMul absA absAinv
  let q := p03ExactResidualAfterCorrection run m
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let t := p03MatVec S (p03AbsVec q)
  let v := p03VecAdd (p03VecScale (1 + run.u) t) (p03VecScale run.u a)
  let α := (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u +
    p03Lemma43c3 run * run.u ^ 2
  let β := constants.c5 * p03ResidualUnitRoundoff run.precision run.u + run.u
  let e := p03VecAdd (p03VecScale α a) (p03VecScale β v)
  have hleft : e i + run.u * p03MatVec constants.C2 v i +
      run.u * p03MatVec
        (p03MatMul (p03MatMul constants.C2 absA) absAinv) e i =
      α * a i + β * v i + run.u * p03MatVec constants.C2 v i +
        run.u * (α * p03MatVec constants.C2 (p03MatVec S a) i +
          β * p03MatVec constants.C2 (p03MatVec S v) i) := by
    rw [p03_mv_assoc]
    have hfun : p03MatVec S e =
        p03VecAdd (p03VecScale α (p03MatVec S a))
          (p03VecScale β (p03MatVec S v)) := by
      funext j
      dsimp only [e]
      rw [p03_mv_add, p03_mv_scale, p03_mv_scale]
      rfl
    rw [hfun]
    simp only [p03_mv_add, p03_mv_scale]
    dsimp only [e, p03VecAdd, p03VecScale]
  have hright : p03MatVec (p03Lemma43Propagation constants)
      (p03AbsVec q) i + p03Lemma43RecurrenceForcing constants i =
      run.u * (1 + run.u) * p03MatVec constants.C6 t i +
        (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u * a i +
        run.u ^ 2 * p03MatVec constants.C9 a i +
        p03ResidualUnitRoundoff run.precision run.u * run.u *
          p03MatVec constants.C7 (p03MatVec S a) i := by
    simp only [p03Lemma43Propagation, p03Lemma43RecurrenceForcing,
      p03VecAdd, p03VecScale, p03_mv_matrix_scale, p03_mv_mul]
    rw [p03_C8_action]
    ring
  rw [hleft, hright]
  have hvi : v i = (1 + run.u) * t i + run.u * a i := rfl
  have hcvi : p03MatVec constants.C2 v i =
      (1 + run.u) * p03MatVec constants.C2 t i +
        run.u * p03MatVec constants.C2 a i := by
    dsimp only [v]
    rw [p03_mv_add, p03_mv_scale, p03_mv_scale]
  have hcsvi : p03MatVec constants.C2 (p03MatVec S v) i =
      (1 + run.u) * p03MatVec constants.C2 (p03MatVec S t) i +
        run.u * p03MatVec constants.C2 (p03MatVec S a) i := by
    have hSv : p03MatVec S v =
        p03VecAdd (p03VecScale (1 + run.u) (p03MatVec S t))
          (p03VecScale run.u (p03MatVec S a)) := by
      funext j
      change p03MatVec S
        (p03VecAdd (p03VecScale (1 + run.u) t) (p03VecScale run.u a)) j = _
      rw [p03_mv_add, p03_mv_scale, p03_mv_scale]
      rfl
    rw [hSv, p03_mv_add, p03_mv_scale, p03_mv_scale]
  rw [hvi, hcvi, hcsvi]
  rw [p03_C9_action run norm dimensionBounds constants a i,
    p03_C7_action run norm dimensionBounds constants (p03MatVec S a) i,
    p03_C6_action run norm dimensionBounds constants t i,
    p03_C6_action run norm dimensionBounds constants a i]
  dsimp only [α, β, S]
  have hu_ne : run.u ≠ 0 := ne_of_gt run.u_pos
  have hubar_ne : p03ResidualUnitRoundoff run.precision run.u ≠ 0 :=
    ne_of_gt (p03_ubar_pos run)
  field_simp [hu_ne, hubar_ne]
  ring

private theorem p03_one_step_bound {n : ℕ}
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
  exact (p03_one_step_major run norm dimensionBounds constants roundoff
    hsmall m i).trans
      (le_of_eq (p03_recurrence_identity run norm dimensionBounds constants m i))

private theorem p03_C10_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (i : Fin n) :
    let S := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
    p03MatVec constants.C10 x i =
      p03MatVec constants.C6 x i +
        (n * p03ResidualUnitRoundoff run.precision run.u / run.u +
          p03Lemma43c3 run * run.u) * x i +
        p03ResidualUnitRoundoff run.precision run.u *
          p03MatVec constants.C7 (p03MatVec S x) i := by
  dsimp only
  rw [constants.C10_definition, p03_mv_matrix_add, p03_mv_matrix_add,
    p03_mv_matrix_scale, p03_mv_id, p03_mv_matrix_scale, p03_mv_mul]

private theorem p03_C2_le_C10_action {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) :
    p03MatVec constants.C2 x i ≤ p03MatVec constants.C10 x i := by
  let S := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  have hS : p03MatNonnegative S :=
    p03_mm_nonneg _ _ (p03_abs_matrix_nonneg _) (p03_abs_matrix_nonneg _)
  have hSx : ∀ j, 0 ≤ p03MatVec S x j :=
    fun j => p03_mv_nonneg S hS x hx j
  have hC2S : 0 ≤ p03MatVec constants.C2 (p03MatVec S x) i :=
    p03_mv_nonneg _ constants.C2_nonnegative _ hSx i
  have hC7S : 0 ≤ p03MatVec constants.C7 (p03MatVec S x) i :=
    p03_mv_nonneg _ constants.C7_nonnegative _ hSx i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p03ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p03_ubar_pos run)
  have hc5 : 0 ≤ constants.c5 :=
    p03_c5_nonneg run norm dimensionBounds constants
  have hc3 : 0 ≤ p03Lemma43c3 run := p03_c3_nonneg run
  have hk : 0 ≤ 1 + constants.c5 *
      p03ResidualUnitRoundoff run.precision run.u / run.u := by positivity
  have hgamma : 0 ≤
      (n : ℝ) * p03ResidualUnitRoundoff run.precision run.u / run.u +
        p03Lemma43c3 run * run.u := by positivity
  rw [p03_C10_action run norm dimensionBounds constants x i,
    p03_C6_action run norm dimensionBounds constants x i]
  nlinarith [mul_nonneg hu hC2S, mul_nonneg hk
    (add_nonneg (hx i) (mul_nonneg hu hC2S)),
    mul_nonneg hgamma (hx i), mul_nonneg hubar hC7S]

private theorem p03_stationary_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) : 0 ≤ p03Lemma43StationaryVector constants i := by
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let absx := p03AbsVec run.exactSolution
  have hA : p03MatNonnegative absA := p03_abs_matrix_nonneg _
  have hAi : p03MatNonnegative absAinv := p03_abs_matrix_nonneg _
  have hx : ∀ j, 0 ≤ absx j := fun j => abs_nonneg _
  have h₁ : 0 ≤ p03MatVec absA absx i := p03_mv_nonneg _ hA _ hx i
  have h₂ : 0 ≤ p03MatVec (p03MatMul constants.C11 absA) absx i :=
    p03_mv_nonneg _ (p03_mm_nonneg _ _ constants.C11_nonnegative hA) _ hx i
  have h₃ : 0 ≤ p03MatVec
      (p03MatMul
        (p03MatMul constants.C12 (p03MatMul absA absAinv)) absA) absx i := by
    exact p03_mv_nonneg _
      (p03_mm_nonneg _ _
        (p03_mm_nonneg _ _ constants.C12_nonnegative
          (p03_mm_nonneg _ _ hA hAi)) hA) _ hx i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : 0 ≤ p03ResidualUnitRoundoff run.precision run.u :=
    le_of_lt (p03_ubar_pos run)
  simp only [p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
  exact add_nonneg (mul_nonneg (mul_nonneg (by positivity) hubar) h₁)
    (add_nonneg (mul_nonneg (sq_nonneg _) h₂)
      (mul_nonneg (mul_nonneg hubar hu) h₃))

private theorem p03_initial_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i := by
  let absA := p03AbsMatrix run.A
  let absx := p03AbsVec run.exactSolution
  let a := p03MatVec absA absx
  have he0 : roundoff.residualError 0 = fun _ => 0 := by
    funext j
    exact p03_residual_error_zero run norm dimensionBounds constants roundoff j
  have hx0 : p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution) =
      absx := by
    funext j
    simp [run.iterate_zero, p03VecSub, p03AbsVec, absx, abs_neg]
  have hq0 := p03_residual_error_identity run norm dimensionBounds constants
    roundoff 0 i
  have hc0 := roundoff.correction_error_bound
    (p03_correction_small run norm dimensionBounds constants hsmall) 0 i
  rw [he0, hx0] at hc0
  have hzeroabs : p03AbsVec (fun _ : Fin n => (0 : ℝ)) =
      fun _ => 0 := by funext j; simp [p03AbsVec]
  have hzero : p03MatVec
      (p03MatMul (p03MatMul constants.C2 absA) (p03AbsMatrix run.Ainv))
      (fun _ => (0 : ℝ)) i = 0 := by simp [p03MatVec]
  rw [hzeroabs, hzero, mul_zero, add_zero, p03_mv_mul] at hc0
  have hc2 : p03MatVec constants.C2 a i ≤ p03MatVec constants.C10 a i :=
    p03_C2_le_C10_action run norm dimensionBounds constants a
      (fun j => p03_abs_action_nonneg run.A run.exactSolution j) i
  have hqabs : |p03ExactResidualAfterCorrection run 0 i| =
      |roundoff.correctionError 0 i| := by
    rw [hq0, he0]
    simp
  calc
    |p03ExactResidualAfterCorrection run 0 i| =
        |roundoff.correctionError 0 i| := hqabs
    _ ≤ run.u * p03MatVec constants.C2 a i := hc0
    _ ≤ run.u * p03MatVec constants.C10 a i :=
      mul_le_mul_of_nonneg_left hc2 (le_of_lt run.u_pos)
    _ = p03Lemma43InitialVector constants i := by
      simp [p03Lemma43InitialVector, p03VecScale, p03_mv_mul, a, absA, absx]

private theorem p03_stationary_fixed_point {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43StationaryVector constants i =
      p03Lemma43RecurrenceForcing constants i +
        p03MatVec (p03Lemma43Propagation constants)
          (p03Lemma43StationaryVector constants) i := by
  let absA := p03AbsMatrix run.A
  let S := p03MatMul absA (p03AbsMatrix run.Ainv)
  let a := p03MatVec absA (p03AbsVec run.exactSolution)
  let P := p03Lemma43Propagation constants
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let sta := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  have hC11 := congrArg (fun M : Fin n → Fin n → ℝ => p03MatVec M a i)
    constants.C11_fixed_point
  change p03MatVec constants.C11 a i =
    p03MatVec (p03MatAdd constants.C9
      (p03MatMul P constants.C11)) a i at hC11
  rw [p03_mv_matrix_add, p03_mv_mul] at hC11
  have hC12 := congrArg (fun M : Fin n → Fin n → ℝ =>
    p03MatVec M (p03MatVec S a) i) constants.C12_fixed_point
  change p03MatVec constants.C12 (p03MatVec S a) i =
    p03MatVec
      (p03MatAdd (p03MatAdd (p03MatScale n constants.C8) constants.C7)
        (p03MatMul P constants.C12)) (p03MatVec S a) i at hC12
  rw [p03_mv_matrix_add, p03_mv_matrix_add, p03_mv_matrix_scale,
    p03_mv_mul] at hC12
  have hP : ∀ x : Fin n → ℝ,
      p03MatVec P x i =
        run.u * p03MatVec constants.C8 (p03MatVec S x) i := by
    intro x
    change p03MatVec (p03MatScale run.u (p03MatMul constants.C8 S)) x i = _
    rw [p03_mv_matrix_scale, p03_mv_mul]
  have hstaFun : sta =
      p03VecAdd (p03VecScale ((n : ℝ) * ubar) a)
        (p03VecAdd
          (p03VecScale (run.u ^ 2) (p03MatVec constants.C11 a))
          (p03VecScale (ubar * run.u)
            (p03MatVec constants.C12 (p03MatVec S a)))) := by
    funext j
    simp only [sta, p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
    rw [p03_mv_triple, p03_mv_mul]
  have hFFun : F =
      p03VecAdd (p03VecScale ((n : ℝ) * ubar) a)
        (p03VecAdd
          (p03VecScale (run.u ^ 2) (p03MatVec constants.C9 a))
          (p03VecScale (ubar * run.u)
            (p03MatVec constants.C7 (p03MatVec S a)))) := by
    funext j
    simp only [F, p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale]
    rw [p03_mv_triple, p03_mv_mul]
  have hsta : sta i =
      (n : ℝ) * ubar * a i +
        run.u ^ 2 * p03MatVec constants.C11 a i +
        ubar * run.u * p03MatVec constants.C12 (p03MatVec S a) i := by
    rw [hstaFun]
    simp only [p03VecAdd, p03VecScale]
    ring
  have hF : F i =
      (n : ℝ) * ubar * a i +
        run.u ^ 2 * p03MatVec constants.C9 a i +
        ubar * run.u * p03MatVec constants.C7 (p03MatVec S a) i := by
    rw [hFFun]
    simp only [p03VecAdd, p03VecScale]
    ring
  have hPsta : p03MatVec P sta i =
      (n : ℝ) * ubar * p03MatVec P a i +
        run.u ^ 2 * p03MatVec P (p03MatVec constants.C11 a) i +
        ubar * run.u *
          p03MatVec P (p03MatVec constants.C12 (p03MatVec S a)) i := by
    rw [hstaFun]
    simp only [p03_mv_add, p03_mv_scale]
    ring
  change sta i = F i + p03MatVec P sta i
  rw [hsta, hF, hPsta, hP a]
  rw [hC11, hC12]
  ring

private theorem p03_propagation_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    p03MatNonnegative (p03Lemma43Propagation constants) := by
  intro i j
  have hS : p03MatNonnegative
      (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)) :=
    p03_mm_nonneg _ _ (p03_abs_matrix_nonneg _) (p03_abs_matrix_nonneg _)
  have hCS : p03MatNonnegative
      (p03MatMul constants.C8
        (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))) :=
    p03_mm_nonneg _ _ constants.C8_nonnegative hS
  exact mul_nonneg (le_of_lt run.u_pos) (hCS i j)

private theorem p03_bound_recurrence {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (m : ℕ) (i : Fin n) :
    p03Lemma43Bound constants (m + 1) i =
      p03MatVec (p03Lemma43Propagation constants)
        (p03Lemma43Bound constants m) i +
        p03Lemma43RecurrenceForcing constants i := by
  let P := p03Lemma43Propagation constants
  let init := p03Lemma43InitialVector constants
  let sta := p03Lemma43StationaryVector constants
  let F := p03Lemma43RecurrenceForcing constants
  have hp : p03MatVec (p03MatPow P (m + 1)) init i =
      p03MatVec P (p03MatVec (p03MatPow P m) init) i := by
    change p03MatVec (p03MatMul P (p03MatPow P m)) init i = _
    exact p03_mv_mul P (p03MatPow P m) init i
  have hs : sta i = F i + p03MatVec P sta i :=
    p03_stationary_fixed_point run norm dimensionBounds constants i
  calc
    p03Lemma43Bound constants (m + 1) i =
        p03MatVec (p03MatPow P (m + 1)) init i + sta i := rfl
    _ = p03MatVec P (p03MatVec (p03MatPow P m) init) i +
          p03MatVec P sta i + F i := by rw [hp, hs]; ring
    _ = p03MatVec P (p03Lemma43Bound constants m) i + F i := by
      change p03MatVec P (p03MatVec (p03MatPow P m) init) i +
          p03MatVec P sta i + F i =
        p03MatVec P
          (p03VecAdd (p03MatVec (p03MatPow P m) init) sta) i + F i
      rw [p03_mv_add]

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
      have hbase := p03_initial_bound run norm dimensionBounds constants
        roundoff hsmall i
      have hs := p03_stationary_nonneg run norm dimensionBounds constants i
      calc
        |p03ExactResidualAfterCorrection run 0 i| ≤
          p03Lemma43InitialVector constants i := hbase
        _ ≤ p03Lemma43InitialVector constants i +
            p03Lemma43StationaryVector constants i :=
          le_add_of_nonneg_right hs
        _ = p03Lemma43Bound constants 0 i := by
          simp [p03Lemma43Bound, p03MatPow, p03_mv_id, p03VecAdd]
  | succ m ih =>
      intro i
      have hP := p03_propagation_nonneg run norm dimensionBounds constants
      have hm := p03_mv_mono (p03Lemma43Propagation constants) hP
        (p03AbsVec (p03ExactResidualAfterCorrection run m))
        (p03Lemma43Bound constants m)
        (fun j => ih j) i
      calc
        |p03ExactResidualAfterCorrection run (m + 1) i| ≤
            p03MatVec (p03Lemma43Propagation constants)
              (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
              p03Lemma43RecurrenceForcing constants i :=
          p03_one_step_bound run norm dimensionBounds constants roundoff
            hsmall m i
        _ ≤ p03MatVec (p03Lemma43Propagation constants)
              (p03Lemma43Bound constants m) i +
              p03Lemma43RecurrenceForcing constants i :=
          add_le_add_left hm _
        _ = p03Lemma43Bound constants (m + 1) i :=
          (p03_bound_recurrence run norm dimensionBounds constants m i).symm

end VSCLReuse
