import VSCLReuse.P03.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p03_mv_add {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecAdd x y) i = p03MatVec A x i + p03MatVec A y i := by
  simp only [p03MatVec, p03VecAdd, mul_add, Finset.sum_add_distrib]

private theorem p03_mv_sub {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecSub x y) i = p03MatVec A x i - p03MatVec A y i := by
  simp only [p03MatVec, p03VecSub, mul_sub, Finset.sum_sub_distrib]

private theorem p03_mv_scale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec A (p03VecScale a x) i = a * p03MatVec A x i := by
  simp only [p03MatVec, p03VecScale, mul_left_comm, ← Finset.mul_sum]

private theorem p03_mv_matAdd {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatAdd A B) x i = p03MatVec A x i + p03MatVec B x i := by
  simp only [p03MatVec, p03MatAdd, add_mul, Finset.sum_add_distrib]

private theorem p03_mv_matScale {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatScale a A) x i = a * p03MatVec A x i := by
  simp only [p03MatVec, p03MatScale, mul_assoc, ← Finset.mul_sum]

private theorem p03_mv_mul {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03MatMul A B) x i = p03MatVec A (p03MatVec B x) i := by
  simp only [p03MatVec, p03MatMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

private theorem p03_mv_add_fun {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) :
    p03MatVec A (p03VecAdd x y) =
      p03VecAdd (p03MatVec A x) (p03MatVec A y) := by
  funext i
  exact p03_mv_add A x y i

private theorem p03_mv_scale_fun {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (x : Fin n → ℝ) :
    p03MatVec A (p03VecScale a x) =
      p03VecScale a (p03MatVec A x) := by
  funext i
  exact p03_mv_scale A a x i

private theorem p03_mv_mul_fun {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    p03MatVec (p03MatMul A B) x = p03MatVec A (p03MatVec B x) := by
  funext i
  exact p03_mv_mul A B x i

private theorem p03_mv_id {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec (p03IdMatrix n) x i = x i := by
  simp [p03MatVec, p03IdMatrix, mul_comm]

private theorem p03_mv_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (hA : p03MatNonnegative A)
    (hx : ∀ j, 0 ≤ x j) (i : Fin n) : 0 ≤ p03MatVec A x i := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hA i j) (hx j)

private theorem p03_mv_mono {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (hA : p03MatNonnegative A)
    (hxy : ∀ j, x j ≤ y j) (i : Fin n) :
    p03MatVec A x i ≤ p03MatVec A y i := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (hA i j)

private theorem p03_mv_abs_le {n : ℕ} (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    |p03MatVec A x i| ≤ p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
  calc
    |p03MatVec A x i| ≤ ∑ j : Fin n, |A i j * x j| := by
      simp only [p03MatVec]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = p03MatVec (p03AbsMatrix A) (p03AbsVec x) i := by
      simp only [p03MatVec, p03AbsMatrix, p03AbsVec, abs_mul]

private theorem p03_absmat_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ) :
    p03MatNonnegative (p03AbsMatrix A) := by
  intro i j
  exact abs_nonneg _

private theorem p03_matmul_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ)
    (hA : p03MatNonnegative A) (hB : p03MatNonnegative B) :
    p03MatNonnegative (p03MatMul A B) := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hA i k) (hB k j)

private theorem p03_matScale_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (hA : p03MatNonnegative A) :
    p03MatNonnegative (p03MatScale a A) := by
  intro i j
  exact mul_nonneg ha (hA i j)

private theorem p03_absvec_nonneg {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ p03AbsVec x i := abs_nonneg _

private theorem p03_absvec_mono {n : ℕ} (x y : Fin n → ℝ)
    (h : ∀ i, |x i| ≤ y i) (i : Fin n) :
    p03AbsVec x i ≤ y i := h i

private theorem p03_mv_inverse {n : ℕ} (run : P03IterativeRefinementRun n)
    (x : Fin n → ℝ) (i : Fin n) :
    p03MatVec run.Ainv (p03MatVec run.A x) i = x i := by
  rw [← p03_mv_mul, run.inverse_left, p03_mv_id]

private theorem p03_mv_exact_sub {n : ℕ} (run : P03IterativeRefinementRun n)
    (m : ℕ) (i : Fin n) :
    p03MatVec run.A (p03VecSub (run.iterate m) run.exactSolution) i =
      p03MatVec run.A (run.iterate m) i - run.b i := by
  rw [p03_mv_sub, run.exact_system]

private theorem p03_residual_identity {n : ℕ}
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
  simp only [p03VecAdd, p03VecSub] at hr hc
  simp only [p03ExactResidualAfterCorrection, p03VecSub, p03_mv_sub]
  linarith

private theorem p03_exact_solution_abs_action_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n) (i : Fin n) :
    0 ≤ p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i :=
  p03_mv_nonneg _ _ (p03_absmat_nonneg _) (p03_absvec_nonneg _) i

private theorem p03_uBar_pos {n : ℕ} (run : P03IterativeRefinementRun n) :
    0 < p03ResidualUnitRoundoff run.precision run.u := by
  cases run.precision with
  | single => exact run.u_pos
  | double => exact sq_pos_of_pos run.u_pos

private theorem p03_coarse_residual_bound {n : ℕ}
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
      (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution) i +
      run.u * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec constants.C7
          (p03MatVec
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))
            (p03MatVec (p03AbsMatrix run.A)
              (p03AbsVec run.exactSolution))) i := by
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let a := (n : ℝ) * ubar + p03Lemma43c3 run * run.u ^ 2
  let T := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let S := p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)
  let w := p03MatVec (p03AbsMatrix run.A)
    (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution))
  let R := p03AbsVec (roundoff.residualError m)
  let H : Fin n → ℝ := fun j ↦ a * S j + constants.c5 * ubar * w j + run.u * w j
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hubar : ubar ≠ 0 := ne_of_gt (p03_uBar_pos run)
  have hT : p03MatNonnegative T :=
    p03_matmul_nonneg _ _ (p03_absmat_nonneg _) (p03_absmat_nonneg _)
  have hsmall1 : constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 := by
    have hk : 0 ≤ p03KappaInverse run norm := norm.matrix_norm_nonnegative _
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr constants.c1_le_c8) hu) hk]
  have hR : ∀ j, R j ≤ H j := by
    intro j
    have hr := roundoff.residual_error_bound m j
    have he : |p03MatVec run.A
        (p03VecSub (run.iterate m) run.exactSolution) j| ≤ w j :=
      p03_mv_abs_le _ _ _
    dsimp [R, H, a, S, w, ubar, p03AbsVec] at *
    nlinarith [mul_nonneg hu (sub_nonneg.mpr he)]
  have hC : ∀ j, |roundoff.correctionError m j| ≤
      run.u * p03MatVec constants.C2 w j +
        run.u * p03MatVec constants.C2 (p03MatVec T R) j := by
    intro j
    have hc := roundoff.correction_error_bound hsmall1 m j
    have hfirst : p03MatVec
        (p03MatMul constants.C2 (p03AbsMatrix run.A))
        (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution)) j =
        p03MatVec constants.C2 w j := by
      exact p03_mv_mul _ _ _ _
    have hsecond : p03MatVec
        (p03MatMul (p03MatMul constants.C2 (p03AbsMatrix run.A))
          (p03AbsMatrix run.Ainv))
        (p03AbsVec (roundoff.residualError m)) j =
        p03MatVec constants.C2 (p03MatVec T R) j := by
      simp only [T, R, p03_mv_mul_fun, p03_mv_mul]
    simpa only [hfirst, hsecond] using hc
  have hq : |p03ExactResidualAfterCorrection run m i| ≤
      R i + run.u * p03MatVec constants.C2 w i +
        run.u * p03MatVec constants.C2 (p03MatVec T R) i := by
    rw [p03_residual_identity run norm dimensionBounds constants roundoff]
    calc
      |-(roundoff.residualError m i) - roundoff.correctionError m i| ≤
          |roundoff.residualError m i| + |roundoff.correctionError m i| := by
        simpa only [abs_neg] using abs_sub (-(roundoff.residualError m i))
          (roundoff.correctionError m i)
      _ ≤ _ := by dsimp [R, p03AbsVec]; linarith [hC i]
  have hM : p03MatNonnegative (p03MatMul constants.C2 T) :=
    p03_matmul_nonneg _ _ constants.C2_nonnegative hT
  have hqH : |p03ExactResidualAfterCorrection run m i| ≤
      H i + run.u * p03MatVec constants.C2 w i +
        run.u * p03MatVec constants.C2 (p03MatVec T H) i := by
    have hmono := p03_mv_mono (p03MatMul constants.C2 T) R H hM hR i
    simp only [p03_mv_mul] at hmono
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hmono), hR i]
  have hcalc : H i + run.u * p03MatVec constants.C2 w i +
        run.u * p03MatVec constants.C2 (p03MatVec T H) i =
      run.u * p03MatVec constants.C6 w i + a * S i +
        run.u * ubar * p03MatVec constants.C7 (p03MatVec T S) i := by
    have hH : H = p03VecAdd (p03VecScale a S)
        (p03VecAdd (p03VecScale (constants.c5 * ubar) w)
          (p03VecScale run.u w)) := by
      funext j
      dsimp [H, p03VecAdd, p03VecScale]
      ring
    rw [hH]
    rw [constants.C6_definition, constants.C7_definition]
    simp only [p03_mv_matAdd, p03_mv_matScale, p03_mv_id, p03_mv_mul,
      p03_mv_scale_fun, p03_mv_add_fun, p03_mv_scale, p03_mv_add]
    dsimp [p03VecAdd, p03VecScale, a]
    dsimp [T]
    field_simp [ne_of_gt run.u_pos, ne_of_gt (p03_uBar_pos run)]
    ring
  exact hqH.trans (le_of_eq (hcalc.trans (by rfl)))

private theorem p03_next_iterate_error_bound {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) (i : Fin n) :
    |run.iterate (m + 1) i - run.exactSolution i| ≤
      (1 + run.u) *
        p03MatVec (p03AbsMatrix run.Ainv)
          (p03AbsVec (p03ExactResidualAfterCorrection run m)) i +
      run.u * |run.exactSolution i| := by
  let z := p03VecSub (run.iterate m) (run.correction m)
  let q := p03ExactResidualAfterCorrection run m
  have hq : q = p03MatVec run.A (p03VecSub z run.exactSolution) := by
    funext j
    simp only [q, p03ExactResidualAfterCorrection, z, p03VecSub,
      p03_mv_sub, run.exact_system]
  have hz : z i - run.exactSolution i = p03MatVec run.Ainv q i := by
    rw [hq, p03_mv_inverse]
    rfl
  have habs : |z i - run.exactSolution i| ≤
      p03MatVec (p03AbsMatrix run.Ainv) (p03AbsVec q) i := by
    rw [hz]
    exact p03_mv_abs_le _ _ _
  have hu : |run.updateError (m + 1) i| ≤ run.u * |z i| := by
    convert run.update_error_bound m i using 1
  have hzu : |z i| ≤ |z i - run.exactSolution i| + |run.exactSolution i| := by
    calc
      |z i| = |(z i - run.exactSolution i) + run.exactSolution i| := by ring
      _ ≤ _ := abs_add_le _ _
  have hi : run.iterate (m + 1) i - run.exactSolution i =
      (z i - run.exactSolution i) + run.updateError (m + 1) i := by
    have h := congrFun (run.update_equation m) i
    dsimp [p03VecAdd, p03VecSub, z] at *
    linarith
  rw [hi]
  have htri := abs_add_le (z i - run.exactSolution i) (run.updateError (m + 1) i)
  have hmul := mul_le_mul_of_nonneg_left hzu (le_of_lt run.u_pos)
  have hmul2 := mul_le_mul_of_nonneg_left habs
    (show 0 ≤ 1 + run.u by linarith [run.u_pos])
  nlinarith [hmul2]

private theorem p03_stationary_nonneg {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) : 0 ≤ p03Lemma43StationaryVector constants i := by
  have hS : 0 ≤ p03MatVec (p03AbsMatrix run.A)
      (p03AbsVec run.exactSolution) i :=
    p03_exact_solution_abs_action_nonneg run i
  have h11 : 0 ≤ p03MatVec
      (p03MatMul constants.C11 (p03AbsMatrix run.A))
      (p03AbsVec run.exactSolution) i :=
    p03_mv_nonneg _ _
      (p03_matmul_nonneg _ _ constants.C11_nonnegative (p03_absmat_nonneg _))
      (p03_absvec_nonneg _) i
  have h12 : 0 ≤ p03MatVec
      (p03MatMul
        (p03MatMul constants.C12
          (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)))
        (p03AbsMatrix run.A))
      (p03AbsVec run.exactSolution) i := by
    apply p03_mv_nonneg
    · apply p03_matmul_nonneg
      · apply p03_matmul_nonneg
        · exact constants.C12_nonnegative
        · exact p03_matmul_nonneg _ _ (p03_absmat_nonneg _) (p03_absmat_nonneg _)
      · exact p03_absmat_nonneg _
    · exact p03_absvec_nonneg _
  have hu := le_of_lt run.u_pos
  have hubar := le_of_lt (p03_uBar_pos run)
  dsimp [p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
  exact add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hubar) hS)
    (add_nonneg (mul_nonneg (sq_nonneg _) h11)
      (mul_nonneg (mul_nonneg hubar hu) h12))

private theorem p03_initial_residual_bound {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff : P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall : constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2)
    (i : Fin n) :
    |p03ExactResidualAfterCorrection run 0 i| ≤
      p03Lemma43InitialVector constants i := by
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let T := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let S := p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)
  have habs : p03AbsVec (p03VecSub (run.iterate 0) run.exactSolution) =
      p03AbsVec run.exactSolution := by
    funext j
    simp [p03AbsVec, p03VecSub, run.iterate_zero]
  have hcoarse := p03_coarse_residual_bound run norm dimensionBounds
    constants roundoff hsmall 0 i
  rw [habs] at hcoarse
  have heq : run.u * p03MatVec constants.C6 S i +
      (n * ubar + p03Lemma43c3 run * run.u ^ 2) * S i +
      run.u * ubar * p03MatVec constants.C7 (p03MatVec T S) i =
      p03Lemma43InitialVector constants i := by
    dsimp [p03Lemma43InitialVector]
    rw [constants.C10_definition]
    dsimp [p03VecScale]
    simp only [p03_mv_matAdd, p03_mv_matScale, p03_mv_mul,
      p03_mv_id, p03_mv_scale]
    dsimp [S, T, ubar]
    field_simp [ne_of_gt run.u_pos]
  exact hcoarse.trans (le_of_eq heq)

private theorem p03_residual_recurrence {n : ℕ}
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
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let T := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let S := p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)
  let Q := p03AbsVec (p03ExactResidualAfterCorrection run m)
  let w := p03MatVec (p03AbsMatrix run.A)
    (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution))
  let W := p03VecAdd
    (p03VecScale (1 + run.u) (p03MatVec T Q))
    (p03VecScale run.u S)
  have hw : ∀ j, w j ≤ W j := by
    intro j
    let D := p03VecAdd
      (p03VecScale (1 + run.u)
        (p03MatVec (p03AbsMatrix run.Ainv) Q))
      (p03VecScale run.u (p03AbsVec run.exactSolution))
    have hD : ∀ k, p03AbsVec
        (p03VecSub (run.iterate (m + 1)) run.exactSolution) k ≤ D k := by
      intro k
      exact p03_next_iterate_error_bound run m k
    have hmono := p03_mv_mono (p03AbsMatrix run.A)
      (p03AbsVec (p03VecSub (run.iterate (m + 1)) run.exactSolution))
      D (p03_absmat_nonneg _) hD j
    have heq : p03MatVec (p03AbsMatrix run.A) D j = W j := by
      dsimp [D, W]
      simp only [p03_mv_add_fun, p03_mv_scale_fun, p03_mv_mul_fun,
        p03VecAdd, p03VecScale]
      dsimp [T, S]
      simp only [p03_mv_mul]
    exact hmono.trans (le_of_eq heq)
  have hmono := p03_mv_mono constants.C6 w W constants.C6_nonnegative hw i
  have hu : 0 ≤ run.u := le_of_lt run.u_pos
  have hcoarse := p03_coarse_residual_bound run norm dimensionBounds
    constants roundoff hsmall (m + 1) i
  have hbound : |p03ExactResidualAfterCorrection run (m + 1) i| ≤
      run.u * p03MatVec constants.C6 W i +
      (n * ubar + p03Lemma43c3 run * run.u ^ 2) * S i +
      run.u * ubar * p03MatVec constants.C7 (p03MatVec T S) i := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hmono)]
  have heq : run.u * p03MatVec constants.C6 W i +
      (n * ubar + p03Lemma43c3 run * run.u ^ 2) * S i +
      run.u * ubar * p03MatVec constants.C7 (p03MatVec T S) i =
      p03MatVec (p03Lemma43Propagation constants) Q i +
        p03Lemma43RecurrenceForcing constants i := by
    dsimp [p03Lemma43Propagation, p03Lemma43RecurrenceForcing, W]
    rw [constants.C8_definition, constants.C9_definition]
    dsimp [p03VecAdd, p03VecScale]
    simp only [p03_mv_matAdd, p03_mv_matScale, p03_mv_id,
      p03_mv_mul, p03_mv_add_fun, p03_mv_scale_fun,
      p03_mv_add, p03_mv_scale]
    dsimp [T, S, Q, ubar, p03VecAdd, p03VecScale]
    ring
  exact hbound.trans (le_of_eq heq)

private theorem p03_stationary_fixed_point {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (i : Fin n) :
    p03Lemma43StationaryVector constants i =
      p03MatVec (p03Lemma43Propagation constants)
        (p03Lemma43StationaryVector constants) i +
      p03Lemma43RecurrenceForcing constants i := by
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  let T := p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)
  let S := p03MatVec (p03AbsMatrix run.A) (p03AbsVec run.exactSolution)
  let P := p03Lemma43Propagation constants
  have h11 : p03MatVec constants.C11 S i =
      p03MatVec constants.C9 S i +
        p03MatVec P (p03MatVec constants.C11 S) i := by
    conv_lhs => rw [constants.C11_fixed_point]
    simp only [p03_mv_matAdd, p03_mv_mul_fun, p03_mv_mul]
    rfl
  have h12 : p03MatVec constants.C12 (p03MatVec T S) i =
      (n : ℝ) * p03MatVec constants.C8 (p03MatVec T S) i +
        p03MatVec constants.C7 (p03MatVec T S) i +
        p03MatVec P
          (p03MatVec constants.C12 (p03MatVec T S)) i := by
    conv_lhs => rw [constants.C12_fixed_point]
    simp only [p03_mv_matAdd, p03_mv_matScale, p03_mv_mul_fun, p03_mv_mul]
    dsimp [P, p03Lemma43Propagation, T]
    simp only [p03_mv_matScale, p03_mv_mul_fun, p03_mv_mul]
  have hP : p03MatVec P S i =
      run.u * p03MatVec constants.C8 (p03MatVec T S) i := by
    dsimp [P, p03Lemma43Propagation]
    simp only [p03_mv_matScale, p03_mv_mul_fun, p03_mv_mul]
    dsimp [T]
    simp only [p03_mv_mul_fun, p03_mv_mul]
  have hV : p03Lemma43StationaryVector constants i =
      (n : ℝ) * ubar * S i +
        run.u ^ 2 * p03MatVec constants.C11 S i +
        ubar * run.u * p03MatVec constants.C12 (p03MatVec T S) i := by
    dsimp [p03Lemma43StationaryVector, p03VecAdd, p03VecScale]
    simp only [p03_mv_mul_fun, p03_mv_mul]
    dsimp [T]
    simp only [p03_mv_mul_fun, p03_mv_mul]
    ring
  have hPV : p03MatVec P (p03Lemma43StationaryVector constants) i =
      (n : ℝ) * ubar * p03MatVec P S i +
        run.u ^ 2 * p03MatVec P (p03MatVec constants.C11 S) i +
        ubar * run.u * p03MatVec P
          (p03MatVec constants.C12 (p03MatVec T S)) i := by
    dsimp [p03Lemma43StationaryVector]
    simp only [p03_mv_add_fun, p03_mv_scale_fun,
      p03_mv_mul_fun, p03VecAdd, p03VecScale]
    dsimp [T]
    simp only [p03_mv_mul_fun, p03_mv_mul]
    ring
  have hF : p03Lemma43RecurrenceForcing constants i =
      (n : ℝ) * ubar * S i +
        run.u ^ 2 * p03MatVec constants.C9 S i +
        ubar * run.u * p03MatVec constants.C7 (p03MatVec T S) i := by
    dsimp [p03Lemma43RecurrenceForcing, p03VecAdd, p03VecScale]
    simp only [p03_mv_mul_fun, p03_mv_mul]
    dsimp [T]
    simp only [p03_mv_mul_fun, p03_mv_mul]
    ring
  rw [hV, hPV, hF]
  linear_combination run.u ^ 2 * h11 + (ubar * run.u) * h12 -
    ((n : ℝ) * ubar) * hP

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
  have hP : p03MatNonnegative (p03Lemma43Propagation constants) := by
    dsimp [p03Lemma43Propagation]
    apply p03_matScale_nonneg
    · exact le_of_lt run.u_pos
    · apply p03_matmul_nonneg
      · exact constants.C8_nonnegative
      · exact p03_matmul_nonneg _ _
          (p03_absmat_nonneg _) (p03_absmat_nonneg _)
  intro m
  induction m with
  | zero =>
      intro i
      have hinit := p03_initial_residual_bound run norm dimensionBounds
        constants roundoff hsmall i
      have hstat := p03_stationary_nonneg run norm dimensionBounds constants i
      change |p03ExactResidualAfterCorrection run 0 i| ≤
        p03MatVec (p03IdMatrix n) (p03Lemma43InitialVector constants) i +
          p03Lemma43StationaryVector constants i
      rw [p03_mv_id]
      linarith
  | succ m ih =>
      intro i
      have hrec := p03_residual_recurrence run norm dimensionBounds
        constants roundoff hsmall m i
      have hmono := p03_mv_mono (p03Lemma43Propagation constants)
        (p03AbsVec (p03ExactResidualAfterCorrection run m))
        (p03Lemma43Bound constants m) hP (by
          intro j
          exact ih j) i
      have hfix := p03_stationary_fixed_point run norm dimensionBounds constants i
      have heq : p03MatVec (p03Lemma43Propagation constants)
          (p03Lemma43Bound constants m) i +
          p03Lemma43RecurrenceForcing constants i =
          p03Lemma43Bound constants (m + 1) i := by
        calc
          _ = p03MatVec (p03Lemma43Propagation constants)
                (p03MatVec (p03MatPow (p03Lemma43Propagation constants) m)
                  (p03Lemma43InitialVector constants)) i +
              p03MatVec (p03Lemma43Propagation constants)
                (p03Lemma43StationaryVector constants) i +
              p03Lemma43RecurrenceForcing constants i := by
                dsimp [p03Lemma43Bound]
                rw [p03_mv_add]
          _ = p03Lemma43Bound constants (m + 1) i := by
                rw [add_assoc, ← hfix]
                change p03MatVec (p03Lemma43Propagation constants)
                    (p03MatVec (p03MatPow (p03Lemma43Propagation constants) m)
                      (p03Lemma43InitialVector constants)) i +
                    p03Lemma43StationaryVector constants i =
                  p03MatVec
                    (p03MatMul (p03Lemma43Propagation constants)
                      (p03MatPow (p03Lemma43Propagation constants) m))
                    (p03Lemma43InitialVector constants) i +
                    p03Lemma43StationaryVector constants i
                rw [p03_mv_mul]
      linarith [hrec, hmono, heq]

end VSCLReuse
