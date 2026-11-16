import VSCLReuse.P12.Definitions
import NumStability.Algorithms.MatMul
import Mathlib.Tactic

namespace VSCLReuse

private noncomputable def p12AsFPModel (fp : P12FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem p12_matmul_error (fp : P12FPModel) (n : ℕ)
    (A B : P12Matrix n) (hv : P12GammaValid fp.u n) (i j : Fin n) :
    |p12RoundedMatMul fp A B i j - p12MatMul A B i j| ≤
      p12Gamma fp.u n * p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  simpa only [p12RoundedMatMul, p12RoundedDotProduct, p12MatMul,
    p12AbsMatrix, p12Gamma, p12AsFPModel, NumStability.fl_matMul,
    NumStability.fl_matVec, NumStability.fl_dotProduct] using
    (NumStability.matMul_error_bound (p12AsFPModel fp) n n n A B hv i j)

private theorem p12_exact_power_abs (n : ℕ) (X : P12Matrix n) (k : ℕ) :
    ∀ i j, |p12PowerSteps X k i j| ≤ p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      change |∑ l : Fin n, p12PowerSteps X k i l * X l j| ≤
        ∑ l : Fin n, p12PowerSteps (p12AbsMatrix X) k i l * |X l j|
      calc
        |∑ l : Fin n, p12PowerSteps X k i l * X l j| ≤
            ∑ l : Fin n, |p12PowerSteps X k i l * X l j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l : Fin n, |p12PowerSteps X k i l| * |X l j| := by
              simp_rw [abs_mul]
        _ ≤ ∑ l : Fin n, p12PowerSteps (p12AbsMatrix X) k i l * |X l j| := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)

private theorem p12_step_bound (fp : P12FPModel) (n : ℕ)
    (A B P X : P12Matrix n) (g : ℝ)
    (hn : P12GammaValid fp.u n)
    (hA : ∀ i j, |A i j - B i j| ≤ g * P i j)
    (hB : ∀ i j, |B i j| ≤ P i j) (i j : Fin n) :
    |p12RoundedMatMul fp A X i j - p12MatMul B X i j| ≤
      (p12Gamma fp.u n + g + p12Gamma fp.u n * g) *
        p12MatMul P (p12AbsMatrix X) i j := by
  let M := p12MatMul P (p12AbsMatrix X) i j
  have hd : 0 ≤ p12Gamma fp.u n := by
    simpa [p12Gamma, p12AsFPModel, NumStability.gamma] using
      (NumStability.gamma_nonneg (p12AsFPModel fp) hn)
  have hAabs (l : Fin n) : |A i l| ≤ (1 + g) * P i l := by
    calc
      |A i l| = |(A i l - B i l) + B i l| := by ring
      _ ≤ |A i l - B i l| + |B i l| := abs_add_le _ _
      _ ≤ g * P i l + P i l := add_le_add (hA i l) (hB i l)
      _ = (1 + g) * P i l := by ring
  have hround := p12_matmul_error fp n A X hn i j
  have hround' :
      |p12RoundedMatMul fp A X i j - p12MatMul A X i j| ≤
        p12Gamma fp.u n * ((1 + g) * M) := by
    apply hround.trans
    apply mul_le_mul_of_nonneg_left _ hd
    dsimp [M, p12MatMul, p12AbsMatrix]
    calc
      (∑ l : Fin n, |A i l| * |X l j|) ≤
          ∑ l : Fin n, ((1 + g) * P i l) * |X l j| := by
            apply Finset.sum_le_sum
            intro l _
            exact mul_le_mul_of_nonneg_right (hAabs l) (abs_nonneg _)
      _ = (1 + g) * ∑ l : Fin n, P i l * |X l j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
  have hdiff :
      |p12MatMul A X i j - p12MatMul B X i j| ≤ g * M := by
    dsimp [p12MatMul, M, p12AbsMatrix]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ l : Fin n, (A i l * X l j - B i l * X l j)| ≤
          ∑ l : Fin n, |A i l * X l j - B i l * X l j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin n, |A i l - B i l| * |X l j| := by
            apply Finset.sum_congr rfl
            intro l _
            rw [← sub_mul, abs_mul]
      _ ≤ ∑ l : Fin n, (g * P i l) * |X l j| := by
            apply Finset.sum_le_sum
            intro l _
            exact mul_le_mul_of_nonneg_right (hA i l) (abs_nonneg _)
      _ = g * ∑ l : Fin n, P i l * |X l j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
  calc
    |p12RoundedMatMul fp A X i j - p12MatMul B X i j| =
        |(p12RoundedMatMul fp A X i j - p12MatMul A X i j) +
          (p12MatMul A X i j - p12MatMul B X i j)| := by ring
    _ ≤ |p12RoundedMatMul fp A X i j - p12MatMul A X i j| +
        |p12MatMul A X i j - p12MatMul B X i j| := abs_add_le _ _
    _ ≤ p12Gamma fp.u n * ((1 + g) * M) + g * M := add_le_add hround' hdiff
    _ = (p12Gamma fp.u n + g + p12Gamma fp.u n * g) * M := by ring

/-- P12-C2: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p12_c2_lemma_2_2
    (fp : P12FPModel) (n k : ℕ) (X : P12Matrix n)
    (hvalid : P12GammaValid fp.u (k * n)) :
    ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        p12Gamma fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  -- PROOF_START P12-C2-H001
  revert hvalid
  induction k with
  | zero =>
      intro _ i j
      simp [p12RoundedPowerSteps, p12PowerSteps, p12Gamma]
  | succ k ih =>
      intro hvalid i j
      have hlen : n ≤ (k + 1) * n := by
        simp only [Nat.succ_mul]
        omega
      have hleprev : k * n ≤ (k + 1) * n := by
        simp only [Nat.succ_mul]
        omega
      have hvalidFP : NumStability.gammaValid (p12AsFPModel fp) ((k + 1) * n) :=
        hvalid
      have hn : P12GammaValid fp.u n :=
        NumStability.gammaValid_mono (p12AsFPModel fp) hlen hvalidFP
      have hprev : P12GammaValid fp.u (k * n) :=
        NumStability.gammaValid_mono (p12AsFPModel fp) hleprev hvalidFP
      have hsum :
          p12Gamma fp.u n + p12Gamma fp.u (k * n) +
            p12Gamma fp.u n * p12Gamma fp.u (k * n) ≤
              p12Gamma fp.u ((k + 1) * n) := by
        have hs := NumStability.gamma_sum_le (p12AsFPModel fp)
          n (k * n) (by simpa [NumStability.gammaValid, p12AsFPModel,
            P12GammaValid, Nat.succ_mul, Nat.add_comm] using hvalid)
        change p12Gamma fp.u n + p12Gamma fp.u (k * n) +
          p12Gamma fp.u n * p12Gamma fp.u (k * n) ≤
            p12Gamma fp.u (n + k * n) at hs
        simpa [Nat.succ_mul, Nat.add_comm] using hs
      have hPnonneg :
          0 ≤ p12PowerSteps (p12AbsMatrix X) (k + 1) i j :=
        (abs_nonneg _).trans (p12_exact_power_abs n X (k + 1) i j)
      have hstep := p12_step_bound fp n
        (p12RoundedPowerSteps fp X k) (p12PowerSteps X k)
        (p12PowerSteps (p12AbsMatrix X) k) X
        (p12Gamma fp.u (k * n)) hn (ih hprev) (p12_exact_power_abs n X k) i j
      calc
        |p12RoundedPowerSteps fp X (k + 1) i j - p12PowerSteps X (k + 1) i j| =
          |p12RoundedMatMul fp (p12RoundedPowerSteps fp X k) X i j -
            p12MatMul (p12PowerSteps X k) X i j| := rfl
        _ ≤ (p12Gamma fp.u n + p12Gamma fp.u (k * n) +
              p12Gamma fp.u n * p12Gamma fp.u (k * n)) *
            p12MatMul (p12PowerSteps (p12AbsMatrix X) k) (p12AbsMatrix X) i j :=
          hstep
        _ ≤ p12Gamma fp.u ((k + 1) * n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by
          exact mul_le_mul_of_nonneg_right hsum hPnonneg

end VSCLReuse
