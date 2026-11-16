import VSCLReuse.P12.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p12FPBridge (fp : P12FPModel) : NumStability.FPModel where
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

private lemma p12_dot_bound (fp : P12FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P12GammaValid fp.u n) :
    |p12RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p12Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  simpa [p12RoundedDotProduct, NumStability.fl_dotProduct,
    p12FPBridge, P12GammaValid, NumStability.gammaValid,
    p12Gamma, NumStability.gamma] using
    (NumStability.dotProduct_error_bound (p12FPBridge fp) n x y hn)

private lemma p12_gamma_nonneg (fp : P12FPModel) (m : ℕ)
    (hm : P12GammaValid fp.u m) : 0 ≤ p12Gamma fp.u m := by
  simpa [p12FPBridge, P12GammaValid, NumStability.gammaValid,
    p12Gamma, NumStability.gamma] using
    (NumStability.gamma_nonneg (p12FPBridge fp) hm)

private lemma p12_gamma_sum (fp : P12FPModel) (a b : ℕ)
    (hab : P12GammaValid fp.u (a + b)) :
    p12Gamma fp.u a + p12Gamma fp.u b +
      p12Gamma fp.u a * p12Gamma fp.u b ≤ p12Gamma fp.u (a + b) := by
  simpa [p12FPBridge, P12GammaValid, NumStability.gammaValid,
    p12Gamma, NumStability.gamma] using
    (NumStability.gamma_sum_le (p12FPBridge fp) a b hab)

private lemma p12_valid_mono (fp : P12FPModel) {a b : ℕ}
    (hab : a ≤ b) (hb : P12GammaValid fp.u b) :
    P12GammaValid fp.u a := by
  unfold P12GammaValid at *
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) fp.u_nonneg) hb

private lemma p12_power_abs (n : ℕ) (X : P12Matrix n) :
    ∀ k i j, |p12PowerSteps X k i j| ≤
      p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      change |∑ l : Fin n, p12PowerSteps X k i l * X l j| ≤
        ∑ l : Fin n, p12PowerSteps (p12AbsMatrix X) k i l * |X l j|
      calc
        |∑ l : Fin n, p12PowerSteps X k i l * X l j|
            ≤ ∑ l : Fin n, |p12PowerSteps X k i l * X l j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l : Fin n, |p12PowerSteps X k i l| * |X l j| := by
              apply Finset.sum_congr rfl
              intro l _
              rw [abs_mul]
        _ ≤ ∑ l : Fin n, p12PowerSteps (p12AbsMatrix X) k i l * |X l j| := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)

private lemma p12_abs_power_nonneg (n : ℕ) (X : P12Matrix n)
    (k : ℕ) (i j : Fin n) :
    0 ≤ p12PowerSteps (p12AbsMatrix X) k i j :=
  le_trans (abs_nonneg _) (p12_power_abs n X k i j)

private lemma p12_matMul_diff_bound {n : ℕ}
    (A B C X : P12Matrix n) (c : ℝ)
    (hAB : ∀ i l, |A i l - B i l| ≤ c * C i l) (i j : Fin n) :
    |p12MatMul A X i j - p12MatMul B X i j| ≤
      c * p12MatMul C (p12AbsMatrix X) i j := by
  have heq : p12MatMul A X i j - p12MatMul B X i j =
      ∑ l : Fin n, (A i l - B i l) * X l j := by
    simp only [p12MatMul, ← Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  calc
    |∑ l : Fin n, (A i l - B i l) * X l j|
        ≤ ∑ l : Fin n, |(A i l - B i l) * X l j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin n, (c * C i l) * |X l j| := by
          apply Finset.sum_le_sum
          intro l _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hAB i l) (abs_nonneg _)
    _ = c * p12MatMul C (p12AbsMatrix X) i j := by
          simp only [p12MatMul, p12AbsMatrix, Finset.mul_sum, mul_assoc]

private lemma p12_matMul_abs_bound {n : ℕ}
    (A C X : P12Matrix n) (c : ℝ)
    (hAC : ∀ i l, |A i l| ≤ c * C i l) (i j : Fin n) :
    p12MatMul (p12AbsMatrix A) (p12AbsMatrix X) i j ≤
      c * p12MatMul C (p12AbsMatrix X) i j := by
  change (∑ l : Fin n, |A i l| * |X l j|) ≤
    c * ∑ l : Fin n, C i l * |X l j|
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  calc
    |A i l| * |X l j| ≤ (c * C i l) * |X l j| :=
      mul_le_mul_of_nonneg_right (hAC i l) (abs_nonneg _)
    _ = c * (C i l * |X l j|) := by ring

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
      intro hvalid
      have hkn : P12GammaValid fp.u (k * n) :=
        p12_valid_mono fp
          (by simpa only [Nat.succ_mul, one_mul] using (Nat.le_add_right (k * n) n)) hvalid
      have hn : P12GammaValid fp.u n :=
        p12_valid_mono fp
          (by simpa only [Nat.succ_mul, one_mul] using (Nat.le_add_left n (k * n))) hvalid
      have hsumvalid : P12GammaValid fp.u (k * n + n) := by
        simpa [Nat.succ_mul] using hvalid
      have hgamma_n : 0 ≤ p12Gamma fp.u n := p12_gamma_nonneg fp n hn
      have hgamma_sum := p12_gamma_sum fp (k * n) n hsumvalid
      have hA : ∀ i l,
          |p12RoundedPowerSteps fp X k i l| ≤
            (1 + p12Gamma fp.u (k * n)) *
              p12PowerSteps (p12AbsMatrix X) k i l := by
        intro i l
        calc
          |p12RoundedPowerSteps fp X k i l| =
              |(p12RoundedPowerSteps fp X k i l - p12PowerSteps X k i l) +
                p12PowerSteps X k i l| := by congr 1; ring
          _ ≤ |p12RoundedPowerSteps fp X k i l - p12PowerSteps X k i l| +
                |p12PowerSteps X k i l| := abs_add_le _ _
          _ ≤ p12Gamma fp.u (k * n) *
                p12PowerSteps (p12AbsMatrix X) k i l +
                p12PowerSteps (p12AbsMatrix X) k i l :=
              add_le_add (ih hkn i l) (p12_power_abs n X k i l)
          _ = (1 + p12Gamma fp.u (k * n)) *
                p12PowerSteps (p12AbsMatrix X) k i l := by ring
      intro i j
      have hround :
          |p12RoundedPowerSteps fp X (k + 1) i j -
            p12MatMul (p12RoundedPowerSteps fp X k) X i j| ≤
            p12Gamma fp.u n *
              p12MatMul (p12AbsMatrix (p12RoundedPowerSteps fp X k))
                (p12AbsMatrix X) i j := by
        simpa only [p12RoundedPowerSteps, p12RoundedMatMul,
          p12MatMul, p12AbsMatrix] using
          p12_dot_bound fp n (p12RoundedPowerSteps fp X k i)
            (fun l => X l j) hn
      have hlocal :
          |p12RoundedPowerSteps fp X (k + 1) i j -
            p12MatMul (p12RoundedPowerSteps fp X k) X i j| ≤
            p12Gamma fp.u n *
              ((1 + p12Gamma fp.u (k * n)) *
                p12PowerSteps (p12AbsMatrix X) (k + 1) i j) := by
        apply le_trans hround
        apply mul_le_mul_of_nonneg_left _ hgamma_n
        simpa only [p12PowerSteps] using
          p12_matMul_abs_bound (p12RoundedPowerSteps fp X k)
            (p12PowerSteps (p12AbsMatrix X) k) X
            (1 + p12Gamma fp.u (k * n)) hA i j
      have hprop :
          |p12MatMul (p12RoundedPowerSteps fp X k) X i j -
            p12PowerSteps X (k + 1) i j| ≤
            p12Gamma fp.u (k * n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by
        simpa only [p12PowerSteps] using
          p12_matMul_diff_bound (p12RoundedPowerSteps fp X k)
            (p12PowerSteps X k) (p12PowerSteps (p12AbsMatrix X) k)
            X (p12Gamma fp.u (k * n)) (ih hkn) i j
      calc
        |p12RoundedPowerSteps fp X (k + 1) i j -
            p12PowerSteps X (k + 1) i j| =
          |(p12RoundedPowerSteps fp X (k + 1) i j -
              p12MatMul (p12RoundedPowerSteps fp X k) X i j) +
            (p12MatMul (p12RoundedPowerSteps fp X k) X i j -
              p12PowerSteps X (k + 1) i j)| := by congr 1; ring
        _ ≤ |p12RoundedPowerSteps fp X (k + 1) i j -
              p12MatMul (p12RoundedPowerSteps fp X k) X i j| +
            |p12MatMul (p12RoundedPowerSteps fp X k) X i j -
              p12PowerSteps X (k + 1) i j| := abs_add_le _ _
        _ ≤ p12Gamma fp.u n *
              ((1 + p12Gamma fp.u (k * n)) *
                p12PowerSteps (p12AbsMatrix X) (k + 1) i j) +
            p12Gamma fp.u (k * n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j :=
            add_le_add hlocal hprop
        _ = (p12Gamma fp.u (k * n) + p12Gamma fp.u n +
              p12Gamma fp.u (k * n) * p12Gamma fp.u n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by ring
        _ ≤ p12Gamma fp.u ((k + 1) * n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by
            apply mul_le_mul_of_nonneg_right _
              (p12_abs_power_nonneg n X (k + 1) i j)
            simpa [Nat.succ_mul] using hgamma_sum

end VSCLReuse
