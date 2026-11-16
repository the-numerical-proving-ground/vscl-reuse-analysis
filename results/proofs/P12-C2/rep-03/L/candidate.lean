import VSCLReuse.P12.Definitions
import NumStability.Algorithms.MatMul
import Mathlib.Tactic

namespace VSCLReuse

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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p12GammaValid_mono (fp : P12FPModel) {a b : ℕ}
    (hab : a ≤ b) (hb : P12GammaValid fp.u b) :
    P12GammaValid fp.u a := by
  exact NumStability.gammaValid_mono (p12FPBridge fp) hab hb

private lemma p12Gamma_nonneg (fp : P12FPModel) {a : ℕ}
    (ha : P12GammaValid fp.u a) : 0 ≤ p12Gamma fp.u a := by
  exact NumStability.gamma_nonneg (p12FPBridge fp) ha

private lemma p12Gamma_sum_le (fp : P12FPModel) (a b : ℕ)
    (hab : P12GammaValid fp.u (a + b)) :
    p12Gamma fp.u a + p12Gamma fp.u b +
      p12Gamma fp.u a * p12Gamma fp.u b ≤ p12Gamma fp.u (a + b) := by
  exact NumStability.gamma_sum_le (p12FPBridge fp) a b hab

private lemma p12RoundedMatMul_error (fp : P12FPModel) (n : ℕ)
    (A B : P12Matrix n) (hn : P12GammaValid fp.u n) (i j : Fin n) :
    |p12RoundedMatMul fp A B i j - p12MatMul A B i j| ≤
      p12Gamma fp.u n * p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  exact NumStability.matMul_error_bound (p12FPBridge fp) n n n A B hn i j

private lemma p12MatMul_nonneg {n : ℕ} {A B : P12Matrix n}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i j : Fin n) :
    0 ≤ p12MatMul A B i j := by
  change 0 ≤ ∑ t : Fin n, A i t * B t j
  exact Finset.sum_nonneg (fun t _ => mul_nonneg (hA i t) (hB t j))

private lemma p12AbsMatMul_le {n : ℕ} (A B : P12Matrix n) (i j : Fin n) :
    |p12MatMul A B i j| ≤
      p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  change |∑ t : Fin n, A i t * B t j| ≤ ∑ t : Fin n, |A i t| * |B t j|
  calc
    |∑ t : Fin n, A i t * B t j| ≤ ∑ t : Fin n, |A i t * B t j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t : Fin n, |A i t| * |B t j| := by simp only [abs_mul]

private lemma p12AbsPower_le {n : ℕ} (X : P12Matrix n) :
    ∀ k i j, |p12PowerSteps X k i j| ≤
      p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      calc
        |p12PowerSteps X (k+1) i j| =
            |p12MatMul (p12PowerSteps X k) X i j| := rfl
        _ ≤ p12MatMul (p12AbsMatrix (p12PowerSteps X k))
              (p12AbsMatrix X) i j := p12AbsMatMul_le _ _ i j
        _ ≤ p12PowerSteps (p12AbsMatrix X) (k+1) i j := by
          change (∑ t : Fin n, |p12PowerSteps X k i t| * |X t j|) ≤
            ∑ t : Fin n, p12PowerSteps (p12AbsMatrix X) k i t * |X t j|
          exact Finset.sum_le_sum (fun t _ =>
            mul_le_mul_of_nonneg_right (ih i t) (abs_nonneg _))

private lemma p12AbsPower_nonneg {n : ℕ} (X : P12Matrix n) :
    ∀ k i j, 0 ≤ p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      exact p12MatMul_nonneg (ih) (fun a b => abs_nonneg _) i j

private lemma p12MatMul_sub_le {n : ℕ} (A C B : P12Matrix n) (i j : Fin n) :
    |p12MatMul A B i j - p12MatMul C B i j| ≤
      ∑ t : Fin n, |A i t - C i t| * |B t j| := by
  change |(∑ t : Fin n, A i t * B t j) -
      (∑ t : Fin n, C i t * B t j)| ≤ _
  rw [← Finset.sum_sub_distrib]
  have heq :
      (∑ t : Fin n, (A i t * B t j - C i t * B t j)) =
        ∑ t : Fin n, (A i t - C i t) * B t j := by
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [heq]
  calc
    |∑ t : Fin n, (A i t - C i t) * B t j| ≤
        ∑ t : Fin n, |(A i t - C i t) * B t j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t : Fin n, |A i t - C i t| * |B t j| := by simp only [abs_mul]

private theorem p12BoundAux (fp : P12FPModel) (n : ℕ) (X : P12Matrix n) :
    ∀ k, P12GammaValid fp.u (k * n) → ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        p12Gamma fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro _ i j
      simp [p12RoundedPowerSteps, p12PowerSteps, p12Gamma]
  | succ k ih =>
      intro hvalid i j
      have hvalid' : P12GammaValid fp.u (k * n + n) := by
        simpa only [Nat.succ_mul] using hvalid
      have hprev : P12GammaValid fp.u (k * n) :=
        p12GammaValid_mono fp (by omega) hvalid'
      have hn : P12GammaValid fp.u n :=
        p12GammaValid_mono fp (by omega) hvalid'
      have hγn : 0 ≤ p12Gamma fp.u n := p12Gamma_nonneg fp hn
      let R := p12RoundedPowerSteps fp X k
      let P := p12PowerSteps X k
      let Q := p12PowerSteps (p12AbsMatrix X) k
      let M := p12MatMul Q (p12AbsMatrix X) i j
      have hM : 0 ≤ M := p12AbsPower_nonneg X (k+1) i j
      have hsize (a b : Fin n) :
          |R a b| ≤ (1 + p12Gamma fp.u (k * n)) * Q a b := by
        have herr := ih hprev a b
        have hp := p12AbsPower_le X k a b
        calc
          |R a b| = |(R a b - P a b) + P a b| := by congr 1; ring
          _ ≤ |R a b - P a b| + |P a b| := abs_add_le _ _
          _ ≤ p12Gamma fp.u (k * n) * Q a b + Q a b :=
            add_le_add herr hp
          _ = (1 + p12Gamma fp.u (k * n)) * Q a b := by ring
      have hlocal :
          |p12RoundedMatMul fp R X i j - p12MatMul R X i j| ≤
            p12Gamma fp.u n * ((1 + p12Gamma fp.u (k * n)) * M) := by
        apply le_trans (p12RoundedMatMul_error fp n R X hn i j)
        apply mul_le_mul_of_nonneg_left _ hγn
        change (∑ t : Fin n, |R i t| * |X t j|) ≤
          (1 + p12Gamma fp.u (k * n)) *
            (∑ t : Fin n, Q i t * |X t j|)
        calc
          (∑ t : Fin n, |R i t| * |X t j|) ≤
              ∑ t : Fin n, ((1 + p12Gamma fp.u (k * n)) * Q i t) * |X t j| :=
            Finset.sum_le_sum (fun t _ =>
              mul_le_mul_of_nonneg_right (hsize i t) (abs_nonneg _))
          _ = (1 + p12Gamma fp.u (k * n)) *
                (∑ t : Fin n, Q i t * |X t j|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
      have hdiff :
          |p12MatMul R X i j - p12MatMul P X i j| ≤
            p12Gamma fp.u (k * n) * M := by
        calc
          |p12MatMul R X i j - p12MatMul P X i j| ≤
              ∑ t : Fin n, |R i t - P i t| * |X t j| :=
            p12MatMul_sub_le R P X i j
          _ ≤ ∑ t : Fin n,
                (p12Gamma fp.u (k * n) * Q i t) * |X t j| :=
            Finset.sum_le_sum (fun t _ =>
              mul_le_mul_of_nonneg_right (ih hprev i t) (abs_nonneg _))
          _ = p12Gamma fp.u (k * n) * M := by
            change (∑ t : Fin n,
              (p12Gamma fp.u (k * n) * Q i t) * |X t j|) =
                p12Gamma fp.u (k * n) *
                  (∑ t : Fin n, Q i t * |X t j|)
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
      have hsum :
          p12Gamma fp.u (k * n) + p12Gamma fp.u n +
            p12Gamma fp.u (k * n) * p12Gamma fp.u n ≤
              p12Gamma fp.u ((k+1)*n) := by
        simpa only [Nat.succ_mul] using
          p12Gamma_sum_le fp (k*n) n hvalid'
      calc
        |p12RoundedPowerSteps fp X (k+1) i j -
            p12PowerSteps X (k+1) i j| =
            |(p12RoundedMatMul fp R X i j - p12MatMul R X i j) +
              (p12MatMul R X i j - p12MatMul P X i j)| := by
          dsimp [R, P]
          simp only [p12RoundedPowerSteps, p12PowerSteps]
          congr 1
          ring
        _ ≤ |p12RoundedMatMul fp R X i j - p12MatMul R X i j| +
              |p12MatMul R X i j - p12MatMul P X i j| := abs_add_le _ _
        _ ≤ p12Gamma fp.u n * ((1 + p12Gamma fp.u (k * n)) * M) +
              p12Gamma fp.u (k * n) * M := add_le_add hlocal hdiff
        _ = (p12Gamma fp.u (k * n) + p12Gamma fp.u n +
              p12Gamma fp.u (k * n) * p12Gamma fp.u n) * M := by ring
        _ ≤ p12Gamma fp.u ((k+1)*n) * M :=
          mul_le_mul_of_nonneg_right hsum hM
        _ = p12Gamma fp.u ((k+1)*n) *
              p12PowerSteps (p12AbsMatrix X) (k+1) i j := rfl

/-- P12-C2: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p12_c2_lemma_2_2
    (fp : P12FPModel) (n k : ℕ) (X : P12Matrix n)
    (hvalid : P12GammaValid fp.u (k * n)) :
    ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        p12Gamma fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  -- PROOF_START P12-C2-H001
  exact p12BoundAux fp n X k hvalid

end VSCLReuse
