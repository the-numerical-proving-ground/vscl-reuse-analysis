import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p28_product_identity (run : P28Lemma31Run) (k : ℕ) :
    p28PrefixProduct run.s k * run.cBar k * run.alphaBar (k + 1) =
      p28PrefixProduct run.sBar k * run.alpha 1 := by
  induction k with
  | zero =>
      simp [run.cBar_zero, run.alphaBar_one]
  | succ k ih =>
      have hk : 1 ≤ k + 1 := by omega
      have hstep :
          run.s (k + 1) * run.cBar (k + 1) * run.alphaBar (k + 2) =
            run.cBar k * run.alphaBar (k + 1) * run.sBar (k + 1) := by
        rw [run.alphaBar_succ (k + 1) hk,
            run.cBar_eq (k + 1) hk,
            run.sBar_eq (k + 1) hk,
            run.theta_succ (k + 1) hk,
            run.c_eq (k + 1) hk]
        simp only [Nat.add_sub_cancel_right]
        field_simp [run.rho_ne (k + 1) hk, run.rhoBar_ne (k + 1) hk]
      rw [p28PrefixProduct_succ, p28PrefixProduct_succ]
      calc
        p28PrefixProduct run.s k * run.s (k + 1) *
            run.cBar (k + 1) * run.alphaBar (k + 2) =
          p28PrefixProduct run.s k *
            (run.s (k + 1) * run.cBar (k + 1) * run.alphaBar (k + 2)) := by ring
        _ = p28PrefixProduct run.s k *
            (run.cBar k * run.alphaBar (k + 1) * run.sBar (k + 1)) := by rw [hstep]
        _ = p28PrefixProduct run.sBar k * run.sBar (k + 1) * run.alpha 1 := by
          calc
            _ = (p28PrefixProduct run.s k * run.cBar k *
              run.alphaBar (k + 1)) * run.sBar (k + 1) := by ring
            _ = _ := by rw [ih]; ring

private theorem p28_tilde_rotation_sq (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) : run.cTilde k ^ 2 + run.sTilde k ^ 2 = 1 := by
  rw [run.cTilde_eq k hk, run.sTilde_eq k hk]
  have hr := run.rhoTilde_sq k hk
  field_simp [run.rhoTilde_ne k hk]
  nlinarith

private theorem p28_middle_rotation_identity (run : P28Lemma31Run) (i : ℕ)
    (hi : 1 ≤ i) :
    run.rhoBar i * run.c i -
        run.thetaBar (i + 1) * run.s i * run.c (i + 1) =
      run.cBar i * run.cBar (i - 1) * run.alphaBar i := by
  have hip : 1 ≤ i + 1 := by omega
  have hρ := run.rho_ne i hi
  have hρp := run.rho_ne (i + 1) hip
  have hρb := run.rhoBar_ne i hi
  have hsq := run.rhoBar_sq i hi
  have hθ := run.theta_succ i hi
  rw [run.thetaBar_eq (i + 1) hip]
  simp only [Nat.add_sub_cancel_right]
  rw [run.sBar_eq i hi,
      run.c_eq (i + 1) hip,
      run.alphaBar_succ i hi,
      run.cBar_eq i hi,
      run.c_eq i hi]
  rw [hθ] at hsq ⊢
  field_simp [hρ, hρp, hρb]
  rw [hsq]
  ring

private theorem p28_source_identity (run : P28Lemma31Run) (k : ℕ) :
    (-1 : ℝ) ^ (k + 2) * p28PrefixProduct run.sBar k *
        run.cBar (k + 1) * run.betaBarOne =
      (-1 : ℝ) ^ k * p28PrefixProduct run.s k *
        (run.rhoBar (k + 1) * run.c (k + 1) -
          run.thetaBar (k + 2) * run.s (k + 1) * run.c (k + 2)) *
        run.betaOne := by
  have hk : 1 ≤ k + 1 := by omega
  have hsign : (-1 : ℝ) ^ (k + 2) = (-1 : ℝ) ^ k := by
    simp [pow_add]
  rw [hsign, run.betaBarOne_eq,
      p28_middle_rotation_identity run (k + 1) hk]
  simp only [Nat.add_sub_cancel_right]
  calc
    (-1 : ℝ) ^ k * p28PrefixProduct run.sBar k *
        run.cBar (k + 1) * (run.alpha 1 * run.betaOne) =
      (-1 : ℝ) ^ k *
        (p28PrefixProduct run.sBar k * run.alpha 1) *
        run.cBar (k + 1) * run.betaOne := by ring
    _ = (-1 : ℝ) ^ k *
        (p28PrefixProduct run.s k * run.cBar k *
          run.alphaBar (k + 1)) * run.cBar (k + 1) * run.betaOne := by
      rw [p28_product_identity run k]
    _ = _ := by ring

private theorem p28_transformed_recurrence (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoTilde (k + 1) * run.betaTilde (k + 1) +
        run.thetaTilde (k + 1) * run.betaTilde k =
      (-1 : ℝ) ^ (k + 2) * p28PrefixProduct run.sBar k *
        run.cBar (k + 1) * run.betaBarOne := by
  have hkp : 1 ≤ k + 1 := by omega
  have hct : run.rhoTilde (k + 1) * run.cTilde (k + 1) =
      run.cTilde k * run.rhoBar (k + 1) := by
    rw [run.cTilde_eq (k + 1) hkp, run.rhoDot_succ k hk]
    field_simp [run.rhoTilde_ne (k + 1) hkp]
  have hst : run.rhoTilde (k + 1) * run.sTilde (k + 1) =
      run.thetaBar (k + 2) := by
    rw [run.sTilde_eq (k + 1) hkp]
    field_simp [run.rhoTilde_ne (k + 1) hkp]
  have hs := p28_tilde_rotation_sq run k hk
  have hsign : (-1 : ℝ) ^ (k + 1) = -(-1 : ℝ) ^ k := by
    simp [pow_succ]
  rw [p28_source_identity run k]
  rw [run.betaTilde_eq (k + 1) hkp,
      run.betaDot_succ k hk,
      run.betaTilde_eq k hk,
      run.thetaTilde_succ k hk,
      p28PrefixProduct_succ, hsign]
  calc
    run.rhoTilde (k + 1) *
          (run.cTilde (k + 1) *
              (-run.sTilde k * run.betaDot k +
                run.cTilde k * (-1 : ℝ) ^ k *
                  p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) +
            run.sTilde (k + 1) * -(-1 : ℝ) ^ k *
              (p28PrefixProduct run.s k * run.s (k + 1)) *
              run.c (k + 2) * run.betaOne) +
        run.sTilde k * run.rhoBar (k + 1) *
          (run.cTilde k * run.betaDot k +
            run.sTilde k * (-1 : ℝ) ^ k *
              p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) =
      (run.rhoTilde (k + 1) * run.cTilde (k + 1)) *
          (-run.sTilde k * run.betaDot k +
            run.cTilde k * (-1 : ℝ) ^ k *
              p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) +
        (run.rhoTilde (k + 1) * run.sTilde (k + 1)) *
          (-(-1 : ℝ) ^ k * p28PrefixProduct run.s k *
            run.s (k + 1) * run.c (k + 2) * run.betaOne) +
        run.sTilde k * run.rhoBar (k + 1) *
          (run.cTilde k * run.betaDot k +
            run.sTilde k * (-1 : ℝ) ^ k *
              p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) := by ring
    _ = (-1 : ℝ) ^ k * p28PrefixProduct run.s k *
        (run.rhoBar (k + 1) * run.c (k + 1) -
          run.thetaBar (k + 2) * run.s (k + 1) * run.c (k + 2)) *
        run.betaOne := by
      rw [hct, hst]
      linear_combination
        (run.rhoBar (k + 1) * (-1 : ℝ) ^ k *
          p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) * hs

private theorem p28_transformed_one (run : P28Lemma31Run) :
    run.betaTilde 1 = run.tauTilde 1 := by
  have h1 : 1 ≤ (1 : ℕ) := by omega
  have hct : run.rhoTilde 1 * run.cTilde 1 = run.rhoBar 1 := by
    rw [run.cTilde_eq 1 h1, run.rhoDot_one]
    field_simp [run.rhoTilde_ne 1 h1]
  have hst : run.rhoTilde 1 * run.sTilde 1 = run.thetaBar 2 := by
    rw [run.sTilde_eq 1 h1]
    field_simp [run.rhoTilde_ne 1 h1]
  have hsource :
      run.cBar 1 * run.betaBarOne =
        (run.rhoBar 1 * run.c 1 -
          run.thetaBar 2 * run.s 1 * run.c 2) * run.betaOne := by
    simpa [p28PrefixProduct_succ] using p28_source_identity run 0
  have hmul : run.rhoTilde 1 * run.betaTilde 1 =
      run.cBar 1 * run.betaBarOne := by
    rw [run.betaTilde_eq 1 h1, run.betaDot_one]
    simp only [p28PrefixProduct_succ, p28PrefixProduct_zero]
    norm_num
    calc
      run.rhoTilde 1 *
          (run.cTilde 1 * (run.c 1 * run.betaOne) -
            run.sTilde 1 * run.s 1 * run.c 2 * run.betaOne) =
        (run.rhoTilde 1 * run.cTilde 1) * run.c 1 * run.betaOne -
          (run.rhoTilde 1 * run.sTilde 1) * run.s 1 * run.c 2 * run.betaOne := by ring
      _ = run.cBar 1 * run.betaBarOne := by
        rw [hct, hst]
        rw [hsource]
        ring
  rw [run.tauTilde_one]
  apply (eq_div_iff (run.rhoTilde_ne 1 h1)).2
  simpa [mul_comm] using hmul

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  induction k, hk using Nat.le_induction with
  | base => exact p28_transformed_one run
  | succ k hk ih =>
      have hkp : 1 ≤ k + 1 := by omega
      rw [run.tauTilde_succ k hk, ← ih]
      apply (eq_div_iff (run.rhoTilde_ne (k + 1) hkp)).2
      linear_combination p28_transformed_recurrence run k hk

end VSCLReuse
