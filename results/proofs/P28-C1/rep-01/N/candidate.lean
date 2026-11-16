import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p28_c_mul_rho (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.c k * run.rho k = run.alphaBar k := by
  rw [run.c_eq k hk]
  exact div_mul_cancel₀ _ (run.rho_ne k hk)

private theorem p28_cBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.cBar k * run.rhoBar k = run.cBar (k - 1) * run.rho k := by
  rw [run.cBar_eq k hk]
  exact div_mul_cancel₀ _ (run.rhoBar_ne k hk)

private theorem p28_sBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.sBar k * run.rhoBar k = run.theta (k + 1) := by
  rw [run.sBar_eq k hk]
  exact div_mul_cancel₀ _ (run.rhoBar_ne k hk)

private theorem p28_bar_cross (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.cBar k * run.theta (k + 1) =
      run.cBar (k - 1) * run.rho k * run.sBar k := by
  apply mul_right_cancel₀ (run.rhoBar_ne k hk)
  rw [← p28_sBar_mul_rhoBar run k hk]
  rw [← p28_cBar_mul_rhoBar run k hk]
  ring

private theorem p28_product_step (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.s k * run.c (k + 1) * run.cBar k * run.rho (k + 1) =
      run.c k * run.cBar (k - 1) * run.rho k * run.sBar k := by
  have hcr := p28_c_mul_rho run (k + 1) (by omega)
  have hs := run.theta_succ k hk
  have ha := run.alphaBar_succ k hk
  have hcross := p28_bar_cross run k hk
  calc
    run.s k * run.c (k + 1) * run.cBar k * run.rho (k + 1)
        = run.s k * run.alphaBar (k + 1) * run.cBar k := by rw [← hcr]; ring
    _ = run.c k * (run.cBar k * run.theta (k + 1)) := by rw [ha, hs]; ring
    _ = run.c k * (run.cBar (k - 1) * run.rho k * run.sBar k) := by rw [hcross]
    _ = _ := by ring

private theorem p28_product (run : P28Lemma31Run) (n : ℕ) :
    p28PrefixProduct run.s n * run.c (n + 1) * run.cBar n *
      run.rho (n + 1) =
    p28PrefixProduct run.sBar n * run.alpha 1 := by
  induction n with
  | zero =>
      simpa [run.cBar_zero, run.alphaBar_one] using p28_c_mul_rho run 1 (by omega)
  | succ n ih =>
      have hstep := p28_product_step run (n + 1) (by omega)
      rw [p28PrefixProduct_succ, p28PrefixProduct_succ]
      calc
        (p28PrefixProduct run.s n * run.s (n + 1)) *
              run.c (n + 1 + 1) * run.cBar (n + 1) * run.rho (n + 1 + 1)
            = p28PrefixProduct run.s n *
                (run.s (n + 1) * run.c (n + 1 + 1) *
                  run.cBar (n + 1) * run.rho (n + 1 + 1)) := by ring
        _ = p28PrefixProduct run.s n *
              (run.c (n + 1) * run.cBar n * run.rho (n + 1) *
                run.sBar (n + 1)) := by simpa using congrArg (p28PrefixProduct run.s n * ·) (by simpa using hstep)
        _ = (p28PrefixProduct run.sBar n * run.alpha 1) *
              run.sBar (n + 1) := by rw [← ih]; ring
        _ = (p28PrefixProduct run.sBar n * run.sBar (n + 1)) *
              run.alpha 1 := by ring

private theorem p28_sc (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.s k * run.c (k + 1) * run.rho (k + 1) =
      run.c k * run.theta (k + 1) := by
  rw [mul_assoc, p28_c_mul_rho run (k + 1) (by omega)]
  rw [run.alphaBar_succ k hk, run.theta_succ k hk]
  ring

private theorem p28_local_balance (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoBar k * run.c k =
      run.thetaBar (k + 1) * run.s k * run.c (k + 1) +
      run.cBar k * run.cBar (k - 1) * run.rho k * run.c k := by
  have hb := p28_cBar_mul_rhoBar run k hk
  have hs := p28_sBar_mul_rhoBar run k hk
  have hsc := p28_sc run k hk
  have hsq := run.rhoBar_sq k hk
  have ht := run.thetaBar_eq (k + 1) (by omega)
  have hfirst :
      (run.thetaBar (k + 1) * run.s k * run.c (k + 1)) *
          run.rhoBar k = run.c k * run.theta (k + 1) ^ 2 := by
    rw [ht]
    calc
      (run.sBar k * run.rho (k + 1) * run.s k * run.c (k + 1)) *
          run.rhoBar k
          = (run.s k * run.c (k + 1) * run.rho (k + 1)) *
              (run.sBar k * run.rhoBar k) := by ring
      _ = run.c k * run.theta (k + 1) ^ 2 := by rw [hsc, hs]; ring
  have hsecond :
      (run.cBar k * run.cBar (k - 1) * run.rho k * run.c k) *
          run.rhoBar k =
        run.c k * (run.cBar (k - 1) * run.rho k) ^ 2 := by
    rw [show (run.cBar k * run.cBar (k - 1) * run.rho k * run.c k) *
        run.rhoBar k =
        (run.cBar k * run.rhoBar k) * run.cBar (k - 1) *
          run.rho k * run.c k by ring, hb]
    ring
  apply mul_right_cancel₀ (run.rhoBar_ne k hk)
  rw [add_mul, hfirst, hsecond]
  calc
    run.rhoBar k * run.c k * run.rhoBar k =
        run.c k * run.rhoBar k ^ 2 := by ring
    _ = run.c k * ((run.cBar (k - 1) * run.rho k) ^ 2 +
          run.theta (k + 1) ^ 2) := by rw [hsq]
    _ = run.c k * run.theta (k + 1) ^ 2 +
          run.c k * (run.cBar (k - 1) * run.rho k) ^ 2 := by ring

private noncomputable def p28_A (run : P28Lemma31Run) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * p28PrefixProduct run.s n * run.c (n + 1) * run.betaOne

private noncomputable def p28_B (run : P28Lemma31Run) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 2) * p28PrefixProduct run.sBar n *
    run.cBar (n + 1) * run.betaBarOne

private theorem p28_A_step (run : P28Lemma31Run) (n : ℕ) :
    p28_A run (n + 1) =
      -((-1 : ℝ) ^ n * p28PrefixProduct run.s n *
        run.s (n + 1) * run.c (n + 2) * run.betaOne) := by
  simp only [p28_A, p28PrefixProduct_succ, pow_succ]
  ring

private theorem p28_rhs_rotation_unsigned (run : P28Lemma31Run) (n : ℕ) :
    p28PrefixProduct run.sBar n * run.cBar (n + 1) * run.betaBarOne =
      (run.rhoBar (n + 1) * p28PrefixProduct run.s n * run.c (n + 1) -
        run.thetaBar (n + 2) * p28PrefixProduct run.s (n + 1) *
          run.c (n + 2)) * run.betaOne := by
  have hp := p28_product run n
  have hl := p28_local_balance run (n + 1) (by omega)
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hl
  calc
    p28PrefixProduct run.sBar n * run.cBar (n + 1) * run.betaBarOne =
        (p28PrefixProduct run.s n * run.c (n + 1) *
          run.cBar n * run.rho (n + 1)) * run.cBar (n + 1) *
          run.betaOne := by rw [hp, run.betaBarOne_eq]; ring
    _ = (run.rhoBar (n + 1) * p28PrefixProduct run.s n * run.c (n + 1) -
          run.thetaBar (n + 2) * p28PrefixProduct run.s (n + 1) *
            run.c (n + 2)) * run.betaOne := by
      rw [p28PrefixProduct_succ]
      linear_combination -(p28PrefixProduct run.s n * run.betaOne) * hl

private theorem p28_rhs_rotation (run : P28Lemma31Run) (n : ℕ) :
    p28_B run n =
      run.rhoBar (n + 1) * p28_A run n +
        run.thetaBar (n + 2) * p28_A run (n + 1) := by
  have h := p28_rhs_rotation_unsigned run n
  have hp : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
    simp [pow_add]
  rw [p28_B, hp, p28_A, p28_A_step]
  rw [p28PrefixProduct_succ] at h
  linear_combination ((-1 : ℝ) ^ n) * h

private theorem p28_cTilde_mul_rhoTilde (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoTilde k * run.cTilde k = run.rhoDot k := by
  rw [run.cTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private theorem p28_sTilde_mul_rhoTilde (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoTilde k * run.sTilde k = run.thetaBar (k + 1) := by
  rw [run.sTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private theorem p28_tilde_norm (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.cTilde k ^ 2 + run.sTilde k ^ 2 = 1 := by
  rw [run.cTilde_eq k hk, run.sTilde_eq k hk]
  have hsq := run.rhoTilde_sq k hk
  field_simp [run.rhoTilde_ne k hk]
  nlinarith

private theorem p28_beta_balance (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoTilde (k + 1) * run.betaTilde (k + 1) +
      run.thetaTilde (k + 1) * run.betaTilde k = p28_B run k := by
  have hb := p28_rhs_rotation run k
  have hbn : run.betaTilde k =
      run.cTilde k * run.betaDot k + run.sTilde k * p28_A run k := by
    simpa only [p28_A, mul_assoc] using run.betaTilde_eq k hk
  have hbnext : run.betaTilde (k + 1) =
      run.cTilde (k + 1) * run.betaDot (k + 1) +
        run.sTilde (k + 1) * p28_A run (k + 1) := by
    simpa only [p28_A, mul_assoc] using run.betaTilde_eq (k + 1) (by omega)
  have hdnext : run.betaDot (k + 1) =
      -run.sTilde k * run.betaDot k + run.cTilde k * p28_A run k := by
    simpa only [p28_A, mul_assoc] using run.betaDot_succ k hk
  have hct : run.rhoTilde (k + 1) * run.cTilde (k + 1) =
      run.cTilde k * run.rhoBar (k + 1) := by
    rw [p28_cTilde_mul_rhoTilde run (k + 1) (by omega),
      run.rhoDot_succ k hk]
  have hst := p28_sTilde_mul_rhoTilde run (k + 1) (by omega)
  have hnorm := p28_tilde_norm run k hk
  rw [hbnext, hbn, hdnext, run.thetaTilde_succ k hk, hb]
  linear_combination
    (-run.sTilde k * run.betaDot k + run.cTilde k * p28_A run k) * hct +
    (p28_A run (k + 1)) * hst +
    (run.rhoBar (k + 1) * p28_A run k) * hnorm

private theorem p28_base (run : P28Lemma31Run) :
    run.betaTilde 1 = run.tauTilde 1 := by
  have hbn : run.betaTilde 1 =
      run.cTilde 1 * run.betaDot 1 + run.sTilde 1 * p28_A run 1 := by
    simpa only [p28_A, mul_assoc] using run.betaTilde_eq 1 (by omega)
  have hA0 : p28_A run 0 = run.c 1 * run.betaOne := by
    simp [p28_A]
  have hB0 : p28_B run 0 = run.cBar 1 * run.betaBarOne := by
    simp [p28_B]
  have hrot := p28_rhs_rotation run 0
  rw [hB0, hA0] at hrot
  have hprod : run.rhoTilde 1 * run.betaTilde 1 =
      run.cBar 1 * run.betaBarOne := by
    rw [hbn, run.betaDot_one]
    calc
      run.rhoTilde 1 *
          (run.cTilde 1 * (run.c 1 * run.betaOne) +
            run.sTilde 1 * p28_A run 1) =
          (run.rhoTilde 1 * run.cTilde 1) *
            (run.c 1 * run.betaOne) +
          (run.rhoTilde 1 * run.sTilde 1) * p28_A run 1 := by ring
      _ = run.rhoBar 1 * (run.c 1 * run.betaOne) +
            run.thetaBar 2 * p28_A run 1 := by
          rw [p28_cTilde_mul_rhoTilde run 1 (by omega),
            p28_sTilde_mul_rhoTilde run 1 (by omega), run.rhoDot_one]
      _ = run.cBar 1 * run.betaBarOne := hrot.symm
  rw [run.tauTilde_one]
  apply (eq_div_iff (run.rhoTilde_ne 1 (by omega))).2
  calc
    run.betaTilde 1 * run.rhoTilde 1 =
        run.rhoTilde 1 * run.betaTilde 1 := by ring
    _ = run.cBar 1 * run.betaBarOne := hprod

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  have h : ∀ n : ℕ, run.betaTilde (n + 1) = run.tauTilde (n + 1) := by
    intro n
    induction n with
    | zero => simpa using p28_base run
    | succ n ih =>
        have hn : 1 ≤ n + 1 := by omega
        have hbalance := p28_beta_balance run (n + 1) hn
        rw [run.tauTilde_succ (n + 1) hn, ← ih]
        change run.betaTilde (n + 1 + 1) =
          (p28_B run (n + 1) -
            run.thetaTilde (n + 1 + 1) * run.betaTilde (n + 1)) /
            run.rhoTilde (n + 1 + 1)
        apply (eq_div_iff (run.rhoTilde_ne (n + 1 + 1) (by omega))).2
        linear_combination hbalance
  simpa only [Nat.sub_add_cancel hk] using h (k - 1)

end VSCLReuse
