import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private noncomputable def p28E (run : P28Lemma31Run) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne

private lemma p28_c_mul_rho (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.c k * run.rho k = run.alphaBar k := by
  rw [run.c_eq k hk]
  field_simp [run.rho_ne k hk]

private lemma p28_cBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.cBar k * run.rhoBar k = run.cBar (k - 1) * run.rho k := by
  rw [run.cBar_eq k hk]
  field_simp [run.rhoBar_ne k hk]

private lemma p28_sBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.sBar k * run.rhoBar k = run.theta (k + 1) := by
  rw [run.sBar_eq k hk]
  field_simp [run.rhoBar_ne k hk]

private lemma p28_cTilde_mul_rhoTilde (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.cTilde k * run.rhoTilde k = run.rhoDot k := by
  rw [run.cTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private lemma p28_sTilde_mul_rhoTilde (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.sTilde k * run.rhoTilde k = run.thetaBar (k + 1) := by
  rw [run.sTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private lemma p28_cTilde_sq_add_sTilde_sq (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) : run.cTilde k ^ 2 + run.sTilde k ^ 2 = 1 := by
  have hc := p28_cTilde_mul_rhoTilde run k hk
  have hs := p28_sTilde_mul_rhoTilde run k hk
  have hsq := run.rhoTilde_sq k hk
  have h : run.rhoTilde k ^ 2 *
      (run.cTilde k ^ 2 + run.sTilde k ^ 2) =
      run.rhoTilde k ^ 2 * 1 := by
    calc
      _ = (run.cTilde k * run.rhoTilde k) ^ 2 +
          (run.sTilde k * run.rhoTilde k) ^ 2 := by ring
      _ = run.rhoDot k ^ 2 + run.thetaBar (k + 1) ^ 2 := by rw [hc, hs]
      _ = run.rhoTilde k ^ 2 * 1 := by rw [hsq]; ring
  exact (mul_left_cancel₀ (pow_ne_zero 2 (run.rhoTilde_ne k hk)) h)

private lemma p28_cross (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.s k * run.alpha (k + 1) * run.cBar k =
      run.sBar k * run.cBar (k - 1) * run.rho k := by
  have hc := p28_cBar_mul_rhoBar run k hk
  have hs := p28_sBar_mul_rhoBar run k hk
  have ht := run.theta_succ k hk
  have h : run.rhoBar k *
      (run.s k * run.alpha (k + 1) * run.cBar k -
        run.sBar k * run.cBar (k - 1) * run.rho k) = 0 := by
    calc
      _ = (run.s k * run.alpha (k + 1)) *
            (run.cBar k * run.rhoBar k) -
          (run.sBar k * run.rhoBar k) *
            (run.cBar (k - 1) * run.rho k) := by ring
      _ = 0 := by rw [hc, hs, ← ht]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (run.rhoBar_ne k hk))

private lemma p28_product_invariant (run : P28Lemma31Run) (k : ℕ) :
    p28PrefixProduct run.s k * run.c (k + 1) *
        run.cBar k * run.rho (k + 1) =
      p28PrefixProduct run.sBar k * run.alpha 1 := by
  induction k with
  | zero =>
      simpa [p28PrefixProduct_zero, run.cBar_zero, run.alphaBar_one] using
        p28_c_mul_rho run 1 (by omega)
  | succ k ih =>
      have hk : 1 ≤ k + 1 := by omega
      have hcross := p28_cross run (k + 1) hk
      simp only [Nat.add_sub_cancel_right, Nat.add_assoc] at hcross
      calc
        p28PrefixProduct run.s (k + 1) * run.c (k + 2) *
            run.cBar (k + 1) * run.rho (k + 2) =
          p28PrefixProduct run.s k * run.s (k + 1) *
            (run.c (k + 2) * run.rho (k + 2)) * run.cBar (k + 1) := by
              rw [p28PrefixProduct_succ]
              ring
        _ =
          p28PrefixProduct run.s k * run.c (k + 1) *
            (run.s (k + 1) * run.alpha (k + 2) * run.cBar (k + 1)) := by
              rw [p28_c_mul_rho run (k + 2) (by omega),
                run.alphaBar_succ (k + 1) hk]
              ring
        _ = (p28PrefixProduct run.s k * run.c (k + 1) *
              run.cBar k * run.rho (k + 1)) * run.sBar (k + 1) := by
              rw [hcross]
              ring
        _ = p28PrefixProduct run.sBar (k + 1) * run.alpha 1 := by
              rw [ih, p28PrefixProduct_succ]
              ring

private lemma p28_bar_diff (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.rhoBar k - run.sBar k * run.theta (k + 1) =
      run.cBar k * run.cBar (k - 1) * run.rho k := by
  have hc := p28_cBar_mul_rhoBar run k hk
  have hs := p28_sBar_mul_rhoBar run k hk
  have hsq := run.rhoBar_sq k hk
  have h : run.rhoBar k *
      (run.rhoBar k - run.sBar k * run.theta (k + 1) -
        run.cBar k * run.cBar (k - 1) * run.rho k) = 0 := by
    calc
      _ = run.rhoBar k ^ 2 -
          (run.sBar k * run.rhoBar k) * run.theta (k + 1) -
          (run.cBar k * run.rhoBar k) *
            (run.cBar (k - 1) * run.rho k) := by ring
      _ = 0 := by rw [hc, hs, hsq]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (run.rhoBar_ne k hk))

private lemma p28_mix (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.rhoBar k * run.c k -
        run.thetaBar (k + 1) * run.s k * run.c (k + 1) =
      run.c k * run.cBar (k - 1) * run.rho k * run.cBar k := by
  have htb : run.thetaBar (k + 1) = run.sBar k * run.rho (k + 1) := by
    simpa using run.thetaBar_eq (k + 1) (by omega)
  have hterm : run.thetaBar (k + 1) * run.s k * run.c (k + 1) =
      run.sBar k * run.theta (k + 1) * run.c k := by
    calc
      _ = run.sBar k * run.s k *
          (run.c (k + 1) * run.rho (k + 1)) := by rw [htb]; ring
      _ = run.sBar k * run.s k *
          (run.c k * run.alpha (k + 1)) := by
            rw [p28_c_mul_rho run (k + 1) (by omega),
              run.alphaBar_succ k hk]
      _ = run.sBar k * run.theta (k + 1) * run.c k := by
            rw [run.theta_succ k hk]
            ring
  calc
    _ = (run.rhoBar k - run.sBar k * run.theta (k + 1)) * run.c k := by
      rw [hterm]; ring
    _ = run.c k * run.cBar (k - 1) * run.rho k * run.cBar k := by
      rw [p28_bar_diff run k hk]
      ring

private lemma p28_driving_identity (run : P28Lemma31Run) (k : ℕ) :
    run.rhoBar (k + 1) * p28E run k +
        run.thetaBar (k + 2) * p28E run (k + 1) =
      (-1 : ℝ) ^ (k + 2) * p28PrefixProduct run.sBar k *
        run.cBar (k + 1) * run.betaBarOne := by
  calc
    _ = (-1 : ℝ) ^ k * p28PrefixProduct run.s k * run.betaOne *
          (run.rhoBar (k + 1) * run.c (k + 1) -
            run.thetaBar (k + 2) * run.s (k + 1) * run.c (k + 2)) := by
          simp only [p28E, p28PrefixProduct_succ, pow_succ]
          ring
    _ = (-1 : ℝ) ^ k * p28PrefixProduct run.s k * run.betaOne *
          (run.c (k + 1) * run.cBar k * run.rho (k + 1) *
            run.cBar (k + 1)) := by
          simpa only [Nat.add_sub_cancel_right] using
            congrArg
              (fun x : ℝ => (-1 : ℝ) ^ k * p28PrefixProduct run.s k * run.betaOne * x)
              (p28_mix run (k + 1) (by omega))
    _ = (-1 : ℝ) ^ k *
          (p28PrefixProduct run.s k * run.c (k + 1) *
            run.cBar k * run.rho (k + 1)) *
          run.cBar (k + 1) * run.betaOne := by ring
    _ = (-1 : ℝ) ^ k * p28PrefixProduct run.sBar k *
          run.cBar (k + 1) * run.betaBarOne := by
          rw [p28_product_invariant run k, run.betaBarOne_eq]
          ring
    _ = (-1 : ℝ) ^ (k + 2) * p28PrefixProduct run.sBar k *
          run.cBar (k + 1) * run.betaBarOne := by
          rw [pow_succ, pow_succ]
          ring

private lemma p28_betaTilde_eq_E (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.betaTilde k = run.cTilde k * run.betaDot k + run.sTilde k * p28E run k := by
  rw [run.betaTilde_eq k hk]
  simp only [p28E]
  ring

private lemma p28_betaDot_succ_E (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.betaDot (k + 1) =
      -run.sTilde k * run.betaDot k + run.cTilde k * p28E run k := by
  rw [run.betaDot_succ k hk]
  simp only [p28E]
  ring

private lemma p28_betaTilde_recurrence (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.rhoTilde (k + 1) * run.betaTilde (k + 1) +
        run.thetaTilde (k + 1) * run.betaTilde k =
      run.rhoBar (k + 1) * p28E run k +
        run.thetaBar (k + 2) * p28E run (k + 1) := by
  calc
    _ = (run.cTilde (k + 1) * run.rhoTilde (k + 1)) *
          run.betaDot (k + 1) +
        (run.sTilde (k + 1) * run.rhoTilde (k + 1)) *
          p28E run (k + 1) +
        run.thetaTilde (k + 1) *
          (run.cTilde k * run.betaDot k + run.sTilde k * p28E run k) := by
          rw [p28_betaTilde_eq_E run (k + 1) (by omega),
            p28_betaTilde_eq_E run k hk]
          ring
    _ = run.rhoDot (k + 1) * run.betaDot (k + 1) +
        run.thetaBar (k + 2) * p28E run (k + 1) +
        run.thetaTilde (k + 1) *
          (run.cTilde k * run.betaDot k + run.sTilde k * p28E run k) := by
          rw [p28_cTilde_mul_rhoTilde run (k + 1) (by omega),
            p28_sTilde_mul_rhoTilde run (k + 1) (by omega)]
    _ = (run.cTilde k * run.rhoBar (k + 1)) *
          (-run.sTilde k * run.betaDot k + run.cTilde k * p28E run k) +
        run.thetaBar (k + 2) * p28E run (k + 1) +
        (run.sTilde k * run.rhoBar (k + 1)) *
          (run.cTilde k * run.betaDot k + run.sTilde k * p28E run k) := by
          rw [run.rhoDot_succ k hk, p28_betaDot_succ_E run k hk,
            run.thetaTilde_succ k hk]
    _ = run.rhoBar (k + 1) *
          (run.cTilde k ^ 2 + run.sTilde k ^ 2) * p28E run k +
        run.thetaBar (k + 2) * p28E run (k + 1) := by ring
    _ = run.rhoBar (k + 1) * p28E run k +
        run.thetaBar (k + 2) * p28E run (k + 1) := by
          rw [p28_cTilde_sq_add_sTilde_sq run k hk]
          ring

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  have hbase : run.betaTilde 1 = run.tauTilde 1 := by
    have h : run.rhoTilde 1 * run.betaTilde 1 =
        run.cBar 1 * run.betaBarOne := by
      calc
        _ = (run.cTilde 1 * run.rhoTilde 1) * run.betaDot 1 +
            (run.sTilde 1 * run.rhoTilde 1) * p28E run 1 := by
              rw [p28_betaTilde_eq_E run 1 (by omega)]
              ring
        _ = run.rhoBar 1 * p28E run 0 +
            run.thetaBar 2 * p28E run 1 := by
              rw [p28_cTilde_mul_rhoTilde run 1 (by omega),
                p28_sTilde_mul_rhoTilde run 1 (by omega),
                run.rhoDot_one, run.betaDot_one]
              simp only [p28E, p28PrefixProduct_zero, pow_zero, one_mul]
        _ = run.cBar 1 * run.betaBarOne := by
              simpa [p28PrefixProduct_zero] using p28_driving_identity run 0
    rw [run.tauTilde_one]
    apply (eq_div_iff (run.rhoTilde_ne 1 (by omega))).2
    simpa only [mul_comm] using h
  have hmain : ∀ n : ℕ, run.betaTilde (n + 1) = run.tauTilde (n + 1) := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
        have hj : 1 ≤ n + 1 := by omega
        have hrec := p28_betaTilde_recurrence run (n + 1) hj
        have hdrive := p28_driving_identity run (n + 1)
        have hnumer := hrec.trans hdrive
        rw [run.tauTilde_succ (n + 1) hj, ← ih]
        apply (eq_div_iff (run.rhoTilde_ne (n + 1 + 1) (by omega))).2
        linear_combination hnumer
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact hmain n

end VSCLReuse
