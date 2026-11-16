import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p28_c_mul_rho (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.c k * run.rho k = run.alphaBar k := by
  rw [run.c_eq k hk]
  field_simp [run.rho_ne k hk]

private theorem p28_sBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.sBar k * run.rhoBar k = run.theta (k + 1) := by
  rw [run.sBar_eq k hk]
  field_simp [run.rhoBar_ne k hk]

private theorem p28_cBar_mul_rhoBar (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.cBar k * run.rhoBar k = run.cBar (k - 1) * run.rho k := by
  rw [run.cBar_eq k hk]
  field_simp [run.rhoBar_ne k hk]

private theorem p28_product_core (run : P28Lemma31Run) (k : ℕ) :
    run.alphaBar (k + 1) * run.cBar k * run.sBar (k + 1) =
      run.s (k + 1) * run.alphaBar (k + 2) * run.cBar (k + 1) := by
  have hk : 1 ≤ k + 1 := by omega
  have hcb := p28_cBar_mul_rhoBar run (k + 1) hk
  have hsb := p28_sBar_mul_rhoBar run (k + 1) hk
  have hc := p28_c_mul_rho run (k + 1) hk
  have hth := run.theta_succ (k + 1) hk
  have ha := run.alphaBar_succ (k + 1) hk
  have hpred : k + 1 - 1 = k := by omega
  rw [hpred] at hcb
  have hidx : k + 1 + 1 = k + 2 := by omega
  rw [hidx] at hth ha hsb
  apply mul_right_cancel₀ (run.rhoBar_ne (k + 1) hk)
  calc
    (run.alphaBar (k + 1) * run.cBar k * run.sBar (k + 1)) *
        run.rhoBar (k + 1) =
      run.alphaBar (k + 1) * run.cBar k * run.theta (k + 2) := by
        rw [← hsb]; ring
    _ = (run.c (k + 1) * run.rho (k + 1)) * run.cBar k *
          (run.s (k + 1) * run.alpha (k + 2)) := by rw [hc, hth]
    _ = (run.s (k + 1) * (run.c (k + 1) * run.alpha (k + 2))) *
          (run.cBar k * run.rho (k + 1)) := by ring
    _ = (run.s (k + 1) * (run.c (k + 1) * run.alpha (k + 2))) *
          (run.cBar (k + 1) * run.rhoBar (k + 1)) := by rw [hcb]
    _ = (run.s (k + 1) * (run.c (k + 1) * run.alpha (k + 2)) *
          run.cBar (k + 1)) * run.rhoBar (k + 1) := by ring
    _ = (run.s (k + 1) * run.alphaBar (k + 2) *
          run.cBar (k + 1)) * run.rhoBar (k + 1) := by rw [ha]

private theorem p28_prefix_identity (run : P28Lemma31Run) (k : ℕ) :
    p28PrefixProduct run.sBar k * run.betaBarOne =
      p28PrefixProduct run.s k * run.alphaBar (k + 1) *
        run.cBar k * run.betaOne := by
  induction k with
  | zero =>
      simp [run.betaBarOne_eq, run.alphaBar_one, run.cBar_zero]
  | succ k ih =>
      rw [p28PrefixProduct_succ, p28PrefixProduct_succ]
      calc
        (p28PrefixProduct run.sBar k * run.sBar (k + 1)) * run.betaBarOne =
            (p28PrefixProduct run.sBar k * run.betaBarOne) * run.sBar (k + 1) := by ring
        _ = (p28PrefixProduct run.s k * run.alphaBar (k + 1) *
              run.cBar k * run.betaOne) * run.sBar (k + 1) := by rw [ih]
        _ = (p28PrefixProduct run.s k * run.s (k + 1)) *
              run.alphaBar (k + 1 + 1) * run.cBar (k + 1) * run.betaOne := by
          rw [show k + 1 + 1 = k + 2 by omega]
          calc
            _ = p28PrefixProduct run.s k *
                (run.alphaBar (k + 1) * run.cBar k * run.sBar (k + 1)) *
                run.betaOne := by ring
            _ = p28PrefixProduct run.s k *
                (run.s (k + 1) * run.alphaBar (k + 2) *
                  run.cBar (k + 1)) * run.betaOne := by
                    rw [p28_product_core run k]
            _ = _ := by ring

private noncomputable def p28P (run : P28Lemma31Run) (k : ℕ) : ℝ :=
  p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne

private noncomputable def p28Q (run : P28Lemma31Run) (k : ℕ) : ℝ :=
  p28PrefixProduct run.sBar k * run.cBar (k + 1) * run.betaBarOne

private theorem p28_product_rotation (run : P28Lemma31Run) (k : ℕ) :
    p28Q run k * run.rhoBar (k + 1) =
      p28P run k * (run.cBar k * run.rho (k + 1)) ^ 2 := by
  have hk : 1 ≤ k + 1 := by omega
  have hcb := p28_cBar_mul_rhoBar run (k + 1) hk
  have hc := p28_c_mul_rho run (k + 1) hk
  have hpred : k + 1 - 1 = k := by omega
  rw [hpred] at hcb
  dsimp [p28Q, p28P]
  calc
    p28PrefixProduct run.sBar k * run.cBar (k + 1) *
        run.betaBarOne * run.rhoBar (k + 1) =
      (p28PrefixProduct run.sBar k * run.betaBarOne) *
        (run.cBar (k + 1) * run.rhoBar (k + 1)) := by ring
    _ = (p28PrefixProduct run.s k * run.alphaBar (k + 1) *
          run.cBar k * run.betaOne) *
          (run.cBar k * run.rho (k + 1)) := by
        rw [p28_prefix_identity, hcb]
    _ = (p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) *
          (run.cBar k * run.rho (k + 1)) ^ 2 := by
        rw [← hc]; ring

private theorem p28_theta_product (run : P28Lemma31Run) (k : ℕ) :
    run.thetaBar (k + 2) * p28P run (k + 1) * run.rhoBar (k + 1) =
      p28P run k * run.theta (k + 2) ^ 2 := by
  have hk : 1 ≤ k + 1 := by omega
  have hk2 : 1 ≤ k + 2 := by omega
  have hsb := p28_sBar_mul_rhoBar run (k + 1) hk
  have hc := p28_c_mul_rho run (k + 2) hk2
  have ha := run.alphaBar_succ (k + 1) hk
  have hth := run.theta_succ (k + 1) hk
  have htb := run.thetaBar_eq (k + 2) hk2
  have hidx : k + 1 + 1 = k + 2 := by omega
  have hpred : k + 2 - 1 = k + 1 := by omega
  rw [hidx] at hsb ha hth
  rw [hpred] at htb
  rw [htb, p28P, p28P, p28PrefixProduct_succ]
  calc
    run.sBar (k + 1) * run.rho (k + 2) *
        (p28PrefixProduct run.s k * run.s (k + 1) *
          run.c (k + 1 + 1) * run.betaOne) *
        run.rhoBar (k + 1) =
      p28PrefixProduct run.s k * run.s (k + 1) *
        (run.sBar (k + 1) * run.rhoBar (k + 1)) *
        (run.rho (k + 2) * run.c (k + 2)) * run.betaOne := by
          rw [hidx]; ring
    _ = p28PrefixProduct run.s k * run.s (k + 1) *
          run.theta (k + 2) * run.alphaBar (k + 2) * run.betaOne := by
        rw [hsb, mul_comm (run.rho (k + 2)) (run.c (k + 2)), hc]
    _ = p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne *
          run.theta (k + 2) ^ 2 := by
        rw [ha, hth]; ring

private theorem p28_unsigned_forcing (run : P28Lemma31Run) (k : ℕ) :
    p28Q run k = run.rhoBar (k + 1) * p28P run k -
      run.thetaBar (k + 2) * p28P run (k + 1) := by
  have hk : 1 ≤ k + 1 := by omega
  have hrbar := run.rhoBar_ne (k + 1) hk
  have hrho := run.rhoBar_sq (k + 1) hk
  have hpred : k + 1 - 1 = k := by omega
  rw [hpred] at hrho
  apply mul_right_cancel₀ hrbar
  calc
    p28Q run k * run.rhoBar (k + 1) =
        p28P run k * (run.cBar k * run.rho (k + 1)) ^ 2 :=
      p28_product_rotation run k
    _ = p28P run k *
          (run.rhoBar (k + 1) ^ 2 - run.theta (k + 2) ^ 2) := by
            rw [hrho]; ring
    _ = (run.rhoBar (k + 1) * p28P run k -
          run.thetaBar (k + 2) * p28P run (k + 1)) *
          run.rhoBar (k + 1) := by
            have ht := p28_theta_product run k
            nlinarith [ht]

private noncomputable def p28X (run : P28Lemma31Run) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * p28P run k

private noncomputable def p28Y (run : P28Lemma31Run) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * p28Q run k

private theorem p28_signed_forcing (run : P28Lemma31Run) (k : ℕ) :
    p28Y run k = run.rhoBar (k + 1) * p28X run k +
      run.thetaBar (k + 2) * p28X run (k + 1) := by
  rw [p28Y, p28X, p28X, p28_unsigned_forcing]
  rw [pow_succ]
  ring

private theorem p28_cTilde_mul (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.cTilde k * run.rhoTilde k = run.rhoDot k := by
  rw [run.cTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private theorem p28_sTilde_mul (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.sTilde k * run.rhoTilde k = run.thetaBar (k + 1) := by
  rw [run.sTilde_eq k hk]
  field_simp [run.rhoTilde_ne k hk]

private theorem p28_tilde_unit (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.cTilde k ^ 2 + run.sTilde k ^ 2 = 1 := by
  have hc := p28_cTilde_mul run k hk
  have hs := p28_sTilde_mul run k hk
  have hsq := run.rhoTilde_sq k hk
  have hc2 : run.cTilde k ^ 2 * run.rhoTilde k ^ 2 =
      run.rhoDot k ^ 2 := by
    calc
      _ = (run.cTilde k * run.rhoTilde k) ^ 2 := by ring
      _ = _ := by rw [hc]
  have hs2 : run.sTilde k ^ 2 * run.rhoTilde k ^ 2 =
      run.thetaBar (k + 1) ^ 2 := by
    calc
      _ = (run.sTilde k * run.rhoTilde k) ^ 2 := by ring
      _ = _ := by rw [hs]
  have hzero :
      (run.cTilde k ^ 2 + run.sTilde k ^ 2 - 1) *
        run.rhoTilde k ^ 2 = 0 := by nlinarith [hc2, hs2, hsq]
  have hnz : run.rhoTilde k ^ 2 ≠ 0 := pow_ne_zero 2 (run.rhoTilde_ne k hk)
  have h := (mul_eq_zero.mp hzero).resolve_right hnz
  linarith

private theorem p28_betaTilde_formula (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.betaTilde k = run.cTilde k * run.betaDot k +
      run.sTilde k * p28X run k := by
  rw [run.betaTilde_eq k hk]
  dsimp [p28X, p28P]
  ring

private theorem p28_betaDot_formula (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.betaDot (k + 1) = -run.sTilde k * run.betaDot k +
      run.cTilde k * p28X run k := by
  rw [run.betaDot_succ k hk]
  dsimp [p28X, p28P]
  ring

private theorem p28_betaTilde_mul (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.betaTilde k * run.rhoTilde k =
      run.rhoDot k * run.betaDot k + run.thetaBar (k + 1) * p28X run k := by
  rw [p28_betaTilde_formula run k hk]
  rw [← p28_cTilde_mul run k hk, ← p28_sTilde_mul run k hk]
  ring

private theorem p28_bridge (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    p28Y run k =
      run.rhoDot (k + 1) * run.betaDot (k + 1) +
        run.thetaBar (k + 2) * p28X run (k + 1) +
        run.thetaTilde (k + 1) * run.betaTilde k := by
  have hu := p28_tilde_unit run k hk
  have hdot := run.rhoDot_succ k hk
  have htheta := run.thetaTilde_succ k hk
  have hbd := p28_betaDot_formula run k hk
  have hbt := p28_betaTilde_formula run k hk
  rw [hbd, hbt, hdot, htheta]
  calc
    p28Y run k = run.rhoBar (k + 1) * p28X run k +
        run.thetaBar (k + 2) * p28X run (k + 1) :=
      p28_signed_forcing run k
    _ = run.cTilde k * run.rhoBar (k + 1) *
          (-run.sTilde k * run.betaDot k + run.cTilde k * p28X run k) +
        run.thetaBar (k + 2) * p28X run (k + 1) +
        run.sTilde k * run.rhoBar (k + 1) *
          (run.cTilde k * run.betaDot k + run.sTilde k * p28X run k) := by
            calc
              _ = run.rhoBar (k + 1) *
                    ((run.cTilde k ^ 2 + run.sTilde k ^ 2) * p28X run k) +
                  run.thetaBar (k + 2) * p28X run (k + 1) := by simp [hu]
              _ = _ := by ring

private theorem p28_tau_succ_formula (run : P28Lemma31Run) (k : ℕ)
    (hk : 1 ≤ k) :
    run.tauTilde (k + 1) =
      (p28Y run k - run.thetaTilde (k + 1) * run.tauTilde k) /
        run.rhoTilde (k + 1) := by
  rw [run.tauTilde_succ k hk]
  simp only [p28Y, p28Q, pow_add, pow_two]
  ring

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  induction k, hk using Nat.le_induction with
  | base =>
      rw [run.tauTilde_one]
      apply (eq_div_iff (run.rhoTilde_ne 1 (by omega))).2
      have hmul := p28_betaTilde_mul run 1 (by omega)
      have hfirst : run.betaDot 1 = p28X run 0 := by
        simp [run.betaDot_one, p28X, p28P]
      calc
        run.betaTilde 1 * run.rhoTilde 1 =
            run.rhoBar 1 * p28X run 0 +
              run.thetaBar 2 * p28X run 1 := by
                rw [run.rhoDot_one, hfirst] at hmul
                simpa using hmul
        _ = p28Y run 0 := (p28_signed_forcing run 0).symm
        _ = run.cBar 1 * run.betaBarOne := by
          simp [p28Y, p28Q]
  | succ k hk ih =>
      rw [p28_tau_succ_formula run k hk]
      apply (eq_div_iff (run.rhoTilde_ne (k + 1) (by omega))).2
      calc
        run.betaTilde (k + 1) * run.rhoTilde (k + 1) =
            run.rhoDot (k + 1) * run.betaDot (k + 1) +
              run.thetaBar (k + 2) * p28X run (k + 1) :=
          p28_betaTilde_mul run (k + 1) (by omega)
        _ = p28Y run k - run.thetaTilde (k + 1) * run.betaTilde k := by
          rw [p28_bridge run k hk]
          ring
        _ = p28Y run k - run.thetaTilde (k + 1) * run.tauTilde k := by
          rw [ih]

end VSCLReuse
