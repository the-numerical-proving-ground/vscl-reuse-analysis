import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p28_product_identity (run : P28Lemma31Run) (n : ℕ) :
    p28PrefixProduct run.s n * run.cBar n * run.alphaBar (n + 1) =
      p28PrefixProduct run.sBar n * run.alpha 1 := by
  induction n with
  | zero =>
      simp [run.cBar_zero, run.alphaBar_one]
  | succ n ih =>
      have hn : 1 ≤ n + 1 := by omega
      have hr : run.rho (n + 1) ≠ 0 := run.rho_ne (n + 1) hn
      have hb : run.rhoBar (n + 1) ≠ 0 := run.rhoBar_ne (n + 1) hn
      have hsub : n + 1 - 1 = n := by omega
      rw [p28PrefixProduct_succ, p28PrefixProduct_succ,
        run.cBar_eq (n + 1) hn, run.alphaBar_succ (n + 1) hn,
        run.sBar_eq (n + 1) hn, hsub]
      rw [run.c_eq (n + 1) hn]
      field_simp
      rw [run.theta_succ (n + 1) hn]
      calc
        _ = (p28PrefixProduct run.s n * run.cBar n *
            run.alphaBar (n + 1)) *
            (run.s (n + 1) * run.alpha (n + 1 + 1)) := by ring
        _ = (p28PrefixProduct run.sBar n * run.alpha 1) *
            (run.s (n + 1) * run.alpha (n + 1 + 1)) := by rw [ih]
        _ = _ := by ring

private theorem p28_bridge (run : P28Lemma31Run) (n : ℕ) :
    p28PrefixProduct run.s n *
        (run.rhoBar (n + 1) * run.c (n + 1) -
          run.thetaBar (n + 2) * run.s (n + 1) * run.c (n + 2)) *
        run.betaOne =
      p28PrefixProduct run.sBar n * run.cBar (n + 1) *
        run.betaBarOne := by
  have hn : 1 ≤ n + 1 := by omega
  have hn' : 1 ≤ n + 2 := by omega
  have hb : run.rhoBar (n + 1) ≠ 0 := run.rhoBar_ne (n + 1) hn
  have hc : run.rho (n + 1) * run.c (n + 1) =
      run.alphaBar (n + 1) := by
    rw [run.c_eq (n + 1) hn]
    field_simp [run.rho_ne (n + 1) hn]
  have hc' : run.rho (n + 2) * run.c (n + 2) =
      run.alphaBar (n + 2) := by
    rw [run.c_eq (n + 2) hn']
    field_simp [run.rho_ne (n + 2) hn']
  have hcb : run.rhoBar (n + 1) * run.cBar (n + 1) =
      run.cBar n * run.rho (n + 1) := by
    rw [run.cBar_eq (n + 1) hn]
    simp only [show n + 1 - 1 = n by omega]
    field_simp [hb]
  have hsb : run.rhoBar (n + 1) * run.sBar (n + 1) =
      run.theta (n + 2) := by
    rw [run.sBar_eq (n + 1) hn]
    field_simp [hb]
  have htb : run.thetaBar (n + 2) =
      run.sBar (n + 1) * run.rho (n + 2) := by
    simpa [show n + 2 - 1 = n + 1 by omega] using
      run.thetaBar_eq (n + 2) hn'
  have hth := run.theta_succ (n + 1) hn
  have hab := run.alphaBar_succ (n + 1) hn
  have hsq : run.rhoBar (n + 1) ^ 2 =
      (run.cBar n * run.rho (n + 1)) ^ 2 +
        run.theta (n + 2) ^ 2 := by
    simpa [show n + 1 - 1 = n by omega] using
      run.rhoBar_sq (n + 1) hn
  have hcore_mul :
      run.rhoBar (n + 1) *
          (run.rhoBar (n + 1) * run.c (n + 1) -
            run.thetaBar (n + 2) * run.s (n + 1) * run.c (n + 2)) =
        run.rhoBar (n + 1) *
          (run.cBar n * run.alphaBar (n + 1) *
            run.cBar (n + 1)) := by
    calc
      _ = run.rhoBar (n + 1) ^ 2 * run.c (n + 1) -
            (run.rhoBar (n + 1) * run.sBar (n + 1)) *
              (run.rho (n + 2) * run.c (n + 2)) *
              run.s (n + 1) := by rw [htb]; ring
      _ = run.rhoBar (n + 1) ^ 2 * run.c (n + 1) -
            run.theta (n + 2) *
              (run.c (n + 1) * run.alpha (n + 2)) *
              run.s (n + 1) := by rw [hsb, hc', hab]
      _ = (run.rhoBar (n + 1) ^ 2 - run.theta (n + 2) ^ 2) *
            run.c (n + 1) := by rw [hth]; ring
      _ = (run.cBar n * run.rho (n + 1)) ^ 2 *
            run.c (n + 1) := by rw [hsq]; ring
      _ = run.cBar n *
            (run.rho (n + 1) * run.c (n + 1)) *
            (run.cBar n * run.rho (n + 1)) := by ring
      _ = run.rhoBar (n + 1) *
            (run.cBar n * run.alphaBar (n + 1) *
              run.cBar (n + 1)) := by rw [← hc, ← hcb]; ring
  have hcore := (mul_left_cancel₀ hb) hcore_mul
  rw [hcore, run.betaBarOne_eq]
  calc
    _ = (p28PrefixProduct run.s n * run.cBar n *
          run.alphaBar (n + 1)) *
        (run.cBar (n + 1) * run.betaOne) := by ring
    _ = (p28PrefixProduct run.sBar n * run.alpha 1) *
        (run.cBar (n + 1) * run.betaOne) := by
          rw [p28_product_identity]
    _ = _ := by ring

private noncomputable def p28A (run : P28Lemma31Run) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * p28PrefixProduct run.s n *
    run.c (n + 1) * run.betaOne

private noncomputable def p28B (run : P28Lemma31Run) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 2) * p28PrefixProduct run.sBar n *
    run.cBar (n + 1) * run.betaBarOne

private theorem p28_signed_bridge (run : P28Lemma31Run) (n : ℕ) :
    run.rhoBar (n + 1) * p28A run n +
      run.thetaBar (n + 2) * p28A run (n + 1) =
      p28B run n := by
  have h := p28_bridge run n
  unfold p28A p28B
  rw [p28PrefixProduct_succ, pow_succ]
  have hp : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
    ring
  rw [hp]
  calc
    _ = (-1 : ℝ) ^ n *
          (p28PrefixProduct run.s n *
            (run.rhoBar (n + 1) * run.c (n + 1) -
              run.thetaBar (n + 2) * run.s (n + 1) *
                run.c (n + 2)) * run.betaOne) := by ring
    _ = (-1 : ℝ) ^ n *
          (p28PrefixProduct run.sBar n * run.cBar (n + 1) *
            run.betaBarOne) := by rw [h]
    _ = _ := by ring

private theorem p28_tilde_orthogonal (run : P28Lemma31Run) (n : ℕ)
    (hn : 1 ≤ n) :
    run.cTilde n ^ 2 + run.sTilde n ^ 2 = 1 := by
  rw [run.cTilde_eq n hn, run.sTilde_eq n hn]
  have hne := run.rhoTilde_ne n hn
  field_simp
  nlinarith [run.rhoTilde_sq n hn]

private theorem p28_beta_recurrence (run : P28Lemma31Run) (n : ℕ)
    (hn : 1 ≤ n) :
    run.rhoTilde (n + 1) * run.betaTilde (n + 1) +
      run.thetaTilde (n + 1) * run.betaTilde n =
      p28B run n := by
  have hn' : 1 ≤ n + 1 := by omega
  have hct :
      run.rhoTilde (n + 1) * run.cTilde (n + 1) =
        run.rhoDot (n + 1) := by
    rw [run.cTilde_eq (n + 1) hn']
    field_simp [run.rhoTilde_ne (n + 1) hn']
  have hst :
      run.rhoTilde (n + 1) * run.sTilde (n + 1) =
        run.thetaBar (n + 2) := by
    rw [run.sTilde_eq (n + 1) hn']
    field_simp [run.rhoTilde_ne (n + 1) hn']
  have hbn : run.betaTilde n =
      run.cTilde n * run.betaDot n + run.sTilde n * p28A run n := by
    rw [p28A]
    convert run.betaTilde_eq n hn using 1; ring
  have hbn' : run.betaTilde (n + 1) =
      run.cTilde (n + 1) * run.betaDot (n + 1) +
        run.sTilde (n + 1) * p28A run (n + 1) := by
    rw [p28A]
    convert run.betaTilde_eq (n + 1) hn' using 1; ring
  have hdot : run.betaDot (n + 1) =
      -run.sTilde n * run.betaDot n +
        run.cTilde n * p28A run n := by
    rw [p28A]
    convert run.betaDot_succ n hn using 1; ring
  calc
    _ = run.rhoDot (n + 1) * run.betaDot (n + 1) +
          run.thetaBar (n + 2) * p28A run (n + 1) +
          run.sTilde n * run.rhoBar (n + 1) *
            run.betaTilde n := by
      rw [hbn', run.thetaTilde_succ n hn]
      calc
        _ = (run.rhoTilde (n + 1) * run.cTilde (n + 1)) *
              run.betaDot (n + 1) +
            (run.rhoTilde (n + 1) * run.sTilde (n + 1)) *
              p28A run (n + 1) +
            run.sTilde n * run.rhoBar (n + 1) *
              run.betaTilde n := by ring
        _ = _ := by rw [hct, hst]
    _ = (run.cTilde n ^ 2 + run.sTilde n ^ 2) *
          run.rhoBar (n + 1) * p28A run n +
          run.thetaBar (n + 2) * p28A run (n + 1) := by
      rw [run.rhoDot_succ n hn, hdot, hbn]
      ring
    _ = run.rhoBar (n + 1) * p28A run n +
          run.thetaBar (n + 2) * p28A run (n + 1) := by
      rw [p28_tilde_orthogonal run n hn]
      ring
    _ = p28B run n := p28_signed_bridge run n

private theorem p28_base (run : P28Lemma31Run) :
    run.betaTilde 1 = run.tauTilde 1 := by
  have hne := run.rhoTilde_ne 1 (by omega)
  have hct : run.rhoTilde 1 * run.cTilde 1 = run.rhoBar 1 := by
    rw [run.cTilde_eq 1 (by omega), run.rhoDot_one]
    field_simp [hne]
  have hst : run.rhoTilde 1 * run.sTilde 1 =
      run.thetaBar 2 := by
    rw [run.sTilde_eq 1 (by omega)]
    field_simp [hne]
  have hb : run.betaTilde 1 =
      run.cTilde 1 * run.betaDot 1 + run.sTilde 1 * p28A run 1 := by
    rw [p28A]
    convert run.betaTilde_eq 1 (by omega) using 1; ring
  have ha : p28A run 0 = run.c 1 * run.betaOne := by
    simp [p28A]
  have hbridge : run.rhoBar 1 * p28A run 0 +
      run.thetaBar 2 * p28A run 1 =
      run.cBar 1 * run.betaBarOne := by
    simpa [p28B] using p28_signed_bridge run 0
  rw [run.tauTilde_one]
  apply (eq_div_iff hne).2
  calc
    run.betaTilde 1 * run.rhoTilde 1 =
        (run.cTilde 1 * p28A run 0 +
          run.sTilde 1 * p28A run 1) *
          run.rhoTilde 1 := by rw [hb, run.betaDot_one, ha]
    _ = run.rhoBar 1 * p28A run 0 +
          run.thetaBar 2 * p28A run 1 := by
      calc
        _ = (run.rhoTilde 1 * run.cTilde 1) * p28A run 0 +
              (run.rhoTilde 1 * run.sTilde 1) * p28A run 1 := by ring
        _ = _ := by rw [hct, hst]
    _ = run.cBar 1 * run.betaBarOne := hbridge

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  have hmain : ∀ n : ℕ,
      run.betaTilde (n + 1) = run.tauTilde (n + 1) := by
    intro n
    induction n with
    | zero =>
        simpa using p28_base run
    | succ n ih =>
        have hn : 1 ≤ n + 1 := by omega
        have hn' : 1 ≤ (n + 1) + 1 := by omega
        have hrec := p28_beta_recurrence run (n + 1) hn
        rw [run.tauTilde_succ (n + 1) hn, ← ih]
        apply (eq_div_iff (run.rhoTilde_ne ((n + 1) + 1) hn')).2
        dsimp [p28B] at hrec
        nlinarith
  have hidx : k - 1 + 1 = k := by omega
  simpa [hidx] using hmain (k - 1)

end VSCLReuse
