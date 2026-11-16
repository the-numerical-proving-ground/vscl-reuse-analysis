import VSCLReuse.P28.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p28_local_bridge (run : P28Lemma31Run) (i : ℕ) (hi : 1 ≤ i) :
    run.s i * run.alphaBar (i + 1) * run.cBar i =
      run.sBar i * run.alphaBar i * run.cBar (i - 1) := by
  rw [run.alphaBar_succ i hi, run.cBar_eq i hi, run.sBar_eq i hi,
    run.theta_succ i hi, run.c_eq i hi]
  field_simp [run.rho_ne i hi, run.rhoBar_ne i hi]

private theorem p28_prefix_bridge (run : P28Lemma31Run) (k : ℕ) :
    p28PrefixProduct run.s k * run.alphaBar (k + 1) * run.cBar k *
        run.betaOne =
      p28PrefixProduct run.sBar k * run.betaBarOne := by
  induction k with
  | zero =>
      simp [run.alphaBar_one, run.cBar_zero, run.betaBarOne_eq]
  | succ k ih =>
      have h := p28_local_bridge run (k + 1) (by omega)
      simp only [p28PrefixProduct_succ] at *
      have hidx : k + 1 - 1 = k := by omega
      rw [hidx] at h
      calc
        (p28PrefixProduct run.s k * run.s (k + 1)) *
            run.alphaBar (k + 1 + 1) * run.cBar (k + 1) * run.betaOne =
            (p28PrefixProduct run.s k * run.alphaBar (k + 1) *
              run.cBar k * run.betaOne) * run.sBar (k + 1) := by
                calc
                  _ = p28PrefixProduct run.s k *
                    (run.s (k + 1) * run.alphaBar (k + 1 + 1) *
                      run.cBar (k + 1)) * run.betaOne := by ring
                  _ = _ := by rw [h]; ring
        _ = (p28PrefixProduct run.sBar k * run.betaBarOne) *
              run.sBar (k + 1) := by rw [ih]
        _ = (p28PrefixProduct run.sBar k * run.sBar (k + 1)) *
              run.betaBarOne := by ring

private theorem p28_theta_c_relation (run : P28Lemma31Run)
    (i : ℕ) (hi : 1 ≤ i) :
    run.thetaBar (i + 1) * run.s i * run.c (i + 1) * run.rhoBar i =
      run.c i * run.theta (i + 1) ^ 2 := by
  rw [run.thetaBar_eq (i + 1) (by omega),
    run.c_eq (i + 1) (by omega), run.alphaBar_succ i hi]
  have hidx : i + 1 - 1 = i := by omega
  rw [hidx]
  rw [run.sBar_eq i hi, run.theta_succ i hi]
  field_simp [run.rho_ne (i + 1) (by omega), run.rhoBar_ne i hi]

private theorem p28_tilde_pythagoras (run : P28Lemma31Run)
    (i : ℕ) (hi : 1 ≤ i) :
    run.cTilde i ^ 2 + run.sTilde i ^ 2 = 1 := by
  rw [run.cTilde_eq i hi, run.sTilde_eq i hi]
  have hr := run.rhoTilde_sq i hi
  field_simp [run.rhoTilde_ne i hi]
  nlinarith [hr]

private theorem p28_force_identity (run : P28Lemma31Run) (k : ℕ) :
    run.rhoBar (k + 1) * p28PrefixProduct run.s k * run.c (k + 1) *
        run.betaOne -
      run.thetaBar (k + 2) * p28PrefixProduct run.s (k + 1) *
        run.c (k + 2) * run.betaOne =
      p28PrefixProduct run.sBar k * run.cBar (k + 1) * run.betaBarOne := by
  have hi : 1 ≤ k + 1 := by omega
  have hci : run.c (k + 1) * run.rho (k + 1) =
      run.alphaBar (k + 1) := by
    rw [run.c_eq (k + 1) hi]
    field_simp [run.rho_ne (k + 1) hi]
  have hcb : run.cBar (k + 1) * run.rhoBar (k + 1) =
      run.cBar k * run.rho (k + 1) := by
    rw [run.cBar_eq (k + 1) hi]
    have hidx : k + 1 - 1 = k := by omega
    rw [hidx]
    field_simp [run.rhoBar_ne (k + 1) hi]
  have hinv :
      (p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) *
          (run.cBar k * run.rho (k + 1)) =
        p28PrefixProduct run.sBar k * run.betaBarOne := by
    calc
      _ = p28PrefixProduct run.s k * run.alphaBar (k + 1) *
          run.cBar k * run.betaOne := by rw [← hci]; ring
      _ = _ := p28_prefix_bridge run k
  have ht := p28_theta_c_relation run (k + 1) hi
  have hidx : k + 1 + 1 = k + 2 := by omega
  rw [hidx] at ht
  have hsqr := run.rhoBar_sq (k + 1) hi
  have hidx' : k + 1 - 1 = k := by omega
  rw [hidx', hidx] at hsqr
  apply (mul_right_cancel₀ (run.rhoBar_ne (k + 1) hi))
  calc
    (run.rhoBar (k + 1) * p28PrefixProduct run.s k * run.c (k + 1) *
          run.betaOne -
        run.thetaBar (k + 2) * p28PrefixProduct run.s (k + 1) *
          run.c (k + 2) * run.betaOne) * run.rhoBar (k + 1) =
        (run.rhoBar (k + 1) ^ 2 - run.theta (k + 2) ^ 2) *
          (p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) := by
            rw [p28PrefixProduct_succ]
            calc
              _ = run.rhoBar (k + 1) ^ 2 *
                    (p28PrefixProduct run.s k * run.c (k + 1) *
                      run.betaOne) -
                  (run.thetaBar (k + 2) * run.s (k + 1) *
                    run.c (k + 2) * run.rhoBar (k + 1)) *
                    p28PrefixProduct run.s k * run.betaOne := by ring
              _ = _ := by rw [ht]; ring
    _ = (run.cBar k * run.rho (k + 1)) ^ 2 *
          (p28PrefixProduct run.s k * run.c (k + 1) * run.betaOne) := by
            rw [hsqr]
            ring
    _ = (p28PrefixProduct run.sBar k * run.betaBarOne) *
          (run.cBar k * run.rho (k + 1)) := by rw [← hinv]; ring
    _ = (p28PrefixProduct run.sBar k * run.cBar (k + 1) *
          run.betaBarOne) * run.rhoBar (k + 1) := by rw [← hcb]; ring

private theorem p28_base (run : P28Lemma31Run) :
    run.betaTilde 1 = run.tauTilde 1 := by
  have hf := p28_force_identity run 0
  calc
    run.betaTilde 1 =
        (run.rhoBar 1 * run.c 1 * run.betaOne -
          run.thetaBar 2 * run.s 1 * run.c 2 * run.betaOne) /
          run.rhoTilde 1 := by
            rw [run.betaTilde_eq 1 (by omega), run.betaDot_one,
              run.cTilde_eq 1 (by omega), run.sTilde_eq 1 (by omega),
              run.rhoDot_one]
            simp [p28PrefixProduct_succ]
            ring
    _ = run.cBar 1 * run.betaBarOne / run.rhoTilde 1 := by
          congr 1
          simpa [p28PrefixProduct_succ] using hf
    _ = run.tauTilde 1 := run.tauTilde_one.symm

private theorem p28_step_algebra (r c s u e d f b : ℝ)
    (hpy : c ^ 2 + s ^ 2 = 1) (hsource : r * e + d * f = b) :
    c * r * (-s * u + c * e) + d * f =
      b - s * r * (c * u + s * e) := by
  calc
    _ = (r * e + d * f) - s * r * (c * u + s * e) +
          r * e * (c ^ 2 + s ^ 2 - 1) := by ring
    _ = _ := by rw [hpy, hsource]; ring

private theorem p28_step (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k)
    (ih : run.betaTilde k = run.tauTilde k) :
    run.betaTilde (k + 1) = run.tauTilde (k + 1) := by
  let e : ℝ := (-1 : ℝ) ^ k * p28PrefixProduct run.s k *
    run.c (k + 1) * run.betaOne
  let f : ℝ := (-1 : ℝ) ^ (k + 1) * p28PrefixProduct run.s (k + 1) *
    run.c (k + 2) * run.betaOne
  let b : ℝ := (-1 : ℝ) ^ (k + 2) * p28PrefixProduct run.sBar k *
    run.cBar (k + 1) * run.betaBarOne
  have hsign1 : (-1 : ℝ) ^ (k + 1) = -(-1 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  have hsign2 : (-1 : ℝ) ^ (k + 2) = (-1 : ℝ) ^ k := by
    rw [pow_add]
    norm_num
    rfl
  have hsource : run.rhoBar (k + 1) * e + run.thetaBar (k + 2) * f = b := by
    dsimp [e, f, b]
    calc
      _ = (-1 : ℝ) ^ k *
            (run.rhoBar (k + 1) * p28PrefixProduct run.s k *
              run.c (k + 1) * run.betaOne -
              run.thetaBar (k + 2) * p28PrefixProduct run.s (k + 1) *
                run.c (k + 2) * run.betaOne) := by rw [hsign1]; ring
      _ = (-1 : ℝ) ^ k *
            (p28PrefixProduct run.sBar k * run.cBar (k + 1) *
              run.betaBarOne) := by rw [p28_force_identity run k]
      _ = _ := by rw [hsign2]; ring
  have hdot : run.betaDot (k + 1) =
      -run.sTilde k * run.betaDot k + run.cTilde k * e := by
    dsimp [e]
    rw [run.betaDot_succ k hk]
    ring
  have hprev : run.betaTilde k =
      run.cTilde k * run.betaDot k + run.sTilde k * e := by
    dsimp [e]
    rw [run.betaTilde_eq k hk]
    ring
  have hτ : run.tauTilde (k + 1) =
      (b - run.thetaTilde (k + 1) * run.tauTilde k) /
        run.rhoTilde (k + 1) := by
    simpa [b] using run.tauTilde_succ k hk
  have hpy := p28_tilde_pythagoras run k hk
  have halg := p28_step_algebra (run.rhoBar (k + 1))
    (run.cTilde k) (run.sTilde k) (run.betaDot k) e
    (run.thetaBar (k + 2)) f b hpy hsource
  calc
    run.betaTilde (k + 1) =
        (run.rhoDot (k + 1) * run.betaDot (k + 1) +
          run.thetaBar (k + 2) * f) / run.rhoTilde (k + 1) := by
            rw [run.betaTilde_eq (k + 1) (by omega),
              run.cTilde_eq (k + 1) (by omega),
              run.sTilde_eq (k + 1) (by omega)]
            dsimp [f]
            ring
    _ = (run.cTilde k * run.rhoBar (k + 1) *
          (-run.sTilde k * run.betaDot k + run.cTilde k * e) +
          run.thetaBar (k + 2) * f) / run.rhoTilde (k + 1) := by
            rw [run.rhoDot_succ k hk, hdot]
    _ = (b - run.sTilde k * run.rhoBar (k + 1) *
          (run.cTilde k * run.betaDot k + run.sTilde k * e)) /
          run.rhoTilde (k + 1) := by rw [halg]
    _ = (b - run.thetaTilde (k + 1) * run.tauTilde k) /
          run.rhoTilde (k + 1) := by
            rw [run.thetaTilde_succ k hk, ← ih, hprev]
    _ = run.tauTilde (k + 1) := hτ.symm

/-- P28-C1: the transformed-component identity of Lemma 3.1. -/
theorem p28_c1_lsmr_transformed_components
    (run : P28Lemma31Run) (k : ℕ) (hk : 1 ≤ k) :
    run.betaTilde k = run.tauTilde k := by
  -- PROOF_START P28-C1-H001
  induction k, hk using Nat.le_induction with
  | base => exact p28_base run
  | succ k hk ih => exact p28_step run k hk ih

end VSCLReuse
