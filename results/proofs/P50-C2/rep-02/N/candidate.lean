import VSCLReuse.P50.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p50GammaValid_mono {u : ℝ} (hu : 0 ≤ u) {k n : ℕ}
    (hkn : k ≤ n) (hn : P50GammaValid u n) : P50GammaValid u k := by
  unfold P50GammaValid at *
  have hc : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hn

private theorem p50SourceBudget_le (n : ℕ) (i : Fin n) :
    p50SourceBudget n i ≤ n := by
  unfold p50SourceBudget
  split_ifs with h
  · rfl
  · have hi : i.val < n := i.isLt
    omega

private theorem p50SourceBudget_castSucc (n : ℕ) (i : Fin (n + 1)) :
    p50SourceBudget (n + 2) i.castSucc = p50SourceBudget (n + 1) i + 1 := by
  simp only [p50SourceBudget, Fin.val_castSucc]
  split_ifs with h
  · omega
  · have hi : i.val < n + 1 := i.isLt
    omega

private theorem p50SourceBudget_last (n : ℕ) :
    p50SourceBudget (n + 2) (Fin.last (n + 1)) = 2 := by
  simp [p50SourceBudget, Fin.val_last]

private theorem p50Dot_succ_succ (fp : P50FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p50Dot fp (n + 2) x y =
      fp.fl_add
        (p50Dot fp (n + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [p50Dot, Fin.foldl_succ_last]
  rfl

private theorem p50Gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ)
    (hk : P50GammaValid u k) : 0 ≤ p50Gamma u k := by
  unfold p50Gamma P50GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private theorem p50Gamma_one_ge {u : ℝ} (hu : 0 ≤ u)
    (h1 : P50GammaValid u 1) : u ≤ p50Gamma u 1 := by
  have hden : 0 < 1 - u := by simpa [P50GammaValid] using h1
  unfold p50Gamma
  norm_num
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem p50Gamma_step {u a d : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hk : P50GammaValid u (k + 1))
    (ha : |a| ≤ p50Gamma u k) (hd : |d| ≤ u) :
    |(1 + a) * (1 + d) - 1| ≤ p50Gamma u (k + 1) := by
  have hk0 : P50GammaValid u k :=
    p50GammaValid_mono hu (Nat.le_succ k) hk
  have hg : 0 ≤ p50Gamma u k := p50Gamma_nonneg hu k hk0
  have hbound : |(1 + a) * (1 + d) - 1| ≤
      p50Gamma u k + u + p50Gamma u k * u := by
    have htri : |(1 + a) * (1 + d) - 1| ≤ |a| + |d| + |a| * |d| := by
      have heq : (1 + a) * (1 + d) - 1 = (a + d) + a * d := by ring
      rw [heq]
      calc
        |(a + d) + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
        _ ≤ |a| + |d| + |a| * |d| := by
          rw [abs_mul]
          linarith [abs_add_le a d]
    calc
      _ ≤ |a| + |d| + |a| * |d| := htri
      _ ≤ p50Gamma u k + u + p50Gamma u k * u := by
        have hm : |a| * |d| ≤ p50Gamma u k * u :=
          mul_le_mul ha hd (abs_nonneg _) hg
        linarith
  have hku : (k : ℝ) * u < 1 := hk0
  have hsu : ((k + 1 : ℕ) : ℝ) * u < 1 := hk
  have hden0 : 0 < 1 - (k : ℝ) * u := by linarith
  have hden1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hgamma : p50Gamma u k + u + p50Gamma u k * u ≤
      p50Gamma u (k + 1) := by
    let t : ℝ := (k : ℝ) * u
    have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hu
    have hd₀ : 0 < 1 - t := hden0
    have hd₁ : 0 < 1 - t - u := by
      dsimp [t]
      push_cast at hden1 ⊢
      nlinarith
    have heq : t / (1 - t) + u + t / (1 - t) * u =
        (t + u) / (1 - t) := by
      field_simp
      ring
    have hpoly : (t + u) * (1 - t - u) ≤ (t + u) * (1 - t) :=
      mul_le_mul_of_nonneg_left (by linarith) (add_nonneg ht hu)
    have hcalc : t / (1 - t) + u + t / (1 - t) * u ≤
        (t + u) / (1 - t - u) := by
      rw [heq]
      apply (le_div_iff₀ hd₁).2
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hd₀).2 hpoly
    simpa only [p50Gamma, t, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      sub_add_eq_sub_sub] using hcalc
  exact hbound.trans hgamma

/-- P50-C2: complete named Theorem 3.5, the position-specific diagonal
backward-error representation for the sequential dot product. -/
theorem p50_c2_full_theorem35 (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P50GammaValid fp.u n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget n i)) ∧
      p50Dot fp n x y =
        ∑ i : Fin n, x i * y i * (1 + θ i) := by
  -- PROOF_START P50-C2-H001
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i
        exact i.elim0
      · simp [p50Dot]
    | succ m =>
      cases m with
      | zero =>
        obtain ⟨d, hd, hmul⟩ := fp.model_mul (x 0) (y 0)
        refine ⟨fun _ => d, ?_, ?_⟩
        · intro i
          have hg : fp.u ≤ p50Gamma fp.u 1 := by
            exact p50Gamma_one_ge fp.u_nonneg hn
          fin_cases i
          simpa [p50SourceBudget] using hd.trans hg
        · simp [p50Dot, hmul]
      | succ k =>
        let x' : Fin (k + 1) → ℝ := fun i => x i.castSucc
        let y' : Fin (k + 1) → ℝ := fun i => y i.castSucc
        have hprev : P50GammaValid fp.u (k + 1) :=
          p50GammaValid_mono fp.u_nonneg (by omega) hn
        obtain ⟨θ, hθ, hrep⟩ := ih (k + 1) (by omega) x' y' hprev
        let l : Fin (k + 2) := Fin.last (k + 1)
        obtain ⟨da, hda, hadd⟩ :=
          fp.model_add (p50Dot fp (k + 1) x' y') (fp.fl_mul (x l) (y l))
        obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (x l) (y l)
        let θ' : Fin (k + 2) → ℝ :=
          Fin.snoc (fun i => (1 + θ i) * (1 + da) - 1)
            ((1 + dm) * (1 + da) - 1)
        refine ⟨θ', ?_, ?_⟩
        · intro i
          cases i using Fin.lastCases with
          | last =>
            simp only [θ', Fin.snoc_last]
            rw [p50SourceBudget_last]
            have h2 : P50GammaValid fp.u 2 :=
              p50GammaValid_mono fp.u_nonneg (by omega) hn
            have h1 : P50GammaValid fp.u 1 :=
              p50GammaValid_mono fp.u_nonneg (by omega) hn
            exact p50Gamma_step fp.u_nonneg h2
              (hdm.trans (p50Gamma_one_ge fp.u_nonneg h1)) hda
          | cast i =>
            simp only [θ', Fin.snoc_castSucc]
            rw [p50SourceBudget_castSucc]
            have hb : p50SourceBudget (k + 1) i + 1 ≤ k + 2 := by
              have hle := p50SourceBudget_le (k + 1) i
              omega
            exact p50Gamma_step fp.u_nonneg
              (p50GammaValid_mono fp.u_nonneg hb hn) (hθ i) hda
        · calc
            p50Dot fp (k + 2) x y =
                fp.fl_add (p50Dot fp (k + 1) x' y')
                  (fp.fl_mul (x l) (y l)) := by
                    exact p50Dot_succ_succ fp k x y
            _ = ((∑ i : Fin (k + 1), x' i * y' i * (1 + θ i)) +
                  (x l * y l) * (1 + dm)) * (1 + da) := by
                    rw [hadd, hmul, hrep]
            _ = ∑ i : Fin (k + 2), x i * y i * (1 + θ' i) := by
                  conv => rhs; rw [Fin.sum_univ_castSucc]
                  simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]
                  rw [add_mul, Finset.sum_mul]
                  congr 1
                  · apply Finset.sum_congr rfl
                    intro i hi
                    dsimp [x', y']
                    ring
                  · ring

end VSCLReuse
