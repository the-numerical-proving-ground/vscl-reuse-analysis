import VSCLReuse.P50.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p50_valid_mono (u : ℝ) (hu : 0 ≤ u) {k n : ℕ}
    (hkn : k ≤ n) (hn : P50GammaValid u n) : P50GammaValid u k := by
  unfold P50GammaValid at *
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hu) hn

private lemma p50_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P50GammaValid u k) : 0 ≤ p50Gamma u k := by
  unfold p50Gamma P50GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p50_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P50GammaValid u (k + 1)) :
    p50Gamma u k + u + p50Gamma u k * u ≤ p50Gamma u (k + 1) := by
  have hk0 := p50_valid_mono u hu (Nat.le_succ k) hk
  have h₁ : 0 < 1 - (k : ℝ) * u := by
    unfold P50GammaValid at hk0
    linarith
  have h₂ : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold P50GammaValid at hk
    linarith
  have hnum : 0 ≤ (k : ℝ) * u + u := add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hu) hu
  unfold p50Gamma
  rw [Nat.cast_add, Nat.cast_one]
  have heq : (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
      (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
      ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ h₁ (by norm_num at h₂ ⊢; nlinarith [h₂])).2
  nlinarith [mul_nonneg hnum hu]

private lemma p50_error_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P50GammaValid u (k + 1)) {a b : ℝ}
    (ha : |a| ≤ p50Gamma u k) (hb : |b| ≤ u) :
    |(1 + a) * (1 + b) - 1| ≤ p50Gamma u (k + 1) := by
  have hg : 0 ≤ p50Gamma u k :=
    p50_gamma_nonneg u hu k (p50_valid_mono u hu (Nat.le_succ k) hk)
  have hm : |a| * |b| ≤ p50Gamma u k * u :=
    mul_le_mul ha hb (abs_nonneg _) hg
  have hs : |a + b + a * b| ≤ |a| + |b| + |a| * |b| := by
    calc
      |a + b + a * b| ≤ |a + b| + |a * b| := abs_add_le _ _
      _ ≤ |a| + |b| + |a * b| := by linarith [abs_add_le a b]
      _ = |a| + |b| + |a| * |b| := by rw [abs_mul]
  have hstep := p50_gamma_step u hu k hk
  have heq : (1 + a) * (1 + b) - 1 = a + b + a * b := by ring
  rw [heq]
  linarith

private lemma p50_dot_succ_last (fp : P50FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p50Dot fp (n + 2) x y =
      fp.fl_add
        (p50Dot fp (n + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [Nat.add_succ, Nat.add_zero, p50Dot]
  rw [Fin.foldl_succ_last]
  simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]

private lemma p50_budget_castSucc (n : ℕ) (i : Fin (n + 1)) :
    p50SourceBudget (n + 2) i.castSucc =
      p50SourceBudget (n + 1) i + 1 := by
  have hi := i.isLt
  simp only [p50SourceBudget, Fin.val_castSucc]
  split_ifs <;> omega

private lemma p50_budget_last (n : ℕ) :
    p50SourceBudget (n + 2) (Fin.last (n + 1)) = 2 := by
  simp [p50SourceBudget, Fin.val_last]

private lemma p50_u_le_gamma_one (u : ℝ) (hu : 0 ≤ u)
    (h : P50GammaValid u 1) : u ≤ p50Gamma u 1 := by
  simpa [p50Gamma] using p50_gamma_step u hu 0 h

private lemma p50_positive (fp : P50FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) (hn : P50GammaValid fp.u (n + 1)) :
    ∃ θ : Fin (n + 1) → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget (n + 1) i)) ∧
      p50Dot fp (n + 1) x y =
        ∑ i : Fin (n + 1), x i * y i * (1 + θ i) := by
  induction n with
  | zero =>
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      refine ⟨fun _ => δ, ?_, ?_⟩
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [p50SourceBudget] using
          (le_trans hδ (p50_u_le_gamma_one fp.u fp.u_nonneg hn))
      · simp [p50Dot, hmul]
  | succ n ih =>
      let x₀ : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let y₀ : Fin (n + 1) → ℝ := fun i => y i.castSucc
      have hprev : P50GammaValid fp.u (n + 1) :=
        p50_valid_mono fp.u fp.u_nonneg (by omega) hn
      obtain ⟨θ, hθ, heq⟩ := ih x₀ y₀ hprev
      obtain ⟨δm, hδm, hmul⟩ := fp.model_mul
        (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
      obtain ⟨δa, hδa, hadd⟩ := fp.model_add
        (p50Dot fp (n + 1) x₀ y₀)
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
      let θ' : Fin (n + 2) → ℝ :=
        Fin.snoc (fun i => (1 + θ i) * (1 + δa) - 1)
          ((1 + δm) * (1 + δa) - 1)
      refine ⟨θ', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [θ', Fin.snoc_last, p50_budget_last]
          have h2 : P50GammaValid fp.u 2 :=
            p50_valid_mono fp.u fp.u_nonneg (by omega) hn
          have h1 : P50GammaValid fp.u 1 :=
            p50_valid_mono fp.u fp.u_nonneg (by omega) hn
          exact p50_error_step fp.u fp.u_nonneg 1 h2
            (le_trans hδm (p50_u_le_gamma_one fp.u fp.u_nonneg h1)) hδa
        · simp only [θ', Fin.snoc_castSucc, p50_budget_castSucc]
          have hj : p50SourceBudget (n + 1) j + 1 ≤ n + 2 := by
            unfold p50SourceBudget
            split_ifs <;> omega
          exact p50_error_step fp.u fp.u_nonneg
            (p50SourceBudget (n + 1) j)
            (p50_valid_mono fp.u fp.u_nonneg hj hn) (hθ j) hδa
      · rw [p50_dot_succ_last, hadd, hmul, heq]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [θ', Fin.snoc_castSucc, Fin.snoc_last, x₀, y₀]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · ring

/-- P50-C2: complete named Theorem 3.5, the position-specific diagonal
backward-error representation for the sequential dot product. -/
theorem p50_c2_full_theorem35 (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P50GammaValid fp.u n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget n i)) ∧
      p50Dot fp n x y =
        ∑ i : Fin n, x i * y i * (1 + θ i) := by
  -- PROOF_START P50-C2-H001
  cases n with
  | zero =>
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i
        exact i.elim0
      · simp [p50Dot]
  | succ n =>
      exact p50_positive fp n x y hn

end VSCLReuse
