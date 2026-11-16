import VSCLReuse.P50.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p50_gamma_one_bound (u : ℝ) (hu : 0 ≤ u) (h : u < 1) :
    u ≤ p50Gamma u 1 := by
  unfold p50Gamma
  norm_num
  apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
  nlinarith

private theorem p50_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (h : ((k + 1 : ℕ) : ℝ) * u < 1) (a b : ℝ)
    (ha : |a| ≤ p50Gamma u k) (hb : |b| ≤ u) :
    |(1 + a) * (1 + b) - 1| ≤ p50Gamma u (k + 1) := by
  let t : ℝ := (k : ℝ) * u
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hu
  have htu : t + u < 1 := by
    simpa [t, Nat.cast_add, add_mul] using h
  have hden : 0 < 1 - t := by linarith
  have hden' : 0 < 1 - t - u := by linarith
  have hgam : p50Gamma u k = t / (1 - t) := rfl
  have hgam' : p50Gamma u (k + 1) = (t + u) / (1 - t - u) := by
    simp only [p50Gamma, Nat.cast_add, Nat.cast_one, add_mul]
    dsimp [t]
    congr 1 <;> ring
  have hgeom : t / (1 - t) + u + t / (1 - t) * u = (t + u) / (1 - t) := by
    field_simp
    ring
  have hfrac : (t + u) / (1 - t) ≤ (t + u) / (1 - t - u) := by
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [mul_nonneg (add_nonneg ht hu) hu]
  have hsum : |a + b + a * b| ≤ p50Gamma u k + u + p50Gamma u k * u := by
    calc
      |a + b + a * b| ≤ |a| + |b| + |a * b| := by
        calc
          _ ≤ |a + b| + |a * b| := abs_add_le _ _
          _ ≤ (|a| + |b|) + |a * b| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ p50Gamma u k + u + p50Gamma u k * u := by
        rw [abs_mul]
        have hg_nonneg : 0 ≤ p50Gamma u k := by rw [hgam]; positivity
        nlinarith [mul_le_mul ha hb (abs_nonneg _) hg_nonneg]
  calc
    |(1 + a) * (1 + b) - 1| = |a + b + a * b| := by congr 1; ring
    _ ≤ p50Gamma u k + u + p50Gamma u k * u := hsum
    _ = (t + u) / (1 - t) := by rw [hgam, hgeom]
    _ ≤ (t + u) / (1 - t - u) := hfrac
    _ = p50Gamma u (k + 1) := hgam'.symm

private theorem p50_dot_succ_succ (fp : P50FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p50Dot fp (n + 2) x y =
      fp.fl_add
        (p50Dot fp (n + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [p50Dot, Fin.foldl_succ_last]
  congr 1

private theorem p50_budget_le (n : ℕ) (i : Fin n) :
    p50SourceBudget n i ≤ n := by
  unfold p50SourceBudget
  split_ifs <;> omega

private theorem p50_budget_castSucc (n : ℕ) (i : Fin (n + 1)) :
    p50SourceBudget (n + 2) i.castSucc = p50SourceBudget (n + 1) i + 1 := by
  unfold p50SourceBudget
  simp only [Fin.val_castSucc]
  split_ifs <;> omega

private theorem p50_budget_last (n : ℕ) :
    p50SourceBudget (n + 2) (Fin.last (n + 1)) = 2 := by
  simp [p50SourceBudget]

/-- P50-C2: complete named Theorem 3.5, the position-specific diagonal
backward-error representation for the sequential dot product. -/
theorem p50_c2_full_theorem35 (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P50GammaValid fp.u n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget n i)) ∧
      p50Dot fp n x y =
        ∑ i : Fin n, x i * y i * (1 + θ i) := by
  -- PROOF_START P50-C2-H001
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i; exact i.elim0
      · simp [p50Dot]
  | one =>
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      refine ⟨fun _ => δ, ?_, ?_⟩
      · intro i
        have hu : fp.u < 1 := by simpa [P50GammaValid] using hn
        simpa [p50SourceBudget] using le_trans hδ
          (p50_gamma_one_bound fp.u fp.u_nonneg hu)
      · simp [p50Dot, hmul]
  | more k _ ih =>
      let x' : Fin (k + 1) → ℝ := fun i => x i.castSucc
      let y' : Fin (k + 1) → ℝ := fun i => y i.castSucc
      have hprev : P50GammaValid fp.u (k + 1) := by
        have hc : (k + 1 : ℕ) ≤ k + 2 := by omega
        have hr : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hc
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hr fp.u_nonneg) hn
      obtain ⟨θ, hθ, hdot⟩ := ih x' y' hprev
      let last : Fin (k + 2) := Fin.last (k + 1)
      obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (x last) (y last)
      obtain ⟨δa, hδa, hadd⟩ :=
        fp.model_add (p50Dot fp (k + 1) x' y') (fp.fl_mul (x last) (y last))
      let θ' : Fin (k + 2) → ℝ :=
        Fin.snoc (fun i => (1 + θ i) * (1 + δa) - 1)
          ((1 + δm) * (1 + δa) - 1)
      refine ⟨θ', ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            have htwo : (2 : ℝ) * fp.u < 1 := by
              have hc : (2 : ℕ) ≤ k + 2 := by omega
              have hr : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hc
              exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hr fp.u_nonneg) hn
            have hu : fp.u < 1 := by nlinarith [fp.u_nonneg]
            simpa [θ', p50_budget_last] using
              p50_gamma_step fp.u fp.u_nonneg 1 (by norm_num at htwo ⊢; exact htwo)
                δm δa (le_trans hδm (p50_gamma_one_bound fp.u fp.u_nonneg hu)) hδa
        | cast i =>
            have hb : p50SourceBudget (k + 2) i.castSucc ≤ k + 2 :=
              p50_budget_le _ _
            have hc : (p50SourceBudget (k + 2) i.castSucc : ℝ) ≤
                ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hb
            have hs : (((p50SourceBudget (k + 1) i + 1 : ℕ) : ℝ) * fp.u) < 1 := by
              rw [← p50_budget_castSucc]
              exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hn
            simpa [θ', p50_budget_castSucc] using
              p50_gamma_step fp.u fp.u_nonneg (p50SourceBudget (k + 1) i)
                hs (θ i) δa (hθ i) hδa
      · rw [p50_dot_succ_succ]
        change fp.fl_add (p50Dot fp (k + 1) x' y')
            (fp.fl_mul (x last) (y last)) = _
        rw [hadd, hmul, hdot]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          ring
        · ring

end VSCLReuse
