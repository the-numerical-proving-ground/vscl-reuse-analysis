import VSCLReuse.P50.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p50AsFPModel (fp : P50FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro a b
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_mul := fp.model_mul
  model_div := by
    intro a b _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_sqrt := by
    intro a _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private lemma p50_gamma_eq (fp : P50FPModel) (k : ℕ) :
    NumStability.gamma (p50AsFPModel fp) k = p50Gamma fp.u k := by
  rfl

private lemma p50_valid_eq (fp : P50FPModel) (k : ℕ) :
    NumStability.gammaValid (p50AsFPModel fp) k ↔ P50GammaValid fp.u k := by
  rfl

private lemma p50_dot_eq (fp : P50FPModel) (n : ℕ) (x y : Fin n → ℝ) :
    NumStability.fl_dotProduct (p50AsFPModel fp) n x y = p50Dot fp n x y := by
  cases n <;> rfl

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
      exact ⟨fun i => i.elim0, (fun i => i.elim0), by simp [p50Dot]⟩
  | succ m =>
      let F := p50AsFPModel fp
      have hvalid : NumStability.gammaValid F (m + 1) := by
        exact (p50_valid_eq fp (m + 1)).2 hn
      obtain ⟨mulDelta, addDelta, hmul, hadd, hexp⟩ :=
        NumStability.dotProduct_factor_expansion_sum_succ F m x y
      let θ : Fin (m + 1) → ℝ :=
        fun i => NumStability.dotProductLocalFactor m mulDelta addDelta i - 1
      refine ⟨θ, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · let deltaTerm : Fin (m + 1) → ℝ := Fin.cons (mulDelta 0) addDelta
          have hdelta : ∀ j, |deltaTerm j| ≤ F.u := by
            intro j
            refine Fin.cases ?_ ?_ j
            · simpa [deltaTerm] using hmul 0
            · intro k
              simpa [deltaTerm] using hadd k
          obtain ⟨e, he, hprod⟩ :=
            NumStability.prod_error_bound F (m + 1) deltaTerm hdelta hvalid
          have hfactor :
              NumStability.dotProductLocalFactor m mulDelta addDelta 0 = 1 + e := by
            rw [← hprod]
            simp [NumStability.dotProductLocalFactor, deltaTerm, Fin.prod_univ_succ]
          simpa [θ, p50SourceBudget, hfactor, p50_gamma_eq] using he
        · intro j
          have hbudget : m - j.val + 1 ≤ m + 1 := by omega
          have hvalid_suffix : NumStability.gammaValid F (m - j.val) :=
            NumStability.gammaValid_mono F (by omega) hvalid
          obtain ⟨e, he, hsuffix⟩ :=
            NumStability.sumSuffixErrorProduct_exists_theta_le_gamma
              F m addDelta hadd j hvalid_suffix
          have hvalid1 : NumStability.gammaValid F 1 :=
            NumStability.gammaValid_mono F (by omega) hvalid
          have hmul1 : |mulDelta j.succ| ≤ NumStability.gamma F 1 :=
            (hmul j.succ).trans (NumStability.u_le_gamma F (by omega) hvalid1)
          have hvalid_comb : NumStability.gammaValid F ((m - j.val) + 1) :=
            NumStability.gammaValid_mono F hbudget hvalid
          obtain ⟨e', he', hcombined⟩ :=
            NumStability.gamma_mul F 1 (m - j.val) (mulDelta j.succ) e
              hmul1 he (by simpa [Nat.add_comm] using hvalid_comb)
          have hfactor :
              NumStability.dotProductLocalFactor m mulDelta addDelta j.succ = 1 + e' := by
            simpa [NumStability.dotProductLocalFactor, hsuffix] using hcombined
          simpa [θ, p50SourceBudget, hfactor, p50_gamma_eq,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using he'
      · rw [← p50_dot_eq, hexp]
        apply Finset.sum_congr rfl
        intro i _
        simp [θ]

end VSCLReuse
