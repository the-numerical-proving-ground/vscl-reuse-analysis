import VSCLReuse.P42.Definitions

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p42ErrPow (u : ℝ) (n : ℕ) : ℝ := (1 + u) ^ n - 1

private lemma p42ErrPow_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ p42ErrPow u n := by
  unfold p42ErrPow
  have h : (1 : ℝ) ≤ 1 + u := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h n
  simpa using hp

private lemma p42ErrPow_succ (u : ℝ) (n : ℕ) :
    p42ErrPow u (n + 1) = p42ErrPow u n + u + p42ErrPow u n * u := by
  simp only [p42ErrPow, pow_succ]
  ring

private lemma p42_error_comp {a d A D : ℝ}
    (ha : |a| ≤ A) (hd : |d| ≤ D) (hA : 0 ≤ A) :
    |a + d + a * d| ≤ A + D + A * D := by
  calc
    |a + d + a * d| ≤ |a| + |d| + |a| * |d| := by
      calc
        _ ≤ |a + d| + |a * d| := abs_add_le _ _
        _ ≤ |a| + |d| + |a| * |d| := by rw [abs_mul]; linarith [abs_add_le a d]
    _ ≤ A + D + A * D := by
      have hmul : |a| * |d| ≤ A * D := mul_le_mul ha hd (abs_nonneg _) hA
      linarith

private lemma p42ErrPow_le_gamma {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (hn : P42GammaValid u n) : p42ErrPow u n ≤ p42Gamma u n := by
  have hpow : ∀ m : ℕ, P42GammaValid u m →
      (1 + u) ^ m ≤ 1 / (1 - (m : ℝ) * u) := by
    intro m
    induction m with
    | zero =>
        intro _
        norm_num
    | succ m ih =>
        intro hm
        have hm' : P42GammaValid u m := by
          unfold P42GammaValid at hm ⊢
          push_cast at hm
          have hmu : 0 ≤ (m : ℝ) * u := mul_nonneg (by positivity) hu
          nlinarith
        have hden : 0 < 1 - (m : ℝ) * u := by
          unfold P42GammaValid at hm'
          linarith
        have hden' : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by
          unfold P42GammaValid at hm
          linarith
        have hstep : (1 + u) / (1 - (m : ℝ) * u) ≤
            1 / (1 - ((m + 1 : ℕ) : ℝ) * u) := by
          apply (div_le_div_iff₀ hden hden').2
          have hs : 0 ≤ ((m : ℝ) + 1) * u ^ 2 :=
            mul_nonneg (by positivity) (sq_nonneg u)
          push_cast
          nlinarith
        rw [pow_succ]
        calc
          (1 + u) ^ m * (1 + u) ≤
              (1 / (1 - (m : ℝ) * u)) * (1 + u) :=
            mul_le_mul_of_nonneg_right (ih hm') (by linarith)
          _ = (1 + u) / (1 - (m : ℝ) * u) := one_div_mul_eq_div _ _
          _ ≤ _ := hstep
  have hd : 0 < 1 - (n : ℝ) * u := by
    unfold P42GammaValid at hn
    linarith
  have hfrac : 1 / (1 - (n : ℝ) * u) - 1 =
      (n : ℝ) * u / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  unfold p42ErrPow p42Gamma
  rw [← hfrac]
  linarith [hpow n hn]

private lemma p42Gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (hn : P42GammaValid u n) : 0 ≤ p42Gamma u n := by
  unfold p42Gamma
  apply div_nonneg
  · exact mul_nonneg (by positivity) hu
  · unfold P42GammaValid at hn
    linarith

private lemma p42RecursiveSum_error (fp : P42FPModel) :
    ∀ n : ℕ, ∀ v : Fin (n + 1) → ℝ,
      ∃ μ : Fin (n + 1) → ℝ,
        (∀ j, |μ j| ≤ p42ErrPow fp.u n) ∧
        p42RecursiveSum fp (n + 1) v = ∑ j, v j * (1 + μ j) := by
  intro n
  induction n with
  | zero =>
      intro v
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro j
        simp [p42ErrPow]
      · simp [p42RecursiveSum, Fin.foldl_succ, fp.fl_add_zero]
  | succ n ih =>
      intro v
      obtain ⟨α, hα, hsum⟩ := ih (fun j => v j.castSucc)
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add
        (p42RecursiveSum fp (n + 1) (fun j => v j.castSucc))
        (v (Fin.last (n + 1)))
      let μ : Fin (n + 1 + 1) → ℝ :=
        Fin.snoc (fun j => α j + δ + α j * δ) δ
      refine ⟨μ, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simp only [μ, Fin.snoc_last]
          have hE := p42ErrPow_nonneg fp.u_nonneg n
          rw [p42ErrPow_succ]
          have hp : 0 ≤ p42ErrPow fp.u n * fp.u :=
            mul_nonneg hE fp.u_nonneg
          linarith
        · intro j
          simp only [μ, Fin.snoc_castSucc]
          rw [p42ErrPow_succ]
          exact p42_error_comp (hα j) hδ (p42ErrPow_nonneg fp.u_nonneg n)
      · have hrec : p42RecursiveSum fp (n + 1 + 1) v =
            fp.fl_add (p42RecursiveSum fp (n + 1) (fun j => v j.castSucc))
              (v (Fin.last (n + 1))) := by
          simp only [p42RecursiveSum, Fin.foldl_succ_last]
        rw [hrec, hadd, hsum]
        calc
          ((∑ j, v j.castSucc * (1 + α j)) + v (Fin.last (n + 1))) * (1 + δ) =
              (∑ j, v j.castSucc * (1 + (α j + δ + α j * δ))) +
                v (Fin.last (n + 1)) * (1 + δ) := by
            rw [add_mul, Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = ∑ j, v j * (1 + μ j) := by
            conv_rhs => rw [Fin.sum_univ_castSucc]
            simp only [μ, Fin.snoc_castSucc, Fin.snoc_last]

private def p42Left (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val, by
    have hi := i.isLt
    simp only [pow_succ, mul_two]
    omega⟩

private def p42Right (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val + 2 ^ r, by
    have hi := i.isLt
    simp only [pow_succ, mul_two]
    omega⟩

private lemma p42_sum_split (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, f i) =
      (∑ i : Fin (2 ^ r), f (p42Left r i)) +
        (∑ i : Fin (2 ^ r), f (p42Right r i)) := by
  have hp : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by simp [pow_succ, mul_two]
  have hs : (∑ i : Fin (2 ^ (r + 1)), f i) =
      ∑ i : Fin (2 ^ r + 2 ^ r), f (Fin.cast hp i) := by
    apply Fintype.sum_equiv (finCongr hp.symm)
    intro i
    simp
  rw [hs, Fin.sum_univ_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Fin.ext
  simp [p42Right]

private lemma p42PairwiseSum_error (fp : P42FPModel) :
    ∀ r : ℕ, ∀ v : Fin (2 ^ r) → ℝ,
      ∃ μ : Fin (2 ^ r) → ℝ,
        (∀ i, |μ i| ≤ p42ErrPow fp.u r) ∧
        p42PairwiseSum fp r v = ∑ i, v i * (1 + μ i) := by
  intro r
  induction r with
  | zero =>
      intro v
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp [p42ErrPow]
      · simp [p42PairwiseSum]
  | succ r ih =>
      intro v
      obtain ⟨α, hα, hsα⟩ := ih (fun i => v (p42Left r i))
      obtain ⟨β, hβ, hsβ⟩ := ih (fun i => v (p42Right r i))
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add
        (p42PairwiseSum fp r (fun i => v (p42Left r i)))
        (p42PairwiseSum fp r (fun i => v (p42Right r i)))
      have hp : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by simp [pow_succ, mul_two]
      let a : Fin (2 ^ r) → ℝ := fun i => α i + δ + α i * δ
      let c : Fin (2 ^ r) → ℝ := fun i => β i + δ + β i * δ
      let μ : Fin (2 ^ (r + 1)) → ℝ :=
        fun i => Fin.append a c (Fin.cast hp.symm i)
      have hμL (i : Fin (2 ^ r)) : μ (p42Left r i) = a i := by
        dsimp [μ]
        have hi : Fin.cast hp.symm (p42Left r i) = Fin.castAdd (2 ^ r) i :=
          Fin.ext rfl
        rw [hi, Fin.append_left]
      have hμR (i : Fin (2 ^ r)) : μ (p42Right r i) = c i := by
        dsimp [μ]
        have hi : Fin.cast hp.symm (p42Right r i) = Fin.natAdd (2 ^ r) i :=
          Fin.ext (by simp [p42Right])
        rw [hi, Fin.append_right]
      refine ⟨μ, ?_, ?_⟩
      · intro i
        have hbound : ∀ k : Fin (2 ^ r + 2 ^ r),
            |Fin.append a c k| ≤ p42ErrPow fp.u (r + 1) := by
          intro k
          refine Fin.addCases ?_ ?_ k
          · intro j
            rw [Fin.append_left]
            change |α j + δ + α j * δ| ≤ _
            rw [p42ErrPow_succ]
            exact p42_error_comp (hα j) hδ (p42ErrPow_nonneg fp.u_nonneg r)
          · intro j
            rw [Fin.append_right]
            change |β j + δ + β j * δ| ≤ _
            rw [p42ErrPow_succ]
            exact p42_error_comp (hβ j) hδ (p42ErrPow_nonneg fp.u_nonneg r)
        exact hbound (Fin.cast hp.symm i)
      · have hpair : p42PairwiseSum fp (r + 1) v =
            fp.fl_add
              (p42PairwiseSum fp r (fun i => v (p42Left r i)))
              (p42PairwiseSum fp r (fun i => v (p42Right r i))) := by
          simp only [p42PairwiseSum]
          congr 1
        rw [hpair, hadd, hsα, hsβ]
        calc
          ((∑ i, v (p42Left r i) * (1 + α i)) +
              (∑ i, v (p42Right r i) * (1 + β i))) * (1 + δ) =
            (∑ i, v (p42Left r i) * (1 + a i)) +
              (∑ i, v (p42Right r i) * (1 + c i)) := by
            rw [add_mul, Finset.sum_mul, Finset.sum_mul]
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              dsimp [a]
              ring
            · apply Finset.sum_congr rfl
              intro i _
              dsimp [c]
              ring
          _ = ∑ i, v i * (1 + μ i) := by
            conv_rhs => rw [p42_sum_split]
            simp only [hμL, hμR]

/-- Theorem 3.1, recursive-block and pairwise-outer specialization. -/
theorem p42_c3_fabsum_backward_error
    (fp : P42FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ)
    (hb : 0 < b)
    (hbvalid : P42GammaValid fp.u (b - 1))
    (hrvalid : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → Fin b → ℝ,
      (∀ i j, |μ i j| ≤
        p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r) ∧
      p42FABsum fp b r x =
        ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
  -- PROOF_START P42-C3-H001
  cases b with
  | zero => omega
  | succ n =>
      have hnvalid : P42GammaValid fp.u n := by simpa using hbvalid
      have hloc : ∀ i : Fin (2 ^ r),
          ∃ α : Fin (n + 1) → ℝ,
            (∀ j, |α j| ≤ p42ErrPow fp.u n) ∧
            p42RecursiveSum fp (n + 1) (x i) =
              ∑ j, x i j * (1 + α j) := by
        intro i
        exact p42RecursiveSum_error fp n (x i)
      choose α hα hsα using hloc
      obtain ⟨β, hβ, hsβ⟩ := p42PairwiseSum_error fp r
        (fun i => p42RecursiveSum fp (n + 1) (x i))
      let μ : Fin (2 ^ r) → Fin (n + 1) → ℝ :=
        fun i j => α i j + β i + α i j * β i
      refine ⟨μ, ?_, ?_⟩
      · intro i j
        have hlocal : |α i j| ≤ p42Gamma fp.u n :=
          (hα i j).trans (p42ErrPow_le_gamma fp.u_nonneg n hnvalid)
        have houter : |β i| ≤ p42Gamma fp.u r :=
          (hβ i).trans (p42ErrPow_le_gamma fp.u_nonneg r hrvalid)
        exact p42_error_comp hlocal houter
          (p42Gamma_nonneg fp.u_nonneg n hnvalid)
      · calc
          p42FABsum fp (n + 1) r x =
              ∑ i, (∑ j, x i j * (1 + α i j)) * (1 + β i) := by
            unfold p42FABsum
            rw [hsβ]
            apply Finset.sum_congr rfl
            intro i _
            rw [hsα i]
          _ = ∑ i, ∑ j, x i j * (1 + μ i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            dsimp [μ]
            ring

end VSCLReuse
