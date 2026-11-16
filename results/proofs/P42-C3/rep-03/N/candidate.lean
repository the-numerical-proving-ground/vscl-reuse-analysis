import VSCLReuse.P42.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p42_valid_mono (u : ℝ) (hu : 0 ≤ u) {n m : ℕ}
    (h : n ≤ m) (hm : P42GammaValid u m) : P42GammaValid u n := by
  unfold P42GammaValid at *
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
  nlinarith

private lemma p42_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P42GammaValid u n) : 0 ≤ p42Gamma u n := by
  unfold p42Gamma P42GammaValid at *
  apply div_nonneg
  · positivity
  · linarith

private lemma p42_gamma_step (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P42GammaValid u (n + 1)) :
    p42Gamma u n + u + p42Gamma u n * u ≤ p42Gamma u (n + 1) := by
  have hn' := p42_valid_mono u hu (Nat.le_succ n) hn
  unfold p42Gamma P42GammaValid at *
  have hn0 : 0 < 1 - (n : ℝ) * u := by linarith
  have hn1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have hnu : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  calc
    (n : ℝ) * u / (1 - (n : ℝ) * u) + u +
        (n : ℝ) * u / (1 - (n : ℝ) * u) * u =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
          field_simp
          push_cast
          ring
    _ ≤ ((n + 1 : ℕ) : ℝ) * u / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hn1
      · push_cast
        nlinarith

private lemma p42_error_extend (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P42GammaValid u (n + 1)) {e δ : ℝ}
    (he : |e| ≤ p42Gamma u n) (hδ : |δ| ≤ u) :
    |e + δ + e * δ| ≤ p42Gamma u (n + 1) := by
  calc
    |e + δ + e * δ| ≤ |e| + |δ| + |e * δ| := by
      have h1 := abs_add_le (e + δ) (e * δ)
      have h2 := abs_add_le e δ
      linarith
    _ ≤ p42Gamma u n + u + p42Gamma u n * u := by
      rw [abs_mul]
      have hnonneg := p42_gamma_nonneg u hu n
        (p42_valid_mono u hu (Nat.le_succ n) hn)
      gcongr
    _ ≤ p42Gamma u (n + 1) := p42_gamma_step u hu n hn

private lemma p42_recursive_backward (fp : P42FPModel) (n : ℕ)
    (v : Fin (n + 1) → ℝ) (hn : P42GammaValid fp.u n) :
    ∃ μ : Fin (n + 1) → ℝ,
      (∀ i, |μ i| ≤ p42Gamma fp.u n) ∧
      p42RecursiveSum fp (n + 1) v = ∑ i, v i * (1 + μ i) := by
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp [p42Gamma]
      · simp [p42RecursiveSum, Fin.foldl_succ, fp.fl_add_zero]
  | succ n ih =>
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      have hn' : P42GammaValid fp.u n :=
        p42_valid_mono fp.u fp.u_nonneg (Nat.le_succ n) hn
      obtain ⟨μ, hμ, hrec⟩ := ih w hn'
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add (p42RecursiveSum fp (n + 1) w)
        (v (Fin.last (n + 1)))
      let ν : Fin (n + 2) → ℝ :=
        Fin.snoc (fun i => μ i + δ + μ i * δ) δ
      refine ⟨ν, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            have hg := p42_gamma_step fp.u fp.u_nonneg n hn
            have hgn := p42_gamma_nonneg fp.u fp.u_nonneg n hn'
            have hp : 0 ≤ p42Gamma fp.u n * fp.u :=
              mul_nonneg hgn fp.u_nonneg
            simp only [ν, Fin.snoc_last]
            linarith
        | cast i =>
            simpa [ν, Fin.snoc_castSucc] using
              p42_error_extend fp.u fp.u_nonneg n hn (hμ i) hδ
      · have hfold : p42RecursiveSum fp (n + 2) v =
            fp.fl_add (p42RecursiveSum fp (n + 1) w) (v (Fin.last (n + 1))) := by
          simp [p42RecursiveSum, Fin.foldl_succ_last, w]
        rw [hfold, hfl, hrec]
        conv => rhs; rw [Fin.sum_univ_castSucc]
        simp only [ν, Fin.snoc_castSucc, Fin.snoc_last]
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring

private def p42_left (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val, by
    have hi := i.isLt
    simp only [pow_succ, mul_two]
    omega⟩

private def p42_right (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val + 2 ^ r, by
    have hi := i.isLt
    simp only [pow_succ, mul_two]
    omega⟩

private lemma p42_sum_cast {n m : ℕ} (h : n = m) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) = ∑ i : Fin m, f (i.cast h.symm) := by
  subst m
  simp

private lemma p42_sum_split (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, f i) = (∑ i : Fin (2 ^ r), f (p42_left r i)) +
      ∑ i : Fin (2 ^ r), f (p42_right r i) := by
  let g : Fin (2 ^ r + 2 ^ r) → ℝ := fun i =>
    f ⟨i.val, by simpa [pow_succ, mul_two] using i.isLt⟩
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ, mul_two]
  calc
    (∑ i : Fin (2 ^ (r + 1)), f i) = ∑ i : Fin (2 ^ r + 2 ^ r), g i := by
      rw [p42_sum_cast hpow f]
      rfl
    _ = (∑ i : Fin (2 ^ r), f (p42_left r i)) +
        ∑ i : Fin (2 ^ r), f (p42_right r i) := by
      rw [Fin.sum_univ_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        simp [g, p42_left, p42_right, Fin.castAdd, Fin.natAdd, Nat.add_comm]

private lemma p42_pairwise_backward (fp : P42FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) (hr : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → ℝ,
      (∀ i, |μ i| ≤ p42Gamma fp.u r) ∧
      p42PairwiseSum fp r v = ∑ i, v i * (1 + μ i) := by
  induction r with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp [p42Gamma]
      · simp [p42PairwiseSum]
  | succ r ih =>
      let vl : Fin (2 ^ r) → ℝ := fun i => v (p42_left r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (p42_right r i)
      have hr' : P42GammaValid fp.u r :=
        p42_valid_mono fp.u fp.u_nonneg (Nat.le_succ r) hr
      obtain ⟨μl, hμl, hl⟩ := ih vl hr'
      obtain ⟨μr, hμr, hright⟩ := ih vr hr'
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (p42PairwiseSum fp r vl) (p42PairwiseSum fp r vr)
      have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
        simp [pow_succ, mul_two]
      let ν : Fin (2 ^ (r + 1)) → ℝ := fun i =>
        Fin.addCases (fun j => μl j + δ + μl j * δ)
          (fun j => μr j + δ + μr j * δ) (i.cast hpow)
      have hνl (i : Fin (2 ^ r)) :
          ν (p42_left r i) = μl i + δ + μl i * δ := by
        have hidx : (p42_left r i).cast hpow = Fin.castAdd (2 ^ r) i := by
          apply Fin.ext
          rfl
        simp only [ν, hidx, Fin.addCases_left]
      have hνr (i : Fin (2 ^ r)) :
          ν (p42_right r i) = μr i + δ + μr i * δ := by
        have hidx : (p42_right r i).cast hpow = Fin.natAdd (2 ^ r) i := by
          apply Fin.ext
          simp [p42_right, Fin.natAdd, Nat.add_comm]
        simp only [ν, hidx, Fin.addCases_right]
      refine ⟨ν, ?_, ?_⟩
      · intro i
        have hb (j : Fin (2 ^ r + 2 ^ r)) :
            |Fin.addCases (fun k => μl k + δ + μl k * δ)
              (fun k => μr k + δ + μr k * δ) j| ≤ p42Gamma fp.u (r + 1) := by
          induction j using Fin.addCases with
          | left j =>
              simpa only [Fin.addCases_left] using
                p42_error_extend fp.u fp.u_nonneg r hr (hμl j) hδ
          | right j =>
              simpa only [Fin.addCases_right] using
                p42_error_extend fp.u fp.u_nonneg r hr (hμr j) hδ
        exact hb (i.cast hpow)
      · have hpw : p42PairwiseSum fp (r + 1) v =
            fp.fl_add (p42PairwiseSum fp r vl) (p42PairwiseSum fp r vr) := by
          rfl
        rw [hpw, hfl, hl, hright]
        conv => rhs; rw [p42_sum_split]
        simp only [hνl, hνr]
        rw [add_mul, Finset.sum_mul, Finset.sum_mul]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private lemma p42_compose_bound {a b e d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : |e| ≤ a) (hd : |d| ≤ b) :
    |e + d + e * d| ≤ a + b + a * b := by
  have h1 := abs_add_le (e + d) (e * d)
  have h2 := abs_add_le e d
  calc
    |e + d + e * d| ≤ |e| + |d| + |e * d| := by linarith
    _ ≤ a + b + a * b := by
      rw [abs_mul]
      gcongr

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
      let y : Fin (2 ^ r) → ℝ := fun i => p42RecursiveSum fp (n + 1) (x i)
      have hlocal (i : Fin (2 ^ r)) :
          ∃ η : Fin (n + 1) → ℝ,
            (∀ j, |η j| ≤ p42Gamma fp.u n) ∧
            y i = ∑ j, x i j * (1 + η j) := by
        exact p42_recursive_backward fp n (x i) hnvalid
      choose η hη hy using hlocal
      obtain ⟨θ, hθ, hout⟩ := p42_pairwise_backward fp r y hrvalid
      let μ : Fin (2 ^ r) → Fin (n + 1) → ℝ :=
        fun i j => η i j + θ i + η i j * θ i
      refine ⟨μ, ?_, ?_⟩
      · intro i j
        exact p42_compose_bound
          (p42_gamma_nonneg fp.u fp.u_nonneg n hnvalid)
          (p42_gamma_nonneg fp.u fp.u_nonneg r hrvalid)
          (hη i j) (hθ i)
      · change p42PairwiseSum fp r y =
          ∑ i : Fin (2 ^ r), ∑ j : Fin (n + 1), x i j * (1 + μ i j)
        rw [hout]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hy i, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [μ]
        ring

end VSCLReuse
