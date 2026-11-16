import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p37_alternating_sum_factor
    (a r : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (hrec : ∀ k, k + 1 < m → a (k + 1) = r k * a k)
    (hr : ∀ k, k + 1 < m → -1 < r k ∧ r k ≤ 0) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      (∑ k ∈ Finset.range m, a k) = q * a 0 := by
  induction m generalizing a r with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp
    | succ m =>
      have htailrec : ∀ k, k + 1 < m + 1 →
          a (k + 1 + 1) = r (k + 1) * a (k + 1) := by
        intro k hk
        exact hrec (k + 1) (by omega)
      have htailratio : ∀ k, k + 1 < m + 1 →
          -1 < r (k + 1) ∧ r (k + 1) ≤ 0 := by
        intro k hk
        exact hr (k + 1) (by omega)
      obtain ⟨q, hq0, hq1, hsum⟩ :=
        ih (fun k => a (k + 1)) (fun k => r (k + 1)) (by omega)
          htailrec htailratio
      have hrec0 := hrec 0 (by omega)
      have hr0 := hr 0 (by omega)
      refine ⟨1 + q * r 0, ?_, ?_, ?_⟩
      · have hnonneg := mul_nonneg (show 0 ≤ 1 - q by linarith) (show 0 ≤ -r 0 by linarith)
        nlinarith
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hq0) hr0.2]
      · rw [Finset.sum_range_succ', hsum, hrec0]
        ring

private theorem p37_mu_step (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 ≤ n) :
    p37Mu nodes n d (i + 1) x * (nodes (i + d + 1) - x) =
      p37Mu nodes n d i x * (x - nodes i) := by
  have hs : (∏ j ∈ Finset.Ico (i + d + 1) (n + 1), (nodes j - x)) =
      (nodes (i + d + 1) - x) *
        ∏ j ∈ Finset.Ico (i + d + 2) (n + 1), (nodes j - x) := by
    simpa only [show i + d + 1 + 1 = i + d + 2 by omega] using
      Finset.prod_eq_prod_Ico_succ_bot (by omega : i + d + 1 < n + 1)
        (fun j => nodes j - x)
  unfold p37Mu
  rw [Finset.prod_range_succ, hs]
  simp only [show i + 1 + d + 1 = i + d + 2 by omega]
  ring

private theorem p37_mu_pos_central (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1)) (hilo : i ≤ alpha + 1)
    (hihi : alpha < i + d + 1) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  apply mul_pos
  · apply Finset.prod_pos
    intro j hj
    have hjlt : j < i := Finset.mem_range.mp hj
    have hle : nodes j ≤ nodes alpha := hmono.monotone (by omega)
    linarith
  · apply Finset.prod_pos
    intro j hj
    have hjge : i + d + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hle : nodes (alpha + 1) ≤ nodes j := hmono.monotone (by omega)
    linarith

private theorem p37_mu_step_right (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hxhi : x < nodes (alpha + 1))
    (hstart : alpha + 1 ≤ i) (hi : i + d + 1 ≤ n) :
    p37Mu nodes n d (i + 1) x =
        ((x - nodes i) / (nodes (i + d + 1) - x)) * p37Mu nodes n d i x ∧
      -1 < (x - nodes i) / (nodes (i + d + 1) - x) ∧
      (x - nodes i) / (nodes (i + d + 1) - x) ≤ 0 := by
  have hxi : x < nodes i := lt_of_lt_of_le hxhi (hmono.monotone hstart)
  have hgap : nodes i < nodes (i + d + 1) := hmono (by omega)
  have hden : 0 < nodes (i + d + 1) - x := by linarith
  have hnum : x - nodes i ≤ 0 := by linarith
  refine ⟨?_, ?_, div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)⟩
  · have hstep := p37_mu_step nodes n d i x hi
    calc
      p37Mu nodes n d (i + 1) x =
          (p37Mu nodes n d i x * (x - nodes i)) /
            (nodes (i + d + 1) - x) :=
        (eq_div_iff (ne_of_gt hden)).2 hstep
      _ = ((x - nodes i) / (nodes (i + d + 1) - x)) *
          p37Mu nodes n d i x := by ring
  · apply (lt_div_iff₀ hden).2
    nlinarith

private theorem p37_mu_step_left (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hfinish : i + d + 1 ≤ alpha) :
    p37Mu nodes n d i x =
        ((nodes (i + d + 1) - x) / (x - nodes i)) * p37Mu nodes n d (i + 1) x ∧
      -1 < (nodes (i + d + 1) - x) / (x - nodes i) ∧
      (nodes (i + d + 1) - x) / (x - nodes i) ≤ 0 := by
  have hxi : nodes i < x := lt_of_lt_of_le (hmono (by omega))
    (le_of_lt hxlo)
  have hnode : nodes (i + d + 1) ≤ nodes alpha := hmono.monotone hfinish
  have hgap : nodes i < nodes (i + d + 1) := hmono (by omega)
  have hden : 0 < x - nodes i := by linarith
  have hnum : nodes (i + d + 1) - x ≤ 0 := by linarith
  refine ⟨?_, ?_, div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)⟩
  · have hstep := p37_mu_step nodes n d i x (by omega)
    calc
      p37Mu nodes n d i x =
          (p37Mu nodes n d (i + 1) x * (nodes (i + d + 1) - x)) /
            (x - nodes i) :=
        (eq_div_iff (ne_of_gt hden)).2 (by rw [hstep])
      _ = ((nodes (i + d + 1) - x) / (x - nodes i)) *
          p37Mu nodes n d (i + 1) x := by ring
  · apply (lt_div_iff₀ hden).2
    nlinarith

private theorem p37_right_sum_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1))
    (hstart : alpha + 1 ≤ n - d + 1) :
    0 ≤ ∑ i ∈ Finset.Ico (alpha + 1) (n - d + 1), p37Mu nodes n d i x := by
  by_cases hlen : alpha + 1 < n - d + 1
  · let m := n - d + 1 - (alpha + 1)
    let a : ℕ → ℝ := fun k => p37Mu nodes n d (alpha + 1 + k) x
    let r : ℕ → ℝ := fun k =>
      (x - nodes (alpha + 1 + k)) /
        (nodes (alpha + 1 + k + d + 1) - x)
    have hm : 0 < m := by dsimp [m]; omega
    have hrec : ∀ k, k + 1 < m → a (k + 1) = r k * a k := by
      intro k hk
      have hi : alpha + 1 + k + d + 1 ≤ n := by
        dsimp [m] at hk
        omega
      have hs := (p37_mu_step_right nodes hmono n d alpha (alpha + 1 + k) x
        hxhi (by omega) hi).1
      simpa only [a, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    have hratio : ∀ k, k + 1 < m → -1 < r k ∧ r k ≤ 0 := by
      intro k hk
      have hi : alpha + 1 + k + d + 1 ≤ n := by
        dsimp [m] at hk
        omega
      exact (p37_mu_step_right nodes hmono n d alpha (alpha + 1 + k) x
        hxhi (by omega) hi).2
    obtain ⟨q, hq0, hq1, hsum⟩ :=
      p37_alternating_sum_factor a r m hm hrec hratio
    have hmu : 0 < a 0 := by
      dsimp [a]
      simpa using p37_mu_pos_central nodes hmono n d alpha (alpha + 1) x
        hxlo hxhi (by omega) (by omega)
    rw [Finset.sum_Ico_eq_sum_range]
    change 0 ≤ ∑ k ∈ Finset.range m, a k
    rw [hsum]
    exact le_of_lt (mul_pos hq0 hmu)
  · have heq : alpha + 1 = n - d + 1 := by omega
    rw [← heq]
    simp

private theorem p37_left_sum_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 ≤ ∑ i ∈ Finset.range (alpha + 1 - d), p37Mu nodes n d i x := by
  let L := alpha + 1 - d
  by_cases hL : 0 < L
  · let a : ℕ → ℝ := fun k => p37Mu nodes n d (L - 1 - k) x
    let r : ℕ → ℝ := fun k =>
      (nodes ((L - 1 - (k + 1)) + d + 1) - x) /
        (x - nodes (L - 1 - (k + 1)))
    have hrec : ∀ k, k + 1 < L → a (k + 1) = r k * a k := by
      intro k hk
      have hidx : (L - 1 - (k + 1)) + 1 = L - 1 - k := by omega
      have hi : L - 1 - (k + 1) + d + 1 ≤ alpha := by
        dsimp [L] at *
        omega
      have hs := (p37_mu_step_left nodes hmono n d alpha (L - 1 - (k + 1)) x
        halpha hxlo hi).1
      dsimp [a, r]
      rw [hidx] at hs
      exact hs
    have hratio : ∀ k, k + 1 < L → -1 < r k ∧ r k ≤ 0 := by
      intro k hk
      have hi : L - 1 - (k + 1) + d + 1 ≤ alpha := by
        dsimp [L] at *
        omega
      exact (p37_mu_step_left nodes hmono n d alpha (L - 1 - (k + 1)) x
        halpha hxlo hi).2
    obtain ⟨q, hq0, hq1, hsum⟩ :=
      p37_alternating_sum_factor a r L hL hrec hratio
    have hmu : 0 < a 0 := by
      dsimp [a]
      exact p37_mu_pos_central nodes hmono n d alpha (L - 1) x
        hxlo hxhi (by dsimp [L] at *; omega) (by dsimp [L] at *; omega)
    change 0 ≤ ∑ i ∈ Finset.range L, p37Mu nodes n d i x
    calc
      0 ≤ ∑ k ∈ Finset.range L, a k := by
        rw [hsum]
        exact le_of_lt (mul_pos hq0 hmu)
      _ = ∑ i ∈ Finset.range L, p37Mu nodes n d i x := by
        simpa [a] using Finset.sum_range_reflect
          (fun i => p37Mu nodes n d i x) L
  · have hzero : L = 0 := by omega
    simp [L, hzero]

/-- P37-C1: the interior-interval positivity argument in Theorem 1. -/
theorem p37_c1_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Denominator nodes n d x := by
  -- PROOF_START P37-C1-H001
  let L := alpha + 1 - d
  let M := n - d + 1
  let B := min (alpha + 1) M
  have hLB : L < B := by
    dsimp [L, B, M]
    omega
  have hBM : B ≤ M := by simp [B]
  have hBA : B ≤ alpha + 1 := by simp [B]
  have hleft :
      0 ≤ ∑ i ∈ Finset.Ico 0 L, p37Mu nodes n d i x := by
    simpa only [Nat.Ico_zero_eq_range] using
      p37_left_sum_nonneg nodes hmono n d alpha x halpha hxlo hxhi
  have hmid :
      0 < ∑ i ∈ Finset.Ico L B, p37Mu nodes n d i x := by
    apply Finset.sum_pos
    · intro i hi
      have hLi : L ≤ i := (Finset.mem_Ico.mp hi).1
      have hiB : i < B := (Finset.mem_Ico.mp hi).2
      exact p37_mu_pos_central nodes hmono n d alpha i x hxlo hxhi
        (by omega) (by dsimp [L] at hLi; omega)
    · exact ⟨L, Finset.mem_Ico.mpr ⟨le_rfl, hLB⟩⟩
  have hright :
      0 ≤ ∑ i ∈ Finset.Ico B M, p37Mu nodes n d i x := by
    by_cases h : alpha + 1 ≤ M
    · have hB : B = alpha + 1 := min_eq_left h
      rw [hB]
      exact p37_right_sum_nonneg nodes hmono n d alpha x hxlo hxhi h
    · have hB : B = M := min_eq_right (by omega : M ≤ alpha + 1)
      rw [hB]
      simp
  have hsplit1 := Finset.sum_Ico_consecutive
    (fun i => p37Mu nodes n d i x) (Nat.zero_le L) (le_of_lt hLB)
  have hsplit2 := Finset.sum_Ico_consecutive
    (fun i => p37Mu nodes n d i x) (Nat.zero_le B) hBM
  have htotal : 0 < ∑ i ∈ Finset.Ico 0 M, p37Mu nodes n d i x := by
    rw [← hsplit2, ← hsplit1]
    linarith
  simpa only [p37Denominator, Nat.Ico_zero_eq_range, M] using htotal

end VSCLReuse
