import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p37_mu_step (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 ≤ n) :
    (nodes (i + d + 1) - x) * p37Mu nodes n d (i + 1) x =
      (x - nodes i) * p37Mu nodes n d i x := by
  have hIco : i + d + 1 < n + 1 := by omega
  have hIco' : i + 1 + d + 1 = i + d + 1 + 1 := by omega
  rw [p37Mu, p37Mu, Finset.prod_range_succ, hIco',
    Finset.prod_eq_prod_Ico_succ_bot hIco]
  ring

private theorem p37_alt_sum_nonneg (f : ℕ → ℝ) (m : ℕ)
    (h0 : 0 ≤ f 0)
    (hstep : ∀ i, i + 1 < m →
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ f (i + 1) = -r * f i) :
    0 ≤ ∑ i ∈ Finset.range m, f i := by
  induction m using Nat.twoStepInduction generalizing f with
  | zero => simp
  | one => simpa using h0
  | more m ih0 ih1 =>
      obtain ⟨r₀, hr₀pos, hr₀le, heq₀⟩ := hstep 0 (by omega)
      have hpair : 0 ≤ f 0 + f 1 := by
        rw [heq₀]
        nlinarith [mul_nonneg (sub_nonneg.mpr hr₀le) h0]
      have htail : 0 ≤ ∑ i ∈ Finset.range m, f (i + 2) := by
        cases m with
        | zero => simp
        | succ k =>
            obtain ⟨r₁, hr₁pos, hr₁le, heq₁⟩ := hstep 1 (by omega)
            have h2pos : 0 ≤ f 2 := by
              rw [heq₁, heq₀]
              convert mul_nonneg (mul_nonneg hr₁pos hr₀pos) h0 using 1; ring
            apply ih0 (fun i => f (i + 2)) h2pos
            intro i hi
            obtain ⟨r, hrpos, hrle, heq⟩ := hstep (i + 2) (by omega)
            refine ⟨r, hrpos, hrle, ?_⟩
            simpa only [show i + 2 + 1 = i + 1 + 2 by omega] using heq
      rw [show m + 2 = 2 + m by omega, Finset.sum_range_add]
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.add_comm 2] using add_nonneg hpair htail

private theorem p37_mu_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1))
    (hi : i ≤ alpha + 1) (hdi : alpha + 1 ≤ i + d + 1) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  apply mul_pos
  · apply Finset.prod_pos
    intro j hj
    have hj' : j ≤ alpha := by
      have := Finset.mem_range.mp hj
      omega
    exact sub_pos.mpr (lt_of_le_of_lt (hmono.monotone hj') hxlo)
  · apply Finset.prod_pos
    intro j hj
    have hj' : alpha + 1 ≤ j := by
      have := (Finset.mem_Ico.mp hj).1
      omega
    exact sub_pos.mpr (lt_of_lt_of_le hxhi (hmono.monotone hj'))

private theorem p37_mu_right_ratio (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hxhi : x < nodes (alpha + 1))
    (hi : alpha + 1 ≤ i) (hin : i + d + 1 ≤ n) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      p37Mu nodes n d (i + 1) x = -r * p37Mu nodes n d i x := by
  have hni : x < nodes i := lt_of_lt_of_le hxhi (hmono.monotone hi)
  have hnext : nodes i < nodes (i + d + 1) := hmono (by omega)
  have hden : 0 < nodes (i + d + 1) - x := by linarith
  let r : ℝ := (nodes i - x) / (nodes (i + d + 1) - x)
  refine ⟨r, div_nonneg (by linarith) (le_of_lt hden), ?_, ?_⟩
  · exact (div_le_one hden).2 (by linarith)
  · have hstep := p37_mu_step nodes n d i x hin
    apply (mul_left_cancel₀ (ne_of_gt hden))
    rw [hstep]
    dsimp [r]
    field_simp
    ring

private theorem p37_mu_left_ratio (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (hi : i + d + 1 ≤ alpha) (halpha : alpha < n) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      p37Mu nodes n d i x = -r * p37Mu nodes n d (i + 1) x := by
  have hni : nodes i < x := lt_of_le_of_lt (hmono.monotone (by omega)) hxlo
  have hnext : nodes i < nodes (i + d + 1) := hmono (by omega)
  have hnxtx : nodes (i + d + 1) < x := lt_of_le_of_lt (hmono.monotone hi) hxlo
  have hden : 0 < x - nodes i := by linarith
  let r : ℝ := (x - nodes (i + d + 1)) / (x - nodes i)
  refine ⟨r, div_nonneg (by linarith) (le_of_lt hden), ?_, ?_⟩
  · exact (div_le_one hden).2 (by linarith)
  · have hstep := p37_mu_step nodes n d i x (by omega)
    apply (mul_left_cancel₀ (ne_of_gt hden))
    dsimp [r]
    field_simp
    nlinarith [hstep]

/-- P37-C1: the interior-interval positivity argument in Theorem 1. -/
theorem p37_c1_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Denominator nodes n d x := by
  -- PROOF_START P37-C1-H001
  let N := n - d + 1
  let a := alpha + 1 - d
  let b := alpha + 1
  let c := min b N
  have haN : a ≤ N := by dsimp [a, N]; omega
  have hac : a ≤ c := by dsimp [a, b, c, N]; omega
  have hcN : c ≤ N := by dsimp [c]; omega
  have hac' : a < c := by dsimp [a, b, c, N]; omega
  have hleft : 0 ≤ ∑ i ∈ Finset.range a, p37Mu nodes n d i x := by
    rw [← Finset.sum_range_reflect (fun i => p37Mu nodes n d i x) a]
    apply p37_alt_sum_nonneg
    · have hpos := p37_mu_pos nodes hmono n d alpha (a - 1) x hxlo hxhi
        (by dsimp [a]; omega) (by dsimp [a]; omega)
      simpa using le_of_lt hpos
    · intro j hj
      let i := a - 1 - (j + 1)
      have hi : i + d + 1 ≤ alpha := by
        dsimp [i, a] at *
        omega
      obtain ⟨r, hrpos, hrle, heq⟩ :=
        p37_mu_left_ratio nodes hmono n d alpha i x hxlo hi halpha
      refine ⟨r, hrpos, hrle, ?_⟩
      have hidx : a - 1 - j = i + 1 := by dsimp [i]; omega
      simpa only [hidx] using heq
  have hmiddle : 0 < ∑ i ∈ Finset.Ico a c, p37Mu nodes n d i x := by
    apply Finset.sum_pos
    · intro i hi
      have hia := (Finset.mem_Ico.mp hi).1
      have hic := (Finset.mem_Ico.mp hi).2
      apply p37_mu_pos nodes hmono n d alpha i x hxlo hxhi
      · dsimp [c, b] at hic
        omega
      · dsimp [a] at hia
        omega
    · exact Finset.nonempty_Ico.mpr hac'
  have hright : 0 ≤ ∑ i ∈ Finset.Ico c N, p37Mu nodes n d i x := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply p37_alt_sum_nonneg
    · have hpos := p37_mu_pos nodes hmono n d alpha c x hxlo hxhi
        (by dsimp [c, b]; omega) (by dsimp [c, b, N]; omega)
      simpa using le_of_lt hpos
    · intro j hj
      have hcb : c = b := by dsimp [c]; omega
      have hi : c + j + d + 1 ≤ n := by dsimp [N] at hj; omega
      obtain ⟨r, hrpos, hrle, heq⟩ :=
        p37_mu_right_ratio nodes hmono n d alpha (c + j) x hxhi
          (by dsimp [b] at hcb; omega) hi
      refine ⟨r, hrpos, hrle, ?_⟩
      simpa only [Nat.add_assoc] using heq
  unfold p37Denominator
  calc
    0 < (∑ i ∈ Finset.range a, p37Mu nodes n d i x) +
          (∑ i ∈ Finset.Ico a c, p37Mu nodes n d i x) +
          (∑ i ∈ Finset.Ico c N, p37Mu nodes n d i x) := by
            linarith
    _ = ∑ i ∈ Finset.range N, p37Mu nodes n d i x := by
      rw [← Finset.sum_range_add_sum_Ico _ haN,
        ← Finset.sum_Ico_consecutive _ hac hcN]
      ring
    _ = ∑ i ∈ Finset.range (n - d + 1), p37Mu nodes n d i x := rfl

end VSCLReuse
