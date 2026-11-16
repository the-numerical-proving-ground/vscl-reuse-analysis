import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private noncomputable def p37Pre (nodes : ℕ → ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range i, (x - nodes j)

private noncomputable def p37Post (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico (i + d + 1) (n + 1), (nodes j - x)

private lemma p37_pre_succ (nodes : ℕ → ℝ) (i : ℕ) (x : ℝ) :
    p37Pre nodes (i + 1) x = p37Pre nodes i x * (x - nodes i) := by
  simp [p37Pre, Finset.prod_range_succ]

private lemma p37_post_step (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 ≤ n) :
    p37Post nodes n d i x =
      (nodes (i + d + 1) - x) * p37Post nodes n d (i + 1) x := by
  unfold p37Post
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : i + d + 1 < n + 1)]
  have heq : i + d + 1 + 1 = i + 1 + d + 1 := by omega
  rw [heq]

private lemma p37_mu_pair (nodes : ℕ → ℝ)
    (n d i : ℕ) (x : ℝ) (hi : i + d + 1 ≤ n) :
    p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x =
      p37Pre nodes i x * p37Post nodes n d (i + 1) x *
        (nodes (i + d + 1) - nodes i) := by
  rw [show p37Mu nodes n d i x =
      p37Pre nodes i x * p37Post nodes n d i x from rfl,
    show p37Mu nodes n d (i + 1) x =
      p37Pre nodes (i + 1) x * p37Post nodes n d (i + 1) x from rfl,
    p37_pre_succ, p37_post_step nodes n d i x hi]
  ring

private lemma p37_pre_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha i : ℕ) (x : ℝ) (hi : i ≤ alpha + 1)
    (hxlo : nodes alpha < x) : 0 < p37Pre nodes i x := by
  unfold p37Pre
  apply Finset.prod_pos
  intro j hj
  have hj' : j ≤ alpha := by
    simp only [Finset.mem_range] at hj
    omega
  exact sub_pos.mpr ((hmono.monotone hj').trans_lt hxlo)

private lemma p37_post_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hi : alpha + 1 ≤ i + d + 1)
    (hxhi : x < nodes (alpha + 1)) : 0 < p37Post nodes n d i x := by
  unfold p37Post
  apply Finset.prod_pos
  intro j hj
  have hj' : alpha + 1 ≤ j := by
    simp only [Finset.mem_Ico] at hj
    omega
  exact sub_pos.mpr (hxhi.trans_le (hmono.monotone hj'))

private lemma p37_right_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (hdn : d ≤ n)
    (hxhi : x < nodes (alpha + 1)) (k : ℕ) :
    ∀ a : ℕ, alpha + 1 ≤ a → a + k ≤ n - d + 1 →
      0 ≤ p37Pre nodes a x →
      0 ≤ ∑ i ∈ Finset.Ico a (a + k), p37Mu nodes n d i x := by
  induction k using Nat.twoStepInduction with
  | zero =>
      intro a ha hbound hpre
      simp
  | one =>
      intro a ha hbound hpre
      have hpost : 0 ≤ p37Post nodes n d a x :=
        le_of_lt (p37_post_pos nodes hmono n d alpha a x (by omega) hxhi)
      simpa [p37Mu, p37Pre, p37Post] using mul_nonneg hpre hpost
  | more k hk hk1 =>
      intro a ha hbound hpre
      have hb : a + d + 1 ≤ n := by omega
      have hgap : 0 ≤ nodes (a + d + 1) - nodes a :=
        le_of_lt (sub_pos.mpr (hmono (by omega : a < a + d + 1)))
      have hpost : 0 ≤ p37Post nodes n d (a + 1) x :=
        le_of_lt (p37_post_pos nodes hmono n d alpha (a + 1) x (by omega) hxhi)
      have hpair : 0 ≤ p37Mu nodes n d a x + p37Mu nodes n d (a + 1) x := by
        rw [p37_mu_pair nodes n d a x hb]
        exact mul_nonneg (mul_nonneg hpre hpost) hgap
      have hxa : x - nodes a ≤ 0 :=
        sub_nonpos.mpr (le_of_lt (hxhi.trans_le (hmono.monotone ha)))
      have hxa1 : x - nodes (a + 1) ≤ 0 :=
        sub_nonpos.mpr (le_of_lt (hxhi.trans_le (hmono.monotone (by omega : alpha + 1 ≤ a + 1))))
      have hpre2 : 0 ≤ p37Pre nodes (a + 2) x := by
        have heq : p37Pre nodes (a + 2) x =
            p37Pre nodes a x * ((x - nodes a) * (x - nodes (a + 1))) := by
          rw [show a + 2 = (a + 1) + 1 by omega, p37_pre_succ, p37_pre_succ]
          ring
        rw [heq]
        exact mul_nonneg hpre (mul_nonneg_of_nonpos_of_nonpos hxa hxa1)
      have htail := hk (a + 2) (by omega) (by omega) hpre2
      have hsplit :
          (∑ i ∈ Finset.Ico a (a + (k + 2)), p37Mu nodes n d i x) =
          (p37Mu nodes n d a x + p37Mu nodes n d (a + 1) x) +
            ∑ i ∈ Finset.Ico (a + 2) (a + 2 + k), p37Mu nodes n d i x := by
        have h := Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x)
          (by omega : a ≤ a + 2) (by omega : a + 2 ≤ a + (k + 2))
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + 2)] at h
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : a + 1 < a + 2)] at h
        simpa [show a + 1 + 1 = a + 2 by omega, show a + (k + 2) = a + 2 + k by omega] using h.symm
      rw [hsplit]
      exact add_nonneg hpair htail

private lemma p37_left_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (hdpos : 0 < d) (hdalpha : d ≤ alpha + 1)
    (halpha : alpha < n) (hxlo : nodes alpha < x) (k : ℕ) :
    ∀ a : ℕ, a + k ≤ alpha + 1 - d →
      (k = 0 ∨ 0 ≤ p37Post nodes n d (a + k - 1) x) →
      0 ≤ ∑ i ∈ Finset.Ico a (a + k), p37Mu nodes n d i x := by
  induction k using Nat.twoStepInduction with
  | zero =>
      intro a hbound hpost
      simp
  | one =>
      intro a hbound hpost
      have hpre : 0 ≤ p37Pre nodes a x :=
        le_of_lt (p37_pre_pos nodes hmono alpha a x (by omega) hxlo)
      have hpost' : 0 ≤ p37Post nodes n d a x := by
        rcases hpost with h | h
        · omega
        · simpa using h
      simpa [p37Mu, p37Pre, p37Post] using mul_nonneg hpre hpost'
  | more k hk hk1 =>
      intro a hbound hpost
      let i := a + k
      have hi : i + d + 1 ≤ n := by
        dsimp [i]
        omega
      have hi_alpha : i + d + 1 ≤ alpha := by
        dsimp [i]
        omega
      have hpre : 0 ≤ p37Pre nodes i x :=
        le_of_lt (p37_pre_pos nodes hmono alpha i x (by omega) hxlo)
      have hpost' : 0 ≤ p37Post nodes n d (i + 1) x := by
        rcases hpost with h | h
        · omega
        · simpa [i, show a + (k + 2) - 1 = a + k + 1 by omega] using h
      have hgap : 0 ≤ nodes (i + d + 1) - nodes i :=
        le_of_lt (sub_pos.mpr (hmono (by omega : i < i + d + 1)))
      have hpair : 0 ≤ p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
        rw [p37_mu_pair nodes n d i x hi]
        exact mul_nonneg (mul_nonneg hpre hpost') hgap
      have hrecPost : k = 0 ∨ 0 ≤ p37Post nodes n d (a + k - 1) x := by
        by_cases hkzero : k = 0
        · exact Or.inl hkzero
        · right
          have hi0 : 0 < i := by dsimp [i]; omega
          have hstep1 :
              p37Post nodes n d (i - 1) x =
                (nodes (i + d) - x) * p37Post nodes n d i x := by
            have heq1 : i - 1 + d + 1 = i + d := by omega
            have heq2 : i - 1 + 1 = i := by omega
            simpa only [heq1, heq2] using
              (p37_post_step nodes n d (i - 1) x (by omega))
          have hstep2 := p37_post_step nodes n d i x hi
          have hneg1 : nodes (i + d) - x ≤ 0 :=
            sub_nonpos.mpr (le_of_lt ((hmono.monotone (by omega : i + d ≤ alpha)).trans_lt hxlo))
          have hneg2 : nodes (i + d + 1) - x ≤ 0 :=
            sub_nonpos.mpr (le_of_lt ((hmono.monotone hi_alpha).trans_lt hxlo))
          have hpostrec : 0 ≤ p37Post nodes n d (i - 1) x := by
            rw [hstep1, hstep2]
            simpa only [mul_assoc] using
              (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hneg1 hneg2) hpost')
          simpa [i] using hpostrec
      have htail := hk a (by omega) hrecPost
      have hsplit :
          (∑ j ∈ Finset.Ico a (a + (k + 2)), p37Mu nodes n d j x) =
            (∑ j ∈ Finset.Ico a (a + k), p37Mu nodes n d j x) +
              (p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x) := by
        rw [show a + (k + 2) = (a + k + 1) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : a ≤ a + k + 1),
          show a + k + 1 = (a + k) + 1 by omega,
          Finset.sum_Ico_succ_top (by omega : a ≤ a + k)]
        dsimp [i]
        ring
      rw [hsplit]
      exact add_nonneg htail hpair

private lemma p37_middle_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (hdpos : 0 < d) (hdn : d ≤ n)
    (halpha : alpha < n) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1)) :
    0 < ∑ i ∈ Finset.Ico (alpha + 1 - d)
      (min (alpha + 1) (n - d + 1)), p37Mu nodes n d i x := by
  have hleft : alpha + 1 - d < alpha + 1 := by omega
  have hright : alpha + 1 - d < n - d + 1 := by omega
  apply Finset.sum_pos
  · intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hpre : 0 < p37Pre nodes i x :=
      p37_pre_pos nodes hmono alpha i x (by omega) hxlo
    have hpost : 0 < p37Post nodes n d i x :=
      p37_post_pos nodes hmono n d alpha i x (by omega) hxhi
    change 0 < p37Pre nodes i x * p37Post nodes n d i x
    exact mul_pos hpre hpost
  · exact Finset.nonempty_Ico.mpr (lt_min hleft hright)

/-- P37-C1: the interior-interval positivity argument in Theorem 1. -/
theorem p37_c1_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Denominator nodes n d x := by
  -- PROOF_START P37-C1-H001
  let N := n - d + 1
  let L := alpha + 1 - d
  let M := min (alpha + 1) N
  have hLN : L ≤ N := by dsimp [L, N]; omega
  have hLM : L ≤ M := by dsimp [L, M, N]; omega
  have hMN : M ≤ N := min_le_right _ _
  have hleft : 0 ≤ ∑ i ∈ Finset.Ico 0 L, p37Mu nodes n d i x := by
    by_cases hdalpha : d ≤ alpha + 1
    · have hpost : L = 0 ∨ 0 ≤ p37Post nodes n d (L - 1) x := by
        by_cases hzero : L = 0
        · exact Or.inl hzero
        · right
          have heq : alpha + 1 ≤ (L - 1) + d + 1 := by
            dsimp [L]
            omega
          exact le_of_lt (p37_post_pos nodes hmono n d alpha (L - 1) x heq hxhi)
      have h := p37_left_tail_nonneg nodes hmono n d alpha x hdpos hdalpha
        halpha hxlo L 0 (by simp [L]) (by simpa using hpost)
      simpa using h
    · have hzero : L = 0 := by dsimp [L]; omega
      simp [hzero]
  have hmid : 0 < ∑ i ∈ Finset.Ico L M, p37Mu nodes n d i x := by
    exact p37_middle_pos nodes hmono n d alpha x hdpos hdn halpha hxlo hxhi
  have hright : 0 ≤ ∑ i ∈ Finset.Ico M N, p37Mu nodes n d i x := by
    by_cases hRN : alpha + 1 ≤ N
    · have hM : M = alpha + 1 := min_eq_left hRN
      have hpre : 0 ≤ p37Pre nodes M x :=
        le_of_lt (p37_pre_pos nodes hmono alpha M x (by omega) hxlo)
      have h := p37_right_tail_nonneg nodes hmono n d alpha x hdn hxhi
        (N - M) M (by omega) (by omega) hpre
      simpa [Nat.add_sub_of_le hMN] using h
    · have hM : M = N := min_eq_right (by omega : N ≤ alpha + 1)
      simp [hM]
  have hsum :
      (∑ i ∈ Finset.Ico 0 N, p37Mu nodes n d i x) =
        (∑ i ∈ Finset.Ico 0 L, p37Mu nodes n d i x) +
        (∑ i ∈ Finset.Ico L M, p37Mu nodes n d i x) +
        (∑ i ∈ Finset.Ico M N, p37Mu nodes n d i x) := by
    calc
      (∑ i ∈ Finset.Ico 0 N, p37Mu nodes n d i x) =
          (∑ i ∈ Finset.Ico 0 L, p37Mu nodes n d i x) +
            (∑ i ∈ Finset.Ico L N, p37Mu nodes n d i x) :=
        (Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x)
          (Nat.zero_le L) hLN).symm
      _ = _ := by
        rw [← Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x) hLM hMN]
        ring
  unfold p37Denominator
  change 0 < ∑ i ∈ Finset.range N, p37Mu nodes n d i x
  rw [← Nat.Ico_zero_eq_range]
  rw [hsum]
  positivity

end VSCLReuse
