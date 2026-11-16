import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p37_prod_pos_of_even_negative
    (f : ℕ → ℝ) (a b : ℕ)
    (hf : ∀ j ∈ Finset.Ico a b, f j < 0)
    (he : Even (b - a)) :
    0 < ∏ j ∈ Finset.Ico a b, f j := by
  have hp : 0 < ∏ j ∈ Finset.Ico a b, -f j :=
    Finset.prod_pos fun j hj => neg_pos.mpr (hf j hj)
  rw [Finset.prod_neg, Nat.card_Ico, he.neg_one_pow, one_mul] at hp
  exact hp

private lemma p37_sum_pairs_nonneg (f : ℕ → ℝ) (k : ℕ)
    (hpair : ∀ j, 2*j+1 < k → 0 ≤ f (2*j) + f (2*j+1))
    (hsingle : ∀ j, 2*j < k → 0 ≤ f (2*j)) :
    0 ≤ ∑ j ∈ Finset.range k, f j := by
  have heven : ∀ m : ℕ, 2*m ≤ k → 0 ≤ ∑ j ∈ Finset.range (2*m), f j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        have hform : 2 * (m + 1) = (2*m+1)+1 := by omega
        rw [hform, Finset.sum_range_succ, Finset.sum_range_succ]
        linarith [ih (by omega), hpair m (by omega)]
  rcases (show k = 2*(k/2) ∨ k = 2*(k/2)+1 by omega) with h | h
  · rw [h]
    exact heven (k/2) (by omega)
  · rw [h, Finset.sum_range_succ]
    exact add_nonneg (heven (k/2) (by omega)) (hsingle (k/2) (by omega))

private lemma p37_prefix_pos_even (nodes : ℕ → ℝ) (alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (hi : alpha + 1 ≤ i) (he : Even (i - (alpha + 1))) :
    0 < ∏ j ∈ Finset.range i, (x - nodes j) := by
  rw [← Finset.prod_range_mul_prod_Ico (fun j => x - nodes j) hi]
  apply mul_pos
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hleft j (by have := Finset.mem_range.mp hj; omega))
  · apply p37_prod_pos_of_even_negative
    · intro j hj
      exact sub_neg.mpr (hright j (Finset.mem_Ico.mp hj).1)
    · exact he

private lemma p37_suffix_pos_even (nodes : ℕ → ℝ) (n alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (halpha : alpha < n) (hi : i ≤ alpha + 1)
    (he : Even (alpha + 1 - i)) :
    0 < ∏ j ∈ Finset.Ico i (n + 1), (nodes j - x) := by
  rw [← Finset.prod_Ico_consecutive (fun j => nodes j - x) hi (by omega : alpha + 1 ≤ n + 1)]
  apply mul_pos
  · apply p37_prod_pos_of_even_negative
    · intro j hj
      exact sub_neg.mpr (hleft j (by have := (Finset.mem_Ico.mp hj).2; omega))
    · exact he
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hright j (Finset.mem_Ico.mp hj).1)

private lemma p37_mu_pos_middle (nodes : ℕ → ℝ) (n d alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (hi : i ≤ alpha + 1) (hdi : alpha ≤ i + d) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  apply mul_pos
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hleft j (by have := Finset.mem_range.mp hj; omega))
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hright j (by have := (Finset.mem_Ico.mp hj).1; omega))

private lemma p37_mu_pos_right_even (nodes : ℕ → ℝ) (n d alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (hi : alpha + 1 ≤ i) (he : Even (i - (alpha + 1))) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  apply mul_pos
  · exact p37_prefix_pos_even nodes alpha i x hleft hright hi he
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hright j (by have := (Finset.mem_Ico.mp hj).1; omega))

private lemma p37_mu_pos_left_even (nodes : ℕ → ℝ) (n d alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (halpha : alpha < n) (hi : i ≤ alpha + 1)
    (hdi : i + d + 1 ≤ alpha + 1)
    (he : Even (alpha + 1 - (i + d + 1))) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  apply mul_pos
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hleft j (by have := Finset.mem_range.mp hj; omega))
  · exact p37_suffix_pos_even nodes n alpha (i + d + 1) x hleft hright halpha hdi he

private lemma p37_mu_pair (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 < n + 1) :
    p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x =
      (∏ j ∈ Finset.range i, (x - nodes j)) *
        (nodes (i+d+1) - nodes i) *
        (∏ j ∈ Finset.Ico (i+d+2) (n+1), (nodes j - x)) := by
  unfold p37Mu
  rw [Finset.prod_range_succ]
  rw [Finset.prod_eq_prod_Ico_succ_bot hi]
  ring_nf

private lemma p37_mu_pair_pos_right (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ) (hdn : d ≤ n)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (hi : alpha + 1 ≤ i) (he : Even (i - (alpha + 1)))
    (hmax : i + 1 ≤ n - d) :
    0 < p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
  rw [p37_mu_pair nodes n d i x (by omega)]
  apply mul_pos
  · apply mul_pos
    · exact p37_prefix_pos_even nodes alpha i x hleft hright hi he
    · exact sub_pos.mpr (hmono (by omega : i < i+d+1))
  · apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hright j (by have := (Finset.mem_Ico.mp hj).1; omega))

private lemma p37_mu_pair_pos_left (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (halpha : alpha < n)
    (hi : i + d + 2 ≤ alpha + 1)
    (he : Even (alpha + 1 - (i+d+2))) :
    0 < p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
  rw [p37_mu_pair nodes n d i x (by omega)]
  apply mul_pos
  · apply mul_pos
    · apply Finset.prod_pos
      intro j hj
      exact sub_pos.mpr (hleft j (by have := Finset.mem_range.mp hj; omega))
    · exact sub_pos.mpr (hmono (by omega : i < i+d+1))
  · exact p37_suffix_pos_even nodes n alpha (i+d+2) x hleft hright halpha hi he

private lemma p37_right_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (hdn : d ≤ n)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j)
    (ha : alpha + 1 ≤ n - d + 1) :
    0 ≤ ∑ i ∈ Finset.Ico (alpha+1) (n-d+1), p37Mu nodes n d i x := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply p37_sum_pairs_nonneg (fun j => p37Mu nodes n d (alpha+1+j) x)
  · intro j hj
    have he : Even ((alpha+1+2*j) - (alpha+1)) := by
      simpa only [Nat.add_sub_cancel_left] using (even_two_mul j)
    exact (p37_mu_pair_pos_right nodes hmono n d alpha (alpha+1+2*j) x hdn
      hleft hright (by omega) he (by omega)).le
  · intro j hj
    have he : Even ((alpha+1+2*j) - (alpha+1)) := by
      simpa only [Nat.add_sub_cancel_left] using (even_two_mul j)
    exact (p37_mu_pos_right_even nodes n d alpha (alpha+1+2*j) x
      hleft hright (by omega) he).le

private lemma p37_left_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ) (halpha : alpha < n)
    (hleft : ∀ j ≤ alpha, nodes j < x)
    (hright : ∀ j, alpha + 1 ≤ j → x < nodes j) :
    0 ≤ ∑ i ∈ Finset.Ico 0 (alpha+1-d), p37Mu nodes n d i x := by
  let b := alpha + 1 - d
  have hrev :
      (∑ i ∈ Finset.Ico 0 b, p37Mu nodes n d i x) =
        ∑ j ∈ Finset.range b, p37Mu nodes n d (b-1-j) x := by
    simpa [Nat.Ico_zero_eq_range] using
      (Finset.sum_range_reflect (fun i => p37Mu nodes n d i x) b).symm
  change 0 ≤ ∑ i ∈ Finset.Ico 0 b, p37Mu nodes n d i x
  rw [hrev]
  apply p37_sum_pairs_nonneg (fun j => p37Mu nodes n d (b-1-j) x)
  · intro j hj
    let i := b-1-(2*j+1)
    have hidx : b-1-(2*j) = i+1 := by dsimp [i]; omega
    have hi : i+d+2 ≤ alpha+1 := by dsimp [i, b]; omega
    have he : Even (alpha+1-(i+d+2)) := by
      have heq : alpha+1-(i+d+2) = 2*j := by dsimp [i, b]; omega
      rw [heq]
      exact even_two_mul j
    change 0 ≤ p37Mu nodes n d (b-1-(2*j)) x +
      p37Mu nodes n d (b-1-(2*j+1)) x
    rw [hidx]
    simpa [i, add_comm] using
      (p37_mu_pair_pos_left nodes hmono n d alpha i x hleft hright halpha hi he).le
  · intro j hj
    let i := b-1-(2*j)
    have hi : i ≤ alpha+1 := by dsimp [i, b]; omega
    have hdi : i+d+1 ≤ alpha+1 := by dsimp [i, b]; omega
    have he : Even (alpha+1-(i+d+1)) := by
      have heq : alpha+1-(i+d+1) = 2*j := by dsimp [i, b]; omega
      rw [heq]
      exact even_two_mul j
    exact (p37_mu_pos_left_even nodes n d alpha i x hleft hright halpha hi hdi he).le

/-- P37-C1: the interior-interval positivity argument in Theorem 1. -/
theorem p37_c1_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Denominator nodes n d x := by
  -- PROOF_START P37-C1-H001
  have hleft : ∀ j ≤ alpha, nodes j < x := by
    intro j hj
    exact (hmono.monotone hj).trans_lt hxlo
  have hright : ∀ j, alpha + 1 ≤ j → x < nodes j := by
    intro j hj
    exact hxhi.trans_le (hmono.monotone hj)
  let b := alpha + 1 - d
  let m := n - d + 1
  let r := min (alpha + 1) m
  have hb_alpha : b ≤ alpha := by dsimp [b]; omega
  have hb_m : b < m := by dsimp [b, m]; omega
  have hb_r : b < r := by
    dsimp [r]
    exact lt_min (by omega) hb_m
  have hr_m : r ≤ m := by dsimp [r]; exact min_le_right _ _
  have hlefttail : 0 ≤ ∑ i ∈ Finset.Ico 0 b, p37Mu nodes n d i x := by
    simpa [b] using p37_left_tail_nonneg nodes hmono n d alpha x halpha hleft hright
  have hmid : 0 < ∑ i ∈ Finset.Ico b r, p37Mu nodes n d i x := by
    apply Finset.sum_pos
    · intro i hi
      have hib : b ≤ i := (Finset.mem_Ico.mp hi).1
      have hir : i < r := (Finset.mem_Ico.mp hi).2
      apply p37_mu_pos_middle nodes n d alpha i x hleft hright
      · have : r ≤ alpha + 1 := by dsimp [r]; exact min_le_left _ _
        omega
      · dsimp [b] at hib
        omega
    · exact Finset.nonempty_Ico.mpr hb_r
  have hrighttail : 0 ≤ ∑ i ∈ Finset.Ico r m, p37Mu nodes n d i x := by
    by_cases ha : alpha + 1 ≤ m
    · have hr : r = alpha + 1 := by dsimp [r]; exact min_eq_left ha
      rw [hr]
      simpa [m] using p37_right_tail_nonneg nodes hmono n d alpha x hdn hleft hright
        (by simpa [m] using ha)
    · have hr : r = m := by dsimp [r]; exact min_eq_right (by omega : m ≤ alpha + 1)
      simp [hr]
  have hsplit : p37Denominator nodes n d x =
      (∑ i ∈ Finset.Ico 0 b, p37Mu nodes n d i x) +
      (∑ i ∈ Finset.Ico b r, p37Mu nodes n d i x) +
      (∑ i ∈ Finset.Ico r m, p37Mu nodes n d i x) := by
    unfold p37Denominator
    change (∑ i ∈ Finset.range m, p37Mu nodes n d i x) = _
    rw [← Nat.Ico_zero_eq_range]
    calc
      (∑ i ∈ Finset.Ico 0 m, p37Mu nodes n d i x) =
          (∑ i ∈ Finset.Ico 0 r, p37Mu nodes n d i x) +
          (∑ i ∈ Finset.Ico r m, p37Mu nodes n d i x) :=
        (Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x)
          (Nat.zero_le r) hr_m).symm
      _ = _ := by
        rw [← Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x)
          (Nat.zero_le b) (le_of_lt hb_r)]
  rw [hsplit]
  linarith

end VSCLReuse
