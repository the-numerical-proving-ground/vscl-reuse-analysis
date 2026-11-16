import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p37_prod_pos_of_even_neg (f : ℕ → ℝ) (a b k : ℕ)
    (hlen : b - a = 2 * k)
    (hf : ∀ j ∈ Finset.Ico a b, f j < 0) :
    0 < ∏ j ∈ Finset.Ico a b, f j := by
  have hp : 0 < ∏ j ∈ Finset.Ico a b, -f j := by
    apply Finset.prod_pos
    intro j hj
    exact neg_pos.mpr (hf j hj)
  have heq : (∏ j ∈ Finset.Ico a b, f j) =
      ∏ j ∈ Finset.Ico a b, -(-f j) := by simp
  rw [Finset.prod_neg, Nat.card_Ico, hlen] at heq
  simp only [pow_mul, neg_one_sq, one_pow, one_mul] at heq
  rw [heq]
  exact hp

private lemma p37_sum_range_nonneg_of_pairs (f : ℕ → ℝ) (m : ℕ)
    (heven : ∀ k, 2 * k < m → 0 ≤ f (2 * k))
    (hpair : ∀ k, 2 * k + 1 < m → 0 ≤ f (2 * k) + f (2 * k + 1)) :
    0 ≤ ∑ j ∈ Finset.range m, f j := by
  have hE : ∀ k, 2 * k ≤ m → 0 ≤ ∑ j ∈ Finset.range (2 * k), f j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hk0 : 2 * k ≤ m := by omega
      have hk1 : 2 * k + 1 < m := by omega
      have hsum : (∑ j ∈ Finset.range (2 * (k + 1)), f j) =
          (∑ j ∈ Finset.range (2 * k), f j) +
            (f (2 * k) + f (2 * k + 1)) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
        ring
      rw [hsum]
      exact add_nonneg (ih hk0) (hpair k hk1)
  have hO : ∀ k, 2 * k + 1 ≤ m →
      0 ≤ ∑ j ∈ Finset.range (2 * k + 1), f j := by
    intro k hk
    rw [Finset.sum_range_succ]
    exact add_nonneg (hE k (by omega)) (heven k (by omega))
  let k := m / 2
  have hm : m = 2 * k ∨ m = 2 * k + 1 := by dsimp [k]; omega
  rcases hm with h | h
  · rw [h]; exact hE k (by omega)
  · rw [h]; exact hO k (by omega)

private lemma p37_prefix_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha i : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (hi : i ≤ alpha + 1) :
    0 < ∏ j ∈ Finset.range i, (x - nodes j) := by
  apply Finset.prod_pos
  intro j hj
  have hj' : j ≤ alpha := by
    have := Finset.mem_range.mp hj
    omega
  exact sub_pos.mpr (lt_of_le_of_lt (hmono.monotone hj') hxlo)

private lemma p37_suffix_pos (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n alpha a : ℕ) (x : ℝ) (hxhi : x < nodes (alpha + 1))
    (ha : alpha + 1 ≤ a) :
    0 < ∏ j ∈ Finset.Ico a (n + 1), (nodes j - x) := by
  apply Finset.prod_pos
  intro j hj
  have hj' : a ≤ j := (Finset.mem_Ico.mp hj).1
  exact sub_pos.mpr (lt_of_lt_of_le hxhi (hmono.monotone (ha.trans hj')))

private lemma p37_right_prefix_even_pos
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha k : ℕ) (x : ℝ)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < ∏ j ∈ Finset.range (alpha + 1 + 2 * k), (x - nodes j) := by
  have hp := p37_prefix_pos nodes hmono alpha (alpha + 1) x hxlo (le_refl _)
  have hn : 0 < ∏ j ∈ Finset.Ico (alpha + 1) (alpha + 1 + 2 * k),
      (x - nodes j) := by
    apply p37_prod_pos_of_even_neg (fun j => x - nodes j) (alpha + 1)
      (alpha + 1 + 2 * k) k (by omega)
    intro j hj
    have hj' : alpha + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    exact sub_neg.mpr (lt_of_lt_of_le hxhi (hmono.monotone hj'))
  exact (Finset.prod_range_mul_prod_Ico (fun j => x - nodes j)
    (by omega : alpha + 1 ≤ alpha + 1 + 2 * k)) ▸ mul_pos hp hn

private lemma p37_left_suffix_even_pos
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n alpha a k : ℕ) (x : ℝ)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1))
    (ha : a ≤ alpha + 1) (han : alpha + 1 ≤ n + 1)
    (hlen : alpha + 1 - a = 2 * k) :
    0 < ∏ j ∈ Finset.Ico a (n + 1), (nodes j - x) := by
  have hn : 0 < ∏ j ∈ Finset.Ico a (alpha + 1), (nodes j - x) := by
    apply p37_prod_pos_of_even_neg (fun j => nodes j - x) a (alpha + 1) k hlen
    intro j hj
    have hj' : j ≤ alpha := by have := (Finset.mem_Ico.mp hj).2; omega
    exact sub_neg.mpr (lt_of_le_of_lt (hmono.monotone hj') hxlo)
  have hp := p37_suffix_pos nodes hmono n alpha (alpha + 1) x hxhi (le_refl _)
  exact (Finset.prod_Ico_consecutive (fun j => nodes j - x) ha han) ▸ mul_pos hn hp

private lemma p37_mu_middle_pos
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha i : ℕ) (x : ℝ)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1))
    (hi : i ≤ alpha) (hid : alpha + 1 ≤ i + d + 1) :
    0 < p37Mu nodes n d i x := by
  unfold p37Mu
  exact mul_pos (p37_prefix_pos nodes hmono alpha i x hxlo (by omega))
    (p37_suffix_pos nodes hmono n alpha (i + d + 1) x hxhi hid)

private lemma p37_mu_pair (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 ≤ n) :
    p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x =
      (∏ j ∈ Finset.range i, (x - nodes j)) *
      (∏ j ∈ Finset.Ico (i + d + 2) (n + 1), (nodes j - x)) *
      (nodes (i + d + 1) - nodes i) := by
  simp only [p37Mu]
  rw [Finset.prod_range_succ]
  have heq : i + 1 + d + 1 = i + d + 2 := by omega
  rw [heq, Finset.prod_eq_prod_Ico_succ_bot (by omega : i + d + 1 < n + 1)]
  ring

private lemma p37_right_tail_nonneg
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdn : d ≤ n) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1)) :
    0 ≤ ∑ i ∈ Finset.Ico (alpha + 1) (n - d + 1), p37Mu nodes n d i x := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply p37_sum_range_nonneg_of_pairs
  · intro k hk
    have hi : alpha + 1 + 2 * k + d + 1 ≥ alpha + 1 := by omega
    have hp := p37_right_prefix_even_pos nodes hmono alpha k x hxlo hxhi
    have hs := p37_suffix_pos nodes hmono n alpha
      (alpha + 1 + 2 * k + d + 1) x hxhi hi
    simpa only [p37Mu] using mul_pos hp hs |>.le
  · intro k hk
    let i := alpha + 1 + 2 * k
    have hib : i + d + 1 ≤ n := by dsimp [i]; omega
    have hp := p37_right_prefix_even_pos nodes hmono alpha k x hxlo hxhi
    have hs := p37_suffix_pos nodes hmono n alpha (i + d + 2) x hxhi (by dsimp [i]; omega)
    have hg : 0 < nodes (i + d + 1) - nodes i := by
      apply sub_pos.mpr
      exact hmono (by omega)
    have hpair := p37_mu_pair nodes n d i x hib
    have hpos : 0 < p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
      rw [hpair]
      exact mul_pos (mul_pos hp hs) hg
    convert hpos.le using 1

private lemma p37_left_tail_nonneg
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 ≤ ∑ i ∈ Finset.range (alpha + 1 - d), p37Mu nodes n d i x := by
  let L := alpha + 1 - d
  have hrev : (∑ j ∈ Finset.range L, p37Mu nodes n d (L - 1 - j) x) =
      ∑ j ∈ Finset.range L, p37Mu nodes n d j x :=
    Finset.sum_range_reflect (fun j => p37Mu nodes n d j x) L
  have htail : 0 ≤ ∑ j ∈ Finset.range L, p37Mu nodes n d (L - 1 - j) x := by
    apply p37_sum_range_nonneg_of_pairs
    · intro k hk
      let i := L - 1 - 2 * k
      have hil : i ≤ alpha + 1 := by dsimp [i, L]; omega
      have ha : i + d + 1 ≤ alpha + 1 := by dsimp [i, L]; omega
      have hlen : alpha + 1 - (i + d + 1) = 2 * k := by dsimp [i, L]; omega
      have hp := p37_prefix_pos nodes hmono alpha i x hxlo hil
      have hs := p37_left_suffix_even_pos nodes hmono n alpha (i + d + 1) k x
        hxlo hxhi ha (by omega) hlen
      simpa only [p37Mu, i] using (mul_pos hp hs).le
    · intro k hk
      let i := L - 2 - 2 * k
      have hfirst : L - 1 - 2 * k = i + 1 := by dsimp [i]; omega
      have hsecond : L - 1 - (2 * k + 1) = i := by dsimp [i]; omega
      have hil : i ≤ alpha + 1 := by dsimp [i, L]; omega
      have ha : i + d + 2 ≤ alpha + 1 := by dsimp [i, L]; omega
      have hlen : alpha + 1 - (i + d + 2) = 2 * k := by dsimp [i, L]; omega
      have hib : i + d + 1 ≤ n := by omega
      have hp := p37_prefix_pos nodes hmono alpha i x hxlo hil
      have hs := p37_left_suffix_even_pos nodes hmono n alpha (i + d + 2) k x
        hxlo hxhi ha (by omega) hlen
      have hg : 0 < nodes (i + d + 1) - nodes i :=
        sub_pos.mpr (hmono (by omega))
      have hpair := p37_mu_pair nodes n d i x hib
      have hpos : 0 < p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
        rw [hpair]
        exact mul_pos (mul_pos hp hs) hg
      change 0 ≤ p37Mu nodes n d (L - 1 - 2 * k) x +
        p37Mu nodes n d (L - 1 - (2 * k + 1)) x
      rw [hfirst, hsecond]
      linarith
  simpa only [L, hrev] using htail

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
  let U := min (alpha + 1) M
  have hLM : L ≤ M := by dsimp [L, M]; omega
  have hLU : L < U := by dsimp [L, U, M]; omega
  have hUM : U ≤ M := by dsimp [U]; omega
  have hleft : 0 ≤ ∑ i ∈ Finset.range L, p37Mu nodes n d i x := by
    simpa only [L] using p37_left_tail_nonneg nodes hmono n d alpha x halpha hxlo hxhi
  have hmiddle : 0 < ∑ i ∈ Finset.Ico L U, p37Mu nodes n d i x := by
    apply Finset.sum_pos
    · intro i hi
      have hli : L ≤ i := (Finset.mem_Ico.mp hi).1
      have hiu : i < U := (Finset.mem_Ico.mp hi).2
      have hiα : i ≤ alpha := by dsimp [U] at hiu; omega
      have hid : alpha + 1 ≤ i + d + 1 := by dsimp [L] at hli; omega
      exact p37_mu_middle_pos nodes hmono n d alpha i x hxlo hxhi hiα hid
    · exact ⟨L, Finset.mem_Ico.mpr ⟨le_refl _, hLU⟩⟩
  have hright : 0 ≤ ∑ i ∈ Finset.Ico U M, p37Mu nodes n d i x := by
    by_cases hRM : alpha + 1 ≤ M
    · have hU : U = alpha + 1 := min_eq_left hRM
      rw [hU]
      simpa only [M] using p37_right_tail_nonneg nodes hmono n d alpha x hdn hxlo hxhi
    · have hU : U = M := min_eq_right (by omega : M ≤ alpha + 1)
      simp [hU]
  change 0 < ∑ i ∈ Finset.range M, p37Mu nodes n d i x
  rw [← Finset.sum_range_add_sum_Ico (fun i => p37Mu nodes n d i x) hLM,
    ← Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x) hLU.le hUM]
  linarith

end VSCLReuse
