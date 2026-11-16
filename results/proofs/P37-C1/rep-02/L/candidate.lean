import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

private noncomputable def p37Prefix (nodes : ℕ → ℝ) (x : ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, (x - nodes j)

private noncomputable def p37Suffix (nodes : ℕ → ℝ) (n : ℕ) (x : ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico i (n + 1), (nodes j - x)

private lemma p37Prefix_succ (nodes : ℕ → ℝ) (x : ℝ) (i : ℕ) :
    p37Prefix nodes x (i + 1) = p37Prefix nodes x i * (x - nodes i) := by
  simp only [p37Prefix, Finset.prod_range_succ]

private lemma p37Suffix_succ (nodes : ℕ → ℝ) (n : ℕ) (x : ℝ) (i : ℕ)
    (hi : i ≤ n) :
    p37Suffix nodes n x i = (nodes i - x) * p37Suffix nodes n x (i + 1) := by
  unfold p37Suffix
  have h := Finset.prod_Ico_consecutive (fun j => nodes j - x)
    (Nat.le_succ i) (by omega : i + 1 ≤ n + 1)
  simpa using h.symm

private lemma p37Mu_eq (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ) :
    p37Mu nodes n d i x = p37Prefix nodes x i * p37Suffix nodes n x (i + d + 1) :=
  rfl

private lemma p37Mu_pair (nodes : ℕ → ℝ) (n d i : ℕ) (x : ℝ)
    (hi : i + d + 1 ≤ n) :
    p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x =
      p37Prefix nodes x i * p37Suffix nodes n x (i + d + 2) *
        (nodes (i + d + 1) - nodes i) := by
  rw [p37Mu_eq, p37Mu_eq, p37Prefix_succ]
  rw [p37Suffix_succ nodes n x (i + d + 1) hi]
  ring_nf

private lemma p37_sum_range_nonneg_of_pairs (f : ℕ → ℝ) (m : ℕ)
    (heven : ∀ k, 2 * k < m → 0 ≤ f (2 * k))
    (hpair : ∀ k, 2 * k + 1 < m → 0 ≤ f (2 * k) + f (2 * k + 1)) :
    0 ≤ ∑ i ∈ Finset.range m, f i := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using heven 0 (by omega)
  | more m hm hm1 =>
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · have he : m = 2 * k := by omega
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs : 0 ≤ ∑ i ∈ Finset.range m, f i := by
        apply hm
        · intro j hj; exact heven j (by omega)
        · intro j hj; exact hpair j (by omega)
      have hp : 0 ≤ f m + f (m + 1) := by simpa [he] using hpair k (by omega)
      linarith
    · have he : m + 1 = 2 * (k + 1) := by omega
      rw [Finset.sum_range_succ]
      have hs : 0 ≤ ∑ i ∈ Finset.range (m + 1), f i := by
        apply hm1
        · intro j hj; exact heven j (by omega)
        · intro j hj; exact hpair j (by omega)
      have hp : 0 ≤ f (m + 1) := by simpa [he] using heven (k + 1) (by omega)
      linarith

private lemma p37_prefix_pos_before (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha : ℕ) (x : ℝ) (hxlo : nodes alpha < x) :
    0 < p37Prefix nodes x (alpha + 1) := by
  unfold p37Prefix
  apply Finset.prod_pos
  intro j hj
  have hj' : j ≤ alpha := by simpa using hj
  exact sub_pos.mpr (lt_of_le_of_lt (hmono.monotone hj') hxlo)

private lemma p37_suffix_pos_after (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n alpha : ℕ) (x : ℝ) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Suffix nodes n x (alpha + 1) := by
  unfold p37Suffix
  apply Finset.prod_pos
  intro j hj
  have hj' : alpha + 1 ≤ j := (Finset.mem_Ico.mp hj).1
  exact sub_pos.mpr (lt_of_lt_of_le hxhi (hmono.monotone hj'))

private lemma p37_prefix_pos_even (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1)) (t : ℕ) :
    0 < p37Prefix nodes x (alpha + 1 + 2 * t) := by
  induction t with
  | zero => simpa using p37_prefix_pos_before nodes hmono alpha x hxlo
  | succ t ih =>
    let i := alpha + 1 + 2 * t
    have h1 : x - nodes i < 0 := by
      apply sub_neg.mpr
      exact lt_of_lt_of_le hxhi (hmono.monotone (by dsimp [i]; omega))
    have h2 : x - nodes (i + 1) < 0 := by
      apply sub_neg.mpr
      exact lt_of_lt_of_le hxhi (hmono.monotone (by dsimp [i]; omega))
    have hp : 0 < p37Prefix nodes x i := by simpa [i] using ih
    have hstep : 0 < p37Prefix nodes x (i + 2) := by
      rw [show i + 2 = (i + 1) + 1 by omega, p37Prefix_succ, p37Prefix_succ]
      have hh : 0 < (x - nodes i) * (x - nodes (i + 1)) := mul_pos_of_neg_of_neg h1 h2
      nlinarith [mul_pos hp hh]
    simpa [i, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

private lemma p37_suffix_pos_even (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n alpha : ℕ) (x : ℝ) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1))
    (t : ℕ) (ht : 2 * t ≤ alpha + 1) :
    0 < p37Suffix nodes n x (alpha + 1 - 2 * t) := by
  induction t with
  | zero => simpa using p37_suffix_pos_after nodes hmono n alpha x hxhi
  | succ t ih =>
    let k := alpha + 1 - 2 * (t + 1)
    have hkt : k + 2 = alpha + 1 - 2 * t := by dsimp [k]; omega
    have hk1 : k + 1 ≤ alpha := by dsimp [k]; omega
    have h1 : nodes k - x < 0 := by
      apply sub_neg.mpr
      exact lt_of_le_of_lt (hmono.monotone (by omega : k ≤ alpha)) hxlo
    have h2 : nodes (k + 1) - x < 0 := by
      apply sub_neg.mpr
      exact lt_of_le_of_lt (hmono.monotone hk1) hxlo
    have hp : 0 < p37Suffix nodes n x (k + 2) := by
      rw [hkt]
      exact ih (by omega)
    have hstep : 0 < p37Suffix nodes n x k := by
      rw [p37Suffix_succ nodes n x k (by omega),
        p37Suffix_succ nodes n x (k + 1) (by omega)]
      have hh : 0 < (nodes k - x) * (nodes (k + 1) - x) :=
        mul_pos_of_neg_of_neg h1 h2
      nlinarith [mul_pos hh hp]
    simpa [k] using hstep

private lemma p37_prefix_pos_to (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (alpha : ℕ) (x : ℝ) (hxlo : nodes alpha < x)
    (i : ℕ) (hi : i ≤ alpha + 1) :
    0 < p37Prefix nodes x i := by
  unfold p37Prefix
  apply Finset.prod_pos
  intro j hj
  have hj' : j ≤ alpha := by have := Finset.mem_range.mp hj; omega
  exact sub_pos.mpr (lt_of_le_of_lt (hmono.monotone hj') hxlo)

private lemma p37_suffix_pos_from (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n alpha : ℕ) (x : ℝ) (hxhi : x < nodes (alpha + 1))
    (i : ℕ) (hi : alpha + 1 ≤ i) :
    0 < p37Suffix nodes n x i := by
  unfold p37Suffix
  apply Finset.prod_pos
  intro j hj
  have hj' : alpha + 1 ≤ j := by have := (Finset.mem_Ico.mp hj).1; omega
  exact sub_pos.mpr (lt_of_lt_of_le hxhi (hmono.monotone hj'))

private lemma p37_right_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1))
    (hstart : alpha + 1 ≤ n - d + 1) :
    0 ≤ ∑ i ∈ Finset.Ico (alpha + 1) (n - d + 1), p37Mu nodes n d i x := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply p37_sum_range_nonneg_of_pairs
  · intro k hk
    let i := alpha + 1 + 2 * k
    have hi : i < n - d + 1 := by dsimp [i]; omega
    have hp : 0 < p37Prefix nodes x i := by
      simpa [i] using p37_prefix_pos_even nodes hmono alpha x hxlo hxhi k
    have hs : 0 < p37Suffix nodes n x (i + d + 1) :=
      p37_suffix_pos_from nodes hmono n alpha x hxhi _ (by dsimp [i]; omega)
    rw [show alpha + 1 + 2 * k = i by rfl, p37Mu_eq]
    exact le_of_lt (mul_pos hp hs)
  · intro k hk
    let i := alpha + 1 + 2 * k
    have hi : i + d + 1 ≤ n := by dsimp [i]; omega
    have hp : 0 < p37Prefix nodes x i := by
      simpa [i] using p37_prefix_pos_even nodes hmono alpha x hxlo hxhi k
    have hs : 0 < p37Suffix nodes n x (i + d + 2) :=
      p37_suffix_pos_from nodes hmono n alpha x hxhi _ (by dsimp [i]; omega)
    have hdif : 0 < nodes (i + d + 1) - nodes i := by
      apply sub_pos.mpr
      exact hmono (by omega : i < i + d + 1)
    have hsum : 0 ≤ p37Mu nodes n d i x + p37Mu nodes n d (i + 1) x := by
      rw [p37Mu_pair nodes n d i x hi]
      exact le_of_lt (mul_pos (mul_pos hp hs) hdif)
    convert hsum using 1

private lemma p37_left_tail_nonneg (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (halpha : alpha < n) (hxlo : nodes alpha < x)
    (hxhi : x < nodes (alpha + 1)) (hd : d ≤ alpha + 1) :
    0 ≤ ∑ i ∈ Finset.range (alpha + 1 - d), p37Mu nodes n d i x := by
  let L := alpha + 1 - d
  change 0 ≤ ∑ i ∈ Finset.range L, p37Mu nodes n d i x
  rw [← Finset.sum_range_reflect (fun i => p37Mu nodes n d i x) L]
  apply p37_sum_range_nonneg_of_pairs
  · intro k hk
    let i := L - 1 - 2 * k
    have hi : i ≤ alpha + 1 := by dsimp [i, L]; omega
    have hidx : i + d + 1 = alpha + 1 - 2 * k := by dsimp [i, L]; omega
    have htk : 2 * k ≤ alpha + 1 := by dsimp [L] at hk; omega
    have hp : 0 < p37Prefix nodes x i :=
      p37_prefix_pos_to nodes hmono alpha x hxlo i hi
    have hs : 0 < p37Suffix nodes n x (i + d + 1) := by
      rw [hidx]
      exact p37_suffix_pos_even nodes hmono n alpha x halpha hxlo hxhi k htk
    change 0 ≤ p37Mu nodes n d i x
    rw [p37Mu_eq]
    exact le_of_lt (mul_pos hp hs)
  · intro k hk
    let i := L - 1 - 2 * k
    let j := i - 1
    have hji : j + 1 = i := by dsimp [j, i, L]; omega
    have hj : j ≤ alpha + 1 := by dsimp [j, i, L]; omega
    have hidx : j + d + 2 = alpha + 1 - 2 * k := by dsimp [j, i, L]; omega
    have htk : 2 * k ≤ alpha + 1 := by dsimp [L] at hk; omega
    have hbound : j + d + 1 ≤ n := by dsimp [j, i, L]; omega
    have hp : 0 < p37Prefix nodes x j :=
      p37_prefix_pos_to nodes hmono alpha x hxlo j hj
    have hs : 0 < p37Suffix nodes n x (j + d + 2) := by
      rw [hidx]
      exact p37_suffix_pos_even nodes hmono n alpha x halpha hxlo hxhi k htk
    have hdif : 0 < nodes (j + d + 1) - nodes j := by
      apply sub_pos.mpr
      exact hmono (by omega : j < j + d + 1)
    have hpair := le_of_lt (mul_pos (mul_pos hp hs) hdif)
    rw [← p37Mu_pair nodes n d j x hbound, hji] at hpair
    change 0 ≤ p37Mu nodes n d i x + p37Mu nodes n d j x
    linarith

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
  have hMN : M ≤ N := by dsimp [M]; omega
  have hLMlt : L < M := by dsimp [L, M, N]; omega
  have hleft : 0 ≤ ∑ i ∈ Finset.range L, p37Mu nodes n d i x := by
    by_cases hd : d ≤ alpha + 1
    · simpa [L] using p37_left_tail_nonneg nodes hmono n d alpha x halpha hxlo hxhi hd
    · have hL : L = 0 := by dsimp [L]; omega
      simp [hL]
  have hmid : 0 < ∑ i ∈ Finset.Ico L M, p37Mu nodes n d i x := by
    apply Finset.sum_pos
    · intro i hi
      have hiL : L ≤ i := (Finset.mem_Ico.mp hi).1
      have hiM : i < M := (Finset.mem_Ico.mp hi).2
      have hiα : i ≤ alpha + 1 := by dsimp [M] at hiM; omega
      have his : alpha + 1 ≤ i + d + 1 := by dsimp [L] at hiL; omega
      rw [p37Mu_eq]
      exact mul_pos
        (p37_prefix_pos_to nodes hmono alpha x hxlo i hiα)
        (p37_suffix_pos_from nodes hmono n alpha x hxhi _ his)
    · exact ⟨L, Finset.mem_Ico.mpr ⟨le_rfl, hLMlt⟩⟩
  have hright : 0 ≤ ∑ i ∈ Finset.Ico M N, p37Mu nodes n d i x := by
    by_cases h : alpha + 1 ≤ N
    · have hM : M = alpha + 1 := by dsimp [M]; omega
      rw [hM]
      simpa [N] using p37_right_tail_nonneg nodes hmono n d alpha x hxlo hxhi (by simpa [N] using h)
    · have hM : M = N := by dsimp [M]; omega
      simp [hM]
  change 0 < ∑ i ∈ Finset.range N, p37Mu nodes n d i x
  rw [← Finset.sum_range_add_sum_Ico (fun i => p37Mu nodes n d i x) hLN]
  rw [← Finset.sum_Ico_consecutive (fun i => p37Mu nodes n d i x) hLM hMN]
  linarith

end VSCLReuse
