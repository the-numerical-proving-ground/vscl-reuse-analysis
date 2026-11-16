import VSCLReuse.P01.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem round_error (fp : StandardAddModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  have heq : fp.fl_add a b - (a + b) = (a + b) * δ := by
    rw [hfl]
    ring
  rw [heq, abs_mul]
  calc
    |a + b| * |δ| ≤ |a + b| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |a + b| := mul_comm _ _

private theorem round_combine (fp : StandardAddModel) (a b x y : ℝ) :
    |fp.fl_add a b - (x + y)| ≤
      (1 + fp.u) * (|a - x| + |b - y|) + fp.u * (|x| + |y|) := by
  have hinput : |a + b| ≤ |a - x| + |b - y| + (|x| + |y|) := by
    calc
      |a + b| = |(a - x) + (b - y) + (x + y)| := by congr 1; ring
      _ ≤ |a - x| + |b - y| + |x + y| := abs_add_three _ _ _
      _ ≤ |a - x| + |b - y| + (|x| + |y|) := by
        linarith [abs_add_le x y]
  have hcore : |(a + b) - (x + y)| ≤ |a - x| + |b - y| := by
    calc
      |(a + b) - (x + y)| = |(a - x) + (b - y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hround := round_error fp a b
  have hmul := mul_le_mul_of_nonneg_left hinput fp.u_nonneg
  have htri := abs_sub_le (fp.fl_add a b) (a + b) (x + y)
  nlinarith

private theorem gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hv : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr hv.le)

private theorem gamma_valid_mono (u : ℝ) (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (hv : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul := mul_le_mul_of_nonneg_right hcast hu
  linarith

private theorem gamma_step (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hv : GammaValid u (n + 1)) :
    u + (1 + u) * gamma u n ≤ gamma u (n + 1) := by
  unfold gamma GammaValid at *
  have h0 : 0 < 1 - (n : ℝ) * u := by
    have : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
      push_cast
      nlinarith
    linarith
  have h1 : 0 < 1 - (((n + 1 : ℕ) : ℝ) * u) := by linarith
  have heq :
      u + (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) =
        (((n + 1 : ℕ) : ℝ) * u) / (1 - (n : ℝ) * u) := by
    have h0' : 1 - u * (n : ℝ) ≠ 0 := by nlinarith [h0]
    field_simp [h0', ne_of_gt h0]
    push_cast
    ring
  rw [heq]
  apply (div_le_div_iff₀ h0 h1).2
  have hnum : 0 ≤ (((n + 1 : ℕ) : ℝ) * u) :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 0 ≤ (((n + 1 : ℕ) : ℝ) - (n : ℝ)) * u :=
    mul_nonneg (by push_cast; norm_num) hu
  nlinarith

private theorem sum_two_halves (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
      (∑ i : Fin (2 ^ r), f (rightIndex r i)) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ, mul_two]
  let g : ℕ → ℝ := fun i => if h : i < 2 ^ (r + 1) then f ⟨i, h⟩ else 0
  have hfull : (∑ i : Fin (2 ^ (r + 1)), f i) =
      ∑ i ∈ Finset.range (2 ^ (r + 1)), g i := by
    rw [← Fin.sum_univ_eq_sum_range g (2 ^ (r + 1))]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, i.isLt]
  have hleft : (∑ i : Fin (2 ^ r), f (leftIndex r i)) =
      ∑ i ∈ Finset.range (2 ^ r), g i := by
    rw [← Fin.sum_univ_eq_sum_range g (2 ^ r)]
    apply Finset.sum_congr rfl
    intro i hi
    have hlt : (i : ℕ) < 2 ^ (r + 1) := by rw [hpow]; omega
    simp [g, leftIndex, hlt]
  have hright : (∑ i : Fin (2 ^ r), f (rightIndex r i)) =
      ∑ i ∈ Finset.range (2 ^ r), g (2 ^ r + i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => g (2 ^ r + i)) (2 ^ r)]
    apply Finset.sum_congr rfl
    intro i hi
    have hlt : (i : ℕ) + 2 ^ r < 2 ^ (r + 1) := by
      rw [hpow]
      have := i.isLt
      omega
    simp [g, rightIndex, hlt, Nat.add_comm]
  rw [hfull, hleft, hright, hpow, Finset.sum_range_add]

private theorem recursive_sum_step (fp : StandardAddModel) (n : ℕ)
    (hn : 0 < n) (v : Fin (n + 1) → ℝ) :
    recursiveSum fp.fl_add (n + 1) v =
      fp.fl_add (recursiveSum fp.fl_add n (fun i => v i.castSucc))
        (v (Fin.last n)) := by
  simp [recursiveSum, Nat.ne_of_gt hn]

private theorem recursive_running_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      cases n with
      | zero =>
          simp [recursiveSum, recursivePreRound]
          exact mul_nonneg fp.u_nonneg (abs_nonneg _)
      | succ m =>
          let w : Fin (m + 1) → ℝ := fun i => v i.castSucc
          have hprev := ih w
          have hsum : (∑ i : Fin (m + 2), v i) =
              (∑ i : Fin (m + 1), w i) + v (Fin.last (m + 1)) := by
            rw [Fin.sum_univ_castSucc]
          have hpre : (∑ i : Fin (m + 2), |recursivePreRound fp.fl_add v i|) =
              (∑ i : Fin (m + 1), |recursivePreRound fp.fl_add w i|) +
                |recursiveSum fp.fl_add (m + 1) w + v (Fin.last (m + 1))| := by
            rw [Fin.sum_univ_castSucc]
            congr 1
          rw [recursive_sum_step fp (m + 1) (by omega), hsum, hpre]
          have hr := round_error fp (recursiveSum fp.fl_add (m + 1) w)
            (v (Fin.last (m + 1)))
          have ht := abs_sub_le
            (fp.fl_add (recursiveSum fp.fl_add (m + 1) w) (v (Fin.last (m + 1))))
            (recursiveSum fp.fl_add (m + 1) w + v (Fin.last (m + 1)))
            ((∑ i : Fin (m + 1), w i) + v (Fin.last (m + 1)))
          have hc :
              |(recursiveSum fp.fl_add (m + 1) w + v (Fin.last (m + 1))) -
                  ((∑ i : Fin (m + 1), w i) + v (Fin.last (m + 1)))| =
                |recursiveSum fp.fl_add (m + 1) w - ∑ i : Fin (m + 1), w i| := by
            congr 1
            ring
          rw [hc] at ht
          nlinarith

private theorem recursive_gamma_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ), 0 < n → GammaValid fp.u (n - 1) →
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hn
      omega
  | succ n ih =>
      intro v hn hv
      cases n with
      | zero =>
          simp [recursiveSum, gamma]
      | succ m =>
          let w : Fin (m + 1) → ℝ := fun i => v i.castSucc
          have hprevvalid : GammaValid fp.u m := by
            apply gamma_valid_mono fp.u fp.u_nonneg (Nat.le_succ m)
            simpa using hv
          have hprev := ih w (by omega) hprevvalid
          have hstep :
              fp.u + (1 + fp.u) * gamma fp.u m ≤ gamma fp.u (m + 1) :=
            gamma_step fp.u fp.u_nonneg m (by simpa using hv)
          have hgamma : 0 ≤ gamma fp.u m :=
            gamma_nonneg fp.u fp.u_nonneg m hprevvalid
          have hnonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hu_le : fp.u ≤ gamma fp.u (m + 1) := by
            have := mul_nonneg hnonneg hgamma
            linarith
          have habs : |∑ i : Fin (m + 1), w i| ≤
              ∑ i : Fin (m + 1), |w i| :=
            Finset.abs_sum_le_sum_abs w Finset.univ
          have hsum_nonneg : 0 ≤ ∑ i : Fin (m + 1), |w i| := by
            exact Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
          have hlast_nonneg : 0 ≤ |v (Fin.last (m + 1))| := abs_nonneg _
          have hrc := round_combine fp
            (recursiveSum fp.fl_add (m + 1) w) (v (Fin.last (m + 1)))
            (∑ i : Fin (m + 1), w i) (v (Fin.last (m + 1)))
          simp only [sub_self, abs_zero, add_zero] at hrc
          have hmulprev := mul_le_mul_of_nonneg_left hprev hnonneg
          have hmulabs := mul_le_mul_of_nonneg_left habs fp.u_nonneg
          have hmulstep := mul_le_mul_of_nonneg_right hstep hsum_nonneg
          have hmullast := mul_le_mul_of_nonneg_right hu_le hlast_nonneg
          have hsum : (∑ i : Fin (m + 2), v i) =
              (∑ i : Fin (m + 1), w i) + v (Fin.last (m + 1)) := by
            rw [Fin.sum_univ_castSucc]
          have habssum : (∑ i : Fin (m + 2), |v i|) =
              (∑ i : Fin (m + 1), |w i|) + |v (Fin.last (m + 1))| := by
            rw [Fin.sum_univ_castSucc]
          rw [recursive_sum_step fp (m + 1) (by omega), hsum, habssum]
          simp only [Nat.add_sub_cancel_right] at hprev ⊢
          nlinarith

private theorem pairwise_gamma_bound (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ), GammaValid fp.u r →
      |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  intro r
  induction r with
  | zero =>
      intro v hv
      simp [pairwiseSum, gamma]
  | succ r ih =>
      intro v hv
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      have hv0 : GammaValid fp.u r :=
        gamma_valid_mono fp.u fp.u_nonneg (Nat.le_succ r) hv
      have hl := ih vl hv0
      have hr := ih vr hv0
      have hstep := gamma_step fp.u fp.u_nonneg r hv
      have hnonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hvl : 0 ≤ ∑ i : Fin (2 ^ r), |vl i| := by
        exact Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have hvr : 0 ≤ ∑ i : Fin (2 ^ r), |vr i| := by
        exact Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have habsl : |∑ i : Fin (2 ^ r), vl i| ≤ ∑ i : Fin (2 ^ r), |vl i| :=
        Finset.abs_sum_le_sum_abs vl Finset.univ
      have habsr : |∑ i : Fin (2 ^ r), vr i| ≤ ∑ i : Fin (2 ^ r), |vr i| :=
        Finset.abs_sum_le_sum_abs vr Finset.univ
      have hrc := round_combine fp
        (pairwiseSum fp.fl_add r vl) (pairwiseSum fp.fl_add r vr)
        (∑ i : Fin (2 ^ r), vl i) (∑ i : Fin (2 ^ r), vr i)
      have herrors := add_le_add hl hr
      have hmulerrors := mul_le_mul_of_nonneg_left herrors hnonneg
      have hsumabs := add_le_add habsl habsr
      have hmulsums := mul_le_mul_of_nonneg_left hsumabs fp.u_nonneg
      have hmulstep := mul_le_mul_of_nonneg_right hstep (add_nonneg hvl hvr)
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) =
          (∑ i : Fin (2 ^ r), vl i) + (∑ i : Fin (2 ^ r), vr i) :=
        sum_two_halves r v
      have habssum : (∑ i : Fin (2 ^ (r + 1)), |v i|) =
          (∑ i : Fin (2 ^ r), |vl i|) + (∑ i : Fin (2 ^ r), |vr i|) :=
        sum_two_halves r (fun i => |v i|)
      rw [show pairwiseSum fp.fl_add (r + 1) v =
          fp.fl_add (pairwiseSum fp.fl_add r vl) (pairwiseSum fp.fl_add r vr) from rfl,
        hsum, habssum]
      nlinarith

theorem p01_c3_recursive_running_and_pairwise_bounds
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u (2 ^ r - 1)) :
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        fp.u * ∑ i : Fin (2 ^ r), |recursivePreRound fp.fl_add v i| ∧
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  -- PROOF_START P01-C3-H001
  refine ⟨recursive_running_bound fp (2 ^ r) v, ?_, ?_⟩
  · exact recursive_gamma_bound fp (2 ^ r) v (by positivity) hvalid
  · have hrle : r ≤ 2 ^ r - 1 := by
      have hlt : r < 2 ^ r := Nat.lt_two_pow_self
      omega
    have hrvalid : GammaValid fp.u r :=
      gamma_valid_mono fp.u fp.u_nonneg hrle hvalid
    exact pairwise_gamma_bound fp r v hrvalid

end VSCLReuse
