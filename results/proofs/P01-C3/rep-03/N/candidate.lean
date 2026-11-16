import VSCLReuse.P01.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem gamma_step_bound (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : GammaValid u (k + 1)) :
    u + (1 + u) * gamma u k ≤ gamma u (k + 1) := by
  have hk' : (k : ℝ) * u + u < 1 := by
    simpa [GammaValid, Nat.cast_add, add_mul] using hk
  have hden : 0 < 1 - (k : ℝ) * u := by linarith
  have hden_ne : 1 - u * (k : ℝ) ≠ 0 := by
    rw [mul_comm]
    exact ne_of_gt hden
  have hden' : 0 < 1 - ((k : ℝ) * u + u) := by linarith
  have hnum : 0 ≤ (k : ℝ) * u + u := by positivity
  calc
    u + (1 + u) * gamma u k =
        ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
          rw [gamma]
          field_simp [hden_ne]
          ring
    _ ≤ ((k : ℝ) * u + u) / (1 - ((k : ℝ) * u + u)) :=
      div_le_div_of_nonneg_left hnum hden' (by linarith)
    _ = gamma u (k + 1) := by
      rw [gamma]
      push_cast
      ring

private theorem gamma_valid_mono (u : ℝ) (hu : 0 ≤ u)
    {m n : ℕ} (hmn : m ≤ n) (hn : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private theorem gamma_nonneg (u : ℝ) (hu : 0 ≤ u)
    (n : ℕ) (hn : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hn
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private theorem round_add_error (fp : StandardAddModel)
    (x y X Y : ℝ) :
    |fp.fl_add x y - (X + Y)| ≤
      (1 + fp.u) * (|x - X| + |y - Y|) +
        fp.u * (|X| + |Y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  have hfactor : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have herr : |(x - X) + (y - Y)| ≤ |x - X| + |y - Y| := abs_add_le _ _
  have hval : |X + Y| ≤ |X| + |Y| := abs_add_le _ _
  calc
    |fp.fl_add x y - (X + Y)| =
        |(1 + δ) * ((x - X) + (y - Y)) + δ * (X + Y)| := by
          rw [hfl]
          congr 1
          ring
    _ ≤ |1 + δ| * |(x - X) + (y - Y)| + |δ| * |X + Y| := by
      simpa only [abs_mul] using
        (abs_add_le ((1 + δ) * ((x - X) + (y - Y))) (δ * (X + Y)))
    _ ≤ (1 + fp.u) * (|x - X| + |y - Y|) + fp.u * (|X| + |Y|) :=
      add_le_add
        (mul_le_mul hfactor herr (abs_nonneg _) (by linarith [fp.u_nonneg]))
        (mul_le_mul hδ hval (abs_nonneg _) fp.u_nonneg)

private theorem pre_last (fl : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    recursivePreRound fl v (Fin.last n) =
      recursiveSum fl n (fun j => v j.castSucc) + v (Fin.last n) := by
  rfl

private theorem rec_step (fl : ℝ → ℝ → ℝ) {n : ℕ}
    (hn : n ≠ 0) (v : Fin (n + 1) → ℝ) :
    recursiveSum fl (n + 1) v =
      fl (recursiveSum fl n (fun j => v j.castSucc)) (v (Fin.last n)) := by
  simp [recursiveSum, hn]

private theorem recursive_running_bound (fp : StandardAddModel)
    (n : ℕ) (v : Fin n → ℝ) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add v i| := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [recursiveSum, recursivePreRound,
        fp.u_nonneg, mul_nonneg]
    · let w : Fin n → ℝ := fun i => v i.castSucc
      let a := recursiveSum fp.fl_add n w
      let z := v (Fin.last n)
      let A := ∑ i : Fin n, w i
      have hloc : |fp.fl_add a z - (A + z)| ≤
          |a - A| + fp.u * |a + z| := by
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add a z
        calc
          |fp.fl_add a z - (A + z)| = |(a - A) + δ * (a + z)| := by
            rw [hfl]
            congr 1
            ring
          _ ≤ |a - A| + |δ| * |a + z| := by
            simpa only [abs_mul] using (abs_add_le (a - A) (δ * (a + z)))
          _ ≤ |a - A| + fp.u * |a + z| :=
            add_le_add_right (mul_le_mul_of_nonneg_right hδ (abs_nonneg _)) _
      calc
        |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| =
            |fp.fl_add a z - (A + z)| := by
              rw [rec_step fp.fl_add hn, Fin.sum_univ_castSucc]
        _ ≤ |a - A| + fp.u * |a + z| := hloc
        _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
              fp.u * |a + z| := by
              exact add_le_add_left (ih w) _
        _ = fp.u * ∑ i : Fin (n + 1),
              |recursivePreRound fp.fl_add v i| := by
              rw [Fin.sum_univ_castSucc, mul_add]
              simp only [pre_last]
              rfl

private theorem recursive_gamma_bound (fp : StandardAddModel)
    (n : ℕ) (v : Fin n → ℝ) (hn : 0 < n)
    (hvalid : GammaValid fp.u (n - 1)) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [recursiveSum, gamma]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      let w : Fin n → ℝ := fun i => v i.castSucc
      let a := recursiveSum fp.fl_add n w
      let z := v (Fin.last n)
      let A := ∑ i : Fin n, w i
      let B := ∑ i : Fin n, |w i|
      have hvalidn : GammaValid fp.u n := by simpa using hvalid
      have hvalidprev : GammaValid fp.u (n - 1) :=
        gamma_valid_mono fp.u fp.u_nonneg (Nat.sub_le n 1) hvalidn
      have hold : |a - A| ≤ gamma fp.u (n - 1) * B := ih w hnpos hvalidprev
      have hB : 0 ≤ B := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have hA : |A| ≤ B := Finset.abs_sum_le_sum_abs _ _
      have hloc : |fp.fl_add a z - (A + z)| ≤
          (1 + fp.u) * |a - A| + fp.u * (|A| + |z|) := by
        simpa using round_add_error fp a z A z
      have hstep : fp.u + (1 + fp.u) * gamma fp.u (n - 1) ≤ gamma fp.u n := by
        convert gamma_step_bound fp.u fp.u_nonneg (n - 1) (by simpa [Nat.sub_add_cancel hnpos] using hvalidn) using 1
        all_goals simp [Nat.sub_add_cancel hnpos]
      have hugu : fp.u ≤ gamma fp.u n := by
        have hg : 0 ≤ gamma fp.u (n - 1) :=
          gamma_nonneg fp.u fp.u_nonneg (n - 1) hvalidprev
        nlinarith [fp.u_nonneg]
      calc
        |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| =
            |fp.fl_add a z - (A + z)| := by
              rw [rec_step fp.fl_add hn0, Fin.sum_univ_castSucc]
        _ ≤ (1 + fp.u) * |a - A| + fp.u * (|A| + |z|) := hloc
        _ ≤ (1 + fp.u) * (gamma fp.u (n - 1) * B) +
              fp.u * (B + |z|) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hold (by linarith [fp.u_nonneg]))
            (mul_le_mul_of_nonneg_left (add_le_add_left hA _) fp.u_nonneg)
        _ ≤ gamma fp.u n * (B + |z|) := by
          calc
            (1 + fp.u) * (gamma fp.u (n - 1) * B) + fp.u * (B + |z|) =
                (fp.u + (1 + fp.u) * gamma fp.u (n - 1)) * B + fp.u * |z| := by ring
            _ ≤ gamma fp.u n * B + gamma fp.u n * |z| :=
              add_le_add (mul_le_mul_of_nonneg_right hstep hB)
                (mul_le_mul_of_nonneg_right hugu (abs_nonneg _))
            _ = gamma fp.u n * (B + |z|) := by ring
        _ = gamma fp.u ((n + 1) - 1) *
              ∑ i : Fin (n + 1), |v i| := by
          rw [Fin.sum_univ_castSucc]
          rfl

private theorem pair_sum_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      (∑ i : Fin (2 ^ r), v (rightIndex r i)) := by
  have hs : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by simp [pow_succ, mul_two]
  let f : Fin (2 ^ r + 2 ^ r) → ℝ := fun i => v ((finCongr hs).symm i)
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) = ∑ i, f i := by
      apply Fintype.sum_equiv (finCongr hs)
      intro i
      simp [f]
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
        (∑ i : Fin (2 ^ r), v (rightIndex r i)) := by
      rw [Fin.sum_univ_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      change v ((finCongr hs).symm (Fin.natAdd (2 ^ r) i)) = v (rightIndex r i)
      congr 1
      apply Fin.ext
      simp [finCongr_symm, finCongr_apply, rightIndex]

private theorem pairwise_gamma_bound (fp : StandardAddModel)
    (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  induction r with
  | zero => simp [pairwiseSum, gamma]
  | succ r ih =>
    let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
    let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
    let a := pairwiseSum fp.fl_add r vl
    let b := pairwiseSum fp.fl_add r vr
    let A := ∑ i : Fin (2 ^ r), vl i
    let B := ∑ i : Fin (2 ^ r), vr i
    let L := ∑ i : Fin (2 ^ r), |vl i|
    let R := ∑ i : Fin (2 ^ r), |vr i|
    have hvalidr : GammaValid fp.u r :=
      gamma_valid_mono fp.u fp.u_nonneg (Nat.le_succ r) hvalid
    have hleft : |a - A| ≤ gamma fp.u r * L := ih vl hvalidr
    have hright : |b - B| ≤ gamma fp.u r * R := ih vr hvalidr
    have hAB : |A| + |B| ≤ L + R := by
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    have hLR : 0 ≤ L + R := by
      have hL : 0 ≤ L := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have hR : 0 ≤ R := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      linarith
    have hE : |a - A| + |b - B| ≤ gamma fp.u r * (L + R) := by
      calc
        |a - A| + |b - B| ≤ gamma fp.u r * L + gamma fp.u r * R :=
          add_le_add hleft hright
        _ = gamma fp.u r * (L + R) := by ring
    have hstep : fp.u + (1 + fp.u) * gamma fp.u r ≤ gamma fp.u (r + 1) :=
      gamma_step_bound fp.u fp.u_nonneg r hvalid
    calc
      |pairwiseSum fp.fl_add (r + 1) v - ∑ i : Fin (2 ^ (r + 1)), v i| =
          |fp.fl_add a b - (A + B)| := by
            rw [pairwiseSum, pair_sum_split]
      _ ≤ (1 + fp.u) * (|a - A| + |b - B|) +
            fp.u * (|A| + |B|) := round_add_error fp a b A B
      _ ≤ (1 + fp.u) * (gamma fp.u r * (L + R)) +
            fp.u * (L + R) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hE (by linarith [fp.u_nonneg]))
          (mul_le_mul_of_nonneg_left hAB fp.u_nonneg)
      _ = (fp.u + (1 + fp.u) * gamma fp.u r) * (L + R) := by ring
      _ ≤ gamma fp.u (r + 1) * (L + R) :=
        mul_le_mul_of_nonneg_right hstep hLR
      _ = gamma fp.u (r + 1) * ∑ i : Fin (2 ^ (r + 1)), |v i| := by
        rw [pair_sum_split]

private theorem depth_le_pow_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  have h : r + 1 ≤ 2 ^ r := by
    induction r with
    | zero => norm_num
    | succ r ih =>
      simp only [pow_succ, mul_two]
      omega
  omega

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
  · exact pairwise_gamma_bound fp r v
      (gamma_valid_mono fp.u fp.u_nonneg (depth_le_pow_sub_one r) hvalid)

end VSCLReuse
