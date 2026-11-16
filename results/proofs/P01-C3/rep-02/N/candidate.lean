import VSCLReuse.P01.Definitions

namespace VSCLReuse

open scoped BigOperators


private theorem round_local (fp : StandardAddModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private theorem round_error (fp : StandardAddModel) (x y a b : ℝ) :
    |fp.fl_add x y - (a + b)| ≤
      (1 + fp.u) * (|x - a| + |y - b|) + fp.u * (|a| + |b|) := by
  have hlocal := round_local fp x y
  have hxy : |x + y| ≤ (|x - a| + |y - b|) + (|a| + |b|) := by
    have h := abs_add_le (x - a + (y - b)) (a + b)
    have h₁ := abs_add_le (x - a) (y - b)
    have h₂ := abs_add_le a b
    have heq : x - a + (y - b) + (a + b) = x + y := by ring
    rw [heq] at h
    linarith
  have hsplit := abs_add_le (fp.fl_add x y - (x + y)) ((x - a) + (y - b))
  have hdiff := abs_add_le (x - a) (y - b)
  have heq : fp.fl_add x y - (a + b) =
      (fp.fl_add x y - (x + y)) + ((x - a) + (y - b)) := by ring
  rw [← heq] at hsplit
  have hmul := mul_le_mul_of_nonneg_left hxy fp.u_nonneg
  nlinarith

private theorem preRound_castSucc (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    recursivePreRound flAdd v i.castSucc =
      recursivePreRound flAdd (fun j => v j.castSucc) i := by
  rfl

private theorem preRound_last (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    recursivePreRound flAdd v (Fin.last n) =
      recursiveSum flAdd n (fun j => v j.castSucc) + v (Fin.last n) := by
  rfl

private theorem recursive_running_bound (fp : StandardAddModel) :
    ∀ n : ℕ, ∀ v : Fin n → ℝ,
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, fp.u_nonneg, mul_nonneg]
      · let w : Fin n → ℝ := fun i => v i.castSucc
        let s := recursiveSum fp.fl_add n w
        let t := v (Fin.last n)
        have hrec : recursiveSum fp.fl_add (n + 1) v = fp.fl_add s t := by
          simp [recursiveSum, hn, s, t, w]
        have hsum : (∑ i : Fin (n + 1), v i) = (∑ i : Fin n, w i) + t := by
          simpa [w, t] using Fin.sum_univ_castSucc v
        have hpre : (∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i|) =
            (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) + |s + t| := by
          rw [Fin.sum_univ_castSucc]
          simp only [preRound_castSucc, preRound_last]
          rfl
        have hl := round_local fp s t
        have hi := ih w
        have ht := abs_add_le (fp.fl_add s t - (s + t))
          (s - ∑ i : Fin n, w i)
        have heq : fp.fl_add s t - ((∑ i : Fin n, w i) + t) =
            (fp.fl_add s t - (s + t)) + (s - ∑ i : Fin n, w i) := by ring
        rw [← heq] at ht
        rw [hrec, hsum, hpre]
        nlinarith

private theorem round_error_mass (fp : StandardAddModel)
    (x y a b c A B : ℝ) (hx : |x - a| ≤ c * A)
    (hy : |y - b| ≤ c * B) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |fp.fl_add x y - (a + b)| ≤ ((1 + fp.u) * c + fp.u) * (A + B) := by
  calc
    |fp.fl_add x y - (a + b)| ≤
        (1 + fp.u) * (|x - a| + |y - b|) + fp.u * (|a| + |b|) :=
      round_error fp x y a b
    _ ≤ (1 + fp.u) * (c * A + c * B) + fp.u * (A + B) := by
      gcongr
      · linarith [fp.u_nonneg]
      · exact fp.u_nonneg
    _ = ((1 + fp.u) * c + fp.u) * (A + B) := by ring

private theorem pow_mul_one_sub_le_one (u : ℝ) (hu : 0 ≤ u) :
    ∀ n : ℕ, GammaValid u n → (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro _
      norm_num
  | succ n ih =>
      intro hn
      have hn' : GammaValid u n := by
        dsimp [GammaValid] at hn ⊢
        push_cast at hn
        nlinarith [hu]
      have hi := ih hn'
      have hnon : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
      have hstep : (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
          1 - (n : ℝ) * u := by
        push_cast
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sq_nonneg u)]
      have hm := mul_le_mul_of_nonneg_left hstep hnon
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using le_trans hm hi

private theorem pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : GammaValid u n) : (1 + u) ^ n - 1 ≤ gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    dsimp [GammaValid] at hn
    linarith
  have hp := pow_mul_one_sub_le_one u hu n hn
  unfold gamma
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem recursive_error_pow (fp : StandardAddModel) :
    ∀ n : ℕ, ∀ v : Fin (n + 1) → ℝ,
      |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| ≤
        ((1 + fp.u) ^ n - 1) * ∑ i : Fin (n + 1), |v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let s := recursiveSum fp.fl_add (n + 1) w
      let t := v (Fin.last (n + 1))
      let A := ∑ i : Fin (n + 1), |w i|
      let B := |t|
      let c := (1 + fp.u) ^ n - 1
      have hrec : recursiveSum fp.fl_add ((n + 1) + 1) v = fp.fl_add s t := by
        simp [recursiveSum, s, t, w]
      have hsum : (∑ i : Fin ((n + 1) + 1), v i) =
          (∑ i : Fin (n + 1), w i) + t := by
        simpa [w, t] using Fin.sum_univ_castSucc v
      have hmass : (∑ i : Fin ((n + 1) + 1), |v i|) = A + B := by
        simpa [w, t, A, B] using Fin.sum_univ_castSucc (fun i => |v i|)
      have hc : 0 ≤ c := by
        dsimp [c]
        exact sub_nonneg.mpr (one_le_pow₀ (by linarith [fp.u_nonneg]))
      have hzero : |t - t| ≤ c * B := by
        simp only [sub_self, abs_zero]
        exact mul_nonneg hc (abs_nonneg _)
      have hcomp := round_error_mass fp s t
        (∑ i : Fin (n + 1), w i) t c A B
        (ih w) hzero
        (by simpa [A] using Finset.abs_sum_le_sum_abs w Finset.univ)
        (le_refl _)
      have hcoeff : (1 + fp.u) * c + fp.u = (1 + fp.u) ^ (n + 1) - 1 := by
        dsimp [c]
        rw [pow_succ]
        ring
      rw [hrec, hsum, hmass]
      simpa [hcoeff] using hcomp

private theorem sum_halves (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
        ∑ i : Fin (2 ^ r), f (rightIndex r i) := by
  have hcard : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  let g : Fin (2 ^ r + 2 ^ r) → ℝ := fun i => f (Fin.cast hcard.symm i)
  have h := Fin.sum_univ_add g
  have hcast : (∑ i : Fin (2 ^ (r + 1)), f i) = ∑ i, g i := by
    simpa [g, finCongr] using (Equiv.sum_comp (finCongr hcard.symm) f).symm
  have hleft : ∀ i : Fin (2 ^ r),
      Fin.cast hcard.symm (Fin.castAdd (2 ^ r) i) = leftIndex r i := by
    intro i
    apply Fin.ext
    rfl
  have hright : ∀ i : Fin (2 ^ r),
      Fin.cast hcard.symm (Fin.natAdd (2 ^ r) i) = rightIndex r i := by
    intro i
    apply Fin.ext
    simp [rightIndex, Fin.natAdd, Nat.add_comm]
  rw [hcast, h]
  simp only [g, hleft, hright]

private theorem pairwise_error_pow (fp : StandardAddModel) :
    ∀ r : ℕ, ∀ v : Fin (2 ^ r) → ℝ,
      |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        ((1 + fp.u) ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| := by
  intro r
  induction r with
  | zero =>
      intro v
      simp [pairwiseSum]
  | succ r ih =>
      intro v
      let l : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let q : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let x := pairwiseSum fp.fl_add r l
      let y := pairwiseSum fp.fl_add r q
      let a := ∑ i : Fin (2 ^ r), l i
      let b := ∑ i : Fin (2 ^ r), q i
      let A := ∑ i : Fin (2 ^ r), |l i|
      let B := ∑ i : Fin (2 ^ r), |q i|
      let c := (1 + fp.u) ^ r - 1
      have hrec : pairwiseSum fp.fl_add (r + 1) v = fp.fl_add x y := by
        rfl
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = a + b := by
        simpa [l, q, a, b] using sum_halves r v
      have hmass : (∑ i : Fin (2 ^ (r + 1)), |v i|) = A + B := by
        simpa [l, q, A, B] using sum_halves r (fun i => |v i|)
      have hcomp := round_error_mass fp x y a b c A B
        (ih l) (ih q)
        (by simpa [a, A] using Finset.abs_sum_le_sum_abs l Finset.univ)
        (by simpa [b, B] using Finset.abs_sum_le_sum_abs q Finset.univ)
      have hcoeff : (1 + fp.u) * c + fp.u = (1 + fp.u) ^ (r + 1) - 1 := by
        dsimp [c]
        rw [pow_succ]
        ring
      rw [hrec, hsum, hmass]
      simpa [hcoeff] using hcomp

private theorem recursive_error_pow_nat (fp : StandardAddModel) (n : ℕ)
    (hn : 0 < n) (v : Fin n → ℝ) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      ((1 + fp.u) ^ (n - 1) - 1) * ∑ i : Fin n, |v i| := by
  cases n with
  | zero => omega
  | succ n => simpa using recursive_error_pow fp n v

private theorem index_le_pow_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  have hp : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        omega
  have := hp r
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
  have hmass : 0 ≤ ∑ i : Fin (2 ^ r), |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (v i))
  have hrvalid : GammaValid fp.u r := by
    have hr : (r : ℝ) ≤ ((2 ^ r - 1 : ℕ) : ℝ) := by
      exact_mod_cast index_le_pow_sub_one r
    have hmul := mul_le_mul_of_nonneg_right hr fp.u_nonneg
    dsimp [GammaValid] at hvalid ⊢
    linarith
  constructor
  · exact recursive_running_bound fp (2 ^ r) v
  constructor
  · have hn : 0 < 2 ^ r := pow_pos (by norm_num) _
    exact (recursive_error_pow_nat fp (2 ^ r) hn v).trans
      (mul_le_mul_of_nonneg_right
        (pow_sub_one_le_gamma fp.u fp.u_nonneg (2 ^ r - 1) hvalid) hmass)
  · exact (pairwise_error_pow fp r v).trans
      (mul_le_mul_of_nonneg_right
        (pow_sub_one_le_gamma fp.u fp.u_nonneg r hrvalid) hmass)

end VSCLReuse
