import VSCLReuse.P51.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p51Dot_one (fp : P51FPModel) (a x : Fin 1 → ℝ) :
    p51Dot fp 1 a x = fp.fl_mul (a 0) (x 0) := by
  simp [p51Dot]

private theorem p51Dot_succ_succ (fp : P51FPModel) (k : ℕ)
    (a x : Fin (k + 2) → ℝ) :
    p51Dot fp (k + 2) a x =
      fp.fl_add
        (p51Dot fp (k + 1) (fun t => a t.castSucc) (fun t => x t.castSucc))
        (fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))) := by
  simp only [p51Dot, Fin.foldl_succ_last]
  rfl

private theorem p51_round_step (u c s z e δ : ℝ) (hu : 0 ≤ u)
    (he : |e| ≤ u) (hδ : |δ| ≤ u) :
    |(c + z * (1 + e)) * (1 + δ) - (s + z)| ≤
      (1 + u) * |c - s| + u * |s| + (2 * u + u ^ 2) * |z| := by
  have hfactor : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  have hprod : |e| * |δ| ≤ u * u :=
    mul_le_mul he hδ (abs_nonneg _) hu
  have hcross : |e + δ + e * δ| ≤ 2 * u + u ^ 2 := by
    calc
      |e + δ + e * δ| ≤ |e + δ| + |e * δ| := abs_add_le _ _
      _ ≤ |e| + |δ| + |e| * |δ| := by
        rw [abs_mul]
        linarith [abs_add_le e δ]
      _ ≤ 2 * u + u ^ 2 := by nlinarith [hprod]
  have hid : (c + z * (1 + e)) * (1 + δ) - (s + z) =
      (c - s) * (1 + δ) + s * δ + z * (e + δ + e * δ) := by ring
  rw [hid]
  calc
    |(c - s) * (1 + δ) + s * δ + z * (e + δ + e * δ)| ≤
        |(c - s) * (1 + δ)| + |s * δ| + |z * (e + δ + e * δ)| := by
          linarith [abs_add_le ((c - s) * (1 + δ) + s * δ)
            (z * (e + δ + e * δ)), abs_add_le ((c - s) * (1 + δ)) (s * δ)]
    _ = |c - s| * |1 + δ| + |s| * |δ| + |z| * |e + δ + e * δ| := by
          simp only [abs_mul]
    _ ≤ (1 + u) * |c - s| + u * |s| + (2 * u + u ^ 2) * |z| := by
          nlinarith [mul_le_mul_of_nonneg_left hfactor (abs_nonneg (c - s)),
            mul_le_mul_of_nonneg_left hδ (abs_nonneg s),
            mul_le_mul_of_nonneg_left hcross (abs_nonneg z)]

private theorem p51Dot_pow_bound (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      ((1 + fp.u) ^ k - 1) * ∑ t : Fin k, |a t| * |x t| := by
  induction k with
  | zero => simp [p51Dot]
  | succ k ih =>
    cases k with
    | zero =>
      obtain ⟨e, he, hmul⟩ := fp.model_mul (a 0) (x 0)
      rw [p51Dot_one, hmul]
      simp
      have hid : a 0 * x 0 * (1 + e) - a 0 * x 0 = a 0 * x 0 * e := by ring
      rw [hid, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left he
        (mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (x 0)))]
    | succ k =>
      let c := p51Dot fp (k + 1)
        (fun t => a t.castSucc) (fun t => x t.castSucc)
      let s := ∑ t : Fin (k + 1), a t.castSucc * x t.castSucc
      let t := ∑ j : Fin (k + 1), |a j.castSucc| * |x j.castSucc|
      let z := a (Fin.last (k + 1)) * x (Fin.last (k + 1))
      let v := |a (Fin.last (k + 1))| * |x (Fin.last (k + 1))|
      have hprev : |c - s| ≤ ((1 + fp.u) ^ (k + 1) - 1) * t :=
        ih (fun j => a j.castSucc) (fun j => x j.castSucc)
      have hs : |s| ≤ t := by
        dsimp [s, t]
        calc
          |∑ j : Fin (k + 1), a j.castSucc * x j.castSucc| ≤
              ∑ j : Fin (k + 1), |a j.castSucc * x j.castSucc| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin (k + 1), |a j.castSucc| * |x j.castSucc| := by
                simp only [abs_mul]
      have ht : 0 ≤ t := Finset.sum_nonneg (fun j _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hv : 0 ≤ v := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hz : |z| = v := by simp [z, v, abs_mul]
      obtain ⟨e, he, hmul⟩ := fp.model_mul
        (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add c (fp.fl_mul
        (a (Fin.last (k + 1))) (x (Fin.last (k + 1))))
      have hstep : |(c + z * (1 + e)) * (1 + δ) - (s + z)| ≤
          (1 + fp.u) * |c - s| + fp.u * |s| +
            (2 * fp.u + fp.u ^ 2) * |z| :=
        p51_round_step fp.u c s z e δ fp.u_nonneg he hδ
      have hpow : 1 + fp.u ≤ (1 + fp.u) ^ (k + 1) := by
        simpa using (pow_le_pow_right₀ (by linarith [fp.u_nonneg] :
          (1 : ℝ) ≤ 1 + fp.u) (by omega : 1 ≤ k + 1))
      have hcoef : 2 * fp.u + fp.u ^ 2 ≤ (1 + fp.u) ^ (k + 2) - 1 := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        calc
          2 * fp.u + fp.u ^ 2 = (1 + fp.u) * (1 + fp.u) - 1 := by ring
          _ ≤ (1 + fp.u) ^ (k + 1) * (1 + fp.u) - 1 :=
            sub_le_sub_right (mul_le_mul_of_nonneg_right hpow
              (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)) 1
      have hbig : |(c + z * (1 + e)) * (1 + δ) - (s + z)| ≤
          ((1 + fp.u) ^ (k + 2) - 1) * (t + v) := by
        have hT : (1 + fp.u) * |c - s| + fp.u * |s| ≤
            ((1 + fp.u) ^ (k + 2) - 1) * t := by
          calc
            _ ≤ (1 + fp.u) * (((1 + fp.u) ^ (k + 1) - 1) * t) +
                fp.u * t := add_le_add
                  (mul_le_mul_of_nonneg_left hprev (by linarith [fp.u_nonneg]))
                  (mul_le_mul_of_nonneg_left hs fp.u_nonneg)
            _ = ((1 + fp.u) ^ (k + 2) - 1) * t := by
              rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
              ring
        have hZ : (2 * fp.u + fp.u ^ 2) * |z| ≤
            ((1 + fp.u) ^ (k + 2) - 1) * v := by
          rw [hz]
          exact mul_le_mul_of_nonneg_right hcoef hv
        calc
          _ ≤ (1 + fp.u) * |c - s| + fp.u * |s| +
              (2 * fp.u + fp.u ^ 2) * |z| := hstep
          _ ≤ ((1 + fp.u) ^ (k + 2) - 1) * t +
              ((1 + fp.u) ^ (k + 2) - 1) * v := add_le_add hT hZ
          _ = ((1 + fp.u) ^ (k + 2) - 1) * (t + v) := by ring
      have hdot : p51Dot fp (k + 2) a x = (c + z * (1 + e)) * (1 + δ) := by
        rw [p51Dot_succ_succ]
        change fp.fl_add c (fp.fl_mul (a (Fin.last (k + 1)))
          (x (Fin.last (k + 1)))) = _
        rw [hadd, hmul]
      have hsum : (∑ j : Fin (k + 2), a j * x j) = s + z := by
        rw [Fin.sum_univ_castSucc]
      have hmass : (∑ j : Fin (k + 2), |a j| * |x j|) = t + v := by
        rw [Fin.sum_univ_castSucc]
      rw [hdot, hsum, hmass]
      exact hbig

private theorem p51_pow_factor (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 0 ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hfactor : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
        1 - (k : ℝ) * u := by
      have hid : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
          (1 - (k : ℝ) * u) - ((k + 1 : ℕ) : ℝ) * u ^ 2 := by
        push_cast
        ring
      rw [hid]
      nlinarith [mul_nonneg hk (sq_nonneg u)]
    calc
      (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
          (1 + u) ^ k * ((1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
            rw [pow_succ]
            ring
      _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) :=
        mul_le_mul_of_nonneg_left hfactor (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

private theorem p51_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (k l : ℕ)
    (hkl : k ≤ l) (hvalid : P51GammaValid u l) :
    (1 + u) ^ k - 1 ≤ p51Gamma u l := by
  have hp : (1 + u) ^ k ≤ (1 + u) ^ l :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + u) hkl
  have hden : 0 < 1 - (l : ℝ) * u := sub_pos.mpr hvalid
  have hle := p51_pow_factor u hu l
  have hgamma : (1 + u) ^ l - 1 ≤ p51Gamma u l := by
    unfold p51Gamma
    apply (le_div_iff₀ hden).2
    calc
      ((1 + u) ^ l - 1) * (1 - (l : ℝ) * u) =
          (1 + u) ^ l * (1 - (l : ℝ) * u) - 1 + (l : ℝ) * u := by ring
      _ ≤ (l : ℝ) * u := by linarith
  linarith

private theorem p51Dot_gamma_bound (fp : P51FPModel) (k l : ℕ)
    (a x : Fin k → ℝ) (hkl : k ≤ l) (hvalid : P51GammaValid fp.u l) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p51Gamma fp.u l * ∑ t : Fin k, |a t| * |x t| := by
  have hsum : 0 ≤ ∑ t : Fin k, |a t| * |x t| :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact (p51Dot_pow_bound fp k a x).trans
    (mul_le_mul_of_nonneg_right
      (p51_pow_le_gamma fp.u fp.u_nonneg k l hkl hvalid) hsum)

private theorem p51_schedule_sum {m n l : ℕ}
    (A : Fin m → Fin n → ℝ) (schedule : P51SparseSchedule A l)
    (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.univ.image (schedule.col i)
  have hinj : Set.InjOn (schedule.col i) (Finset.univ : Finset (Fin (schedule.count i))) :=
    fun _ _ _ _ h => schedule.col_injective i h
  have h₁ : (∑ j ∈ s, f j) =
      ∑ t : Fin (schedule.count i), f (schedule.col i t) := by
    exact Finset.sum_image hinj
  have h₂ : (∑ j ∈ s, f j) = ∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro j _ hj
    apply hf j
    by_contra hA
    obtain ⟨t, ht⟩ := schedule.covers i j hA
    exact hj (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
  exact h₁.symm.trans h₂

/-- Complete componentwise sparse matrix-vector result of Lemma 3.2. -/
theorem p51_c2_lemma32 {m n l : ℕ} (fp : P51FPModel)
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (η : ℝ)
    (hln : 2 ≤ l ∧ l < n) (hvalid : P51GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin m) :
    |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, A i j * x j| ≤
      p51Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
      (η * fp.u + p51Gamma fp.u l * (η * fp.u)) *
        (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
  -- PROOF_START P51-C2-H001
  let g := p51Gamma fp.u l
  let q := η * fp.u
  let T := ∑ j : Fin n, |A i j| * |x j|
  let V := ∑ j : Fin n, |p51Sign (A i j)| * |x j|
  let U := ∑ j : Fin n, |Ahat i j| * |x j|
  let S := ∑ j : Fin n, A i j * x j
  let Sh := ∑ j : Fin n, Ahat i j * x j
  let C := p51SparseMatVec fp A Ahat x schedule i
  change |C - S| ≤ g * T + (q + g * q) * V
  have hg : 0 ≤ g := by
    dsimp [g, p51Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
      (le_of_lt (sub_pos.mpr hvalid))
  have hq : 0 ≤ q := mul_nonneg hη.le fp.u_nonneg
  have hpoint : ∀ j, |Ahat i j - A i j| ≤ q * |p51Sign (A i j)| := by
    intro j
    by_cases ha : A i j = 0
    · have hh := hzero i j ha
      simp [ha, hh, p51Sign, q]
    · have hs : |p51Sign (A i j)| = 1 := by
        simp [p51Sign, ha, abs_div, abs_abs, abs_ne_zero.mpr ha]
      simpa [hs, q] using hpre i j ha
  have hhat : ∀ j, |Ahat i j| ≤ |A i j| + q * |p51Sign (A i j)| := by
    intro j
    calc
      |Ahat i j| = |A i j + (Ahat i j - A i j)| := by congr 1; ring
      _ ≤ |A i j| + |Ahat i j - A i j| := abs_add_le _ _
      _ ≤ |A i j| + q * |p51Sign (A i j)| := add_le_add_right (hpoint j) _
  have hsumprod :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) = Sh := by
    exact p51_schedule_sum A schedule i (fun j => Ahat i j * x j)
      (by intro j hj; simp [hzero i j hj])
  have hsumabs :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) = U := by
    exact p51_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
      (by intro j hj; simp [hzero i j hj])
  have hround : |C - Sh| ≤ g * U := by
    change |p51Dot fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) - Sh| ≤ g * U
    rw [← hsumprod, ← hsumabs]
    exact p51Dot_gamma_bound fp (schedule.count i) l _ _
      (schedule.count_le i) hvalid
  have hdiff : |Sh - S| ≤ q * V := by
    dsimp [Sh, S, V]
    calc
      |(∑ j : Fin n, Ahat i j * x j) - ∑ j : Fin n, A i j * x j| =
          |∑ j : Fin n, (Ahat i j - A i j) * x j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ ≤ ∑ j : Fin n, |(Ahat i j - A i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, (q * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hpoint j) (abs_nonneg _)
      _ = q * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hmass : U ≤ T + q * V := by
    dsimp [U, T, V]
    calc
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
          ∑ j : Fin n, (|A i j| + q * |p51Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hhat j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A i j| * |x j|) +
          q * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
            simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
  have hid : C - S = (C - Sh) + (Sh - S) := by ring
  rw [hid]
  calc
    |(C - Sh) + (Sh - S)| ≤ |C - Sh| + |Sh - S| := abs_add_le _ _
    _ ≤ g * U + q * V := add_le_add hround hdiff
    _ ≤ g * (T + q * V) + q * V :=
      add_le_add_left (mul_le_mul_of_nonneg_left hmass hg) _
    _ = g * T + (q + g * q) * V := by ring

end VSCLReuse
