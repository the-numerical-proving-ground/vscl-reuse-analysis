import VSCLReuse.P39.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p39_mul_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * (|x| * |y|) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_mul x y
  rw [h]
  have hu := fp.u_nonneg
  calc
    |(x * y) * (1 + δ) - x * y| = |x * y| * |δ| := by
      rw [show (x * y) * (1 + δ) - x * y = (x * y) * δ by ring, abs_mul]
    _ ≤ |x * y| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * (|x| * |y|) := by rw [abs_mul]; ring

private lemma p39_add_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_add x y
  rw [h]
  calc
    |(x + y) * (1 + δ) - (x + y)| = |x + y| * |δ| := by
      rw [show (x + y) * (1 + δ) - (x + y) = (x + y) * δ by ring, abs_mul]
    _ ≤ |x + y| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|x| + |y|) * fp.u := mul_le_mul_of_nonneg_right (abs_add_le _ _) fp.u_nonneg
    _ = fp.u * (|x| + |y|) := by ring

private lemma p39_rounded_dot_eq_fold (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) :
    p39RoundedDotProduct fp m x y =
      Fin.foldl m (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 := by
  cases m with
  | zero => simp [p39RoundedDotProduct]
  | succ m =>
      simp only [p39RoundedDotProduct, Fin.foldl_succ]
      simp [fp.fl_add_zero]

private lemma p39_dot_zero (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (h : ∀ i, x i * y i = 0) :
    p39RoundedDotProduct fp m x y = 0 := by
  rw [p39_rounded_dot_eq_fold]
  have hm : ∀ i : Fin m, fp.fl_mul (x i) (y i) = 0 := by
    intro i
    obtain ⟨δ, _, hδ⟩ := fp.model_mul (x i) (y i)
    rw [hδ, h i, zero_mul]
  simp only [hm]
  have hzero : ∀ t : ℕ,
      Fin.foldl t (fun acc (_ : Fin t) => fp.fl_add acc 0) 0 = 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => simpa [Fin.foldl_succ, fp.fl_add_zero] using ih
  exact hzero m

private lemma p39_dot_error_pow (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) :
    |p39RoundedDotProduct fp m x y - ∑ i : Fin m, x i * y i| ≤
      ((1 + fp.u) ^ (m + 1) - 1) *
        ∑ i : Fin m, |x i| * |y i| := by
  induction m with
  | zero => simp [p39RoundedDotProduct]
  | succ m ih =>
      let x' : Fin m → ℝ := fun i => x i.castSucc
      let y' : Fin m → ℝ := fun i => y i.castSucc
      let A : ℝ := ∑ i : Fin m, x' i * y' i
      let B : ℝ := ∑ i : Fin m, |x' i| * |y' i|
      let p : ℝ := x (Fin.last m) * y (Fin.last m)
      let q : ℝ := |x (Fin.last m)| * |y (Fin.last m)|
      let z : ℝ := p39RoundedDotProduct fp m x' y'
      let w : ℝ := fp.fl_mul (x (Fin.last m)) (y (Fin.last m))
      have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hq : 0 ≤ q := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hp : |p| = q := by simp [p, q, abs_mul]
      have hprev : |z - A| ≤ ((1 + fp.u) ^ (m + 1) - 1) * B := ih x' y'
      have hw : |w - p| ≤ fp.u * q := p39_mul_error fp _ _
      have hzw : |w| ≤ (1 + fp.u) * q := by
        calc
          |w| = |(w - p) + p| := by congr 1; ring
          _ ≤ |w - p| + |p| := abs_add_le _ _
          _ ≤ fp.u * q + q := by rw [hp]; linarith
          _ = (1 + fp.u) * q := by ring
      have hA : |A| ≤ B := by
        calc
          |A| ≤ ∑ i : Fin m, |x' i * y' i| := Finset.abs_sum_le_sum_abs _ _
          _ = B := by simp [B, abs_mul]
      have hsum : (∑ i : Fin (m + 1), x i * y i) = A + p := by
        simp [Fin.sum_univ_castSucc, A, p, x', y']
      have habs : (∑ i : Fin (m + 1), |x i| * |y i|) = B + q := by
        simp [Fin.sum_univ_castSucc, B, q, x', y']
      have hdot : p39RoundedDotProduct fp (m + 1) x y = fp.fl_add z w := by
        rw [p39_rounded_dot_eq_fold, Fin.foldl_succ_last]
        simp only [← p39_rounded_dot_eq_fold]
        rfl
      have hadd := p39_add_error fp z w
      have hz : |z| ≤ |z - A| + B := by
        calc
          |z| = |(z - A) + A| := by congr 1; ring
          _ ≤ |z - A| + |A| := abs_add_le _ _
          _ ≤ |z - A| + B := by linarith
      have hcore : |fp.fl_add z w - (A + p)| ≤
          (1 + fp.u) * |z - A| + fp.u * B + (2 * fp.u + fp.u ^ 2) * q := by
        calc
          |fp.fl_add z w - (A + p)| =
              |(fp.fl_add z w - (z + w)) + (z - A) + (w - p)| := by
                congr 1; ring
          _ ≤ |fp.fl_add z w - (z + w)| + |z - A| + |w - p| := by
                have h := abs_add_le (fp.fl_add z w - (z + w) + (z - A)) (w - p)
                have h' := abs_add_le (fp.fl_add z w - (z + w)) (z - A)
                linarith
          _ ≤ fp.u * (|z| + |w|) + |z - A| + fp.u * q := by linarith
          _ ≤ (1 + fp.u) * |z - A| + fp.u * B +
                (2 * fp.u + fp.u ^ 2) * q := by nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hz), mul_nonneg fp.u_nonneg (sub_nonneg.mpr hzw)]
      rw [hdot, hsum, habs]
      have hu := fp.u_nonneg
      have hbase : 0 ≤ (1 + fp.u) ^ (m + 1) - 1 := by
        have hpow : 1 ≤ (1 + fp.u) ^ (m + 1) := one_le_pow₀ (by linarith)
        linarith
      have hpow2 : 2 * fp.u + fp.u ^ 2 ≤ (1 + fp.u) ^ (m + 2) - 1 := by
        have hpow : 1 + fp.u ≤ (1 + fp.u) ^ (m + 1) := by
          calc
            1 + fp.u = (1 + fp.u) ^ 1 := by ring
            _ ≤ (1 + fp.u) ^ (m + 1) := pow_le_pow_right₀ (by linarith) (by omega)
        calc
          2 * fp.u + fp.u ^ 2 = (1 + fp.u) * (1 + fp.u) - 1 := by ring
          _ ≤ (1 + fp.u) ^ (m + 1) * (1 + fp.u) - 1 := by
            have := mul_le_mul_of_nonneg_right hpow (by linarith : 0 ≤ 1 + fp.u)
            linarith
          _ = (1 + fp.u) ^ (m + 2) - 1 := by
            simp only [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      have hcoeff : (1 + fp.u) * ((1 + fp.u) ^ (m + 1) - 1) + fp.u =
          (1 + fp.u) ^ (m + 2) - 1 := by rw [pow_succ]; ring
      calc
        |fp.fl_add z w - (A + p)| ≤
            (1 + fp.u) * |z - A| + fp.u * B +
              (2 * fp.u + fp.u ^ 2) * q := hcore
        _ ≤ ((1 + fp.u) ^ (m + 2) - 1) * (B + q) := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + fp.u)
            (sub_nonneg.mpr hprev),
            mul_nonneg hq (sub_nonneg.mpr hpow2)]

private lemma p39_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (n t : ℕ)
    (hv : P39GammaValid u n) (ht : t ≤ n) :
    (1 + u) ^ t - 1 ≤ p39Gamma u n := by
  have hn : (n : ℝ) * u < 1 := hv
  have haux : ∀ s : ℕ, s ≤ n → (1 + u) ^ s * (1 - (s : ℝ) * u) ≤ 1 := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
        intro hs
        have hs' : s ≤ n := by omega
        have hp : 0 ≤ (1 + u) ^ s := pow_nonneg (by linarith) _
        have hstep : (1 + u) * (1 - ((s + 1 : ℕ) : ℝ) * u) ≤
            1 - (s : ℝ) * u := by
          push_cast
          nlinarith [mul_nonneg (show 0 ≤ (s : ℝ) + 1 by positivity) (sq_nonneg u)]
        calc
          (1 + u) ^ (s + 1) * (1 - ((s + 1 : ℕ) : ℝ) * u) =
              (1 + u) ^ s * ((1 + u) * (1 - ((s + 1 : ℕ) : ℝ) * u)) := by
                rw [pow_succ]; ring
          _ ≤ (1 + u) ^ s * (1 - (s : ℝ) * u) :=
            mul_le_mul_of_nonneg_left hstep hp
          _ ≤ 1 := ih hs'
  have hp : 0 ≤ (1 + u) ^ t := pow_nonneg (by linarith) _
  have hcast : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht
  have hcomp : 1 - (n : ℝ) * u ≤ 1 - (t : ℝ) * u := by nlinarith
  have hmul : (1 + u) ^ t * (1 - (n : ℝ) * u) ≤ 1 := by
    calc
      _ ≤ (1 + u) ^ t * (1 - (t : ℝ) * u) := mul_le_mul_of_nonneg_left hcomp hp
      _ ≤ 1 := haux t ht
  have hpos : 0 < 1 - (n : ℝ) * u := by linarith
  have hdiv : (1 + u) ^ t ≤ 1 / (1 - (n : ℝ) * u) := by
    apply (le_div_iff₀ hpos).2
    simpa [mul_comm] using hmul
  unfold p39Gamma
  have hnonzero : 1 - (n : ℝ) * u ≠ 0 := ne_of_gt hpos
  have hident : 1 / (1 - (n : ℝ) * u) - 1 =
      (n : ℝ) * u / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  linarith

private lemma p39_step_other_column (fp : P39FPModel) (n : ℕ)
    (L X : P39Matrix n n) (j r i : Fin n) (h : r ≠ j) :
    p39Method2SourceStep fp n L X j i r = X i r := by
  simp [p39Method2SourceStep, h]

private lemma p39_steps_preserve (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n)
    (i j : Fin n) (hj : k ≤ j.val) :
    p39Method2SourceSteps fp n L k hk X i j = X i j := by
  induction k generalizing X with
  | zero => rfl
  | succ k ih =>
      have hkn : k < n := by omega
      have hkj : (⟨k, hkn⟩ : Fin n) ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
        (p39Method2SourceStep fp n L X ⟨k, hkn⟩) i j = X i j
      rw [ih (Nat.le_of_succ_le hk) _ (by omega)]
      exact p39_step_other_column fp n L X _ _ i (Ne.symm hkj)

private lemma p39_step_col_congr (fp : P39FPModel) (n : ℕ)
    (L X Y : P39Matrix n n) (j i : Fin n)
    (h : ∀ r : Fin n, j.val < r.val → X i r = Y i r) :
    p39Method2SourceStep fp n L X j i j =
      p39Method2SourceStep fp n L Y j i j := by
  simp only [p39Method2SourceStep, dite_true]
  split_ifs with hij hijlt
  · rfl
  · congr 1
    congr 1
    funext t
    exact h _ (by change j.val < j.val + 1 + t.val; omega)
  · rfl

private lemma p39_steps_fixed_column (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n)
    (i j : Fin n) (hj : j.val < k) :
    let Y := p39Method2SourceSteps fp n L k hk X
    Y i j = p39Method2SourceStep fp n L Y j i j := by
  induction k generalizing X with
  | zero => omega
  | succ k ih =>
      have hkn : k < n := by omega
      let jk : Fin n := ⟨k, hkn⟩
      let Z := p39Method2SourceStep fp n L X jk
      let Y := p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk) Z
      change Y i j = p39Method2SourceStep fp n L Y j i j
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · exact ih (Nat.le_of_succ_le hk) Z hlt
      · have hjk : j = jk := Fin.ext heq
        subst j
        have hcol : Y i jk = Z i jk := p39_steps_preserve fp n L k
          (Nat.le_of_succ_le hk) Z i jk (le_refl k)
        rw [hcol]
        apply p39_step_col_congr fp n L X Y jk i
        intro r hr
        have hpres : Y i r = Z i r := p39_steps_preserve fp n L k
          (Nat.le_of_succ_le hk) Z i r (by omega)
        rw [hpres]
        exact (p39_step_other_column fp n L X jk r i (by intro e; have := congrArg Fin.val e; omega)).symm

private lemma p39_inverse_fixed_column (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) :
    let X := p39Method2SourceInverse fp n L
    X i j = p39Method2SourceStep fp n L X j i j := by
  exact p39_steps_fixed_column fp n L n (le_refl n) 0 i j j.isLt

private def p39_tail_equiv (n : ℕ) (j : Fin n) :
    Fin (n - j.val - 1) ≃ {k : Fin n // j.val < k.val} where
  toFun t := ⟨⟨j.val + 1 + t.val, by omega⟩, by
    change j.val < j.val + 1 + t.val
    omega⟩
  invFun q := ⟨q.val.val - j.val - 1, by
    have hq := q.property
    have hqn := q.val.isLt
    omega⟩
  left_inv t := by
    apply Fin.ext
    simp only []
    omega
  right_inv q := by
    apply Subtype.ext
    apply Fin.ext
    simp only []
    have hq := q.property
    omega

private lemma p39_tail_sum (n : ℕ) (j : Fin n) (f : Fin n → ℝ) :
    (∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩) =
      ∑ k : Fin n, if j.val < k.val then f k else 0 := by
  let e := p39_tail_equiv n j
  have he := Fintype.sum_equiv e
    (fun t : Fin (n - j.val - 1) => f ⟨j.val + 1 + t.val, by omega⟩)
    (fun q : {k : Fin n // j.val < k.val} => f q.val)
    (by intro t; rfl)
  rw [he]
  have hf : (∑ q : {k : Fin n // j.val < k.val}, f q.val) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k => j.val < k.val), f k := by
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun k => j.val < k.val) f)
  rw [hf]
  simp [Finset.sum_ite]

private lemma p39_sum_diag_tail (n : ℕ) (j : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ k : Fin n, k.val < j.val → f k = 0) :
    (∑ k : Fin n, f k) = f j +
      ∑ k : Fin n, if j.val < k.val then f k else 0 := by
  have hp : ∀ k : Fin n,
      f k = (if k = j then f k else 0) + (if j.val < k.val then f k else 0) := by
    intro k
    by_cases hkj : k = j
    · subst k
      simp
    · by_cases hjk : j.val < k.val
      · simp [hkj, hjk]
      · have hlt : k.val < j.val := by omega
        simp [hkj, hjk, hzero k hlt]
  calc
    (∑ k : Fin n, f k) =
        ∑ k : Fin n, ((if k = j then f k else 0) +
          (if j.val < k.val then f k else 0)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact hp k
    _ = f j + ∑ k : Fin n, if j.val < k.val then f k else 0 := by
      rw [Finset.sum_add_distrib]
      simp

private lemma p39_two_factor_error (u δ ε : ℝ)
    (hu : 0 ≤ u) (hδ : |δ| ≤ u) (hε : |ε| ≤ u) :
    |1 - (1 + δ) * (1 + ε)| ≤ 2 * u + u ^ 2 := by
  have hmul : |δ| * |ε| ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (abs_nonneg ε),
      mul_nonneg hu (sub_nonneg.mpr hε)]
  have htri : |δ + ε + δ * ε| ≤ |δ| + |ε| + |δ| * |ε| := by
    calc
      |δ + ε + δ * ε| ≤ |δ + ε| + |δ * ε| := abs_add_le _ _
      _ ≤ |δ| + |ε| + |δ| * |ε| := by rw [abs_mul]; linarith [abs_add_le δ ε]
  have heq : 1 - (1 + δ) * (1 + ε) = -(δ + ε + δ * ε) := by ring
  rw [heq, abs_neg]
  linarith

private lemma p39_reciprocal_error (u δ : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) (hδ : |δ| ≤ u) :
    |δ| ≤ u / (1 - u) * |1 + δ| := by
  have hpos : 0 < 1 - u := by linarith
  have hlow : 1 - u ≤ |1 + δ| := by
    have := abs_add_le (1 + δ) (-δ)
    simp only [add_neg_cancel_right, abs_one, abs_neg] at this
    linarith
  have hmul : |δ| * (1 - u) ≤ u * |1 + δ| := by
    calc
      |δ| * (1 - u) ≤ u * (1 - u) :=
        mul_le_mul_of_nonneg_right hδ (le_of_lt hpos)
      _ ≤ u * |1 + δ| := mul_le_mul_of_nonneg_left hlow hu
  apply (le_div_iff₀ hpos).2 at hmul
  convert hmul using 1; ring

private lemma p39_inverse_upper (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hij : i.val < j.val) :
    p39Method2SourceInverse fp n L i j = 0 := by
  have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
  have hnot : ¬ j < i := by intro h; have := (Fin.lt_def).mp h; omega
  rw [p39_inverse_fixed_column]
  simp [p39Method2SourceStep, hne, hnot]

private lemma p39_inverse_diag (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (j : Fin n) :
    p39Method2SourceInverse fp n L j j = fp.fl_div 1 (L j j) := by
  rw [p39_inverse_fixed_column]
  simp [p39Method2SourceStep]

private lemma p39_inverse_lower (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hij : j.val < i.val) :
    p39Method2SourceInverse fp n L i j =
      fp.fl_mul (-fp.fl_div 1 (L j j))
        (p39RoundedDotProduct fp (n - j.val - 1)
          (fun t => p39Method2SourceInverse fp n L i ⟨j.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
  have hlt : j < i := hij
  rw [p39_inverse_fixed_column]
  simp [p39Method2SourceStep, hne, hlt]

private lemma p39_matmul_split (n : ℕ) (X L : P39Matrix n n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (i j : Fin n) :
    p39MatMul X L i j = X i j * L j j +
      ∑ t : Fin (n - j.val - 1),
        X i ⟨j.val + 1 + t.val, by omega⟩ *
          L ⟨j.val + 1 + t.val, by omega⟩ j := by
  unfold p39MatMul
  rw [p39_sum_diag_tail n j (fun k => X i k * L k j)]
  · rw [← p39_tail_sum]
  · intro k hk
    rw [hL k j hk, mul_zero]

private lemma p39_abssum_split (n : ℕ) (X L : P39Matrix n n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (i j : Fin n) :
    (∑ k : Fin n, |X i k| * |L k j|) = |X i j| * |L j j| +
      ∑ t : Fin (n - j.val - 1),
        |X i ⟨j.val + 1 + t.val, by omega⟩| *
          |L ⟨j.val + 1 + t.val, by omega⟩ j| := by
  rw [p39_sum_diag_tail n j (fun k => |X i k| * |L k j|)]
  · rw [← p39_tail_sum]
  · intro k hk
    rw [hL k j hk]
    simp

private lemma p39_offdiag_scalar_bound (fp : P39FPModel)
    (a d z T B g δ : ℝ) (ha : a ≠ 0)
    (hd : d = (1 / a) * (1 + δ))
    (hδ : |δ| ≤ fp.u)
    (hz : |z - T| ≤ g * B) (hT : |T| ≤ B) :
    |fp.fl_mul (-d) z * a + T| ≤
      (g + (2 * fp.u + fp.u ^ 2) * (1 + g)) * B := by
  obtain ⟨ε, hε, hmul⟩ := fp.model_mul (-d) z
  let M := 2 * fp.u + fp.u ^ 2
  have hM : 0 ≤ M := by dsimp [M]; nlinarith [sq_nonneg fp.u, fp.u_nonneg]
  have hfac : |1 - (1 + δ) * (1 + ε)| ≤ M :=
    p39_two_factor_error fp.u δ ε fp.u_nonneg hδ hε
  have hda : d * a = 1 + δ := by
    rw [hd]
    field_simp
  have hx : fp.fl_mul (-d) z * a = -((1 + δ) * (1 + ε) * z) := by
    rw [hmul]
    calc
      (-d * z) * (1 + ε) * a = -(d * a) * (1 + ε) * z := by ring
      _ = -((1 + δ) * (1 + ε) * z) := by rw [hda]; ring
  have hzabs : |z| ≤ (1 + g) * B := by
    calc
      |z| = |(z - T) + T| := by congr 1; ring
      _ ≤ |z - T| + |T| := abs_add_le _ _
      _ ≤ (1 + g) * B := by nlinarith
  calc
    |fp.fl_mul (-d) z * a + T| =
        |(T - z) + z * (1 - (1 + δ) * (1 + ε))| := by
          rw [hx]
          congr 1
          ring
    _ ≤ |T - z| + |z| * |1 - (1 + δ) * (1 + ε)| := by
      simpa [abs_mul] using abs_add_le (T - z) (z * (1 - (1 + δ) * (1 + ε)))
    _ ≤ g * B + M * ((1 + g) * B) := by
      have hfirst : |T - z| ≤ g * B := by simpa [abs_sub_comm] using hz
      have hsecond : |z| * |1 - (1 + δ) * (1 + ε)| ≤ M * ((1 + g) * B) := by
        calc
          _ ≤ |z| * M := mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
          _ ≤ ((1 + g) * B) * M := mul_le_mul_of_nonneg_right hzabs hM
          _ = M * ((1 + g) * B) := by ring
      linarith
    _ = (g + M * (1 + g)) * B := by ring

/-- Complete Method 2 left-residual result of Lemma 2.1. -/
theorem p39_c2_method2_lemma21_left_residual
    (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (hdiag : ∀ j : Fin n, L j j ≠ 0)
    (hvalid : P39GammaValid fp.u n) (i j : Fin n) :
    let X := p39Method2SourceInverse fp n L
    |p39MatMul X L i j - if i = j then 1 else 0| ≤
      p39Method2SourceUniformCoefficient fp n *
        ∑ k : Fin n, |X i k| * |L k j| := by
  -- PROOF_START P39-C2-H001
  let X := p39Method2SourceInverse fp n L
  change |p39MatMul X L i j - (if i = j then 1 else 0)| ≤
    p39Method2SourceUniformCoefficient fp n *
      ∑ k : Fin n, |X i k| * |L k j|
  have hn1 : 1 ≤ n := by have := j.isLt; omega
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnu : (n : ℝ) * fp.u < 1 := hvalid
  have hu1 : fp.u < 1 := by
    have hm := mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) fp.u_nonneg
    nlinarith
  have hden : 0 < 1 - fp.u := by linarith
  have hngden : 0 < 1 - (n : ℝ) * fp.u := by linarith
  have hG : 0 ≤ p39Gamma fp.u n := by
    unfold p39Gamma
    exact div_nonneg (mul_nonneg hnnonneg fp.u_nonneg) (le_of_lt hngden)
  let M := 2 * fp.u + fp.u ^ 2
  let D := fp.u / (1 - fp.u)
  let G := p39Gamma fp.u n
  let C := p39Method2SourceUniformCoefficient fp n
  have hM : 0 ≤ M := by dsimp [M]; nlinarith [sq_nonneg fp.u, fp.u_nonneg]
  have hD : 0 ≤ D := div_nonneg fp.u_nonneg (le_of_lt hden)
  have hCeq : C = G + M * (1 + G) + D := rfl
  have hC : 0 ≤ C := by
    rw [hCeq]
    nlinarith [mul_nonneg hM (show 0 ≤ 1 + G by dsimp [G]; linarith)]
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
    have hzero : p39MatMul X L i j = 0 := by
      unfold p39MatMul
      apply Finset.sum_eq_zero
      intro k _
      by_cases hkj : k.val < j.val
      · rw [hL k j hkj, mul_zero]
      · have hik : i.val < k.val := by omega
        have hx : X i k = 0 := p39_inverse_upper fp n L i k hik
        rw [hx, zero_mul]
    have hsum : 0 ≤ ∑ k : Fin n, |X i k| * |L k j| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    simpa [hzero, hne] using mul_nonneg hC hsum
  · have heq : i = j := Fin.ext hij
    subst i
    let a := L j j
    let d := fp.fl_div 1 a
    obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 a (hdiag j)
    have hda : d * a = 1 + δ := by
      change fp.fl_div 1 a * a = 1 + δ
      rw [hd]
      field_simp [show a ≠ 0 from hdiag j]
    have htailzero :
        (∑ t : Fin (n - j.val - 1),
          X j ⟨j.val + 1 + t.val, by omega⟩ *
            L ⟨j.val + 1 + t.val, by omega⟩ j) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      have hx : X j ⟨j.val + 1 + t.val, by omega⟩ = 0 :=
        p39_inverse_upper fp n L j _ (by change j.val < j.val + 1 + t.val; omega)
      rw [hx, zero_mul]
    have hprod : p39MatMul X L j j = d * a := by
      rw [p39_matmul_split n X L hL j j, htailzero, add_zero]
      have hx : X j j = d := p39_inverse_diag fp n L j
      rw [hx]
    have hB : 0 ≤
        ∑ t : Fin (n - j.val - 1),
          |X j ⟨j.val + 1 + t.val, by omega⟩| *
            |L ⟨j.val + 1 + t.val, by omega⟩ j| :=
      Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hsum : |d| * |a| ≤ ∑ k : Fin n, |X j k| * |L k j| := by
      rw [p39_abssum_split n X L hL j j]
      have hx : X j j = d := p39_inverse_diag fp n L j
      rw [hx]
      change |d| * |a| ≤ |d| * |a| + _
      linarith
    have hrec := p39_reciprocal_error fp.u δ fp.u_nonneg hu1 hδ
    have hdabs : |d| * |a| = |1 + δ| := by rw [← abs_mul, hda]
    have hres : |p39MatMul X L j j - 1| ≤ D * (|d| * |a|) := by
      rw [hprod, hda, show 1 + δ - 1 = δ by ring, hdabs]
      exact hrec
    have hDle : D ≤ C := by
      rw [hCeq]
      nlinarith [mul_nonneg hM (show 0 ≤ 1 + G by dsimp [G]; linarith)]
    have hdiagabs : 0 ≤ |d| * |a| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hfinal : D * (|d| * |a|) ≤
        C * ∑ k : Fin n, |X j k| * |L k j| := by
      calc
        _ ≤ C * (|d| * |a|) := mul_le_mul_of_nonneg_right hDle hdiagabs
        _ ≤ C * ∑ k : Fin n, |X j k| * |L k j| := mul_le_mul_of_nonneg_left hsum hC
    simpa using hres.trans hfinal
  · have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
    let m := n - j.val - 1
    let x : Fin m → ℝ := fun t => X i ⟨j.val + 1 + t.val, by omega⟩
    let y : Fin m → ℝ := fun t => L ⟨j.val + 1 + t.val, by omega⟩ j
    let T : ℝ := ∑ t : Fin m, x t * y t
    let B : ℝ := ∑ t : Fin m, |x t| * |y t|
    let z := p39RoundedDotProduct fp m x y
    let a := L j j
    let d := fp.fl_div 1 a
    have hB : 0 ≤ B :=
      Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hT : |T| ≤ B := by
      calc
        |T| ≤ ∑ t : Fin m, |x t * y t| := Finset.abs_sum_le_sum_abs _ _
        _ = B := by simp [B, abs_mul]
    have hmn : m + 1 ≤ n := by dsimp [m]; omega
    have hpw := p39_pow_le_gamma fp.u fp.u_nonneg n (m + 1) hvalid hmn
    have hz0 := p39_dot_error_pow fp m x y
    have hz : |z - T| ≤ G * B := by
      calc
        _ ≤ ((1 + fp.u) ^ (m + 1) - 1) * B := hz0
        _ ≤ G * B := mul_le_mul_of_nonneg_right hpw hB
    obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 a (hdiag j)
    have hlocal := p39_offdiag_scalar_bound fp a d z T B G δ
      (hdiag j) hd hδ hz hT
    have hprod : p39MatMul X L i j = fp.fl_mul (-d) z * a + T := by
      rw [p39_matmul_split n X L hL i j]
      have hx : X i j = fp.fl_mul (-d) z := p39_inverse_lower fp n L i j hij
      rw [hx]
    have habs : (∑ k : Fin n, |X i k| * |L k j|) =
        |X i j| * |a| + B := by
      rw [p39_abssum_split n X L hL i j]
    have hlocalC : G + M * (1 + G) ≤ C := by rw [hCeq]; linarith
    have hdiagabs : 0 ≤ |X i j| * |a| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hrest : |p39MatMul X L i j - (if i = j then 1 else 0)| ≤
        C * (|X i j| * |a| + B) := by
      rw [if_neg hne, sub_zero, hprod]
      calc
        |fp.fl_mul (-d) z * a + T| ≤ (G + M * (1 + G)) * B := hlocal
        _ ≤ C * B := mul_le_mul_of_nonneg_right hlocalC hB
        _ ≤ C * (|X i j| * |a| + B) := by
          apply mul_le_mul_of_nonneg_left _ hC
          linarith
    simpa [habs] using hrest

end VSCLReuse
