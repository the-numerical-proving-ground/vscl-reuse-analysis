import VSCLReuse.P15.Definitions

namespace VSCLReuse

private theorem p15_normsq_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p15VecNormSq v := by
  unfold p15VecNormSq
  positivity

private theorem p15_normsq_eq_sq {n : ℕ} (v : Fin n → ℝ) :
    p15VecNormSq v = p15VecNorm v ^ 2 := by
  unfold p15VecNorm
  exact (Real.sq_sqrt (p15_normsq_nonneg v)).symm

private theorem p15_frobsq_nonneg {m n : ℕ} (A : P15Matrix m n) :
    0 ≤ p15FrobNormSq A := by
  unfold p15FrobNormSq
  exact Finset.sum_nonneg fun i _ => p15_normsq_nonneg (A i)

private theorem p15_frobsq_eq_sq {m n : ℕ} (A : P15Matrix m n) :
    p15FrobNormSq A = p15FrobNorm A ^ 2 := by
  unfold p15FrobNorm
  exact (Real.sq_sqrt (p15_frobsq_nonneg A)).symm

private theorem p15_frob_of_row_bound {m n : ℕ}
    (A B : P15Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, p15VecNorm (A i) ≤ c * p15VecNorm (B i)) :
    p15FrobNorm A ≤ c * p15FrobNorm B := by
  have hsq : p15FrobNormSq A ≤ c ^ 2 * p15FrobNormSq B := by
    rw [p15FrobNormSq, p15FrobNormSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [p15_normsq_eq_sq, p15_normsq_eq_sq]
    have hA : 0 ≤ p15VecNorm (A i) := Real.sqrt_nonneg _
    have hB : 0 ≤ p15VecNorm (B i) := Real.sqrt_nonneg _
    nlinarith [h i]
  rw [p15_frobsq_eq_sq, p15_frobsq_eq_sq] at hsq
  rw [← mul_pow] at hsq
  have hA : 0 ≤ p15FrobNorm A := Real.sqrt_nonneg _
  have hB : 0 ≤ p15FrobNorm B := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hc hB]

private theorem p15_numeric_bound (n : ℕ) (u xNorm : ℝ)
    (hu : 0 ≤ u) (hx : 0 ≤ xNorm) :
    ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * u * xNorm) *
        Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 * u * xNorm := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hs3 : Real.sqrt (3 : ℝ) ≤ 20 / 11 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hcoef : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
    nlinarith
  have heq :
      ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * u * xNorm) *
          Real.sqrt (3 * (n : ℝ)) =
        ((11 : ℝ) / 10 * Real.sqrt 3) *
          ((n : ℝ) ^ 2 * u * xNorm) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * u * xNorm *
          (Real.sqrt 3 * Real.sqrt n) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            (Real.sqrt n * Real.sqrt n) * (n : ℝ) * u * xNorm := by ring
      _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * u * xNorm) := by
        rw [Real.mul_self_sqrt hn]
        ring
  rw [heq]
  have hprod : 0 ≤ (n : ℝ) ^ 2 * u * xNorm := by positivity
  nlinarith

private theorem p15_gamma_step_estimates (u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hvalid : t + u < 1) :
    (t / (1 - t) + u) / (1 - u) ≤
        (t + u) / (1 - t - u) ∧
      t / (1 - t) + u * (1 + t / (1 - t)) ≤
        (t + u) / (1 - t - u) := by
  have hd0 : 0 < 1 - t := by linarith
  have hd1 : 0 < 1 - t - u := by linarith
  have hdu : 0 < 1 - u := by linarith
  constructor
  · apply (div_le_div_iff₀ hdu hd1).2
    field_simp
    nlinarith [mul_nonneg ht hu]
  · have heq : t / (1 - t) + u * (1 + t / (1 - t)) =
        (t + u) / (1 - t) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ hd0 hd1).2
    nlinarith [mul_nonneg ht hu]

private theorem p15_gamma_step (u t a e : ℝ)
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hvalid : t + u < 1)
    (ha : |a - 1| ≤ t / (1 - t)) (he : |e| ≤ u) :
    |a / (1 + e) - 1| ≤ (t + u) / (1 - t - u) ∧
      |a * (1 + e) - 1| ≤ (t + u) / (1 - t - u) := by
  let g := t / (1 - t)
  have hg : 0 ≤ g := by
    dsimp [g]
    exact div_nonneg ht (by linarith)
  have hden : 0 < 1 + e := by
    have := (abs_le.mp he).1
    linarith
  have hdu : 0 < 1 - u := by linarith
  have haminus : |a - 1 - e| ≤ g + u := by
    calc
      |a - 1 - e| ≤ |a - 1| + |e| := abs_sub _ _
      _ ≤ g + u := add_le_add ha he
  have h1 : |a / (1 + e) - 1| ≤ (g + u) / (1 - u) := by
    have heq : a / (1 + e) - 1 = (a - 1 - e) / (1 + e) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hden]
    have hfirst : |a - 1 - e| / (1 + e) ≤ (g + u) / (1 + e) :=
      div_le_div_of_nonneg_right haminus hden.le
    have hsecond : (g + u) / (1 + e) ≤ (g + u) / (1 - u) := by
      apply (div_le_div_iff₀ hden hdu).2
      have he_lower := (abs_le.mp he).1
      nlinarith [mul_nonneg (show 0 ≤ g + u by positivity)
        (show 0 ≤ e + u by linarith)]
    exact hfirst.trans hsecond
  have habsa : |a| ≤ 1 + g := by
    calc
      |a| = |(a - 1) + 1| := by ring
      _ ≤ |a - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 1 + g := by simp only [abs_one]; linarith
  have h2 : |a * (1 + e) - 1| ≤ g + u * (1 + g) := by
    have heq : a * (1 + e) - 1 = (a - 1) + a * e := by ring
    rw [heq]
    calc
      |(a - 1) + a * e| ≤ |a - 1| + |a * e| := abs_add_le _ _
      _ = |a - 1| + |a| * |e| := by rw [abs_mul]
      _ ≤ g + (1 + g) * u := by
        apply add_le_add ha
        exact mul_le_mul habsa he (abs_nonneg _) (by positivity)
      _ = g + u * (1 + g) := by ring
  have hs := p15_gamma_step_estimates u t hu ht hvalid
  constructor
  · exact h1.trans hs.1
  · exact h2.trans hs.2

private theorem p15_fold_backward (fp : P15FPModel) (k : ℕ)
    (hk : P15GammaValid fp.u k)
    (a q : Fin k → ℝ) (b : ℝ) :
    ∃ (α : ℝ) (β : Fin k → ℝ),
      b = α * Fin.foldl k
          (fun s j => fp.fl_sub s (fp.fl_mul (a j) (q j))) b +
            ∑ j : Fin k, β j * (a j * q j) ∧
      |α - 1| ≤ p15Gamma fp.u k ∧
      ∀ j : Fin k, |β j - 1| ≤ p15Gamma fp.u (j.val + 1) := by
  induction k generalizing b with
  | zero =>
      refine ⟨1, Fin.elim0, ?_, ?_, ?_⟩
      · simp
      · simp [p15Gamma]
      · intro j; exact j.elim0
  | succ k ih =>
      have hku : (k : ℝ) * fp.u + fp.u < 1 := by
        simpa [P15GammaValid, Nat.cast_add, add_mul] using hk
      have hk' : P15GammaValid fp.u k := by
        unfold P15GammaValid
        have hu := fp.u_nonneg
        linarith
      let a' : Fin k → ℝ := fun j => a j.castSucc
      let q' : Fin k → ℝ := fun j => q j.castSucc
      obtain ⟨α, β, hrep, hα, hβ⟩ := ih hk' a' q' b
      let s : ℝ := Fin.foldl k
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a' j) (q' j))) b
      let p : ℝ := a (Fin.last k) * q (Fin.last k)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last k)) (q (Fin.last k))
      obtain ⟨σ, hσ, hsub⟩ :=
        fp.model_sub s (fp.fl_mul (a (Fin.last k)) (q (Fin.last k)))
      have hσpos : 0 < 1 + σ := by
        have hσlo := (abs_le.mp hσ).1
        have hu_lt : fp.u < 1 := by
          nlinarith [mul_nonneg (Nat.cast_nonneg k) fp.u_nonneg]
        linarith
      let α' : ℝ := α / (1 + σ)
      let β' : Fin (k + 1) → ℝ := Fin.snoc β (α * (1 + μ))
      have hfold : Fin.foldl (k + 1)
          (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (q j))) b =
          (s - p * (1 + μ)) * (1 + σ) := by
        rw [Fin.foldl_succ_last]
        change fp.fl_sub s (fp.fl_mul (a (Fin.last k)) (q (Fin.last k))) = _
        rw [hsub, hmul]
      have hαstep := p15_gamma_step fp.u ((k : ℝ) * fp.u) α σ
        fp.u_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) hku
        (by simpa [p15Gamma] using hα) hσ
      have hβstep := p15_gamma_step fp.u ((k : ℝ) * fp.u) α μ
        fp.u_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) hku
        (by simpa [p15Gamma] using hα) hμ
      refine ⟨α', β', ?_, ?_, ?_⟩
      · rw [hfold, Fin.sum_univ_castSucc]
        have hrep' : b = α * s + ∑ j : Fin k, β j * (a' j * q' j) := hrep
        have heq : α' * ((s - p * (1 + μ)) * (1 + σ)) =
            α * (s - p * (1 + μ)) := by
          dsimp [α']
          field_simp
        rw [heq]
        simp only [β', Fin.snoc_castSucc, Fin.snoc_last]
        dsimp [a', q'] at hrep'
        dsimp [p]
        rw [hrep']
        ring
      · dsimp [α']
        convert hαstep.1 using 1 <;> simp [p15Gamma, Nat.cast_add, add_mul] <;> ring
      · intro j
        cases j using Fin.lastCases with
        | last =>
            dsimp [β']
            simp only [Fin.snoc_last, Fin.val_last]
            convert hβstep.2 using 1 <;> simp [p15Gamma, Nat.cast_add, add_mul] <;> ring
        | cast j =>
            simpa [β', Fin.snoc_castSucc] using hβ j

private theorem p15_steps_preserve (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (j : Fin n)
    (hj : j.val < n - k) :
    p15ForwardSubSteps fp n L b k hk x j = x j := by
  induction k generalizing x with
  | zero =>
      rfl
  | succ k ih =>
      have hidx : n - k - 1 < n := by omega
      let idx : Fin n := ⟨n - k - 1, hidx⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L idx ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b idx)
      let x' : Fin n → ℝ := Function.update x idx (fp.fl_div s (L idx idx))
      change p15ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' j = x j
      have hj' : j.val < n - k := by omega
      rw [ih (Nat.le_of_succ_le hk) x' hj']
      have hne : j ≠ idx := by
        intro heq
        have : j.val = idx.val := congrArg Fin.val heq
        dsimp [idx] at this
        omega
      simp [x', hne]

private theorem p15_steps_succ (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k + 1 ≤ n) (x : Fin n → ℝ) :
    p15ForwardSubSteps fp n L b (k + 1) hk x =
      p15ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk)
        (Function.update x ⟨n - k - 1, by omega⟩
          (fp.fl_div
            (Fin.foldl (n - k - 1)
              (fun acc (j : Fin (n - k - 1)) =>
                fp.fl_sub acc
                  (fp.fl_mul
                    (L ⟨n - k - 1, by omega⟩ ⟨j.val, by omega⟩)
                    (x ⟨j.val, by omega⟩)))
              (b ⟨n - k - 1, by omega⟩))
            (L ⟨n - k - 1, by omega⟩ ⟨n - k - 1, by omega⟩))) := by
  rfl

private theorem p15_reach_state (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ)
    (t : ℕ) (ht : t ≤ n) :
    ∃ x : Fin n → ℝ,
      p15ForwardSub fp n L b =
        p15ForwardSubSteps fp n L b (n - t) (by omega) x ∧
      ∀ j : Fin n, j.val < t → x j = p15ForwardSub fp n L b j := by
  induction t with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · simp only [Nat.sub_zero]
        rfl
      · intro j hj
        omega
  | succ t ih =>
      have ht' : t ≤ n := by omega
      obtain ⟨x, hx, hprev⟩ := ih ht'
      have hidx : t < n := by omega
      let ik : Fin n := ⟨t, hidx⟩
      let s := Fin.foldl t
        (fun acc (j : Fin t) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨j.val, by omega⟩)
              (x ⟨j.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hstep :
          p15ForwardSubSteps fp n L b (n - t) (by omega) x =
            p15ForwardSubSteps fp n L b (n - (t + 1)) (by omega) x' := by
        have hcount : n - t = (n - (t + 1)) + 1 := by omega
        have hstart : p15ForwardSubSteps fp n L b (n - t) (by omega) x =
            p15ForwardSubSteps fp n L b ((n - (t + 1)) + 1) (by omega) x := by
          let z1 : {z : ℕ // z ≤ n} := ⟨n - t, by omega⟩
          let z2 : {z : ℕ // z ≤ n} := ⟨n - (t + 1) + 1, by omega⟩
          have hz : z1 = z2 := Subtype.ext hcount
          exact congrArg (fun z : {z : ℕ // z ≤ n} =>
            p15ForwardSubSteps fp n L b z.1 z.2 x) hz
        rw [hstart, p15_steps_succ]
        have hnum : n - (n - (t + 1)) - 1 = t := by omega
        simp only [hnum]
        rfl
      refine ⟨x', hx.trans hstep, ?_⟩
      intro j hj
      by_cases hji : j = ik
      · subst j
        have hpres := p15_steps_preserve fp n L b (n - (t + 1))
          (by omega) x' ik (by dsimp [ik]; omega)
        have hQ : p15ForwardSub fp n L b ik = x' ik := by
          rw [hx.trans hstep]
          exact hpres
        exact hQ.symm
      · have hjt : j.val < t := by
          have : j.val ≤ t := by omega
          have : j.val ≠ t := by
            intro h
            apply hji
            exact Fin.ext h
          omega
        simpa [x', hji] using hprev j hjt

private theorem p15_steps_at (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    p15ForwardSubSteps fp n L b (n - i.val) (by omega) x i =
      fp.fl_div
        (Fin.foldl i.val
          (fun acc (j : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨j.val, by omega⟩)
                (x ⟨j.val, by omega⟩)))
          (b i))
        (L i i) := by
  have hcount : n - i.val = (n - (i.val + 1)) + 1 := by omega
  have hstart : p15ForwardSubSteps fp n L b (n - i.val) (by omega) x i =
      p15ForwardSubSteps fp n L b ((n - (i.val + 1)) + 1) (by omega) x i := by
    let z1 : {z : ℕ // z ≤ n} := ⟨n - i.val, by omega⟩
    let z2 : {z : ℕ // z ≤ n} := ⟨n - (i.val + 1) + 1, by omega⟩
    have hz : z1 = z2 := Subtype.ext hcount
    exact congrArg (fun z : {z : ℕ // z ≤ n} =>
      p15ForwardSubSteps fp n L b z.1 z.2 x i) hz
  rw [hstart, p15_steps_succ]
  have hnum : n - (n - (i.val + 1)) - 1 = i.val := by omega
  simp only [hnum]
  simp only [Fin.val_cast]
  have hpres := p15_steps_preserve fp n L b (n - (i.val + 1))
    (by omega)
    (Function.update x ⟨i.val, by omega⟩
      (fp.fl_div (Fin.foldl i.val
        (fun acc (j : Fin i.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)
              (x ⟨j.val, by omega⟩)))
        (b ⟨i.val, by omega⟩))
        (L ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)))
    i (by omega)
  rw [hpres]
  simp

private theorem p15_forward_local (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) (i : Fin n) :
    p15ForwardSub fp n L b i =
      fp.fl_div
        (Fin.foldl i.val
          (fun acc (j : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨j.val, by omega⟩)
                (p15ForwardSub fp n L b ⟨j.val, by omega⟩)))
          (b i))
        (L i i) := by
  obtain ⟨x, hx, hprev⟩ := p15_reach_state fp n L b i.val i.isLt.le
  calc
    p15ForwardSub fp n L b i =
        p15ForwardSubSteps fp n L b (n - i.val) (by omega) x i :=
      congrFun hx i
    _ = fp.fl_div
          (Fin.foldl i.val
            (fun acc (j : Fin i.val) =>
              fp.fl_sub acc
                (fp.fl_mul (L i ⟨j.val, by omega⟩)
                  (x ⟨j.val, by omega⟩)))
            (b i))
          (L i i) := p15_steps_at fp n L b i x
    _ = _ := by
      congr 1
      apply congrArg (fun f : ℝ → Fin i.val → ℝ => Fin.foldl i.val f (b i))
      funext acc j
      rw [hprev ⟨j.val, lt_trans j.isLt i.isLt⟩ j.isLt]

private theorem p15_gamma_mono (u : ℝ) (a b : ℕ)
    (hu : 0 ≤ u) (hab : a ≤ b) (hb : P15GammaValid u b) :
    p15Gamma u a ≤ p15Gamma u b := by
  have hcast : (a : ℝ) * u ≤ (b : ℝ) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hu
  have hdena : 0 < 1 - (a : ℝ) * u := by
    unfold P15GammaValid at hb
    linarith
  have hdenb : 0 < 1 - (b : ℝ) * u := by
    unfold P15GammaValid at hb
    linarith
  unfold p15Gamma
  apply (div_le_div_iff₀ hdena hdenb).2
  nlinarith

private theorem p15_sum_prefix (n k : ℕ) (hk : k < n)
    (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, k < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ j : Fin k, f ⟨j.val, lt_trans j.isLt hk⟩) + f ⟨k, hk⟩ := by
  let g : ℕ → ℝ := fun r => if hr : r < n then f ⟨r, hr⟩ else 0
  have hn : (∑ j : Fin n, f j) = ∑ r ∈ Finset.range n, g r := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g n)
  have hk' : (∑ j : Fin k, f ⟨j.val, lt_trans j.isLt hk⟩) =
      ∑ r ∈ Finset.range k, g r := by
    calc
      (∑ j : Fin k, f ⟨j.val, lt_trans j.isLt hk⟩) =
          ∑ j : Fin k, g j.val := by
        apply Finset.sum_congr rfl
        intro j _
        simp [g, lt_trans j.isLt hk]
      _ = _ := Fin.sum_univ_eq_sum_range g k
  rw [hn, hk']
  have htail : ∑ r ∈ Finset.Ico (k + 1) n, g r = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrlo : k + 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrhi : r < n := (Finset.mem_Ico.mp hr).2
    simp only [g, dif_pos hrhi]
    exact hzero ⟨r, hrhi⟩ (show k < r by omega)
  have hsplit := Finset.sum_range_add_sum_Ico g (Nat.succ_le_of_lt hk)
  rw [htail, add_zero, Finset.sum_range_succ] at hsplit
  simpa [g, dif_pos hk] using hsplit.symm

private theorem p15_local_backward (fp : P15FPModel) (n : ℕ)
    (hvalid : P15GammaValid fp.u n)
    (i : Fin n) (a q : Fin n → ℝ) (b : ℝ)
    (hdiag : a i ≠ 0)
    (hupper : ∀ j : Fin n, i.val < j.val → a j = 0)
    (hlocal : q i = fp.fl_div
      (Fin.foldl i.val
        (fun acc (j : Fin i.val) =>
          fp.fl_sub acc
            (fp.fl_mul (a ⟨j.val, lt_trans j.isLt i.isLt⟩)
              (q ⟨j.val, lt_trans j.isLt i.isLt⟩)))
        b) (a i)) :
    ∃ δ : Fin n → ℝ,
      (∀ j, |δ j| ≤ p15Gamma fp.u n * |a j|) ∧
      (∑ j : Fin n, (a j + δ j) * q j) = b := by
  let a' : Fin i.val → ℝ := fun j => a ⟨j.val, lt_trans j.isLt i.isLt⟩
  let q' : Fin i.val → ℝ := fun j => q ⟨j.val, lt_trans j.isLt i.isLt⟩
  let s : ℝ := Fin.foldl i.val
    (fun acc j => fp.fl_sub acc (fp.fl_mul (a' j) (q' j))) b
  have hki : P15GammaValid fp.u i.val := by
    unfold P15GammaValid at *
    have hu := fp.u_nonneg
    have hic : (i.val : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr i.isLt.le
    nlinarith
  obtain ⟨α, β, hrep, hα, hβ⟩ := p15_fold_backward fp i.val hki a' q' b
  obtain ⟨ε, hε, hfl⟩ := fp.model_div s (a i) hdiag
  have hdiv : q i = (s / a i) * (1 + ε) := by
    rw [hlocal]
    exact hfl
  have hεpos : 0 < 1 + ε := by
    have hu_lt : fp.u < 1 := by
      have hi1 : (1 : ℝ) ≤ (n : ℝ) := by
        have hi : i.val < n := i.isLt
        exact_mod_cast (show 1 ≤ n by omega)
      have hu := fp.u_nonneg
      unfold P15GammaValid at hvalid
      nlinarith [mul_nonneg (sub_nonneg.mpr hi1) hu]
    have he := (abs_le.mp hε).1
    linarith
  have hs : s = (a i * q i) / (1 + ε) := by
    apply (eq_div_iff hεpos.ne').2
    have hmul : a i * q i = s * (1 + ε) := by
      rw [hdiv]
      field_simp
    exact hmul.symm
  let βdiag : ℝ := α / (1 + ε)
  have hrep' : b = (∑ j : Fin i.val, β j * (a' j * q' j)) +
      βdiag * (a i * q i) := by
    dsimp [s] at hs
    rw [hs] at hrep
    dsimp [βdiag]
    convert hrep using 1 <;> ring
  have hiu : (i.val : ℝ) * fp.u + fp.u < 1 := by
    have hic : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
      norm_cast
      exact Nat.succ_le_of_lt i.isLt
    unfold P15GammaValid at hvalid
    nlinarith [mul_nonneg (sub_nonneg.mpr hic) fp.u_nonneg]
  have hstep := p15_gamma_step fp.u ((i.val : ℝ) * fp.u) α ε
    fp.u_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) hiu
    (by simpa [p15Gamma] using hα) hε
  have hdiagβ : |βdiag - 1| ≤ p15Gamma fp.u n := by
    have hsmall : |βdiag - 1| ≤ p15Gamma fp.u (i.val + 1) := by
      dsimp [βdiag]
      convert hstep.1 using 1 <;> simp [p15Gamma, Nat.cast_add, add_mul] <;> ring
    exact hsmall.trans (p15_gamma_mono fp.u (i.val + 1) n fp.u_nonneg
      (Nat.succ_le_of_lt i.isLt) hvalid)
  let δ : Fin n → ℝ := fun j =>
    if hj : j.val < i.val then (β ⟨j.val, hj⟩ - 1) * a j
    else if j = i then (βdiag - 1) * a j else 0
  have hγnonneg : 0 ≤ p15Gamma fp.u n := by
    unfold p15Gamma P15GammaValid at *
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  refine ⟨δ, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < i.val
    · simp only [δ, dif_pos hj, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (hβ ⟨j.val, hj⟩).trans
        (p15_gamma_mono fp.u (j.val + 1) n fp.u_nonneg (by omega) hvalid)
    · by_cases hji : j = i
      · subst j
        have hδi : δ i = (βdiag - 1) * a i := by simp [δ]
        rw [hδi, abs_mul]
        exact mul_le_mul_of_nonneg_right hdiagβ (abs_nonneg _)
      · have hj' : ¬j < i := hj
        have hδj : δ j = 0 := by simp [δ, hj', hji]
        rw [hδj, abs_zero]
        exact mul_nonneg hγnonneg (abs_nonneg _)
  · have hzero : ∀ j : Fin n, i.val < j.val → (a j + δ j) * q j = 0 := by
      intro j hj
      have haj : a j = 0 := hupper j hj
      have hnot : ¬j.val < i.val := by omega
      have hne : j ≠ i := by
        intro heq
        subst j
        omega
      simp [δ, hnot, hne, haj]
    rw [p15_sum_prefix n i.val i.isLt _ hzero]
    have hprefix :
        (∑ j : Fin i.val,
          (a ⟨j.val, lt_trans j.isLt i.isLt⟩ +
            δ ⟨j.val, lt_trans j.isLt i.isLt⟩) *
            q ⟨j.val, lt_trans j.isLt i.isLt⟩) =
          ∑ j : Fin i.val, β j * (a' j * q' j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [δ, dif_pos j.isLt]
      dsimp [a', q']
      ring
    rw [hprefix]
    have hdiag' : (a i + δ i) * q i = βdiag * (a i * q i) := by
      simp [δ]
      ring
    rw [hdiag']
    exact hrep'.symm

private theorem p15_row_witness (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n) (i : Fin m) :
    ∃ deltaL : P15Matrix n n,
      (∀ k j, |deltaL k j| ≤ p15Gamma fp.u n * |R j k|) ∧
      (∀ k, ∑ j : Fin n,
        (p15Transpose R k j + deltaL k j) *
          p15RoundedQ fp X R i j = X i k) := by
  have hlocal (k : Fin n) :
      ∃ δ : Fin n → ℝ,
        (∀ j, |δ j| ≤ p15Gamma fp.u n * |R j k|) ∧
        (∑ j : Fin n, (R j k + δ j) * p15RoundedQ fp X R i j) =
          X i k := by
    apply p15_local_backward fp n hvalid k (fun j => R j k)
      (p15RoundedQ fp X R i) (X i k) (hdiag k)
    · intro j hj
      exact hupper j k hj
    · simpa only [p15RoundedQ, p15Transpose] using
        (p15_forward_local fp n (p15Transpose R) (X i) k)
  choose delta hbound heq using hlocal
  refine ⟨fun k j => delta k j, ?_, ?_⟩
  · exact hbound
  · intro k
    simpa only [p15Transpose] using heq k

theorem p15_c2_lemma_3_2
    (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P15RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p15FrobNorm (p15RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p15FrobNorm
        (p15Residual (p15RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P15-C2-H001
  let Q := p15RoundedQ fp X R
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hx : 0 ≤ xNorm := hxNorm
    positivity
  have hrow (i : Fin m) :
      p15VecNorm (p15Residual Q R X i) ≤ c * p15VecNorm (Q i) := by
    obtain ⟨deltaL, hbound, heq⟩ :=
      p15_row_witness fp m n X R hdiag hupper hvalid i
    exact hperturb i deltaL hbound heq
  have hfrob := p15_frob_of_row_bound
    (p15Residual Q R X) Q c hc hrow
  have hQ : c * p15FrobNorm Q ≤ c * Real.sqrt (3 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hQFrob hc
  have hnum := p15_numeric_bound n fp.u xNorm fp.u_nonneg hxNorm
  exact hfrob.trans (hQ.trans hnum)

end VSCLReuse
