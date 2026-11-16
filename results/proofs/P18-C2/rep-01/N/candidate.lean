import VSCLReuse.P18.Definitions

namespace VSCLReuse

private theorem p18_mul_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl, show (x * y) * (1 + δ) - x * y = (x * y) * δ by ring, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private theorem p18_add_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl, show (x + y) * (1 + δ) - (x + y) = (x + y) * δ by ring, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private theorem p18_sub_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * |x - y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub x y
  rw [hfl, show (x - y) * (1 + δ) - (x - y) = (x - y) * δ by ring, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x - y))

private theorem p18_add_step (fp : P18FPModel) (a b p t : ℝ)
    (hp : |p - t| ≤ fp.u * |t|) :
    |fp.fl_add a p - (b + t)| ≤
      (1 + fp.u) * |a - b| + fp.u * |b| +
        (2 * fp.u + fp.u ^ 2) * |t| := by
  have h₁ : |(a + p) - (b + t)| ≤ |a - b| + |p - t| := by
    have heq : (a + p) - (b + t) = (a - b) + (p - t) := by ring
    rw [heq]
    exact abs_add_le _ _
  have h₂ : |a + p| ≤ |a - b| + |b| + |t| + |p - t| := by
    calc
      |a + p| = |((a - b) + b + t) + (p - t)| := by ring
      _ ≤ |(a - b) + b + t| + |p - t| := abs_add_le _ _
      _ ≤ |(a - b) + b| + |t| + |p - t| := by linarith [abs_add_le ((a - b) + b) t]
      _ ≤ |a - b| + |b| + |t| + |p - t| := by linarith [abs_add_le (a - b) b]
  have h₃ := p18_add_error fp a p
  have h₄ : |fp.fl_add a p - (b + t)| ≤
      |fp.fl_add a p - (a + p)| + |(a + p) - (b + t)| := by
    have heq : fp.fl_add a p - (b + t) =
        (fp.fl_add a p - (a + p)) + ((a + p) - (b + t)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have h₅ := mul_le_mul_of_nonneg_left h₂ fp.u_nonneg
  have h₆ := mul_le_mul_of_nonneg_left hp (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
  nlinarith

private theorem p18_power_bound (u : ℝ) (hu : 0 ≤ u) :
    ∀ n : ℕ, (n : ℝ) * u < 1 →
      (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hn' : (n : ℝ) * u < 1 := by
        have : (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
          apply mul_le_mul_of_nonneg_right _ hu
          exact_mod_cast Nat.le_succ n
        exact lt_of_le_of_lt this hn
      have hfactor : (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
          1 - (n : ℝ) * u := by
        push_cast
        nlinarith [mul_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) (sq_nonneg u)]
      have hp : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
      have hmult := mul_le_mul_of_nonneg_left hfactor hp
      rw [pow_succ]
      nlinarith [ih hn']

private theorem p18_power_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P18GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p18Gamma u n := by
  have hvalid : (n : ℝ) * u < 1 := hn
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  rw [p18Gamma]
  apply (le_div_iff₀ hden).2
  nlinarith [p18_power_bound u hu n hvalid]

private theorem p18_fold_error (fp : P18FPModel) :
    ∀ (n : ℕ) (p t : Fin n → ℝ) (a b : ℝ),
      (∀ i, |p i - t i| ≤ fp.u * |t i|) →
      |Fin.foldl n (fun acc i => fp.fl_add acc (p i)) a -
          (b + ∑ i : Fin n, t i)| ≤
        (1 + fp.u) ^ n * |a - b| +
          ((1 + fp.u) ^ n - 1) * |b| +
          ((1 + fp.u) ^ (n + 1) - 1) * ∑ i : Fin n, |t i| := by
  intro n
  induction n with
  | zero =>
      intro p t a b hp
      simp
  | succ n ih =>
      intro p t a b hp
      let a' := Fin.foldl n (fun acc i => fp.fl_add acc (p i.castSucc)) a
      let b' := b + ∑ i : Fin n, t i.castSucc
      have hpre : |a' - b'| ≤
          (1 + fp.u) ^ n * |a - b| +
            ((1 + fp.u) ^ n - 1) * |b| +
            ((1 + fp.u) ^ (n + 1) - 1) *
              ∑ i : Fin n, |t i.castSucc| :=
        ih (fun i => p i.castSucc) (fun i => t i.castSucc) a b (fun i => hp i.castSucc)
      have hstep := p18_add_step fp a' b' (p (Fin.last n))
        (t (Fin.last n)) (hp (Fin.last n))
      have hsum : |∑ i : Fin n, t i.castSucc| ≤
          ∑ i : Fin n, |t i.castSucc| := Finset.abs_sum_le_sum_abs _ _
      have hb' : |b'| ≤ |b| + ∑ i : Fin n, |t i.castSucc| := by
        dsimp [b']
        linarith [abs_add_le b (∑ i : Fin n, t i.castSucc)]
      have hpow : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (n + 2) :=
        pow_le_pow_right₀ (by linarith [fp.u_nonneg]) (by omega)
      have hnonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, |t i.castSucc| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [← add_assoc]
      change |fp.fl_add a' (p (Fin.last n)) -
          (b + (∑ i : Fin n, t i.castSucc) + t (Fin.last n))| ≤ _
      have hmain : |fp.fl_add a' (p (Fin.last n)) -
          (b + (∑ i : Fin n, t i.castSucc) + t (Fin.last n))| ≤
          (1 + fp.u) * |a' - b'| + fp.u * |b'| +
            (2 * fp.u + fp.u ^ 2) * |t (Fin.last n)| := by
        simpa [b', add_assoc] using hstep
      have hpre' := mul_le_mul_of_nonneg_left hpre hnonneg
      have hb'' := mul_le_mul_of_nonneg_left hb' fp.u_nonneg
      have hlast := mul_le_mul_of_nonneg_right hpow (abs_nonneg (t (Fin.last n)))
      have hlast' : (2 * fp.u + fp.u ^ 2) * |t (Fin.last n)| ≤
          ((1 + fp.u) ^ (n + 2) - 1) * |t (Fin.last n)| := by
        nlinarith [abs_nonneg (t (Fin.last n))]
      rw [show n + 2 = n + 1 + 1 by omega,
        pow_succ (1 + fp.u) (n + 1), pow_succ (1 + fp.u) n] at hlast'
      rw [pow_succ (1 + fp.u) n] at hpre'
      rw [pow_succ (1 + fp.u) (n + 1), pow_succ (1 + fp.u) n]
      nlinarith

private theorem p18_dot_error (fp : P18FPModel) (r : ℕ)
    (x y : Fin r → ℝ) (hvalid : P18GammaValid fp.u r) :
    |p18RoundedDotProduct fp r x y - ∑ k : Fin r, x k * y k| ≤
      p18Gamma fp.u r * ∑ k : Fin r, |x k * y k| := by
  cases r with
  | zero => simp [p18RoundedDotProduct]
  | succ n =>
      let a := fp.fl_mul (x 0) (y 0)
      let b := x 0 * y 0
      let p : Fin n → ℝ := fun i => fp.fl_mul (x i.succ) (y i.succ)
      let t : Fin n → ℝ := fun i => x i.succ * y i.succ
      have hfirst : |a - b| ≤ fp.u * |b| := p18_mul_error fp (x 0) (y 0)
      have htail : ∀ i, |p i - t i| ≤ fp.u * |t i| :=
        fun i => p18_mul_error fp (x i.succ) (y i.succ)
      have hfold := p18_fold_error fp n p t a b htail
      have hqnonneg : 0 ≤ (1 + fp.u) ^ n :=
        pow_nonneg (by linarith [fp.u_nonneg]) _
      have hfirst' := mul_le_mul_of_nonneg_left hfirst hqnonneg
      have hgamma := p18_power_le_gamma fp.u fp.u_nonneg (n + 1) hvalid
      have hsum_nonneg : 0 ≤ |b| + ∑ i : Fin n, |t i| := by
        positivity
      have hgamma' := mul_le_mul_of_nonneg_right hgamma hsum_nonneg
      simp only [p18RoundedDotProduct, Fin.sum_univ_succ]
      change |Fin.foldl n (fun acc i => fp.fl_add acc (p i)) a -
          (b + ∑ i : Fin n, t i)| ≤
        p18Gamma fp.u (n + 1) * (|b| + ∑ i : Fin n, |t i|)
      rw [pow_succ (1 + fp.u) n] at hgamma'
      rw [pow_succ (1 + fp.u) n] at hfold
      nlinarith

/-- P18-C2: the first-step Schur-complement error calculation in Appendix B. -/
theorem p18_c2_first_schur_error
    (fp : P18FPModel) (m r : ℕ)
    (A22 : P18Matrix m m) (L11 : P18Matrix m r)
    (A12 : P18Matrix r m)
    (hvalid : P18GammaValid fp.u r) :
    ∀ i j,
      |p18RoundedSchur fp A22 L11 A12 i j -
          p18ExactSchur A22 L11 A12 i j| ≤
        p18SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P18-C2-H001
  intro i j
  let q := p18RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let s := ∑ k : Fin r, L11 i k * A12 k j
  have hdot : |q - s| ≤
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa only [q, s, abs_mul] using
      p18_dot_error fp r (L11 i) (fun k => A12 k j) hvalid
  have hsub := p18_sub_error fp (A22 i j) q
  have htri : |fp.fl_sub (A22 i j) q - (A22 i j - s)| ≤
      |fp.fl_sub (A22 i j) q - (A22 i j - q)| + |q - s| := by
    have heq : fp.fl_sub (A22 i j) q - (A22 i j - s) =
        (fp.fl_sub (A22 i j) q - (A22 i j - q)) + (s - q) := by ring
    rw [heq]
    have h := abs_add_le
      (fp.fl_sub (A22 i j) q - (A22 i j - q)) (s - q)
    simpa only [abs_sub_comm s q] using h
  change |fp.fl_sub (A22 i j) q - (A22 i j - s)| ≤
    fp.u * |A22 i j - q| +
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  linarith

end VSCLReuse
