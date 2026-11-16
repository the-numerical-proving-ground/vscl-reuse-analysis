import VSCLReuse.P18.Definitions

namespace VSCLReuse

private theorem p18_mul_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul x y
  rw [hmul]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private theorem p18_add_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add x y
  rw [hadd]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private theorem p18_sub_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * |x - y| := by
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub x y
  rw [hsub]
  have heq : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x - y))

private theorem p18_coeff_acc (u : ℝ) (r k : ℕ)
    (hk : k ≤ r) (hr : (r : ℝ) * u < 1) :
    (1 + u) * ((k : ℝ) * u / (1 - (r : ℝ) * u)) + u ≤
      ((k + 1 : ℕ) : ℝ) * u / (1 - (r : ℝ) * u) := by
  have hd : 0 < 1 - (r : ℝ) * u := by linarith
  have hkr : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk
  apply (le_div_iff₀ hd).2
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hd)]
  have hh := mul_nonneg (sub_nonneg.mpr hkr) (sq_nonneg u)
  simp only [Nat.cast_add, Nat.cast_one] at *
  nlinarith

private theorem p18_coeff_term (u : ℝ) (r k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hkr : k + 1 ≤ r)
    (hr : (r : ℝ) * u < 1) :
    2 * u + u ^ 2 ≤
      ((k + 1 : ℕ) : ℝ) * u / (1 - (r : ℝ) * u) := by
  have hd : 0 < 1 - (r : ℝ) * u := by linarith
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 2 ≤ r)
  have hk2 : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
  apply (le_div_iff₀ hd).2
  have h0 := mul_nonneg (sub_nonneg.mpr hr2) hu
  have h1 := mul_nonneg (show 0 ≤ 2 * u + u ^ 2 by positivity)
    (show 0 ≤ (r : ℝ) * u - 2 * u by nlinarith)
  have h2 := mul_nonneg (sub_nonneg.mpr hk2) hu
  have h3 := mul_nonneg (sq_nonneg u) hu
  simp only [Nat.cast_add, Nat.cast_one] at *
  nlinarith only [h1, h2, h3, sq_nonneg u]

private theorem p18_step_bound (fp : P18FPModel) (r k : ℕ)
    (hr : P18GammaValid fp.u r) (hk : 1 ≤ k) (hkr : k + 1 ≤ r)
    (a s q x y : ℝ) (hq : |s| ≤ q)
    (he : |a - s| ≤ ((k : ℝ) * fp.u / (1 - (r : ℝ) * fp.u)) * q) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      (((k + 1 : ℕ) : ℝ) * fp.u / (1 - (r : ℝ) * fp.u)) *
        (q + |x * y|) := by
  let b := fp.fl_mul x y
  let p := x * y
  have hb : |b - p| ≤ fp.u * |p| := p18_mul_error fp x y
  have ha : |a| ≤ |a - s| + |s| := by
    calc
      |a| = |(a - s) + s| := by congr 1; ring
      _ ≤ |a - s| + |s| := abs_add_le _ _
  have hbb : |b| ≤ |b - p| + |p| := by
    calc
      |b| = |(b - p) + p| := by congr 1; ring
      _ ≤ |b - p| + |p| := abs_add_le _ _
  have hab : |a + b| ≤ |a - s| + q + fp.u * |p| + |p| := by
    have h := abs_add_le a b
    linarith
  have hround : |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| :=
    p18_add_error fp a b
  have hdiff : |(a + b) - (s + p)| ≤ |a - s| + |b - p| := by
    calc
      |(a + b) - (s + p)| = |(a - s) + (b - p)| := by congr 1; ring
      _ ≤ |a - s| + |b - p| := abs_add_le _ _
  have htotal : |fp.fl_add a b - (s + p)| ≤
      fp.u * (|a - s| + q + fp.u * |p| + |p|) +
        |a - s| + fp.u * |p| := by
    have htri : |fp.fl_add a b - (s + p)| ≤
        |fp.fl_add a b - (a + b)| + |(a + b) - (s + p)| := by
      calc
        |fp.fl_add a b - (s + p)| =
            |(fp.fl_add a b - (a + b)) + ((a + b) - (s + p))| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hscaled := mul_le_mul_of_nonneg_left hab fp.u_nonneg
    linarith
  have hacc := p18_coeff_acc fp.u r k (by omega) hr
  have hterm := p18_coeff_term fp.u r k fp.u_nonneg hk hkr hr
  have hqnonneg : 0 ≤ q := le_trans (abs_nonneg s) hq
  have hbound := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
  have haccq := mul_le_mul_of_nonneg_right hacc hqnonneg
  have htermp := mul_le_mul_of_nonneg_right hterm (abs_nonneg p)
  change |fp.fl_add a b - (s + p)| ≤
    (((k + 1 : ℕ) : ℝ) * fp.u / (1 - (r : ℝ) * fp.u)) * (q + |p|)
  nlinarith only [htotal, hbound, haccq, htermp]

private theorem p18_fold_bound (fp : P18FPModel) (r : ℕ)
    (hr : P18GammaValid fp.u r) :
    ∀ (n k : ℕ), 1 ≤ k → k + n ≤ r → ∀
      (a s q : ℝ) (x y : Fin n → ℝ),
      |s| ≤ q →
      |a - s| ≤ ((k : ℝ) * fp.u / (1 - (r : ℝ) * fp.u)) * q →
      |Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) a -
          (s + ∑ i : Fin n, x i * y i)| ≤
        (((k + n : ℕ) : ℝ) * fp.u / (1 - (r : ℝ) * fp.u)) *
          (q + ∑ i : Fin n, |x i * y i|) := by
  intro n
  induction n with
  | zero =>
      intro k _ _ a s q x y hq he
      simpa using he
  | succ n ih =>
      intro k hk hkr a s q x y hq he
      have hstep := p18_step_bound fp r k hr hk (by omega : k + 1 ≤ r)
        a s q (x 0) (y 0) hq he
      have hq' : |s + x 0 * y 0| ≤ q + |x 0 * y 0| := by
        exact (abs_add_le s (x 0 * y 0)).trans (by linarith)
      have hi := ih (k + 1) (by omega : 1 ≤ k + 1)
        (by omega : k + 1 + n ≤ r)
        (fp.fl_add a (fp.fl_mul (x 0) (y 0))) (s + x 0 * y 0)
        (q + |x 0 * y 0|) (fun i => x i.succ) (fun i => y i.succ)
        hq' hstep
      simpa [Fin.foldl_succ, Fin.sum_univ_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using hi

private theorem p18_dot_bound (fp : P18FPModel) (r : ℕ)
    (x y : Fin r → ℝ) (hr : P18GammaValid fp.u r) :
    |p18RoundedDotProduct fp r x y - ∑ i : Fin r, x i * y i| ≤
      p18Gamma fp.u r * ∑ i : Fin r, |x i * y i| := by
  cases r with
  | zero => simp [p18RoundedDotProduct]
  | succ n =>
      have hd : 0 < 1 - ((n + 1 : ℕ) : ℝ) * fp.u := by
        dsimp [P18GammaValid] at hr
        linarith
      have hcoeff : fp.u ≤
          (1 : ℝ) * fp.u / (1 - ((n + 1 : ℕ) : ℝ) * fp.u) := by
        apply (le_div_iff₀ hd).2
        have hh := mul_nonneg
          (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity)
          (sq_nonneg fp.u)
        nlinarith
      have he : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
          ((1 : ℝ) * fp.u / (1 - ((n + 1 : ℕ) : ℝ) * fp.u)) *
            |x 0 * y 0| := by
        exact (p18_mul_error fp (x 0) (y 0)).trans
          (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))
      have hfold := p18_fold_bound fp (n + 1) hr n 1
        (by omega : 1 ≤ 1) (by omega : 1 + n ≤ n + 1)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) (|x 0 * y 0|)
        (fun i => x i.succ) (fun i => y i.succ) (le_refl _) (by simpa using he)
      simpa [p18RoundedDotProduct, p18Gamma, Fin.sum_univ_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using hfold

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
  let a := A22 i j
  let b := p18RoundedMatMul fp L11 A12 i j
  let e := p18MatMul L11 A12 i j
  have hdot : |b - e| ≤
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [b, e, p18RoundedMatMul, p18MatMul, abs_mul] using
      p18_dot_bound fp r (L11 i) (fun k => A12 k j) hvalid
  have hsub : |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| :=
    p18_sub_error fp a b
  have htri : |fp.fl_sub a b - (a - e)| ≤
      |fp.fl_sub a b - (a - b)| + |b - e| := by
    calc
      |fp.fl_sub a b - (a - e)| =
          |(fp.fl_sub a b - (a - b)) + (e - b)| := by congr 1; ring
      _ ≤ |fp.fl_sub a b - (a - b)| + |e - b| := abs_add_le _ _
      _ = |fp.fl_sub a b - (a - b)| + |b - e| := by rw [abs_sub_comm e b]
  change |fp.fl_sub a b - (a - e)| ≤
    fp.u * |a - b| +
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  exact htri.trans (add_le_add hsub hdot)

end VSCLReuse
