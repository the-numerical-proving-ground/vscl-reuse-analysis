import VSCLReuse.P45.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p45_add_step (fp : P45FPModel) (b s p t : ℝ) :
    |fp.fl_add b t - (s + p)| ≤
      (1 + fp.u) * (|b - s| + |t - p|) + fp.u * (|s| + |p|) := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add b t
  have hδ' : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have he : (b + t) * (1 + δ) - (s + p) =
      ((b - s) * (1 + δ) + (t - p) * (1 + δ)) + (s + p) * δ := by ring
  rw [heq, he]
  calc
    |((b - s) * (1 + δ) + (t - p) * (1 + δ)) + (s + p) * δ| ≤
        (|(b - s) * (1 + δ)| + |(t - p) * (1 + δ)|) + |(s + p) * δ| := by
          have h₁ := abs_add_le ((b - s) * (1 + δ) + (t - p) * (1 + δ)) ((s + p) * δ)
          have h₂ := abs_add_le ((b - s) * (1 + δ)) ((t - p) * (1 + δ))
          linarith
    _ = (|b - s| * |1 + δ| + |t - p| * |1 + δ|) + |s + p| * |δ| := by
      simp only [abs_mul]
    _ ≤ (|b - s| * (1 + fp.u) + |t - p| * (1 + fp.u)) +
        (|s| + |p|) * fp.u := by
      gcongr
      exact abs_add_le s p
    _ = (1 + fp.u) * (|b - s| + |t - p|) + fp.u * (|s| + |p|) := by ring

private theorem p45_fold_bound (fp : P45FPModel) (p0 t0 : ℝ)
    (h0 : |t0 - p0| ≤ fp.u * |p0|) :
    ∀ (n : ℕ) (p t : Fin n → ℝ),
      (∀ i, |t i - p i| ≤ fp.u * |p i|) →
      |Fin.foldl n (fun acc i => fp.fl_add acc (t i)) t0 -
        (p0 + ∑ i : Fin n, p i)| ≤
        ((1 + fp.u) ^ (n + 1) - 1) *
          (|p0| + ∑ i : Fin n, |p i|) := by
  intro n
  induction n with
  | zero =>
      intro p t ht
      simpa [Fin.foldl_zero] using h0
  | succ n ih =>
      intro p t ht
      let p' : Fin n → ℝ := fun i => p i.castSucc
      let t' : Fin n → ℝ := fun i => t i.castSucc
      let P : ℝ := p (Fin.last n)
      let T : ℝ := t (Fin.last n)
      let B : ℝ := Fin.foldl n (fun acc i => fp.fl_add acc (t' i)) t0
      let S : ℝ := p0 + ∑ i : Fin n, p' i
      let Q : ℝ := |p0| + ∑ i : Fin n, |p' i|
      let c : ℝ := (1 + fp.u) ^ (n + 1) - 1
      let c' : ℝ := (1 + fp.u) ^ (n + 1 + 1) - 1
      have hprefix : |B - S| ≤ c * Q := by
        exact ih p' t' (fun i => ht i.castSucc)
      have hT : |T - P| ≤ fp.u * |P| := ht (Fin.last n)
      have hS : |S| ≤ Q := by
        calc
          |S| ≤ |p0| + |∑ i : Fin n, p' i| := abs_add_le _ _
          _ ≤ Q := by
            dsimp [Q]
            have h := Finset.abs_sum_le_sum_abs p' Finset.univ
            simpa using add_le_add_left h |p0|
      have hu : 0 ≤ fp.u := fp.u_nonneg
      have hu1 : 0 ≤ 1 + fp.u := by linarith
      have hpw : 1 ≤ (1 + fp.u) ^ n := one_le_pow₀ (by linarith)
      have hc : fp.u ≤ c := by
        dsimp [c]
        rw [pow_succ]
        nlinarith [mul_nonneg hu1 (sub_nonneg.mpr hpw)]
      have hc' : c' = (1 + fp.u) * c + fp.u := by
        dsimp [c', c]
        rw [pow_succ]
        ring
      have hfactor : 2 * fp.u + fp.u ^ 2 ≤ c' := by
        rw [hc']
        nlinarith [mul_nonneg hu1 (sub_nonneg.mpr hc)]
      have hstep := p45_add_step fp B S P T
      have h_err : |B - S| + |T - P| ≤ c * Q + fp.u * |P| :=
        add_le_add hprefix hT
      have h_sp : |S| + |P| ≤ Q + |P| := add_le_add hS (le_refl _)
      have hbound : |fp.fl_add B T - (S + P)| ≤ c' * (Q + |P|) := by
        calc
          |fp.fl_add B T - (S + P)| ≤
              (1 + fp.u) * (|B - S| + |T - P|) + fp.u * (|S| + |P|) := hstep
          _ ≤ (1 + fp.u) * (c * Q + fp.u * |P|) + fp.u * (Q + |P|) :=
            add_le_add (mul_le_mul_of_nonneg_left h_err hu1)
              (mul_le_mul_of_nonneg_left h_sp hu)
          _ = c' * Q + (2 * fp.u + fp.u ^ 2) * |P| := by rw [hc']; ring
          _ ≤ c' * Q + c' * |P| := by
            exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hfactor (abs_nonneg P))
          _ = c' * (Q + |P|) := by ring
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc, p', t', P, T,
        B, S, Q, c', add_assoc] using hbound

private theorem p45_mul_error (fp : P45FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * |a * x| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul a x
  rw [heq, show (a * x) * (1 + δ) - a * x = (a * x) * δ by ring, abs_mul]
  calc
    |a * x| * |δ| ≤ |a * x| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |a * x| := mul_comm _ _

private theorem p45_pow_den_le_one (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hfac : (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
          1 - (n : ℝ) * u := by
        have hh : 0 ≤ ((n : ℝ) + 1) * u ^ 2 :=
          mul_nonneg (by positivity) (sq_nonneg u)
        push_cast
        nlinarith
      calc
        (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ n * ((1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hfac (pow_nonneg (by linarith) _)
        _ ≤ 1 := ih

private theorem p45_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hv : P45GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p45Gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    unfold P45GammaValid at hv
    linarith
  have h := p45_pow_den_le_one u hu n
  apply (le_div_iff₀ hden).2
  nlinarith

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  cases n with
  | zero => simp [p45BlockDot, p45Gamma]
  | succ n =>
      let p : Fin n → ℝ := fun i => a i.succ * x i.succ
      let t : Fin n → ℝ := fun i => fp.fl_mul (a i.succ) (x i.succ)
      have hfold := p45_fold_bound fp (a 0 * x 0)
        (fp.fl_mul (a 0) (x 0)) (p45_mul_error fp (a 0) (x 0))
        n p t (fun i => p45_mul_error fp (a i.succ) (x i.succ))
      have hpow := p45_pow_le_gamma fp.u fp.u_nonneg (n + 1) hv
      have hsum : 0 ≤ ∑ j : Fin (n + 1), |a j * x j| :=
        Finset.sum_nonneg (fun j hj => abs_nonneg _)
      calc
        |p45BlockDot fp (n + 1) a x - ∑ j : Fin (n + 1), a j * x j| ≤
            ((1 + fp.u) ^ (n + 1) - 1) *
              ∑ j : Fin (n + 1), |a j * x j| := by
                simpa only [p45BlockDot, Fin.sum_univ_succ, p, t] using hfold
        _ ≤ p45Gamma fp.u (n + 1) * ∑ j : Fin (n + 1), |a j * x j| :=
          mul_le_mul_of_nonneg_right hpow hsum

end VSCLReuse
