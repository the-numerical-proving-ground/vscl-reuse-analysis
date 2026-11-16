import VSCLReuse.P17.Definitions

namespace VSCLReuse

private lemma p17_mul_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul x y
  rw [hmul]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p17_add_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add x y
  rw [hadd]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p17_gamma_step_real (u t : ℝ) (hu : 0 ≤ u)
    (ht : u ≤ t) (hsmall : t + u < 1) :
    (1 + u) * (t / (1 - t)) + u * (1 + u) ≤
      (t + u) / (1 - t - u) := by
  have hd₁ : 0 < 1 - t := by linarith
  have hd₂ : 0 < 1 - t - u := by linarith
  apply (mul_le_mul_iff_of_pos_right (mul_pos hd₁ hd₂)).1
  field_simp
  have ht0 : 0 ≤ t := le_trans hu ht
  have hh : 0 ≤ 2 - u - t := by linarith
  have hfac :
      (1 - t) * (t + u) -
        (1 + u) * (t + u * (1 - t)) * (1 - t - u) =
        u * t + u ^ 3 + t * u ^ 2 * (2 - u - t) := by ring
  have hnonneg : 0 ≤ u * t + u ^ 3 + t * u ^ 2 * (2 - u - t) := by
    positivity
  nlinarith [hfac]

private lemma p17_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P17GammaValid u (k + 1)) :
    (1 + u) * p17Gamma u k + u * (1 + u) ≤ p17Gamma u (k + 1) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k : ℝ) - 1 := by linarith
  have ht : u ≤ (k : ℝ) * u := by
    nlinarith [mul_nonneg hkm hu]
  have hsmall : (k : ℝ) * u + u < 1 := by
    simpa [P17GammaValid, Nat.cast_add, add_mul] using hvalid
  convert p17_gamma_step_real u ((k : ℝ) * u) hu ht hsmall using 1
  simp [p17Gamma, Nat.cast_add, add_mul]
  ring

private lemma p17_gamma_ge_u (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P17GammaValid u k) :
    u ≤ p17Gamma u k := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k : ℝ) - 1 := by linarith
  have ht : u ≤ (k : ℝ) * u := by
    nlinarith [mul_nonneg hkm hu]
  have hd : 0 < 1 - (k : ℝ) * u := by
    unfold P17GammaValid at hvalid
    linarith
  unfold p17Gamma
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg hu (le_trans hu ht)]

private noncomputable def p17FoldDot (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun z i => fp.fl_add z (fp.fl_mul (x i) (y i))) 0

private lemma p17_fold_dot_eq (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p17FoldDot fp n x y = p17RoundedDotProduct fp n x y := by
  cases n with
  | zero => simp [p17FoldDot, p17RoundedDotProduct]
  | succ n =>
    simp [p17FoldDot, p17RoundedDotProduct, Fin.foldl_succ, fp.fl_add_zero]

private lemma p17_fold_dot_succ (fp : P17FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    p17FoldDot fp (n + 1) x y =
      fp.fl_add
        (p17FoldDot fp n (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  simp [p17FoldDot, Fin.foldl_succ_last]

private lemma p17_round_step_bound (fp : P17FPModel)
    (R S b a P γ γ' : ℝ) (hP : 0 ≤ P)
    (hS : |S| ≤ P) (hR : |R - S| ≤ γ * P)
    (hb : |b - a| ≤ fp.u * |a|) (hγ : fp.u ≤ γ)
    (hstep : (1 + fp.u) * γ + fp.u * (1 + fp.u) ≤ γ') :
    |fp.fl_add R b - (S + a)| ≤ γ' * (P + |a|) := by
  have hfirst :
      |fp.fl_add R b - (S + a)| ≤
        |fp.fl_add R b - (R + b)| + |R - S| + |b - a| := by
    have heq : fp.fl_add R b - (S + a) =
        (fp.fl_add R b - (R + b)) + ((R - S) + (b - a)) := by ring
    rw [heq]
    have h₁ := abs_add_le (fp.fl_add R b - (R + b)) ((R - S) + (b - a))
    have h₂ := abs_add_le (R - S) (b - a)
    linarith
  have hRabs : |R| ≤ (γ + 1) * P := by
    have heq : R = (R - S) + S := by ring
    rw [heq]
    have htri := abs_add_le (R - S) S
    nlinarith
  have hbabs : |b| ≤ (1 + fp.u) * |a| := by
    have heq : b = (b - a) + a := by ring
    rw [heq]
    have htri := abs_add_le (b - a) a
    nlinarith
  have haddabs : |R + b| ≤ (γ + 1) * P + (1 + fp.u) * |a| := by
    linarith [abs_add_le R b]
  have hcoeffP : ((1 + fp.u) * γ + fp.u) * P ≤ γ' * P := by
    apply mul_le_mul_of_nonneg_right _ hP
    nlinarith [sq_nonneg fp.u]
  have hcoeffA : (2 * fp.u + fp.u ^ 2) * |a| ≤ γ' * |a| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
    nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hγ)]
  calc
    |fp.fl_add R b - (S + a)| ≤
        fp.u * |R + b| + γ * P + fp.u * |a| := by
          linarith [p17_add_error fp R b]
    _ ≤ fp.u * ((γ + 1) * P + (1 + fp.u) * |a|) +
        γ * P + fp.u * |a| := by
          gcongr
          exact fp.u_nonneg
    _ = ((1 + fp.u) * γ + fp.u) * P +
        (2 * fp.u + fp.u ^ 2) * |a| := by ring
    _ ≤ γ' * (P + |a|) := by nlinarith

private lemma p17_fold_dot_bound (fp : P17FPModel) :
    ∀ n : ℕ, P17GammaValid fp.u n → ∀ x y : Fin n → ℝ,
      |p17FoldDot fp n x y - ∑ i : Fin n, x i * y i| ≤
        p17Gamma fp.u n * (∑ i : Fin n, |x i * y i|) := by
  intro n
  induction n with
  | zero =>
    intro hvalid x y
    simp [p17FoldDot]
  | succ n ih =>
    intro hvalid x y
    cases n with
    | zero =>
      have hγ := p17_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hvalid
      have hmul := p17_mul_error fp (x 0) (y 0)
      have hbound :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p17Gamma fp.u 1 * |x 0 * y 0| :=
        hmul.trans (mul_le_mul_of_nonneg_right hγ (abs_nonneg _))
      simpa [p17FoldDot, Fin.foldl_succ, fp.fl_add_zero] using hbound
    | succ m =>
      let x₀ : Fin (m + 1) → ℝ := fun i => x i.castSucc
      let y₀ : Fin (m + 1) → ℝ := fun i => y i.castSucc
      have hvalid₀ : P17GammaValid fp.u (m + 1) := by
        unfold P17GammaValid at hvalid ⊢
        have hc : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (m + 1)
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) fp.u_nonneg]
      have hprev := ih hvalid₀ x₀ y₀
      have hP : 0 ≤ ∑ i : Fin (m + 1), |x₀ i * y₀ i| :=
        Finset.sum_nonneg fun i _ => abs_nonneg _
      have hS : |∑ i : Fin (m + 1), x₀ i * y₀ i| ≤
          ∑ i : Fin (m + 1), |x₀ i * y₀ i| := by
        simpa using Finset.abs_sum_le_sum_abs (fun i : Fin (m + 1) => x₀ i * y₀ i)
          Finset.univ
      have hγ := p17_gamma_ge_u fp.u (m + 1) fp.u_nonneg (by omega) hvalid₀
      have hstep := p17_gamma_step fp.u (m + 1) fp.u_nonneg (by omega) hvalid
      have hbound := p17_round_step_bound fp
        (p17FoldDot fp (m + 1) x₀ y₀)
        (∑ i : Fin (m + 1), x₀ i * y₀ i)
        (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1))))
        (x (Fin.last (m + 1)) * y (Fin.last (m + 1)))
        (∑ i : Fin (m + 1), |x₀ i * y₀ i|)
        (p17Gamma fp.u (m + 1)) (p17Gamma fp.u (m + 1 + 1))
        hP hS hprev
        (p17_mul_error fp (x (Fin.last (m + 1))) (y (Fin.last (m + 1))))
        hγ hstep
      simpa only [p17_fold_dot_succ, Fin.sum_univ_castSucc, x₀, y₀] using hbound

private lemma p17_rounded_dot_bound (fp : P17FPModel) (n : ℕ)
    (hvalid : P17GammaValid fp.u n) (x y : Fin n → ℝ) :
    |p17RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p17Gamma fp.u n * (∑ i : Fin n, |x i * y i|) := by
  simpa only [p17_fold_dot_eq] using p17_fold_dot_bound fp n hvalid x y

/-- P17-C2: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p17_c2_newton_schulz_triple_product_error
    (fp : P17FPModel) (n : ℕ) (X : P17RealMatrix n)
    (hvalid : P17GammaValid fp.u n) :
    ∀ i j,
      |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        p17GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P17-C2-H001
  intro i j
  let A : P17RealMatrix n := p17RoundedMatMul fp X (p17Transpose X)
  let B : P17RealMatrix n := p17MatMul X (p17Transpose X)
  let γ : ℝ := p17Gamma fp.u n
  have houter :
      |p17RoundedGramTriple fp X i j - p17MatMul A X i j| ≤
        γ * (∑ k : Fin n, |A i k| * |X k j|) := by
    simpa [A, γ, p17RoundedGramTriple, p17RoundedMatMul, p17MatMul,
      abs_mul] using
      p17_rounded_dot_bound fp n hvalid (A i) (fun k => X k j)
  have hinner (k : Fin n) :
      |A i k - B i k| ≤
        γ * (∑ l : Fin n, |X i l| * |X k l|) := by
    simpa [A, B, γ, p17RoundedMatMul, p17MatMul, p17Transpose,
      abs_mul] using
      p17_rounded_dot_bound fp n hvalid (X i)
        (fun l => p17Transpose X l k)
  have htransport :
      |p17MatMul A X i j - p17MatMul B X i j| ≤
        γ * (∑ k : Fin n,
          (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
    change |(∑ k : Fin n, A i k * X k j) -
        (∑ k : Fin n, B i k * X k j)| ≤ _
    have hrew :
        (∑ k : Fin n, A i k * X k j) -
          (∑ k : Fin n, B i k * X k j) =
          ∑ k : Fin n, (A i k - B i k) * X k j := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext k
      ring
    rw [hrew]
    calc
      |∑ k : Fin n, (A i k - B i k) * X k j| ≤
          ∑ k : Fin n, |(A i k - B i k) * X k j| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun k : Fin n => (A i k - B i k) * X k j) Finset.univ
      _ ≤ ∑ k : Fin n,
          γ * (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = γ * (∑ k : Fin n,
          (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
            rw [Finset.mul_sum]
            congr 1
            ext k
            ring
  have htriangle := abs_sub_le
    (p17RoundedGramTriple fp X i j)
    (p17MatMul A X i j)
    (p17ExactGramTriple X i j)
  calc
    |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        |p17RoundedGramTriple fp X i j - p17MatMul A X i j| +
          |p17MatMul A X i j - p17ExactGramTriple X i j| := htriangle
    _ ≤ γ * (∑ k : Fin n, |A i k| * |X k j|) +
        γ * (∑ k : Fin n,
          (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
          simpa [p17ExactGramTriple, B] using add_le_add houter htransport
    _ = p17GramTripleErrorMajorant fp X i j := by
          rfl

end VSCLReuse
