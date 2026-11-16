import VSCLReuse.P39.Definitions
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p39ToFP (fp : P39FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem p39_dot_eq (fp : P39FPModel) (m : ℕ) (x y : Fin m → ℝ) :
    p39RoundedDotProduct fp m x y =
      NumStability.fl_dotProduct (p39ToFP fp) m x y := by
  cases m <;> rfl

private theorem p39_steps_ge (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) (i j : Fin n)
    (hjk : k ≤ j.val) :
    p39Method2SourceSteps fp n L k hk X i j = X i j := by
  induction k generalizing X with
  | zero => rfl
  | succ k ih =>
      simp only [p39Method2SourceSteps]
      rw [ih]
      simp only [p39Method2SourceStep]
      have hne : j ≠ (⟨k, by omega⟩ : Fin n) := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      simp [hne]
      omega

private theorem p39_steps_upper (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n)
    (hX : ∀ i j : Fin n, i.val < j.val → X i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      p39Method2SourceSteps fp n L k hk X i j = 0 := by
  induction k generalizing X with
  | zero => simpa [p39Method2SourceSteps] using hX
  | succ k ih =>
      apply ih
      intro i j hij
      simp only [p39Method2SourceStep]
      by_cases hj : j = (⟨k, by omega⟩ : Fin n)
      · rw [hj]
        have hik : ¬ k < i.val := by simpa [hj] using (Nat.not_lt_of_ge (Nat.le_of_lt hij))
        have hne : i ≠ (⟨k, hk⟩ : Fin n) := by
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        simp [hik, hne]
      · simpa [hj] using hX i j hij

private theorem p39_steps_diag (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) (j : Fin n)
    (hjk : j.val < k) :
    p39Method2SourceSteps fp n L k hk X j j = fp.fl_div 1 (L j j) := by
  induction k generalizing X with
  | zero => omega
  | succ k ih =>
      simp only [p39Method2SourceSteps]
      by_cases h : j.val < k
      · exact ih _ _ h
      · have hj : j = (⟨k, by omega⟩ : Fin n) := Fin.ext (by simp; omega)
        rw [hj]
        rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk)]
        simp [p39Method2SourceStep]
        omega

private theorem p39_steps_below (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) :
    ∀ j i : Fin n, j.val < k → j.val < i.val →
      p39Method2SourceSteps fp n L k hk X i j =
        fp.fl_mul (-(p39Method2SourceSteps fp n L k hk X j j))
          (p39RoundedDotProduct fp (n - j.val - 1)
            (fun t => p39Method2SourceSteps fp n L k hk X i
              ⟨j.val + 1 + t.val, by omega⟩)
            (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  induction k generalizing X with
  | zero => intro j i hjk; omega
  | succ k ih =>
      intro j i hjk hij
      simp only [p39Method2SourceSteps]
      by_cases h : j.val < k
      · exact ih _ _ j i h hij
      · have hj : j = (⟨k, by omega⟩ : Fin n) := Fin.ext (by simp; omega)
        rw [hj]
        have hstep : p39Method2SourceStep fp n L X (⟨k, by omega⟩ : Fin n) i
            (⟨k, by omega⟩ : Fin n) =
            fp.fl_mul (-(fp.fl_div 1 (L (⟨k, by omega⟩ : Fin n) ⟨k, by omega⟩)))
              (p39RoundedDotProduct fp (n - k - 1)
                (fun t => X i ⟨k + 1 + t.val, by omega⟩)
                (fun t => L ⟨k + 1 + t.val, by omega⟩ ⟨k, by omega⟩)) := by
          have hne : i ≠ (⟨k, hk⟩ : Fin n) := by
            intro heq
            have := congrArg Fin.val heq
            simp at this
            omega
          have hki : k < i.val := by simpa [hj] using hij
          simp [p39Method2SourceStep, hne, hki]
        rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk), hstep]
        · rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk)]
          · congr 1
            · simp [p39Method2SourceStep]
            · congr 1
              funext t
              rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk)]
              · have hneq : (⟨k + 1 + t.val, by omega⟩ : Fin n) ≠
                    (⟨k, hk⟩ : Fin n) := by
                    intro heq
                    have := congrArg Fin.val heq
                    simp at this
                    omega
                simp [p39Method2SourceStep, hneq]
              · change k ≤ k + 1 + t.val
                omega
          · omega
        · omega

private theorem p39_tail_sum (n : ℕ) (j : Fin n) (f : Fin n → ℝ) :
    (∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩) =
      ∑ k : Fin n, if j.val < k.val then f k else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun t _ => (⟨j.val + 1 + t.val, by omega⟩ : Fin n))
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro t₁ _ t₂ _ h
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    omega
  · intro k hk
    have hkj : j.val < k.val := (Finset.mem_filter.mp hk).2
    refine ⟨⟨k.val - j.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp
    omega
  · intro t _
    rfl

private theorem p39_dot_tail_error (fp : P39FPModel) (n : ℕ)
    (X L : P39Matrix n n) (hvalid : P39GammaValid fp.u n)
    (i j : Fin n) :
    |p39RoundedDotProduct fp (n - j.val - 1)
        (fun t => X i ⟨j.val + 1 + t.val, by omega⟩)
        (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j) -
      (∑ k : Fin n, if j.val < k.val then X i k * L k j else 0)| ≤
      p39Gamma fp.u n *
        (∑ k : Fin n, if j.val < k.val then |X i k| * |L k j| else 0) := by
  let m := n - j.val - 1
  let x : Fin m → ℝ := fun t => X i ⟨j.val + 1 + t.val, by omega⟩
  let y : Fin m → ℝ := fun t => L ⟨j.val + 1 + t.val, by omega⟩ j
  have hmle : m ≤ n := by dsimp [m]; omega
  have hn : NumStability.gammaValid (p39ToFP fp) n := hvalid
  have hm := NumStability.gammaValid_mono (p39ToFP fp) hmle hn
  have hdot := NumStability.dotProduct_error_bound (p39ToFP fp) m x y hm
  have hsum : (∑ t : Fin m, x t * y t) =
      ∑ k : Fin n, if j.val < k.val then X i k * L k j else 0 := by
    simpa only [x, y, m] using p39_tail_sum n j (fun k => X i k * L k j)
  have habs : (∑ t : Fin m, |x t| * |y t|) =
      ∑ k : Fin n, if j.val < k.val then |X i k| * |L k j| else 0 := by
    simpa only [x, y, m] using p39_tail_sum n j (fun k => |X i k| * |L k j|)
  have hnonneg : 0 ≤ ∑ t : Fin m, |x t| * |y t| :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmono := NumStability.gamma_mono (p39ToFP fp) hmle hn
  change p39Gamma fp.u m ≤ p39Gamma fp.u n at hmono
  have hle := mul_le_mul_of_nonneg_right hmono hnonneg
  calc
    _ = |NumStability.fl_dotProduct (p39ToFP fp) m x y -
          (∑ t : Fin m, x t * y t)| := by rw [p39_dot_eq, hsum]
    _ ≤ NumStability.gamma (p39ToFP fp) m *
          (∑ t : Fin m, |x t| * |y t|) := hdot
    _ ≤ p39Gamma fp.u n *
          (∑ k : Fin n, if j.val < k.val then |X i k| * |L k j| else 0) := by
            rw [← habs]
            exact hle

private theorem p39_tail_update_error (fp : P39FPModel) (n : ℕ)
    (L X : P39Matrix n n) (hvalid : P39GammaValid fp.u n)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧ X j j * L j j = 1 + δ)
    (hStore : ∀ j row : Fin n, j.val < row.val →
      X row j = fp.fl_mul (-X j j)
        (p39RoundedDotProduct fp (n - j.val - 1)
          (fun t => X row ⟨j.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j))) :
    ∀ j row : Fin n, j.val < row.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤
          ((1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) *
            (∑ k : Fin n, if j.val < k.val then |X row k| * |L k j| else 0) ∧
        X row j = -X j j *
          (∑ k : Fin n, if j.val < k.val then X row k * L k j else 0) + Δ := by
  intro j row hij
  let exactTail : ℝ :=
    ∑ k : Fin n, if j.val < k.val then X row k * L k j else 0
  let tailAbs : ℝ :=
    ∑ k : Fin n, if j.val < k.val then |X row k| * |L k j| else 0
  let flTail : ℝ := p39RoundedDotProduct fp (n - j.val - 1)
    (fun t => X row ⟨j.val + 1 + t.val, by omega⟩)
    (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)
  let Δ : ℝ := fp.fl_mul (-X j j) flTail - (-X j j * exactTail)
  refine ⟨Δ, ?_, ?_⟩
  · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X j j) flTail
    have hdot : |flTail - exactTail| ≤ p39Gamma fp.u n * tailAbs :=
      p39_dot_tail_error fp n X L hvalid row j
    have htail_abs : |exactTail| ≤ tailAbs := by
      calc
        |exactTail| ≤ ∑ k : Fin n,
            |if j.val < k.val then X row k * L k j else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = tailAbs := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
    have htail_nonneg : 0 ≤ tailAbs := by
      dsimp [tailAbs]
      exact Finset.sum_nonneg (fun k _ => by
        by_cases hjk : j.val < k.val
        · simpa [hjk] using
            mul_nonneg (abs_nonneg (X row k)) (abs_nonneg (L k j))
        · simp [hjk])
    have hfl_abs : |flTail| ≤ (1 + p39Gamma fp.u n) * tailAbs := by
      calc
        |flTail| = |exactTail + (flTail - exactTail)| := by congr 1; ring
        _ ≤ |exactTail| + |flTail - exactTail| := abs_add_le _ _
        _ ≤ tailAbs + p39Gamma fp.u n * tailAbs := add_le_add htail_abs hdot
        _ = (1 + p39Gamma fp.u n) * tailAbs := by ring
    obtain ⟨δ, hδ, hdiag⟩ := hDiag j
    have hdiag_abs : |X j j * L j j| ≤ 1 + fp.u := by
      calc
        |X j j * L j j| = |1 + δ| := by rw [hdiag]
        _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
        _ ≤ 1 + fp.u := by norm_num; exact hδ
    have hγnonneg : 0 ≤ p39Gamma fp.u n := by
      have hn : NumStability.gammaValid (p39ToFP fp) n := hvalid
      simpa [p39Gamma, NumStability.gamma, p39ToFP] using
        (NumStability.gamma_nonneg (p39ToFP fp) hn)
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ_nonneg : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    have hcoef_nonneg :
        0 ≤ (1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs) :=
      mul_nonneg honeu_nonneg (mul_nonneg honeγ_nonneg htail_nonneg)
    have hΔ_decomp :
        Δ * L j j =
          (-X j j * L j j) * (flTail - exactTail) +
            ((-X j j * L j j) * flTail) * δmul := by
      dsimp [Δ]
      rw [hmul]
      ring
    have hneg_abs : |(-X j j * L j j)| = |X j j * L j j| := by
      have hneg : (-X j j * L j j) = -(X j j * L j j) := by ring
      rw [hneg, abs_neg]
    have hfirst :
        |(-X j j * L j j) * (flTail - exactTail)| ≤
          (1 + fp.u) * (p39Gamma fp.u n * tailAbs) := by
      calc
        |(-X j j * L j j) * (flTail - exactTail)| =
            |X j j * L j j| * |flTail - exactTail| := by rw [abs_mul, hneg_abs]
        _ ≤ (1 + fp.u) * (p39Gamma fp.u n * tailAbs) :=
          mul_le_mul hdiag_abs hdot (abs_nonneg _) honeu_nonneg
    have hsecond :
        |((-X j j * L j j) * flTail) * δmul| ≤
          ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u := by
      have hleft :
          |X j j * L j j| * |flTail| ≤
            (1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs) :=
        mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu_nonneg
      calc
        |((-X j j * L j j) * flTail) * δmul| =
            |X j j * L j j| * |flTail| * |δmul| := by
              rw [abs_mul, abs_mul, hneg_abs]
        _ ≤ ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u :=
          mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
    calc
      |Δ * L j j| =
          |(-X j j * L j j) * (flTail - exactTail) +
            ((-X j j * L j j) * flTail) * δmul| := by rw [hΔ_decomp]
      _ ≤ |(-X j j * L j j) * (flTail - exactTail)| +
            |((-X j j * L j j) * flTail) * δmul| := abs_add_le _ _
      _ ≤ (1 + fp.u) * (p39Gamma fp.u n * tailAbs) +
            ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u :=
          add_le_add hfirst hsecond
      _ = ((1 + fp.u) *
            (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) * tailAbs := by ring
  · have hstore := hStore j row hij
    calc
      X row j = fp.fl_mul (-X j j) flTail := hstore
      _ = -X j j * exactTail + Δ := by dsimp [Δ]; ring

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
  let C := p39Method2SourceUniformCoefficient fp n
  have hn : NumStability.gammaValid (p39ToFP fp) n := hvalid
  have hγnonneg : 0 ≤ p39Gamma fp.u n := by
    simpa [p39Gamma, NumStability.gamma, p39ToFP] using
      (NumStability.gamma_nonneg (p39ToFP fp) hn)
  have hXlower : ∀ a b : Fin n, a.val < b.val → X a b = 0 := by
    intro a b hab
    exact p39_steps_upper fp n L n (le_refl n) 0
      (by intro a b hab; rfl) a b hab
  have hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X j j * L j j = 1 + δ := by
    intro q
    obtain ⟨δ, hδ, hdiv⟩ := fp.model_div 1 (L q q) (hdiag q)
    refine ⟨δ, hδ, ?_⟩
    have hx : X q q = fp.fl_div 1 (L q q) :=
      p39_steps_diag fp n L n (le_refl n) 0 q q.isLt
    rw [hx, hdiv]
    field_simp [hdiag q]
  have hStore : ∀ q row : Fin n, q.val < row.val →
      X row q = fp.fl_mul (-X q q)
        (p39RoundedDotProduct fp (n - q.val - 1)
          (fun t => X row ⟨q.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨q.val + 1 + t.val, by omega⟩ q)) := by
    intro q row hqr
    exact p39_steps_below fp n L n (le_refl n) 0 q row q.isLt hqr
  have hηnonneg :
      0 ≤ (1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n)) := by
    have h1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have h2 : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    exact mul_nonneg h1
      (add_nonneg hγnonneg (mul_nonneg fp.u_nonneg h2))
  have hTrail := p39_tail_update_error fp n L X hvalid hDiag hStore
  have hLowerBase := NumStability.triInv_method2_offdiag_trailing_update_full_bound
    n (p39ToFP fp) L X hηnonneg hL hDiag hTrail
  have hUpperRes := NumStability.triInv_lower_left_residual_upper_zero
    n L X hXlower hL
  have hu_lt_one : fp.u < 1 := by
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have hnu : fp.u ≤ (n : ℝ) * fp.u := by nlinarith [fp.u_nonneg]
    exact lt_of_le_of_lt hnu hvalid
  have hdenpos : 0 < 1 - fp.u := by linarith
  have hdiag_coeff : 0 ≤ fp.u / (1 - fp.u) :=
    div_nonneg fp.u_nonneg (le_of_lt hdenpos)
  have hcoef_nonneg : 0 ≤ C := by
    dsimp [C, p39Method2SourceUniformCoefficient]
    have h2 : 0 ≤ 2 * fp.u + fp.u ^ 2 := by nlinarith [sq_nonneg fp.u, fp.u_nonneg]
    have h3 : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    exact add_nonneg (add_nonneg hγnonneg (mul_nonneg h2 h3)) hdiag_coeff
  have hcoeff_diag : fp.u / (1 - fp.u) ≤ C := by
    dsimp [C, p39Method2SourceUniformCoefficient]
    have h2 : 0 ≤ 2 * fp.u + fp.u ^ 2 := by nlinarith [sq_nonneg fp.u, fp.u_nonneg]
    have h3 : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    nlinarith [mul_nonneg h2 h3]
  have hcoeff_lower :
      fp.u + (1 + fp.u) *
        (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n)) ≤ C := by
    dsimp [C, p39Method2SourceUniformCoefficient]
    nlinarith [hdiag_coeff]
  have hDiagRes : ∀ q : Fin n,
      |∑ k : Fin n, X q k * L k q - 1| ≤
        C * ∑ k : Fin n, |X q k| * |L k q| := by
    intro q
    obtain ⟨δ, hδ, hdiagval⟩ := hDiag q
    have hsum : ∑ k : Fin n, X q k * L k q = X q q * L q q := by
      apply Finset.sum_eq_single q
      · intro k _ hk
        by_cases hqk : q.val < k.val
        · rw [hXlower q k hqk]
          ring
        · have hkq : k.val < q.val := by
            have hne : k.val ≠ q.val := by
              intro heq
              exact hk (Fin.ext heq)
            omega
          rw [hL k q hkq]
          ring
      · intro hnot
        simp at hnot
    have hres : |∑ k : Fin n, X q k * L k q - 1| ≤ fp.u := by
      simpa [hsum, hdiagval] using hδ
    have hdiagterm : 1 - fp.u ≤ |X q q| * |L q q| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      rw [← abs_mul, hdiagval]
      linarith
    have htermle : |X q q| * |L q q| ≤
        ∑ k : Fin n, |X q k| * |L k q| :=
      Finset.single_le_sum (f := fun k : Fin n => |X q k| * |L k q|)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ q)
    have hu_budget : fp.u ≤
        (fp.u / (1 - fp.u)) * ∑ k : Fin n, |X q k| * |L k q| := by
      have hcancel : (fp.u / (1 - fp.u)) * (1 - fp.u) = fp.u := by
        field_simp [ne_of_gt hdenpos]
      calc
        fp.u = (fp.u / (1 - fp.u)) * (1 - fp.u) := hcancel.symm
        _ ≤ (fp.u / (1 - fp.u)) * ∑ k : Fin n, |X q k| * |L k q| :=
          mul_le_mul_of_nonneg_left (le_trans hdiagterm htermle) hdiag_coeff
    have hbudget_nonneg : 0 ≤ ∑ k : Fin n, |X q k| * |L k q| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hres (le_trans hu_budget
      (mul_le_mul_of_nonneg_right hcoeff_diag hbudget_nonneg))
  have hLowerRes : ∀ q row : Fin n, q.val < row.val →
      |(∑ k : Fin n, X row k * L k q) -
        (if row = q then 1 else 0)| ≤
        C * ∑ k : Fin n, |X row k| * |L k q| := by
    intro q row hqr
    have hbase := hLowerBase q row hqr
    have hbudget_nonneg : 0 ≤ ∑ k : Fin n, |X row k| * |L k q| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase
      (mul_le_mul_of_nonneg_right hcoeff_lower hbudget_nonneg)
  have hmain := NumStability.triInv_method2_left_residual_from_region_bounds
    n L X hcoef_nonneg hUpperRes hDiagRes hLowerRes i j
  simpa only [X, C, p39MatMul] using hmain

end VSCLReuse
