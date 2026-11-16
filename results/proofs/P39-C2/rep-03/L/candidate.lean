import VSCLReuse.P39.Definitions
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p39AsFPModel (fp : P39FPModel) : NumStability.FPModel where
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
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩

private theorem p39_dot_bound (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (hm : (m : ℝ) * fp.u < 1) :
    |p39RoundedDotProduct fp m x y - ∑ t : Fin m, x t * y t| ≤
      p39Gamma fp.u m * ∑ t : Fin m, |x t| * |y t| := by
  let F := p39AsFPModel fp
  have h := NumStability.dotProduct_error_bound F m x y hm
  simpa [F, p39AsFPModel, NumStability.fl_dotProduct,
    p39RoundedDotProduct, NumStability.gamma, p39Gamma] using h

private theorem p39_steps_ge (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) :
    ∀ (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n)
      (i j : Fin n), k ≤ j.val →
      p39Method2SourceSteps fp n L k hk X i j = X i j := by
  intro k
  induction k with
  | zero =>
      intro hk X i j _
      rfl
  | succ k ih =>
      intro hk X i j hkj
      have hge : k ≤ j.val := by omega
      have hjne : j ≠ (⟨k, hk⟩ : Fin n) := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
        (p39Method2SourceStep fp n L X ⟨k, hk⟩) i j = X i j
      rw [ih (Nat.le_of_succ_le hk) _ i j hge]
      simp [p39Method2SourceStep, hjne]

private theorem p39_steps_diag (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) :
    ∀ (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) (j : Fin n),
      j.val < k →
      p39Method2SourceSteps fp n L k hk X j j = fp.fl_div 1 (L j j) := by
  intro k
  induction k with
  | zero =>
      intro _ _ j hj
      omega
  | succ k ih =>
      intro hk X j hj
      by_cases h : j.val < k
      · exact ih (Nat.le_of_succ_le hk) _ j h
      · have hjk : j = (⟨k, hk⟩ : Fin n) := Fin.ext (by simp; omega)
        subst j
        change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
          (p39Method2SourceStep fp n L X ⟨k, hk⟩) ⟨k, hk⟩ ⟨k, hk⟩ = _
        rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk)
          (p39Method2SourceStep fp n L X ⟨k, hk⟩) ⟨k, hk⟩ ⟨k, hk⟩ (by simp)]
        simp [p39Method2SourceStep]

private theorem p39_steps_upper (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) :
    ∀ (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) (i j : Fin n),
      j.val < k → i.val < j.val →
      p39Method2SourceSteps fp n L k hk X i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ j hj _
      omega
  | succ k ih =>
      intro hk X i j hj hij
      by_cases h : j.val < k
      · exact ih (Nat.le_of_succ_le hk) _ i j h hij
      · have hjk : j = (⟨k, hk⟩ : Fin n) := Fin.ext (by simp; omega)
        subst j
        change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
          (p39Method2SourceStep fp n L X ⟨k, hk⟩) i ⟨k, hk⟩ = 0
        rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk)
          (p39Method2SourceStep fp n L X ⟨k, hk⟩) i ⟨k, hk⟩ (by simp)]
        have hik : i.val < k := by simpa using hij
        have hine : i ≠ (⟨k, hk⟩ : Fin n) := by
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        simp [p39Method2SourceStep, hine, show ¬ k < i.val by omega]

private theorem p39_steps_below (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) :
    ∀ (k : ℕ) (hk : k ≤ n) (X : P39Matrix n n) (i j : Fin n),
      j.val < k → j.val < i.val →
      p39Method2SourceSteps fp n L k hk X i j =
        fp.fl_mul (-(p39Method2SourceSteps fp n L k hk X j j))
          (p39RoundedDotProduct fp (n - j.val - 1)
            (fun t => p39Method2SourceSteps fp n L k hk X i
              ⟨j.val + 1 + t.val, by omega⟩)
            (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ j hj _
      omega
  | succ k ih =>
      intro hk X i j hj hij
      by_cases h : j.val < k
      · exact ih (Nat.le_of_succ_le hk) _ i j h hij
      · have hjk : j = (⟨k, hk⟩ : Fin n) := Fin.ext (by simp; omega)
        subst j
        let Y := p39Method2SourceStep fp n L X (⟨k, hk⟩ : Fin n)
        have hcol : p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
            Y i ⟨k, hk⟩ = Y i ⟨k, hk⟩ :=
          p39_steps_ge fp n L k (Nat.le_of_succ_le hk) Y i ⟨k, hk⟩ (by simp)
        have hdiag : p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
            Y ⟨k, hk⟩ ⟨k, hk⟩ = Y ⟨k, hk⟩ ⟨k, hk⟩ :=
          p39_steps_ge fp n L k (Nat.le_of_succ_le hk) Y ⟨k, hk⟩ ⟨k, hk⟩ (by simp)
        have htail : ∀ t : Fin (n - k - 1),
            p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk) Y i
              ⟨k + 1 + t.val, by omega⟩ = X i ⟨k + 1 + t.val, by omega⟩ := by
          intro t
          rw [p39_steps_ge fp n L k (Nat.le_of_succ_le hk) Y i
            ⟨k + 1 + t.val, by omega⟩ (by simp; omega)]
          simp [Y, p39Method2SourceStep, show (⟨k + 1 + t.val, by omega⟩ : Fin n) ≠
            ⟨k, hk⟩ by
              intro heq
              have := congrArg Fin.val heq
              simp at this
              omega]
        change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
          Y i ⟨k, hk⟩ =
            fp.fl_mul (-(p39Method2SourceSteps fp n L k
              (Nat.le_of_succ_le hk) Y ⟨k, hk⟩ ⟨k, hk⟩))
              (p39RoundedDotProduct fp (n - k - 1)
                (fun t => p39Method2SourceSteps fp n L k
                  (Nat.le_of_succ_le hk) Y i ⟨k + 1 + t.val, by omega⟩)
                (fun t => L ⟨k + 1 + t.val, by omega⟩ ⟨k, hk⟩))
        rw [hcol, hdiag]
        have hik : k < i.val := by simpa using hij
        have hfun :
            (fun t : Fin (n - k - 1) =>
              p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk) Y i
                ⟨k + 1 + t.val, by omega⟩) =
            (fun t : Fin (n - k - 1) => X i ⟨k + 1 + t.val, by omega⟩) := by
          funext t
          exact htail t
        rw [hfun]
        have hine : i ≠ (⟨k, hk⟩ : Fin n) := by
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        simp [Y, p39Method2SourceStep, hine, hik]

private theorem p39_tail_sum {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩) =
      ∑ k : Fin n, if j.val < k.val then f k else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (fun (t : Fin (n - j.val - 1)) (_ : t ∈ Finset.univ) =>
      (⟨j.val + 1 + t.val, by omega⟩ : Fin n))
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro t₁ _ t₂ _ heq
    apply Fin.ext
    have := congrArg Fin.val heq
    simp at this
    omega
  · intro k hk
    have hjk : j.val < k.val := by simpa using hk
    refine ⟨⟨k.val - j.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp
    omega
  · intro t _
    rfl

private theorem p39_inverse_diag (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (j : Fin n) :
    p39Method2SourceInverse fp n L j j = fp.fl_div 1 (L j j) := by
  exact p39_steps_diag fp n L n (le_refl n) 0 j j.isLt

private theorem p39_inverse_upper (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hij : i.val < j.val) :
    p39Method2SourceInverse fp n L i j = 0 := by
  exact p39_steps_upper fp n L n (le_refl n) 0 i j j.isLt hij

private theorem p39_inverse_below (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hij : j.val < i.val) :
    p39Method2SourceInverse fp n L i j =
      fp.fl_mul (-(p39Method2SourceInverse fp n L j j))
        (p39RoundedDotProduct fp (n - j.val - 1)
          (fun t => p39Method2SourceInverse fp n L i
            ⟨j.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  exact p39_steps_below fp n L n (le_refl n) 0 i j j.isLt hij

private theorem p39_inverse_diag_cert (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (hdiag : ∀ j : Fin n, L j j ≠ 0) :
    ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      p39Method2SourceInverse fp n L j j * L j j = 1 + δ := by
  intro j
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div 1 (L j j) (hdiag j)
  refine ⟨δ, hδ, ?_⟩
  rw [p39_inverse_diag, hdiv]
  have hstep : (1 : ℝ) / L j j * (1 + δ) * L j j =
      (1 + δ) * (L j j / L j j) := by ring
  rw [hstep, div_self (hdiag j), mul_one]

private theorem p39_inverse_update_error (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (hdiag : ∀ j : Fin n, L j j ≠ 0)
    (hvalid : P39GammaValid fp.u n) :
    ∀ j row : Fin n, j.val < row.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤
          ((1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) *
          (∑ k : Fin n, if j.val < k.val then
            |p39Method2SourceInverse fp n L row k| * |L k j| else 0) ∧
        p39Method2SourceInverse fp n L row j =
          -p39Method2SourceInverse fp n L j j *
            (∑ k : Fin n, if j.val < k.val then
              p39Method2SourceInverse fp n L row k * L k j else 0) + Δ := by
  intro j row hij
  let X := p39Method2SourceInverse fp n L
  let m := n - j.val - 1
  let x : Fin m → ℝ := fun t => X row ⟨j.val + 1 + t.val, by omega⟩
  let y : Fin m → ℝ := fun t => L ⟨j.val + 1 + t.val, by omega⟩ j
  let exactTail : ℝ := ∑ t : Fin m, x t * y t
  let tailAbs : ℝ := ∑ t : Fin m, |x t| * |y t|
  let flTail : ℝ := p39RoundedDotProduct fp m x y
  let Δ : ℝ := fp.fl_mul (-X j j) flTail - (-X j j * exactTail)
  refine ⟨Δ, ?_, ?_⟩
  · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X j j) flTail
    let F := p39AsFPModel fp
    have hmle : m ≤ n := by dsimp [m]; omega
    have hmvalid : (m : ℝ) * fp.u < 1 :=
      NumStability.gammaValid_mono F hmle hvalid
    have hγnonneg : 0 ≤ p39Gamma fp.u n :=
      NumStability.gamma_nonneg F hvalid
    have hγmono : p39Gamma fp.u m ≤ p39Gamma fp.u n :=
      NumStability.gamma_mono F hmle hvalid
    have htail_nonneg : 0 ≤ tailAbs := by
      exact Finset.sum_nonneg (fun t _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hdot0 := p39_dot_bound fp m x y hmvalid
    have hdot : |flTail - exactTail| ≤ p39Gamma fp.u n * tailAbs := by
      exact le_trans hdot0 (mul_le_mul_of_nonneg_right hγmono htail_nonneg)
    have htail_abs : |exactTail| ≤ tailAbs := by
      calc
        |exactTail| ≤ ∑ t : Fin m, |x t * y t| := Finset.abs_sum_le_sum_abs _ _
        _ = tailAbs := by simp [tailAbs, abs_mul]
    have hfl_abs : |flTail| ≤ (1 + p39Gamma fp.u n) * tailAbs := by
      calc
        |flTail| = |exactTail + (flTail - exactTail)| := by congr 1; ring
        _ ≤ |exactTail| + |flTail - exactTail| := abs_add_le _ _
        _ ≤ tailAbs + p39Gamma fp.u n * tailAbs := add_le_add htail_abs hdot
        _ = (1 + p39Gamma fp.u n) * tailAbs := by ring
    obtain ⟨δ, hδ, hdiagX⟩ := p39_inverse_diag_cert fp n L hdiag j
    have hdiag_abs : |X j j * L j j| ≤ 1 + fp.u := by
      calc
        |X j j * L j j| = |1 + δ| := by rw [hdiagX]
        _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
        _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
    have honeu : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    have hcoef_nonneg : 0 ≤ (1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs) :=
      mul_nonneg honeu (mul_nonneg honeγ htail_nonneg)
    have hΔdecomp : Δ * L j j =
        (-X j j * L j j) * (flTail - exactTail) +
          ((-X j j * L j j) * flTail) * δmul := by
      dsimp [Δ]
      rw [hmul]
      ring
    have hfirst :
        |(-X j j * L j j) * (flTail - exactTail)| ≤
          (1 + fp.u) * (p39Gamma fp.u n * tailAbs) := by
      have hneg : |(-X j j * L j j)| = |X j j * L j j| := by
        rw [show -X j j * L j j = -(X j j * L j j) by ring, abs_neg]
      calc
        |(-X j j * L j j) * (flTail - exactTail)| =
            |X j j * L j j| * |flTail - exactTail| := by rw [abs_mul, hneg]
        _ ≤ (1 + fp.u) * (p39Gamma fp.u n * tailAbs) :=
          mul_le_mul hdiag_abs hdot (abs_nonneg _) honeu
    have hsecond :
        |((-X j j * L j j) * flTail) * δmul| ≤
          ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u := by
      have hneg : |(-X j j * L j j)| = |X j j * L j j| := by
        rw [show -X j j * L j j = -(X j j * L j j) by ring, abs_neg]
      have hleft : |X j j * L j j| * |flTail| ≤
          (1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs) :=
        mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu
      calc
        |((-X j j * L j j) * flTail) * δmul| =
            |X j j * L j j| * |flTail| * |δmul| := by rw [abs_mul, abs_mul, hneg]
        _ ≤ ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u :=
          mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
    have hbound : |Δ * L j j| ≤
        ((1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) *
          tailAbs := by
      calc
        |Δ * L j j| = |(-X j j * L j j) * (flTail - exactTail) +
            ((-X j j * L j j) * flTail) * δmul| := by rw [hΔdecomp]
        _ ≤ |(-X j j * L j j) * (flTail - exactTail)| +
            |((-X j j * L j j) * flTail) * δmul| := abs_add_le _ _
        _ ≤ (1 + fp.u) * (p39Gamma fp.u n * tailAbs) +
            ((1 + fp.u) * ((1 + p39Gamma fp.u n) * tailAbs)) * fp.u :=
              add_le_add hfirst hsecond
        _ = ((1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) *
              tailAbs := by ring
    have hsumabs : tailAbs =
        ∑ k : Fin n, if j.val < k.val then |X row k| * |L k j| else 0 := by
      simpa [tailAbs, x, y] using
        (p39_tail_sum j (fun k => |X row k| * |L k j|))
    simpa only [X, ← hsumabs] using hbound
  · have hstore := p39_inverse_below fp n L row j hij
    have hsum : exactTail =
        ∑ k : Fin n, if j.val < k.val then X row k * L k j else 0 := by
      simpa [exactTail, x, y] using
        (p39_tail_sum j (fun k => X row k * L k j))
    calc
      X row j = fp.fl_mul (-X j j) flTail := by simpa [X, flTail, x, y, m] using hstore
      _ = -X j j * exactTail + Δ := by dsimp [Δ]; ring
      _ = -X j j * (∑ k : Fin n, if j.val < k.val then X row k * L k j else 0) + Δ := by rw [hsum]

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
  let F := p39AsFPModel fp
  let η : ℝ := (1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))
  have hγnonneg : 0 ≤ p39Gamma fp.u n :=
    NumStability.gamma_nonneg F hvalid
  have hu_lt_one : fp.u < 1 := by
    have hn : 1 ≤ n := by have := j.isLt; omega
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h := mul_le_mul_of_nonneg_right hnreal fp.u_nonneg
    have hv := hvalid
    dsimp [P39GammaValid] at hv
    nlinarith
  have hdenpos : 0 < 1 - fp.u := by linarith
  have hγ1nonneg : 0 ≤ fp.u / (1 - fp.u) :=
    div_nonneg fp.u_nonneg (le_of_lt hdenpos)
  have hη : 0 ≤ η := by
    dsimp [η]
    have h1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have h2 : 0 ≤ 1 + p39Gamma fp.u n := by linarith
    exact mul_nonneg h1 (add_nonneg hγnonneg (mul_nonneg fp.u_nonneg h2))
  have hcoeff : p39Method2SourceUniformCoefficient fp n =
      fp.u + η + fp.u / (1 - fp.u) := by
    dsimp [p39Method2SourceUniformCoefficient, η]
    ring
  have hcoeff_lower : fp.u + η ≤ p39Method2SourceUniformCoefficient fp n := by
    rw [hcoeff]
    linarith
  have hcoeff_diag : fp.u / (1 - fp.u) ≤
      p39Method2SourceUniformCoefficient fp n := by
    rw [hcoeff]
    linarith [fp.u_nonneg]
  have hcoeff_nonneg : 0 ≤ p39Method2SourceUniformCoefficient fp n := by
    linarith
  have hXupper : ∀ a b : Fin n, a.val < b.val → X a b = 0 := by
    intro a b hab
    exact p39_inverse_upper fp n L a b hab
  have hDiag : ∀ q : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧ X q q * L q q = 1 + δ :=
    p39_inverse_diag_cert fp n L hdiag
  have hTrail : ∀ q row : Fin n, row.val > q.val →
      ∃ Δ : ℝ,
        |Δ * L q q| ≤ η *
          (∑ k : Fin n, if q.val < k.val then |X row k| * |L k q| else 0) ∧
        X row q = -X q q *
          (∑ k : Fin n, if q.val < k.val then X row k * L k q else 0) + Δ := by
    simpa only [X, η] using p39_inverse_update_error fp n L hdiag hvalid
  have hUpper :=
    NumStability.triInv_lower_left_residual_upper_zero n L X hXupper hL
  have hLowerBase :=
    NumStability.triInv_method2_offdiag_trailing_update_full_bound
      n F L X hη hL hDiag hTrail
  have hLower : ∀ q row : Fin n, row.val > q.val →
      |∑ k : Fin n, X row k * L k q - (if row = q then 1 else 0)| ≤
        p39Method2SourceUniformCoefficient fp n *
          ∑ k : Fin n, |X row k| * |L k q| := by
    intro q row hqr
    have hS : 0 ≤ ∑ k : Fin n, |X row k| * |L k q| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans (hLowerBase q row hqr)
      (mul_le_mul_of_nonneg_right hcoeff_lower hS)
  have hDiagBudget : ∀ q : Fin n,
      |∑ k : Fin n, X q k * L k q - 1| ≤
        p39Method2SourceUniformCoefficient fp n *
          ∑ k : Fin n, |X q k| * |L k q| := by
    intro q
    obtain ⟨δ, hδ, hdiagX⟩ := hDiag q
    have hsum : ∑ k : Fin n, X q k * L k q = X q q * L q q := by
      apply Finset.sum_eq_single q
      · intro k _ hk
        by_cases hqk : q.val < k.val
        · rw [hXupper q k hqk]
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
      simpa [hsum, hdiagX] using hδ
    let S : ℝ := ∑ k : Fin n, |X q k| * |L k q|
    have hterm : |X q q| * |L q q| ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun k : Fin n => |X q k| * |L k q|)
        (s := Finset.univ)
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ q)
    have hdiaglower : 1 - fp.u ≤ |X q q| * |L q q| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      calc
        1 - fp.u ≤ |1 + δ| := by linarith
        _ = |X q q| * |L q q| := by rw [← abs_mul, hdiagX]
    have heq : (fp.u / (1 - fp.u)) * (1 - fp.u) = fp.u := by
      field_simp
    have huS : fp.u ≤ (fp.u / (1 - fp.u)) * S := by
      calc
        fp.u = (fp.u / (1 - fp.u)) * (1 - fp.u) := heq.symm
        _ ≤ (fp.u / (1 - fp.u)) * (|X q q| * |L q q|) :=
          mul_le_mul_of_nonneg_left hdiaglower hγ1nonneg
        _ ≤ (fp.u / (1 - fp.u)) * S :=
          mul_le_mul_of_nonneg_left hterm hγ1nonneg
    have hS : 0 ≤ S := Finset.sum_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hres (le_trans huS
      (mul_le_mul_of_nonneg_right hcoeff_diag hS))
  have hfinal := NumStability.triInv_method2_left_residual_from_region_bounds
    n L X hcoeff_nonneg hUpper hDiagBudget hLower i j
  simpa only [X, p39MatMul] using hfinal

end VSCLReuse
