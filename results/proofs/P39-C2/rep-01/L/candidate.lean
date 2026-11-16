import VSCLReuse.P39.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p39AsFP (fp : P39FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private theorem p39_steps_keep (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n) :
    ∀ (m : ℕ) (hm : m ≤ n) (X : P39Matrix n n) (i j : Fin n),
      m ≤ j.val → p39Method2SourceSteps fp n L m hm X i j = X i j := by
  intro m
  induction m with
  | zero =>
      intro hm X i j _
      rfl
  | succ m ih =>
      intro hm X i j hj
      have hj' : m ≤ j.val := by omega
      have hne : j ≠ (⟨m, hm⟩ : Fin n) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        omega
      rw [p39Method2SourceSteps, ih (Nat.le_of_succ_le hm) _ i j hj']
      simp [p39Method2SourceStep, hne]

private theorem p39_steps_entry (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n) :
    ∀ (m : ℕ) (hm : m ≤ n) (X : P39Matrix n n) (i j : Fin n),
      j.val < m →
      p39Method2SourceSteps fp n L m hm X i j =
        (if i = j then fp.fl_div 1 (L j j)
         else if j.val < i.val then
           fp.fl_mul (-(fp.fl_div 1 (L j j)))
             (p39RoundedDotProduct fp (n - j.val - 1)
               (fun t => p39Method2SourceSteps fp n L m hm X i
                 ⟨j.val + 1 + t.val, by omega⟩)
               (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j))
         else 0) := by
  intro m
  induction m with
  | zero =>
      intro hm X i j hj
      omega
  | succ m ih =>
      intro hm X i j hj
      let q : Fin n := ⟨m, hm⟩
      let Y := p39Method2SourceStep fp n L X q
      by_cases hjm : j.val < m
      · simpa only [p39Method2SourceSteps] using
          ih (Nat.le_of_succ_le hm) Y i j hjm
      · have hjq : j = q := Fin.ext (by dsimp [q]; omega)
        subst j
        have hkeep : ∀ k : Fin n, m ≤ k.val →
            p39Method2SourceSteps fp n L m (Nat.le_of_succ_le hm) Y i k = Y i k :=
          fun k hk => p39_steps_keep fp n L m (Nat.le_of_succ_le hm) Y i k hk
        rw [p39Method2SourceSteps, hkeep q (by simp [q])]
        have htail :
            p39RoundedDotProduct fp (n - q.val - 1)
              (fun t => p39Method2SourceSteps fp n L m (Nat.le_of_succ_le hm) Y i
                ⟨q.val + 1 + t.val, by omega⟩)
              (fun t => L ⟨q.val + 1 + t.val, by omega⟩ q) =
            p39RoundedDotProduct fp (n - q.val - 1)
              (fun t => Y i ⟨q.val + 1 + t.val, by omega⟩)
              (fun t => L ⟨q.val + 1 + t.val, by omega⟩ q) := by
          congr 1
          funext t
          exact hkeep ⟨q.val + 1 + t.val, by omega⟩ (by dsimp [q]; omega)
        rw [htail]
        have hYtail :
            (fun t : Fin (n - q.val - 1) =>
              Y i ⟨q.val + 1 + t.val, by omega⟩) =
            (fun t : Fin (n - q.val - 1) =>
              X i ⟨q.val + 1 + t.val, by omega⟩) := by
          funext t
          have hne : (⟨q.val + 1 + t.val, by omega⟩ : Fin n) ≠ q := by
            intro h
            have hv := congrArg Fin.val h
            simp at hv
            omega
          simp [Y, p39Method2SourceStep, hne]
        rw [hYtail]
        split_ifs with hi he
        · simp [Y, p39Method2SourceStep, hi]
        · have he' : q < i := he
          simp [Y, p39Method2SourceStep, hi, he']
        · have he' : ¬ q < i := he
          simp [Y, p39Method2SourceStep, hi, he']

private theorem p39_tail_sum {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩) =
      ∑ k : Fin n, if j.val < k.val then f k else 0 := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij (fun t _ => (⟨j.val + 1 + t.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro t _ s _ h
    apply Fin.ext
    simpa using congrArg Fin.val h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    let t : Fin (n - j.val - 1) := ⟨k.val - j.val - 1, by omega⟩
    refine ⟨t, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp [t]
    omega
  · intro t _
    rfl

private theorem p39_source_entry (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (i j : Fin n) :
    p39Method2SourceInverse fp n L i j =
      (if i = j then fp.fl_div 1 (L j j)
       else if j.val < i.val then
         fp.fl_mul (-(fp.fl_div 1 (L j j)))
           (p39RoundedDotProduct fp (n - j.val - 1)
             (fun t => p39Method2SourceInverse fp n L i
               ⟨j.val + 1 + t.val, by omega⟩)
             (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j))
       else 0) := by
  exact p39_steps_entry fp n L n (le_refl n) 0 i j j.isLt

private theorem p39_source_upper (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (i j : Fin n) (hij : i.val < j.val) :
    p39Method2SourceInverse fp n L i j = 0 := by
  rw [p39_source_entry]
  have hne : i ≠ j := by intro h; subst i; omega
  simp [hne, show ¬ j.val < i.val by omega]

private theorem p39_source_diag (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (j : Fin n) :
    p39Method2SourceInverse fp n L j j = fp.fl_div 1 (L j j) := by
  rw [p39_source_entry]
  simp

private theorem p39_source_below (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (i j : Fin n) (hij : j.val < i.val) :
    p39Method2SourceInverse fp n L i j =
      fp.fl_mul (-(p39Method2SourceInverse fp n L j j))
        (p39RoundedDotProduct fp (n - j.val - 1)
          (fun t => p39Method2SourceInverse fp n L i
            ⟨j.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  rw [p39_source_entry, p39_source_diag]
  have hne : i ≠ j := by intro h; subst i; omega
  simp [hne, hij]

private theorem p39_dot_eq_library (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) :
    p39RoundedDotProduct fp m x y =
      NumStability.fl_dotProduct (p39AsFP fp) m x y := by
  cases m <;> rfl

private theorem p39_gamma_valid_library (fp : P39FPModel) (m : ℕ)
    (hm : P39GammaValid fp.u m) : NumStability.gammaValid (p39AsFP fp) m := hm

private theorem p39_gamma_eq_library (fp : P39FPModel) (m : ℕ) :
    p39Gamma fp.u m = NumStability.gamma (p39AsFP fp) m := rfl

private theorem p39_dot_error (fp : P39FPModel) (n m : ℕ) (hm : m ≤ n)
    (hvalid : P39GammaValid fp.u n) (x y : Fin m → ℝ) :
    |p39RoundedDotProduct fp m x y - ∑ t : Fin m, x t * y t| ≤
      p39Gamma fp.u n * ∑ t : Fin m, |x t| * |y t| := by
  let fp' := p39AsFP fp
  have hn : NumStability.gammaValid fp' n := p39_gamma_valid_library fp n hvalid
  have hmvalid : NumStability.gammaValid fp' m :=
    NumStability.gammaValid_mono fp' hm hn
  have hd := NumStability.dotProduct_error_bound fp' m x y hmvalid
  have hmono := NumStability.gamma_mono fp' hm hn
  have hs : 0 ≤ ∑ t : Fin m, |x t| * |y t| := by
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    |p39RoundedDotProduct fp m x y - ∑ t : Fin m, x t * y t|
        ≤ NumStability.gamma fp' m * ∑ t : Fin m, |x t| * |y t| := by
          simpa only [p39_dot_eq_library] using hd
    _ ≤ NumStability.gamma fp' n * ∑ t : Fin m, |x t| * |y t| :=
      mul_le_mul_of_nonneg_right hmono hs
    _ = p39Gamma fp.u n * ∑ t : Fin m, |x t| * |y t| := by
      rw [p39_gamma_eq_library]

private theorem p39_diag_budget (fp : P39FPModel) (n : ℕ)
    (L X : P39Matrix n n) (hvalid : P39GammaValid fp.u n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (hUpper : ∀ a b : Fin n, a.val < b.val → X a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧ X j j * L j j = 1 + δ)
    (j : Fin n) :
    |(∑ k : Fin n, X j k * L k j) - 1| ≤
      (fp.u / (1 - fp.u)) * ∑ k : Fin n, |X j k| * |L k j| := by
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  have hsum : ∑ k : Fin n, X j k * L k j = X j j * L j j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      by_cases hjk : j.val < k.val
      · rw [hUpper j k hjk]
        ring
      · have hkj : k.val < j.val := by
          have hne : k.val ≠ j.val := by
            intro h
            exact hk (Fin.ext h)
          omega
        rw [hL k j hkj]
        ring
    · intro hnot
      simp at hnot
  have hres : |(∑ k : Fin n, X j k * L k j) - 1| ≤ fp.u := by
    simpa [hsum, hdiag] using hδ
  have hvalid1 : P39GammaValid fp.u 1 := by
    have hn : NumStability.gammaValid (p39AsFP fp) n :=
      p39_gamma_valid_library fp n hvalid
    have hle : 1 ≤ n := by have := j.isLt; omega
    exact NumStability.gammaValid_mono (p39AsFP fp) hle hn
  have hu : fp.u < 1 := by simpa [P39GammaValid] using hvalid1
  have hden : 0 < 1 - fp.u := by linarith
  let S : ℝ := ∑ k : Fin n, |X j k| * |L k j|
  have hterm : |X j j| * |L j j| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg (X j k)) (abs_nonneg (L k j)))
      (Finset.mem_univ j)
  have hlow : 1 - fp.u ≤ |X j j| * |L j j| := by
    have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
      simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
    calc
      1 - fp.u ≤ 1 - |δ| := by linarith
      _ ≤ |1 + δ| := by linarith
      _ = |X j j * L j j| := by rw [hdiag]
      _ = |X j j| * |L j j| := abs_mul _ _
  have hS : 1 - fp.u ≤ S := le_trans hlow hterm
  have hcoef : 0 ≤ fp.u / (1 - fp.u) := div_nonneg fp.u_nonneg hden.le
  have hmul : fp.u / (1 - fp.u) * (1 - fp.u) = fp.u := by
    field_simp
  calc
    |(∑ k : Fin n, X j k * L k j) - 1| ≤ fp.u := hres
    _ = fp.u / (1 - fp.u) * (1 - fp.u) := hmul.symm
    _ ≤ fp.u / (1 - fp.u) * S := mul_le_mul_of_nonneg_left hS hcoef

private theorem p39_trail_budget (fp : P39FPModel) (n : ℕ)
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
  let m := n - j.val - 1
  let x : Fin m → ℝ := fun t => X row ⟨j.val + 1 + t.val, by omega⟩
  let y : Fin m → ℝ := fun t => L ⟨j.val + 1 + t.val, by omega⟩ j
  let S : ℝ := ∑ t : Fin m, x t * y t
  let T : ℝ := ∑ t : Fin m, |x t| * |y t|
  let F : ℝ := p39RoundedDotProduct fp m x y
  let Δ : ℝ := fp.fl_mul (-X j j) F - (-X j j * S)
  have hm : m ≤ n := by dsimp [m]; omega
  have hγ : 0 ≤ p39Gamma fp.u n := by
    simpa only [p39_gamma_eq_library] using
      NumStability.gamma_nonneg (p39AsFP fp) (p39_gamma_valid_library fp n hvalid)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hdot : |F - S| ≤ p39Gamma fp.u n * T := by
    simpa only [F, S, T] using p39_dot_error fp n m hm hvalid x y
  have hSabs : |S| ≤ T := by
    calc
      |S| ≤ ∑ t : Fin m, |x t * y t| := Finset.abs_sum_le_sum_abs _ _
      _ = T := by simp [T, abs_mul]
  have hFabs : |F| ≤ (1 + p39Gamma fp.u n) * T := by
    calc
      |F| = |S + (F - S)| := by congr 1; ring
      _ ≤ |S| + |F - S| := abs_add_le _ _
      _ ≤ T + p39Gamma fp.u n * T := add_le_add hSabs hdot
      _ = (1 + p39Gamma fp.u n) * T := by ring
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  have hdiagabs : |X j j * L j j| ≤ 1 + fp.u := by
    calc
      |X j j * L j j| = |1 + δ| := by rw [hdiag]
      _ ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by norm_num; exact hδ
  obtain ⟨ε, hε, hmul⟩ := fp.model_mul (-X j j) F
  have hΔeq :
      Δ * L j j =
        (-X j j * L j j) * (F - S) +
          ((-X j j * L j j) * F) * ε := by
    dsimp [Δ]
    rw [hmul]
    ring
  have hnegabs : |(-X j j * L j j)| = |X j j * L j j| := by
    have h : -X j j * L j j = -(X j j * L j j) := by ring
    rw [h, abs_neg]
  have hfirst :
      |(-X j j * L j j) * (F - S)| ≤
        (1 + fp.u) * (p39Gamma fp.u n * T) := by
    calc
      |(-X j j * L j j) * (F - S)| =
          |X j j * L j j| * |F - S| := by rw [abs_mul, hnegabs]
      _ ≤ (1 + fp.u) * (p39Gamma fp.u n * T) :=
          mul_le_mul hdiagabs hdot (abs_nonneg _) (by linarith [fp.u_nonneg])
  have hsecond :
      |((-X j j * L j j) * F) * ε| ≤
        ((1 + fp.u) * ((1 + p39Gamma fp.u n) * T)) * fp.u := by
    have hleft :
        |X j j * L j j| * |F| ≤
          (1 + fp.u) * ((1 + p39Gamma fp.u n) * T) :=
      mul_le_mul hdiagabs hFabs (abs_nonneg _) (by linarith [fp.u_nonneg])
    calc
      |((-X j j * L j j) * F) * ε| =
          |X j j * L j j| * |F| * |ε| := by rw [abs_mul, abs_mul, hnegabs]
      _ ≤ ((1 + fp.u) * ((1 + p39Gamma fp.u n) * T)) * fp.u :=
          mul_le_mul hleft hε (abs_nonneg _)
            (mul_nonneg (by linarith [fp.u_nonneg])
              (mul_nonneg (by linarith [hγ]) hT))
  have hΔ : |Δ * L j j| ≤
      ((1 + fp.u) * (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) * T := by
    calc
      |Δ * L j j| =
          |(-X j j * L j j) * (F - S) + ((-X j j * L j j) * F) * ε| := by
            rw [hΔeq]
      _ ≤ |(-X j j * L j j) * (F - S)| +
          |((-X j j * L j j) * F) * ε| := abs_add_le _ _
      _ ≤ (1 + fp.u) * (p39Gamma fp.u n * T) +
          ((1 + fp.u) * ((1 + p39Gamma fp.u n) * T)) * fp.u :=
            add_le_add hfirst hsecond
      _ = ((1 + fp.u) *
          (p39Gamma fp.u n + fp.u * (1 + p39Gamma fp.u n))) * T := by ring
  refine ⟨Δ, ?_, ?_⟩
  · have hTeq : T =
        ∑ k : Fin n, if j.val < k.val then |X row k| * |L k j| else 0 := by
      simpa only [T, x, y, m] using
        p39_tail_sum j (fun k => |X row k| * |L k j|)
    rw [← hTeq]
    exact hΔ
  · have hsource := hStore j row hij
    have hSeq : S =
        ∑ k : Fin n, if j.val < k.val then X row k * L k j else 0 := by
      simpa only [S, x, y, m] using
        p39_tail_sum j (fun k => X row k * L k j)
    rw [← hSeq]
    calc
      X row j = fp.fl_mul (-X j j) F := by simpa only [F, x, y, m] using hsource
      _ = -X j j * S + Δ := by dsimp [Δ]; ring

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
  let G := p39Gamma fp.u n
  let η := (1 + fp.u) * (G + fp.u * (1 + G))
  have hγ : 0 ≤ G := by
    simpa only [G, p39_gamma_eq_library] using
      NumStability.gamma_nonneg (p39AsFP fp) (p39_gamma_valid_library fp n hvalid)
  have hη : 0 ≤ η := by
    dsimp [η]
    exact mul_nonneg (by linarith [fp.u_nonneg])
      (add_nonneg hγ (mul_nonneg fp.u_nonneg (by linarith)))
  have hq : 0 ≤ fp.u / (1 - fp.u) := by
    have hle : 1 ≤ n := by have := i.isLt; omega
    have hvalid1 : P39GammaValid fp.u 1 :=
      NumStability.gammaValid_mono (p39AsFP fp) hle
        (p39_gamma_valid_library fp n hvalid)
    have hu : fp.u < 1 := by simpa [P39GammaValid] using hvalid1
    exact div_nonneg fp.u_nonneg (by linarith)
  have hC : C = fp.u + η + fp.u / (1 - fp.u) := by
    dsimp [C, η, G, p39Method2SourceUniformCoefficient]
    ring
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact add_nonneg (add_nonneg fp.u_nonneg hη) hq
  have hUpper : ∀ a b : Fin n, a.val < b.val → X a b = 0 := by
    intro a b hab
    exact p39_source_upper fp n L a b hab
  have hDiag : ∀ a : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X a a * L a a = 1 + δ := by
    intro a
    obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 (L a a) (hdiag a)
    refine ⟨δ, hδ, ?_⟩
    change p39Method2SourceInverse fp n L a a * L a a = 1 + δ
    rw [p39_source_diag, hd]
    have h : (1 : ℝ) / L a a * (1 + δ) * L a a =
        (L a a / L a a) * (1 + δ) := by ring
    rw [h, div_self (hdiag a), one_mul]
  have hStore : ∀ a row : Fin n, a.val < row.val →
      X row a = fp.fl_mul (-X a a)
        (p39RoundedDotProduct fp (n - a.val - 1)
          (fun t => X row ⟨a.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨a.val + 1 + t.val, by omega⟩ a)) := by
    intro a row har
    exact p39_source_below fp n L row a har
  have hTrail := p39_trail_budget fp n L X hvalid hDiag hStore
  have hUpperRes :=
    NumStability.triInv_lower_left_residual_upper_zero n L X hUpper hL
  have hDiagRes : ∀ a : Fin n,
      |(∑ k : Fin n, X a k * L k a) - 1| ≤
        C * ∑ k : Fin n, |X a k| * |L k a| := by
    intro a
    have hbase := p39_diag_budget fp n L X hvalid hL hUpper hDiag a
    have hsum : 0 ≤ ∑ k : Fin n, |X a k| * |L k a| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcoeff : fp.u / (1 - fp.u) ≤ C := by
      rw [hC]
      linarith [fp.u_nonneg, hη]
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hsum)
  have hLowerRes : ∀ a row : Fin n, a.val < row.val →
      |(∑ k : Fin n, X row k * L k a) -
          (if row = a then 1 else 0)| ≤
        C * ∑ k : Fin n, |X row k| * |L k a| := by
    intro a row har
    have hbase :=
      NumStability.triInv_method2_offdiag_trailing_update_full_bound
        n (p39AsFP fp) L X hη hL hDiag hTrail a row har
    have hsum : 0 ≤ ∑ k : Fin n, |X row k| * |L k a| :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcoeff : fp.u + η ≤ C := by
      rw [hC]
      linarith [hq]
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hsum)
  have hAll :=
    NumStability.triInv_method2_left_residual_from_region_bounds
      n L X hCnonneg hUpperRes hDiagRes hLowerRes i j
  simpa only [p39MatMul] using hAll

end VSCLReuse
