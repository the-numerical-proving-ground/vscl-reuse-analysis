import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix Matrix.Norms.Frobenius

private theorem p08_gamma_comp
    {a b u : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hvalid : (a + b) * u < 1) :
    p08GammaReal a u + p08GammaReal b u *
      (1 + p08GammaReal a u) ≤ p08GammaReal (a + b) u := by
  unfold p08GammaReal
  have hau : 0 ≤ a * u := mul_nonneg ha hu
  have hbu : 0 ≤ b * u := mul_nonneg hb hu
  have hab : 0 ≤ a * u + b * u := add_nonneg hau hbu
  have hv : a * u + b * u < 1 := by nlinarith [hvalid]
  have h₁ : 0 < 1 - a * u := by linarith
  have h₂ : 0 < 1 - b * u := by linarith
  have h₃ : 0 < 1 - (a + b) * u := by linarith
  have h₂' : 1 - u * b ≠ 0 := by nlinarith [h₂]
  have heq :
      a * u / (1 - a * u) + b * u / (1 - b * u) *
        (1 + a * u / (1 - a * u)) =
      (a * u + b * u - (a * u) * (b * u)) /
        ((1 - a * u) * (1 - b * u)) := by
    field_simp [ne_of_gt h₁, ne_of_gt h₂, h₂']
    ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos h₁ h₂) h₃).2
  have hident :
      (a + b) * u * ((1 - a * u) * (1 - b * u)) -
      (a * u + b * u - (a * u) * (b * u)) * (1 - (a + b) * u) =
      (a * u) * (b * u) := by ring
  nlinarith [mul_nonneg hau hbu]

private theorem p08_gamma_nonneg
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hvalid : a * u < 1) :
    0 ≤ p08GammaReal a u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg ha hu) (by linarith)

private theorem p08_gamma_mono
    {a b u : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u)
    (hvalid : b * u < 1) :
    p08GammaReal a u ≤ p08GammaReal b u := by
  unfold p08GammaReal
  have hle : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
  have h₁ : 0 < 1 - a * u := by linarith
  have h₂ : 0 < 1 - b * u := by linarith
  apply (div_le_div_iff₀ h₁ h₂).2
  nlinarith

private theorem p08_gamma_one_ge_u
    {u : ℝ} (_hu : 0 ≤ u) (hvalid : u < 1) :
    u ≤ p08GammaReal 1 u := by
  unfold p08GammaReal
  simp only [one_mul]
  rw [le_div_iff₀ (by linarith : 0 < 1 - u)]
  nlinarith [sq_nonneg u]

private theorem p08_gamma_abs_comp
    {a b u δ ε : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hvalid : (a + b) * u < 1)
    (hδ : |δ| ≤ p08GammaReal a u)
    (hε : |ε| ≤ p08GammaReal b u) :
    |δ + ε + δ * ε| ≤ p08GammaReal (a + b) u := by
  have hγa : 0 ≤ p08GammaReal a u :=
    p08_gamma_nonneg ha hu (by nlinarith [hvalid, mul_nonneg hb hu])
  have hγb : 0 ≤ p08GammaReal b u :=
    p08_gamma_nonneg hb hu (by nlinarith [hvalid, mul_nonneg ha hu])
  calc
    |δ + ε + δ * ε| ≤ |δ| + |ε| + |δ| * |ε| := by
      calc
        _ ≤ |δ + ε| + |δ * ε| := abs_add_le _ _
        _ ≤ |δ| + |ε| + |δ * ε| := by gcongr; exact abs_add_le _ _
        _ = _ := by rw [abs_mul]
    _ ≤ p08GammaReal a u + p08GammaReal b u *
          (1 + p08GammaReal a u) := by
      nlinarith [mul_le_mul hδ hε (abs_nonneg ε) hγa,
        mul_le_mul hε hδ (abs_nonneg δ) hγb]
    _ ≤ p08GammaReal (a + b) u := p08_gamma_comp hu ha hb hvalid

private noncomputable def p08RoundedDotAux
    (fp : StandardFPModel) (n : ℕ) (a x : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (a i) (x i))) 0

private theorem p08_roundedDot_eq_aux
    (fp : StandardFPModel) (n : ℕ) (a x : Fin n → ℝ) :
    roundedDotProduct fp n a x = p08RoundedDotAux fp n a x := by
  cases n with
  | zero => simp [roundedDotProduct, p08RoundedDotAux]
  | succ n =>
    simp only [roundedDotProduct, p08RoundedDotAux, Fin.foldl_succ]
    rw [fp.fl_add_zero]

private theorem p08_roundedDotAux_succ
    (fp : StandardFPModel) (n : ℕ) (a x : Fin (n + 1) → ℝ) :
    p08RoundedDotAux fp (n + 1) a x =
      fp.fl_add
        (p08RoundedDotAux fp n (a ∘ Fin.castSucc) (x ∘ Fin.castSucc))
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) := by
  simp only [p08RoundedDotAux, Fin.foldl_succ_last]
  rfl

private theorem p08_dot_coeff_error
    (fp : StandardFPModel) (n : ℕ) (a x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ e : Fin n → ℝ,
      (∀ i, |e i| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      p08RoundedDotAux fp n a x =
        ∑ i : Fin n, (a i * x i) * (1 + e i) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i; exact i.elim0
    · simp [p08RoundedDotAux]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a 0) (x 0)
      refine ⟨fun _ => μ, ?_, ?_⟩
      · intro i
        have hu1 : fp.u < 1 := by simpa using hvalid
        simpa using le_trans hμ (p08_gamma_one_ge_u fp.u_nonneg hu1)
      · simp [p08RoundedDotAux, Fin.foldl_succ, fp.fl_add_zero,
          hmul]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
      have hvalidOld : (n : ℝ) * fp.u < 1 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle fp.u_nonneg)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
      obtain ⟨e, he, hsum⟩ := ih (a ∘ Fin.castSucc) (x ∘ Fin.castSucc) hvalidOld
      let old := p08RoundedDotAux fp n (a ∘ Fin.castSucc) (x ∘ Fin.castSucc)
      let y := a (Fin.last n) * x (Fin.last n)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last n)) (x (Fin.last n))
      obtain ⟨η, hη, hadd⟩ := fp.model_add old
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n)))
      have hu1 : fp.u < 1 := by
        have hle1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have hv : ((n : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
        nlinarith [mul_le_mul_of_nonneg_right hle1 fp.u_nonneg]
      have hη : |η| ≤ p08GammaReal 1 fp.u :=
        hη.trans (p08_gamma_one_ge_u fp.u_nonneg hu1)
      have hμ : |μ| ≤ p08GammaReal 1 fp.u :=
        hμ.trans (p08_gamma_one_ge_u fp.u_nonneg hu1)
      let e' : Fin (n + 1) → ℝ :=
        Fin.snoc (fun i => e i + η + e i * η) (μ + η + μ * η)
      refine ⟨e', ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
          have htwo : (2 : ℝ) * fp.u < 1 := by
            have hle2 : (2 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ hn1
            have hv : ((n : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
            nlinarith [mul_le_mul_of_nonneg_right hle2 fp.u_nonneg]
          have hc := p08_gamma_abs_comp fp.u_nonneg
            (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
            (by norm_num at htwo ⊢; exact htwo) hμ hη
          have hc2 : |μ + η + μ * η| ≤ p08GammaReal 2 fp.u := by
            norm_num at hc ⊢
            exact hc
          have hm : p08GammaReal 2 fp.u ≤ p08GammaReal (n + 1 : ℝ) fp.u :=
            p08_gamma_mono (by norm_num)
              (by exact_mod_cast Nat.succ_le_succ hn1) fp.u_nonneg
              (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
          simpa only [e', Fin.snoc_last, Nat.cast_add, Nat.cast_one] using hc2.trans hm
        | cast i =>
          have hc := p08_gamma_abs_comp fp.u_nonneg
            (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
            (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid) (he i) hη
          simpa only [e', Fin.snoc_castSucc, Nat.cast_add, Nat.cast_one] using hc
      · rw [p08_roundedDotAux_succ, hadd]
        change (p08RoundedDotAux fp n (a ∘ Fin.castSucc) (x ∘ Fin.castSucc) +
          fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) * (1 + η) = _
        rw [hmul, hsum]
        simp only [Fin.sum_univ_castSucc, e', Fin.snoc_castSucc,
          Fin.snoc_last, Function.comp_apply]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          ring
        · ring

private theorem p08_rectNorm_eq_frobenius {m n : ℕ}
    (A : P08RectMatrix m n) : p08RectFrobNorm A = ‖A‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

private theorem p08_blockNorm_eq_frobenius {p b : ℕ}
    (A : P08BlockMatrix p b) :
    p08BlockFrobNorm A = ‖p08AssembleMatrix A‖ := by
  rw [p08BlockFrobNorm, Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs,
    Real.sqrt_eq_rpow, p08AssembleMatrix]
  simp only [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

private theorem p08_l2_le {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i, |f i| ≤ k * |g i|) :
    Real.sqrt (∑ i, f i ^ 2) ≤
      k * Real.sqrt (∑ i, g i ^ 2) := by
  have hs : (∑ i, f i ^ 2) ≤ k ^ 2 * (∑ i, g i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hsq := (sq_le_sq₀ (abs_nonneg (f i))
      (mul_nonneg hk (abs_nonneg (g i)))).2 (h i)
    simpa only [sq_abs, mul_pow, mul_assoc] using hsq
  calc
    Real.sqrt (∑ i, f i ^ 2) ≤
        Real.sqrt (k ^ 2 * (∑ i, g i ^ 2)) := Real.sqrt_le_sqrt hs
    _ = k * Real.sqrt (∑ i, g i ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

private theorem p08_roundedRectMatVec_coeff_error
    (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      (∀ i j, |E i j| ≤ p08GammaReal (n : ℝ) fp.u * |A i j|) ∧
      p08RoundedRectMatVec fp A x = Matrix.mulVec (A + E) x := by
  have hrow (i : Fin m) := p08_dot_coeff_error fp n (A i) x hvalid
  choose e he hsum using hrow
  refine ⟨fun i j => A i j * e i j, ?_, ?_⟩
  · intro i j
    rw [abs_mul]
    calc
      |A i j| * |e i j| ≤ |A i j| * p08GammaReal (n : ℝ) fp.u :=
        mul_le_mul_of_nonneg_left (he i j) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · funext i
    change roundedDotProduct fp n (A i) x = _
    rw [p08_roundedDot_eq_aux, hsum i]
    simp only [Matrix.mulVec, Matrix.add_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem p08_rectNorm_le_of_entrywise {m n : ℕ}
    (E A : P08RectMatrix m n) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i j, |E i j| ≤ k * |A i j|) :
    p08RectFrobNorm E ≤ k * p08RectFrobNorm A := by
  have hp := p08_l2_le
    (fun ij : Fin m × Fin n => E ij.1 ij.2)
    (fun ij : Fin m × Fin n => A ij.1 ij.2) hk
    (fun ij => h ij.1 ij.2)
  simpa only [p08RectFrobNorm, Fintype.sum_prod_type] using hp

private theorem p08_roundedRectMatVec_norm_error
    (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      p08RectFrobNorm E ≤
        p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm A ∧
      p08RoundedRectMatVec fp A x = Matrix.mulVec (A + E) x := by
  obtain ⟨E, hentry, heq⟩ :=
    p08_roundedRectMatVec_coeff_error fp A x hvalid
  refine ⟨E, ?_, heq⟩
  apply p08_rectNorm_le_of_entrywise E A
    (p08_gamma_nonneg (Nat.cast_nonneg n) fp.u_nonneg hvalid)
  exact hentry

private theorem p08_orthonormal_transpose_mul {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    Xᵀ * X = 1 := by
  ext j k
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    using hX j k

private theorem p08_orthonormal_sum_sq {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (z : Fin r → ℝ) :
    (∑ i : Fin b, (∑ k : Fin r, X i k * z k) ^ 2) =
      ∑ k : Fin r, z k ^ 2 := by
  have hXtX := p08_orthonormal_transpose_mul X hX
  calc
    (∑ i : Fin b, (∑ k : Fin r, X i k * z k) ^ 2) =
        (X *ᵥ z) ⬝ᵥ (X *ᵥ z) := by
      simp [dotProduct, Matrix.mulVec, pow_two]
    _ = ((X *ᵥ z) ᵥ* X) ⬝ᵥ z := Matrix.dotProduct_mulVec _ _ _
    _ = (z ᵥ* (Xᵀ * X)) ⬝ᵥ z := by rw [Matrix.vecMul_mulVec]
    _ = z ⬝ᵥ z := by rw [hXtX, Matrix.vecMul_one]
    _ = ∑ k : Fin r, z k ^ 2 := by simp [dotProduct, pow_two]

private theorem p08_orthonormal_mul_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (B : P08RectMatrix r n) :
    p08RectFrobNorm (X * B) = p08RectFrobNorm B := by
  unfold p08RectFrobNorm
  congr 1
  calc
    (∑ i : Fin b, ∑ j : Fin n, (X * B) i j ^ 2) =
        ∑ j : Fin n, ∑ i : Fin b,
          (∑ k : Fin r, X i k * B k j) ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply]
    _ = ∑ j : Fin n, ∑ k : Fin r, B k j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact p08_orthonormal_sum_sq X hX (fun k => B k j)
    _ = ∑ k : Fin r, ∑ j : Fin n, B k j ^ 2 := Finset.sum_comm

private theorem p08_orthonormal_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  congr 1
  calc
    (∑ i : Fin b, ∑ j : Fin r, X i j ^ 2) =
        ∑ j : Fin r, ∑ i : Fin b, X i j ^ 2 := Finset.sum_comm
    _ = ∑ j : Fin r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [pow_two, ite_true] using hX j j
    _ = (r : ℝ) := by simp

private theorem p08_rectNorm_add_le {m n : ℕ}
    (A B : P08RectMatrix m n) :
    p08RectFrobNorm (A + B) ≤
      p08RectFrobNorm A + p08RectFrobNorm B := by
  simp only [p08_rectNorm_eq_frobenius]
  exact norm_add_le A B

private theorem p08_rectNorm_mul_le {m n q : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n q) :
    p08RectFrobNorm (A * B) ≤
      p08RectFrobNorm A * p08RectFrobNorm B := by
  simp only [p08_rectNorm_eq_frobenius]
  exact Matrix.frobenius_norm_mul A B

private theorem p08_rectNorm_transpose {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm Aᵀ = p08RectFrobNorm A := by
  simp only [p08_rectNorm_eq_frobenius]
  exact Matrix.frobenius_norm_transpose A

private theorem p08_rectNorm_nonneg {m n : ℕ}
    (A : P08RectMatrix m n) : 0 ≤ p08RectFrobNorm A := by
  rw [p08_rectNorm_eq_frobenius]
  exact norm_nonneg _

private theorem p08_rank_le_rank_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => simp
  | succ r =>
    have hr : (1 : ℝ) ≤ (↑(r + 1) : ℝ) := by exact_mod_cast Nat.zero_lt_succ r
    have hs : (1 : ℝ) ≤ Real.sqrt (↑(r + 1) : ℝ) := Real.one_le_sqrt.mpr hr
    have hr0 : (0 : ℝ) ≤ (↑(r + 1) : ℝ) := by positivity
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs)]

private theorem p08_gamma_rank_sqrt_le
    (r : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  let q := (r : ℝ) * Real.sqrt (r : ℝ)
  have hrq : (r : ℝ) ≤ q := p08_rank_le_rank_sqrt r
  have hq0 : 0 ≤ q := le_trans (Nat.cast_nonneg r) hrq
  have hru : (r : ℝ) * u ≤ q * u := mul_le_mul_of_nonneg_right hrq hu
  have hv : q * u < 1 := hvalid
  have hdenr : 0 < 1 - (r : ℝ) * u := by linarith
  have hdenq : 0 < 1 - q * u := by linarith
  unfold p08GammaReal
  have heq : (↑r * u / (1 - ↑r * u)) * Real.sqrt (↑r) =
      q * u / (1 - ↑r * u) := by
    dsimp [q]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hdenr hdenq).2
  have hnum : 0 ≤ q * u := mul_nonneg hq0 hu
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hru)]

private theorem p08_lowrank_norm_eq {b r : ℕ}
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  change p08RectFrobNorm (X * Yᵀ) = _
  rw [p08_orthonormal_mul_norm X hX Yᵀ, p08_rectNorm_transpose]

private theorem p08_lowrank_combine_errors
    {b r : ℕ} (u : ℝ) (hu : 0 ≤ u)
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (E₁ : P08RectMatrix r b) (E₂ : P08RectMatrix b r)
    (hE₁ : p08RectFrobNorm E₁ ≤
      p08GammaReal (b : ℝ) u * p08RectFrobNorm Y)
    (hE₂ : p08RectFrobNorm E₂ ≤
      p08GammaReal (r : ℝ) u * p08RectFrobNorm X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    ∃ F : P08Matrix b,
      (X + E₂) * (Yᵀ + E₁) = p08LowRankMatrix X Y + F ∧
      p08RectFrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) u *
          p08RectFrobNorm (p08LowRankMatrix X Y) := by
  let q := (r : ℝ) * Real.sqrt (r : ℝ)
  let gb := p08GammaReal (b : ℝ) u
  let gq := p08GammaReal q u
  let A := p08RectFrobNorm Y
  let B := p08RectFrobNorm E₁
  let C := p08RectFrobNorm E₂
  have hq0 : 0 ≤ q := le_trans (Nat.cast_nonneg r) (p08_rank_le_rank_sqrt r)
  have hvalidq : q * u < 1 := by
    have hb0 : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg b) hu
    change ((b : ℝ) + q) * u < 1 at hvalid
    nlinarith
  have hvalidb : (b : ℝ) * u < 1 := by
    have hqu : 0 ≤ q * u := mul_nonneg hq0 hu
    change ((b : ℝ) + q) * u < 1 at hvalid
    nlinarith
  have hgb : 0 ≤ gb := p08_gamma_nonneg (Nat.cast_nonneg b) hu hvalidb
  have hgq : 0 ≤ gq := p08_gamma_nonneg hq0 hu hvalidq
  have hA : 0 ≤ A := p08_rectNorm_nonneg Y
  have hB : 0 ≤ B := p08_rectNorm_nonneg E₁
  have hC : 0 ≤ C := p08_rectNorm_nonneg E₂
  have hE₂q : C ≤ gq := by
    calc
      C ≤ p08GammaReal (r : ℝ) u * p08RectFrobNorm X := hE₂
      _ = p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) := by
        rw [p08_orthonormal_norm X hX]
      _ ≤ gq := p08_gamma_rank_sqrt_le r hu hvalidq
  let F : P08Matrix b := X * E₁ + E₂ * Yᵀ + E₂ * E₁
  refine ⟨F, ?_, ?_⟩
  · change (X + E₂) * (Yᵀ + E₁) = X * Yᵀ + F
    dsimp [F]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  · have hnorm₁ : p08RectFrobNorm (X * E₁) = B :=
      p08_orthonormal_mul_norm X hX E₁
    have hnorm₂ : p08RectFrobNorm (E₂ * Yᵀ) ≤ C * A := by
      simpa only [C, A, p08_rectNorm_transpose] using
        p08_rectNorm_mul_le E₂ Yᵀ
    have hnorm₃ : p08RectFrobNorm (E₂ * E₁) ≤ C * B :=
      p08_rectNorm_mul_le E₂ E₁
    have hF : p08RectFrobNorm F ≤ B + C * A + C * B := by
      calc
        p08RectFrobNorm F ≤
            p08RectFrobNorm (X * E₁ + E₂ * Yᵀ) +
              p08RectFrobNorm (E₂ * E₁) := p08_rectNorm_add_le _ _
        _ ≤ p08RectFrobNorm (X * E₁) +
              p08RectFrobNorm (E₂ * Yᵀ) +
              p08RectFrobNorm (E₂ * E₁) := by
          linarith [p08_rectNorm_add_le (X * E₁) (E₂ * Yᵀ)]
        _ ≤ B + C * A + C * B := by linarith
    have hCA : C * A ≤ gq * A := mul_le_mul_of_nonneg_right hE₂q hA
    have hCB : C * B ≤ gq * (gb * A) := by
      calc
        C * B ≤ gq * B := mul_le_mul_of_nonneg_right hE₂q hB
        _ ≤ gq * (gb * A) := mul_le_mul_of_nonneg_left hE₁ hgq
    have hcomp : gb + gq * (1 + gb) ≤
        p08GammaReal ((b : ℝ) + q) u := by
      exact p08_gamma_comp hu (Nat.cast_nonneg b) hq0 hvalid
    rw [p08_lowrank_norm_eq X Y hX]
    change p08RectFrobNorm F ≤
      p08GammaReal ((b : ℝ) + q) u * A
    calc
      p08RectFrobNorm F ≤ B + C * A + C * B := hF
      _ ≤ gb * A + gq * A + gq * (gb * A) := by linarith [hE₁, hCA, hCB]
      _ = (gb + gq * (1 + gb)) * A := by ring
      _ ≤ p08GammaReal ((b : ℝ) + q) u * A :=
        mul_le_mul_of_nonneg_right hcomp hA

private theorem p08_lowrank_matvec_error
    (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (x : Fin b → ℝ)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      p08RectFrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08RectFrobNorm (p08LowRankMatrix X Y) ∧
      p08RoundedLowRankMatVec fp X Y x =
        Matrix.mulVec (p08LowRankMatrix X Y + F) x := by
  let q := (r : ℝ) * Real.sqrt (r : ℝ)
  have hq0 : 0 ≤ q := le_trans (Nat.cast_nonneg r) (p08_rank_le_rank_sqrt r)
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have hqu : 0 ≤ q * fp.u := mul_nonneg hq0 fp.u_nonneg
    change ((b : ℝ) + q) * fp.u < 1 at hvalid
    nlinarith
  have hrvalid : (r : ℝ) * fp.u < 1 := by
    have hrq : (r : ℝ) ≤ q := p08_rank_le_rank_sqrt r
    have hru : (r : ℝ) * fp.u ≤ q * fp.u :=
      mul_le_mul_of_nonneg_right hrq fp.u_nonneg
    have hbu : 0 ≤ (b : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg b) fp.u_nonneg
    change ((b : ℝ) + q) * fp.u < 1 at hvalid
    nlinarith
  let z := p08RoundedRectMatVec fp (p08RectTranspose Y) x
  obtain ⟨E₁, hE₁, hz⟩ :=
    p08_roundedRectMatVec_norm_error fp (p08RectTranspose Y) x hbvalid
  obtain ⟨E₂, hE₂, hout⟩ :=
    p08_roundedRectMatVec_norm_error fp X z hrvalid
  have hE₁' : p08RectFrobNorm E₁ ≤
      p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm Y := by
    change p08RectFrobNorm E₁ ≤
      p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm Yᵀ at hE₁
    rwa [p08_rectNorm_transpose] at hE₁
  obtain ⟨F, hcombine, hF⟩ :=
    p08_lowrank_combine_errors fp.u fp.u_nonneg X Y hX E₁ E₂ hE₁' hE₂ hvalid
  refine ⟨F, hF, ?_⟩
  calc
    p08RoundedLowRankMatVec fp X Y x =
        Matrix.mulVec (X + E₂) z := hout
    _ = Matrix.mulVec (X + E₂) (Matrix.mulVec (Yᵀ + E₁) x) := by
      dsimp [z]
      rw [hz]
      rfl
    _ = Matrix.mulVec ((X + E₂) * (Yᵀ + E₁)) x := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (p08LowRankMatrix X Y + F) x := by rw [hcombine]

private noncomputable def p08ForwardRow
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n)
    (b : Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  let s := Fin.foldl i.val
    (fun acc (t : Fin i.val) =>
      let j : Fin n := ⟨t.val, by omega⟩
      fp.fl_sub acc (fp.fl_mul (L i j) (x j)))
    (b i)
  fp.fl_div s (L i i)

private theorem p08_forwardRow_congr
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n)
    (b : Fin n → ℝ) (x y : Fin n → ℝ) (i : Fin n)
    (h : ∀ j : Fin n, j < i → x j = y j) :
    p08ForwardRow fp n L b x i = p08ForwardRow fp n L b y i := by
  dsimp only [p08ForwardRow]
  congr 1
  apply congrArg (fun f : ℝ → Fin i.val → ℝ => Fin.foldl i.val f (b i))
  funext acc t
  have hj : (⟨t.val, by omega⟩ : Fin n) < i := t.isLt
  rw [h _ hj]

private theorem p08_forward_steps_spec
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n) (b : Fin n → ℝ) :
    ∀ k : ℕ, ∀ hk : k ≤ n, ∀ x : Fin n → ℝ,
      let y := roundedForwardSubSteps fp n L b k hk x
      (∀ i : Fin n, i.val < n - k → y i = x i) ∧
      (∀ i : Fin n, n - k ≤ i.val → y i = p08ForwardRow fp n L b y i) := by
  intro k
  induction k with
  | zero =>
    intro hk x
    constructor
    · intro i _
      rfl
    · intro i hi
      have := i.isLt
      omega
  | succ k ih =>
    intro hk x
    let ik : Fin n := ⟨n - k - 1, by omega⟩
    let x' : Fin n → ℝ := Function.update x ik (p08ForwardRow fp n L b x ik)
    let hk' : k ≤ n := Nat.le_of_succ_le hk
    let y := roundedForwardSubSteps fp n L b k hk' x'
    have hstep : roundedForwardSubSteps fp n L b (k + 1) hk x = y := by
      dsimp only [roundedForwardSubSteps, y, x', p08ForwardRow, ik]
    obtain ⟨hpre, hrow⟩ := ih hk' x'
    change (∀ i : Fin n, i.val < n - (k + 1) →
        roundedForwardSubSteps fp n L b (k + 1) hk x i = x i) ∧
      (∀ i : Fin n, n - (k + 1) ≤ i.val →
        roundedForwardSubSteps fp n L b (k + 1) hk x i =
          p08ForwardRow fp n L b
            (roundedForwardSubSteps fp n L b (k + 1) hk x) i)
    rw [hstep]
    constructor
    · intro i hi
      have hipre : i.val < n - k := by omega
      have hine : i ≠ ik := by
        intro heq
        have : i.val = ik.val := congrArg Fin.val heq
        dsimp [ik] at this
        omega
      calc
        y i = x' i := hpre i hipre
        _ = x i := Function.update_of_ne hine _ _
    · intro i hi
      by_cases hieq : i = ik
      · subst i
        have hikpre : ik.val < n - k := by dsimp [ik]; omega
        have hprefix : ∀ j : Fin n, j < ik → x j = y j := by
          intro j hj
          have hjpre : j.val < n - k := by dsimp [ik] at hj; omega
          have hjne : j ≠ ik := ne_of_lt hj
          calc
            x j = x' j := (Function.update_of_ne hjne _ _).symm
            _ = y j := (hpre j hjpre).symm
        calc
          y ik = x' ik := hpre ik hikpre
          _ = p08ForwardRow fp n L b x ik := Function.update_self ..
          _ = p08ForwardRow fp n L b y ik :=
            p08_forwardRow_congr fp n L b x y ik hprefix
      · have hig : n - k ≤ i.val := by
          have hne : i.val ≠ n - k - 1 := by
            intro heq
            apply hieq
            apply Fin.ext
            simpa [ik] using heq
          omega
        exact hrow i hig

private theorem p08_roundedForwardSub_row
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n)
    (b : Fin n → ℝ) (i : Fin n) :
    roundedForwardSub fp n L b i =
      p08ForwardRow fp n L b (roundedForwardSub fp n L b) i := by
  obtain ⟨_, hrow⟩ :=
    p08_forward_steps_spec fp n L b n (le_refl n) (fun _ => 0)
  have hi : n - n ≤ i.val := by omega
  exact hrow i hi

private theorem p08_inv_one_add_error
    {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hδ : |δ| ≤ u) :
    |(1 + δ)⁻¹ - 1| ≤ p08GammaReal 1 u := by
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1
  have hδhi : δ ≤ u := (abs_le.mp hδ).2
  have hden : 0 < 1 + δ := by linarith
  have hden1 : 0 < 1 - u := by linarith
  have heq : (1 + δ)⁻¹ - 1 = -δ / (1 + δ) := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hden]
  unfold p08GammaReal
  simp only [one_mul]
  apply (div_le_div_iff₀ hden hden1).2
  by_cases hd : 0 ≤ δ
  · rw [abs_of_nonneg hd]
    nlinarith [mul_nonneg hu hd]
  · rw [abs_of_neg (lt_of_not_ge hd)]
    nlinarith

private noncomputable def p08SubMulFold
    (fp : StandardFPModel) (n : ℕ) (v : ℝ)
    (a x : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) v

private theorem p08_subMulFold_succ
    (fp : StandardFPModel) (n : ℕ) (v : ℝ)
    (a x : Fin (n + 1) → ℝ) :
    p08SubMulFold fp (n + 1) v a x =
      fp.fl_sub
        (p08SubMulFold fp n v (a ∘ Fin.castSucc) (x ∘ Fin.castSucc))
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) := by
  simp only [p08SubMulFold, Fin.foldl_succ_last]
  rfl

private theorem p08_subMulFold_back_error
    (fp : StandardFPModel) (n : ℕ) (v : ℝ)
    (a x : Fin n → ℝ) (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ θ : ℝ, ∃ e : Fin n → ℝ,
      |θ| ≤ p08GammaReal (n : ℝ) fp.u ∧
      (∀ j, |e j| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      v = p08SubMulFold fp n v a x * (1 + θ) +
        ∑ j : Fin n, (a j * x j) * (1 + e j) := by
  induction n generalizing v with
  | zero =>
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp [p08GammaReal]
    · intro j; exact j.elim0
    · simp [p08SubMulFold]
  | succ n ih =>
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
    have hvalidOld : (n : ℝ) * fp.u < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle fp.u_nonneg)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
    obtain ⟨θ, e, hθ, he, heq⟩ :=
      ih v (a ∘ Fin.castSucc) (x ∘ Fin.castSucc) hvalidOld
    let old := p08SubMulFold fp n v (a ∘ Fin.castSucc) (x ∘ Fin.castSucc)
    let new := p08SubMulFold fp (n + 1) v a x
    let w := a (Fin.last n) * x (Fin.last n)
    obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last n)) (x (Fin.last n))
    obtain ⟨δ, hδ, hsub⟩ := fp.model_sub old
      (fp.fl_mul (a (Fin.last n)) (x (Fin.last n)))
    have hu1 : fp.u < 1 := by
      have hle1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hv : ((n : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
      nlinarith [mul_le_mul_of_nonneg_right hle1 fp.u_nonneg]
    let ε := (1 + δ)⁻¹ - 1
    have hε : |ε| ≤ p08GammaReal 1 fp.u :=
      p08_inv_one_add_error fp.u_nonneg hu1 hδ
    have hμ' : |μ| ≤ p08GammaReal 1 fp.u :=
      hμ.trans (p08_gamma_one_ge_u fp.u_nonneg hu1)
    have hback : old = new * (1 + ε) + w * (1 + μ) := by
      dsimp only [new]
      rw [p08_subMulFold_succ]
      change old = fp.fl_sub old (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) *
        (1 + ε) + w * (1 + μ)
      rw [hsub, hmul]
      have hnz : 1 + δ ≠ 0 := by
        have hδlo := (abs_le.mp hδ).1
        have : 0 < 1 + δ := by linarith
        exact ne_of_gt this
      dsimp [ε]
      field_simp [hnz]
      ring
    let e' : Fin (n + 1) → ℝ := Fin.snoc e (μ + θ + μ * θ)
    refine ⟨θ + ε + θ * ε, e', ?_, ?_, ?_⟩
    · have hc := p08_gamma_abs_comp fp.u_nonneg
        (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid) hθ hε
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    · intro j
      induction j using Fin.lastCases with
      | last =>
        have hv : (1 + (n : ℝ)) * fp.u < 1 := by
          simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℝ) 1] using hvalid
        have hc := p08_gamma_abs_comp fp.u_nonneg
          (show (0 : ℝ) ≤ 1 by norm_num) (Nat.cast_nonneg n)
          hv
          hμ' hθ
        simpa only [e', Fin.snoc_last, Nat.cast_add, Nat.cast_one,
          add_comm (1 : ℝ) (n : ℝ)] using hc
      | cast j =>
        have hm := p08_gamma_mono (Nat.cast_nonneg n) hle fp.u_nonneg
          (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
        simpa only [e', Fin.snoc_castSucc, Nat.cast_add, Nat.cast_one] using
          (he j).trans hm
    · change v = new * (1 + (θ + ε + θ * ε)) +
        ∑ j : Fin (n + 1), (a j * x j) * (1 + e' j)
      calc
        v = old * (1 + θ) +
            ∑ j : Fin n,
              ((a ∘ Fin.castSucc) j * (x ∘ Fin.castSucc) j) * (1 + e j) := heq
        _ = (new * (1 + ε) + w * (1 + μ)) * (1 + θ) +
            ∑ j : Fin n, (a j.castSucc * x j.castSucc) * (1 + e j) := by
          rw [hback]
          rfl
        _ = new * (1 + (θ + ε + θ * ε)) +
            (∑ j : Fin n, (a j.castSucc * x j.castSucc) * (1 + e j)) +
            w * (1 + (μ + θ + μ * θ)) := by ring
        _ = new * (1 + (θ + ε + θ * ε)) +
            ∑ j : Fin (n + 1), (a j * x j) * (1 + e' j) := by
          rw [Fin.sum_univ_castSucc]
          simp only [e', Fin.snoc_castSucc, Fin.snoc_last]
          ring

private theorem p08_sum_lower_diag {n : ℕ} (i : Fin n)
    (f : Fin n → ℝ) (hupper : ∀ j : Fin n, i < j → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  let F : ℕ → ℝ := fun k => if h : k < n then f ⟨k, h⟩ else 0
  have hfull : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := by
    rw [← Fin.sum_univ_eq_sum_range F n]
    apply Finset.sum_congr rfl
    intro j _
    simp [F, j.isLt]
  have hbefore : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
      ∑ k ∈ Finset.range i.val, F k := by
    rw [← Fin.sum_univ_eq_sum_range F i.val]
    apply Finset.sum_congr rfl
    intro t _
    have ht : t.val < n := by omega
    simp [F, ht]
  have htail : (∑ k ∈ Finset.range (n - (i.val + 1)), F (i.val + 1 + k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < n - (i.val + 1) := Finset.mem_range.mp hk
    have hkn : i.val + 1 + k < n := by omega
    have hgt : i < (⟨i.val + 1 + k, hkn⟩ : Fin n) := by exact_mod_cast (by omega : i.val < i.val + 1 + k)
    simpa [F, hkn] using hupper ⟨i.val + 1 + k, hkn⟩ hgt
  calc
    (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := hfull
    _ = ∑ k ∈ Finset.range ((i.val + 1) + (n - (i.val + 1))), F k := by
      congr 2
      omega
    _ = (∑ k ∈ Finset.range (i.val + 1), F k) +
          ∑ k ∈ Finset.range (n - (i.val + 1)), F (i.val + 1 + k) :=
      Finset.sum_range_add F (i.val + 1) (n - (i.val + 1))
    _ = (∑ k ∈ Finset.range i.val, F k) + F i.val := by
      rw [Finset.sum_range_succ, htail]
      ring
    _ = (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
      rw [← hbefore]
      simp [F, i.isLt]

private theorem p08_forward_row_error
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n)
    (b : Fin n → ℝ) (i : Fin n)
    (hdiag : L i i ≠ 0) (hlower : p08LowerTriangular L)
    (hvalid : (n : ℝ) * fp.u < 1) :
    let x := roundedForwardSub fp n L b
    ∃ E : Fin n → ℝ,
      (∀ j, |E j| ≤ p08GammaReal (n : ℝ) fp.u * |L i j|) ∧
      (∑ j : Fin n, (L i j + E j) * x j) = b i := by
  let x := roundedForwardSub fp n L b
  let a : Fin i.val → ℝ := fun t => L i ⟨t.val, by omega⟩
  let xx : Fin i.val → ℝ := fun t => x ⟨t.val, by omega⟩
  let s := p08SubMulFold fp i.val (b i) a xx
  have hi1 : (i.val + 1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast i.isLt
  have hi0 : (i.val : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_lt i.isLt
  have hvalid1 : (i.val + 1 : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hi1 fp.u_nonneg) hvalid
  have hvalid0 : (i.val : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hi0 fp.u_nonneg) hvalid
  obtain ⟨θ, e, hθ, he, hback⟩ :=
    p08_subMulFold_back_error fp i.val (b i) a xx hvalid0
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (L i i) hdiag
  have hu1 : fp.u < 1 := by
    have hle1 : (1 : ℝ) ≤ (i.val + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
    nlinarith [mul_le_mul_of_nonneg_right hle1 fp.u_nonneg, hvalid1]
  let ε := (1 + δ)⁻¹ - 1
  let χ := θ + ε + θ * ε
  have hε : |ε| ≤ p08GammaReal 1 fp.u :=
    p08_inv_one_add_error fp.u_nonneg hu1 hδ
  have hχ1 : |χ| ≤ p08GammaReal (i.val + 1 : ℝ) fp.u := by
    have hc := p08_gamma_abs_comp fp.u_nonneg
      (Nat.cast_nonneg i.val) (show (0 : ℝ) ≤ 1 by norm_num)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid1) hθ hε
    simpa only [χ, Nat.cast_add, Nat.cast_one] using hc
  have hχ : |χ| ≤ p08GammaReal (n : ℝ) fp.u :=
    hχ1.trans (p08_gamma_mono (by positivity) hi1 fp.u_nonneg hvalid)
  have he' (t : Fin i.val) : |e t| ≤ p08GammaReal (n : ℝ) fp.u :=
    (he t).trans (p08_gamma_mono (by positivity) hi0 fp.u_nonneg hvalid)
  have hrow := p08_roundedForwardSub_row fp n L b i
  have hx : x i = fp.fl_div s (L i i) := by
    change x i = p08ForwardRow fp n L b x i at hrow
    convert hrow using 1
  have hden : 1 + δ ≠ 0 := by
    have hδlo := (abs_le.mp hδ).1
    exact ne_of_gt (by linarith : 0 < 1 + δ)
  have hbase : L i i * x i * (1 + ε) = s := by
    rw [hx, hdiv]
    dsimp [ε]
    field_simp [hdiag, hden]
    ring
  have hdiagEq : L i i * x i * (1 + χ) = s * (1 + θ) := by
    calc
      L i i * x i * (1 + χ) =
          (L i i * x i * (1 + ε)) * (1 + θ) := by dsimp [χ]; ring
      _ = s * (1 + θ) := by rw [hbase]
  let E : Fin n → ℝ := fun j =>
    if h : j.val < i.val then L i j * e ⟨j.val, h⟩
    else if j = i then L i j * χ else 0
  refine ⟨E, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < i.val
    · simp only [E, dif_pos hj, abs_mul]
      calc
        |L i j| * |e ⟨j.val, hj⟩| ≤
            |L i j| * p08GammaReal (n : ℝ) fp.u :=
          mul_le_mul_of_nonneg_left (he' ⟨j.val, hj⟩) (abs_nonneg _)
        _ = _ := mul_comm _ _
    · by_cases hji : j = i
      · subst j
        simp only [E, dif_neg (by omega : ¬i.val < i.val)]
        simp only [ite_true, abs_mul]
        calc
          |L i i| * |χ| ≤ |L i i| * p08GammaReal (n : ℝ) fp.u :=
            mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
          _ = _ := mul_comm _ _
      · simp only [E, dif_neg hj, if_neg hji, abs_zero]
        exact mul_nonneg
          (p08_gamma_nonneg (Nat.cast_nonneg n) fp.u_nonneg hvalid) (abs_nonneg _)
  · have hsum := p08_sum_lower_diag i
        (fun j => (L i j + E j) * x j) (by
          intro j hij
          have hL : L i j = 0 := hlower i j hij
          have hji : j ≠ i := ne_of_gt hij
          simp [E, hL, hji])
    have hlow : (∑ t : Fin i.val,
        (L i ⟨t.val, by omega⟩ + E ⟨t.val, by omega⟩) *
          x ⟨t.val, by omega⟩) =
        ∑ t : Fin i.val, (a t * xx t) * (1 + e t) := by
      apply Finset.sum_congr rfl
      intro t _
      have ht : t.val < i.val := t.isLt
      simp only [E, dif_pos ht]
      dsimp [a, xx]
      ring
    have hdiag' : (L i i + E i) * x i = L i i * x i * (1 + χ) := by
      simp [E, χ]
      ring
    rw [hsum, hlow]
    change (∑ t : Fin i.val, (a t * xx t) * (1 + e t)) +
      (L i i + E i) * x i = b i
    rw [hdiag']
    have hb : b i = s * (1 + θ) +
        ∑ t : Fin i.val, (a t * xx t) * (1 + e t) := hback
    rw [← hdiagEq] at hb
    linarith

private theorem p08_forward_backward_error
    (fp : StandardFPModel) (n : ℕ) (L : P08Matrix n)
    (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hlower : p08LowerTriangular L)
    (hvalid : (n : ℝ) * fp.u < 1) :
    let x := roundedForwardSub fp n L b
    ∃ F : P08Matrix n,
      p08RectFrobNorm F ≤
        p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm L ∧
      Matrix.mulVec (L + F) x = b := by
  have hrow (i : Fin n) :=
    p08_forward_row_error fp n L b i (hdiag i) hlower hvalid
  choose E hE heq using hrow
  let F : P08Matrix n := fun i j => E i j
  refine ⟨F, ?_, ?_⟩
  · exact p08_rectNorm_le_of_entrywise F L
      (p08_gamma_nonneg (Nat.cast_nonneg n) fp.u_nonneg hvalid) hE
  · funext i
    change (∑ j : Fin n, (L i j + F i j) *
      roundedForwardSub fp n L b j) = b i
    exact heq i

private noncomputable def p08SubFold
    (fp : StandardFPModel) (n : ℕ) (v : ℝ) (w : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc j => fp.fl_sub acc (w j)) v

private theorem p08_subFold_succ
    (fp : StandardFPModel) (n : ℕ) (v : ℝ) (w : Fin (n + 1) → ℝ) :
    p08SubFold fp (n + 1) v w =
      fp.fl_sub (p08SubFold fp n v (w ∘ Fin.castSucc)) (w (Fin.last n)) := by
  simp only [p08SubFold, Fin.foldl_succ_last]
  rfl

private theorem p08_subFold_forward_error
    (fp : StandardFPModel) (n : ℕ) (v : ℝ) (w : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ θ : ℝ, ∃ e : Fin n → ℝ,
      |θ| ≤ p08GammaReal (n : ℝ) fp.u ∧
      (∀ j, |e j| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      p08SubFold fp n v w =
        v * (1 + θ) - ∑ j : Fin n, w j * (1 + e j) := by
  induction n with
  | zero =>
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp [p08GammaReal]
    · intro j; exact j.elim0
    · simp [p08SubFold]
  | succ n ih =>
    have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
    have hvalidOld : (n : ℝ) * fp.u < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle fp.u_nonneg)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
    obtain ⟨θ, e, hθ, he, heq⟩ :=
      ih (w ∘ Fin.castSucc) hvalidOld
    let old := p08SubFold fp n v (w ∘ Fin.castSucc)
    obtain ⟨δ, hδ, hsub⟩ := fp.model_sub old (w (Fin.last n))
    have hu1 : fp.u < 1 := by
      have hle1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hv : ((n : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
      nlinarith [mul_le_mul_of_nonneg_right hle1 fp.u_nonneg]
    have hδ' : |δ| ≤ p08GammaReal 1 fp.u :=
      hδ.trans (p08_gamma_one_ge_u fp.u_nonneg hu1)
    let e' : Fin (n + 1) → ℝ :=
      Fin.snoc (fun j => e j + δ + e j * δ) δ
    refine ⟨θ + δ + θ * δ, e', ?_, ?_, ?_⟩
    · have hc := p08_gamma_abs_comp fp.u_nonneg
        (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid) hθ hδ'
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    · intro j
      induction j using Fin.lastCases with
      | last =>
        have hm := p08_gamma_mono (by norm_num : (0 : ℝ) ≤ 1)
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n) :
            (1 : ℝ) ≤ (n + 1 : ℝ)) fp.u_nonneg
          (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid)
        simpa only [e', Fin.snoc_last, Nat.cast_add, Nat.cast_one] using
          hδ'.trans hm
      | cast j =>
        have hc := p08_gamma_abs_comp fp.u_nonneg
          (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hvalid) (he j) hδ'
        simpa only [e', Fin.snoc_castSucc, Nat.cast_add, Nat.cast_one] using hc
    · rw [p08_subFold_succ, hsub]
      change old = v * (1 + θ) -
        ∑ j : Fin n, (w ∘ Fin.castSucc) j * (1 + e j) at heq
      rw [heq]
      simp only [Fin.sum_univ_castSucc, e', Fin.snoc_castSucc, Fin.snoc_last,
        Function.comp_apply]
      have hs : (∑ j : Fin n, w j.castSucc * (1 + e j)) * (1 + δ) =
          ∑ j : Fin n, w j.castSucc * (1 + (e j + δ + e j * δ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [← hs]
      ring

private theorem p08_vector_subFold_component
    (fp : StandardFPModel) (n b : ℕ)
    (v : Fin b → ℝ) (w : Fin n → Fin b → ℝ) (α : Fin b) :
    (Fin.foldl n (fun acc j => fun β => fp.fl_sub (acc β) (w j β)) v) α =
      p08SubFold fp n (v α) (fun j => w j α) := by
  induction n with
  | zero => simp [p08SubFold]
  | succ n ih =>
    rw [Fin.foldl_succ_last, p08_subFold_succ]
    change fp.fl_sub
      ((Fin.foldl n
        (fun acc j => fun β => fp.fl_sub (acc β) (w j.castSucc β)) v) α)
      (w (Fin.last n) α) =
      fp.fl_sub (p08SubFold fp n (v α) (fun j => w j.castSucc α))
        (w (Fin.last n) α)
    simpa only [Function.comp_apply] using
      congrArg (fun t => fp.fl_sub t (w (Fin.last n) α))
        (ih (w ∘ Fin.castSucc))

private theorem p08_scaled_matrix_error
    {b : ℕ} (u a q : ℝ) (hu : 0 ≤ u) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hvalid : (a + q) * u < 1)
    (T F : P08Matrix b) (θ : Fin b → ℝ)
    (hF : p08RectFrobNorm F ≤
      p08GammaReal a u * p08RectFrobNorm T)
    (hθ : ∀ α, |θ α| ≤ p08GammaReal q u) :
    p08RectFrobNorm
        (fun α β => θ α * T α β + (1 + θ α) * F α β) ≤
      p08GammaReal (a + q) u * p08RectFrobNorm T := by
  let ga := p08GammaReal a u
  let gq := p08GammaReal q u
  have hga : 0 ≤ ga := p08_gamma_nonneg ha hu (by
    have hqu := mul_nonneg hq hu
    nlinarith [hvalid])
  have hgq : 0 ≤ gq := p08_gamma_nonneg hq hu (by
    have hau := mul_nonneg ha hu
    nlinarith [hvalid])
  have hT : 0 ≤ p08RectFrobNorm T := p08_rectNorm_nonneg T
  have hFn : 0 ≤ p08RectFrobNorm F := p08_rectNorm_nonneg F
  let A : P08Matrix b := fun α β => θ α * T α β
  let B : P08Matrix b := fun α β => (1 + θ α) * F α β
  have hA : p08RectFrobNorm A ≤ gq * p08RectFrobNorm T := by
    apply p08_rectNorm_le_of_entrywise A T hgq
    intro α β
    simp only [A, abs_mul]
    exact mul_le_mul_of_nonneg_right (hθ α) (abs_nonneg _)
  have hB : p08RectFrobNorm B ≤ (1 + gq) * p08RectFrobNorm F := by
    apply p08_rectNorm_le_of_entrywise B F (by linarith)
    intro α β
    simp only [B, abs_mul]
    have hh : |1 + θ α| ≤ 1 + gq := by
      calc
        |1 + θ α| ≤ |(1 : ℝ)| + |θ α| := abs_add_le _ _
        _ ≤ 1 + gq := by simpa using add_le_add_left (hθ α) 1
    exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)
  have hcomp : ga + gq * (1 + ga) ≤ p08GammaReal (a + q) u := by
    exact p08_gamma_comp hu ha hq hvalid
  have hresult : p08RectFrobNorm (A + B) ≤
      p08GammaReal (a + q) u * p08RectFrobNorm T := by
    calc
      p08RectFrobNorm (A + B) ≤ p08RectFrobNorm A + p08RectFrobNorm B :=
        p08_rectNorm_add_le A B
      _ ≤ gq * p08RectFrobNorm T + (1 + gq) * p08RectFrobNorm F := by
        linarith
      _ ≤ (ga + gq * (1 + ga)) * p08RectFrobNorm T := by
        have hm := mul_le_mul_of_nonneg_left hF (by linarith : 0 ≤ 1 + gq)
        nlinarith
      _ ≤ p08GammaReal (a + q) u * p08RectFrobNorm T :=
        mul_le_mul_of_nonneg_right hcomp hT
  exact hresult

private theorem p08_blockNorm_eq_sqrt_blocks {p b : ℕ}
    (T : P08BlockMatrix p b) :
    p08BlockFrobNorm T =
      Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
        p08RectFrobNorm (T i j) ^ 2) := by
  unfold p08BlockFrobNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) =
    (Real.sqrt (∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2)) ^ 2
  rw [Real.sq_sqrt (by positivity)]

private theorem p08_blockNorm_le_of_blocks {p b : ℕ}
    (D T : P08BlockMatrix p b) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i j, p08RectFrobNorm (D i j) ≤ k * p08RectFrobNorm (T i j)) :
    p08BlockFrobNorm D ≤ k * p08BlockFrobNorm T := by
  rw [p08_blockNorm_eq_sqrt_blocks D, p08_blockNorm_eq_sqrt_blocks T]
  have hp := p08_l2_le
    (fun ij : Fin p × Fin p => p08RectFrobNorm (D ij.1 ij.2))
    (fun ij : Fin p × Fin p => p08RectFrobNorm (T ij.1 ij.2)) hk
    (fun ij => by
      simpa only [abs_of_nonneg (p08_rectNorm_nonneg _)] using h ij.1 ij.2)
  simpa only [Fintype.sum_prod_type] using hp

private theorem p08_blockVecNorm_le_of_entrywise {p b : ℕ}
    (d v : P08BlockVector p b) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i α, |d i α| ≤ k * |v i α|) :
    p08BlockVecNorm d ≤ k * p08BlockVecNorm v := by
  have hp := p08_l2_le
    (fun iα : Fin p × Fin b => d iα.1 iα.2)
    (fun iα : Fin p × Fin b => v iα.1 iα.2) hk
    (fun iα => h iα.1 iα.2)
  simpa only [p08BlockVecNorm, Fintype.sum_prod_type] using hp

private theorem p08_trace_rhs_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (i : Fin p) (hvalid : (p : ℝ) * fp.u < 1) :
    let w : Fin i.val → Fin b → ℝ := fun j =>
      let j' : Fin p := ⟨j.val, by omega⟩
      p08RoundedLowRankMatVec fp (X i j') (Y i j') (trace.x j')
    ∃ θv : Fin b → ℝ, ∃ θw : Fin i.val → Fin b → ℝ,
      (∀ α, |θv α| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      (∀ j α, |θw j α| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      (∀ α, trace.rhs i α =
        v i α * (1 + θv α) -
          ∑ j : Fin i.val, w j α * (1 + θw j α)) := by
  let w : Fin i.val → Fin b → ℝ := fun j =>
    let j' : Fin p := ⟨j.val, by omega⟩
    p08RoundedLowRankMatVec fp (X i j') (Y i j') (trace.x j')
  have hle : (i.val : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
  have hiValid : (i.val : ℝ) * fp.u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle fp.u_nonneg) hvalid
  have hα (α : Fin b) :=
    p08_subFold_forward_error fp i.val (v i α) (fun j => w j α) hiValid
  choose θ e hθ he heq using hα
  refine ⟨θ, (fun j α => e α j), ?_, ?_, ?_⟩
  · intro α
    exact (hθ α).trans
      (p08_gamma_mono (Nat.cast_nonneg i.val) hle fp.u_nonneg hvalid)
  · intro j α
    exact (he α j).trans
      (p08_gamma_mono (Nat.cast_nonneg i.val) hle fp.u_nonneg hvalid)
  · intro α
    have hrhs := congrFun (trace.rhs_eq i) α
    have hfold := p08_vector_subFold_component fp i.val b (v i) w α
    have hrhs' : trace.rhs i α =
        p08SubFold fp i.val (v i α) (fun j => w j α) := by
      exact hrhs.trans hfold
    rw [hrhs', heq α]

private theorem p08_trace_lower_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1)
    (i j : Fin p) (hji : j < i) :
    ∃ F : P08Matrix b,
      p08RectFrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08RectFrobNorm (T i j) ∧
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) =
        Matrix.mulVec (T i j + F) (trace.x j) := by
  obtain ⟨F, hF, heq⟩ :=
    p08_lowrank_matvec_error fp (X i j) (Y i j) (trace.x j)
      (hX i j hji) hvalid
  refine ⟨F, ?_, ?_⟩
  · rwa [hlr i j hji]
  · rwa [hlr i j hji]

private theorem p08_trace_diag_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hvalid : (b : ℝ) * fp.u < 1)
    (i : Fin p) :
    ∃ F : P08Matrix b,
      p08RectFrobNorm F ≤
        p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm (T i i) ∧
      Matrix.mulVec (T i i + F) (trace.x i) = trace.rhs i := by
  obtain ⟨F, hF, heq⟩ :=
    p08_forward_backward_error fp b (T i i) (trace.rhs i)
      (hdiag i) (hlower i) hvalid
  refine ⟨F, hF, ?_⟩
  rwa [trace.x_eq i]

private theorem p08_assemble_mulVec_add {p b : ℕ}
    (T D : P08BlockMatrix p b) (x : P08BlockVector p b)
    (i : Fin p) (α : Fin b) :
    Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix D)
        (p08AssembleVector x) (i, α) =
      ∑ j : Fin p, Matrix.mulVec (T i j + D i j) (x j) α := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.add_apply, p08AssembleMatrix, p08AssembleVector]

private def p08ScaleError {b : ℕ}
    (T F : P08Matrix b) (θ : Fin b → ℝ) : P08Matrix b :=
  fun γ β => θ γ * T γ β + (1 + θ γ) * F γ β

private theorem p08_scaled_mulVec {b : ℕ}
    (T F : P08Matrix b) (θ : Fin b → ℝ) (x : Fin b → ℝ)
    (α : Fin b) :
    Matrix.mulVec (T + p08ScaleError T F θ) x α =
      (1 + θ α) * Matrix.mulVec (T + F) x α := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply,
    p08ScaleError, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

private theorem p08_trace_block_row_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hupper : ∀ i j : Fin p, i < j → T i j = 0)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1)
    (i : Fin p) :
    ∃ D : Fin p → P08Matrix b, ∃ d : Fin b → ℝ,
      (∀ j, p08RectFrobNorm (D j) ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ))
          fp.u * p08RectFrobNorm (T i j)) ∧
      (∀ α, |d α| ≤ p08GammaReal (p : ℝ) fp.u * |v i α|) ∧
      (∀ α, (∑ j : Fin p,
          Matrix.mulVec (T i j + D j) (trace.x j) α) = v i α + d α) := by
  let q := (r : ℝ) * Real.sqrt (r : ℝ)
  let a := (b : ℝ) + q
  let c := a + (p : ℝ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have ha0 : 0 ≤ a := add_nonneg (Nat.cast_nonneg b) hq0
  have hc : c * fp.u < 1 := hvalid
  have hpvalid : (p : ℝ) * fp.u < 1 := by
    have hau := mul_nonneg ha0 fp.u_nonneg
    change (a + (p : ℝ)) * fp.u < 1 at hvalid
    nlinarith
  have hadvalid : a * fp.u < 1 := by
    have hpu := mul_nonneg (Nat.cast_nonneg p) fp.u_nonneg
    change (a + (p : ℝ)) * fp.u < 1 at hvalid
    nlinarith
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have hqu := mul_nonneg hq0 fp.u_nonneg
    change ((b : ℝ) + q) * fp.u < 1 at hadvalid
    nlinarith
  obtain ⟨Fdiag, hFdiag, heqdiag⟩ :=
    p08_trace_diag_error fp T X Y v trace hdiag hlower hbvalid i
  have hlowErr (j : Fin p) (hji : j < i) :=
    p08_trace_lower_error fp T X Y v trace hlr hX hadvalid i j hji
  choose Flow hFlow heqFlow using hlowErr
  let w : Fin i.val → Fin b → ℝ := fun t =>
    let j : Fin p := ⟨t.val, by omega⟩
    p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j)
  obtain ⟨θv, θw, hθv, hθw, heqrhs⟩ :=
    p08_trace_rhs_error fp T X Y v trace i hpvalid
  let D : Fin p → P08Matrix b := fun j =>
    if hji : j < i then
      p08ScaleError (T i j) (Flow j hji) (θw ⟨j.val, hji⟩)
    else if j = i then Fdiag else 0
  let d : Fin b → ℝ := fun α => v i α * θv α
  refine ⟨D, d, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j < i
    · have hθ : ∀ α, |θw ⟨j.val, hji⟩ α| ≤
          p08GammaReal (p : ℝ) fp.u := fun α => hθw ⟨j.val, hji⟩ α
      have hbound := p08_scaled_matrix_error fp.u a (p : ℝ)
        fp.u_nonneg ha0 (Nat.cast_nonneg p) hc
        (T i j) (Flow j hji) (θw ⟨j.val, hji⟩) (hFlow j hji) hθ
      simpa only [D, dif_pos hji, c, a, q, p08ScaleError] using hbound
    · by_cases hji' : j = i
      · subst j
        have hle : (b : ℝ) ≤ c := by
          dsimp [c, a]
          have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
          nlinarith [hq0, hp0]
        have hm := p08_gamma_mono (Nat.cast_nonneg b) hle fp.u_nonneg hc
        simpa only [D, dif_neg (lt_irrefl i), if_pos rfl] using
          (hFdiag.trans (mul_le_mul_of_nonneg_right hm
            (p08_rectNorm_nonneg (T i i))))
      · have hzero : D j = 0 := by simp [D, hji, hji']
        rw [hzero]
        have hgc : 0 ≤ p08GammaReal c fp.u :=
          p08_gamma_nonneg (by dsimp [c]; positivity) fp.u_nonneg hc
        simpa [p08RectFrobNorm] using
          (mul_nonneg hgc (p08_rectNorm_nonneg (T i j)))
  · intro α
    simp only [d, abs_mul]
    calc
      |v i α| * |θv α| ≤
          |v i α| * p08GammaReal (p : ℝ) fp.u :=
        mul_le_mul_of_nonneg_left (hθv α) (abs_nonneg _)
      _ = _ := mul_comm _ _
  · intro α
    have hsum := p08_sum_lower_diag i
      (fun j => Matrix.mulVec (T i j + D j) (trace.x j) α) (by
        intro j hij
        have ht : T i j = 0 := hupper i j hij
        have hji : ¬j < i := by omega
        have hne : j ≠ i := ne_of_gt hij
        have hd : D j = 0 := by simp [D, hji, hne]
        simp [ht, hd])
    have hdiag' : Matrix.mulVec (T i i + D i) (trace.x i) α =
        trace.rhs i α := by
      have hnot : ¬i < i := lt_irrefl i
      simpa [D, hnot] using congrFun heqdiag α
    have hlow : (∑ t : Fin i.val,
        Matrix.mulVec
          (T i ⟨t.val, by omega⟩ + D ⟨t.val, by omega⟩)
          (trace.x ⟨t.val, by omega⟩) α) =
        ∑ t : Fin i.val, w t α * (1 + θw t α) := by
      apply Finset.sum_congr rfl
      intro t _
      let j : Fin p := ⟨t.val, by omega⟩
      have hji : j < i := t.isLt
      have hD : D j = p08ScaleError (T i j) (Flow j hji) (θw t) := by
        simp only [D, dif_pos hji]
        rfl
      change Matrix.mulVec (T i j + D j) (trace.x j) α =
        w t α * (1 + θw t α)
      rw [hD, p08_scaled_mulVec]
      have hF := congrFun (heqFlow j hji) α
      rw [← hF]
      dsimp only [w]
      ring
    rw [hsum, hlow]
    change (∑ t : Fin i.val, w t α * (1 + θw t α)) +
      Matrix.mulVec (T i i + D i) (trace.x i) α =
        v i α + d α
    rw [hdiag', heqrhs α]
    dsimp [d]
    ring

/-- P08-C3: complete Theorem 4.4 for a triangular BLR block system. -/
theorem p08_c3_blr_triangular_backward_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b)
    (trace : P08BLRTrace fp T X Y v)
    (hp : 0 < p) (hb : 0 < b)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hupper : ∀ i j : Fin p, i < j → T i j = 0)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    let x := trace.x
    let c := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)
    ∃ DT : P08BlockMatrix p b, ∃ dv : P08BlockVector p b,
      Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
          (p08AssembleVector x) =
        p08AssembleVector v + p08AssembleVector dv ∧
      p08BlockFrobNorm DT ≤
        p08GammaReal c fp.u * p08BlockFrobNorm T ∧
      p08BlockVecNorm dv ≤
        p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
  -- PROOF_START P08-C3-H001
  dsimp only
  have hrow (i : Fin p) :=
    p08_trace_block_row_error fp T X Y v trace hdiag hlower hupper hlr hX hvalid i
  choose D d hD hd heq using hrow
  let DT : P08BlockMatrix p b := fun i j => D i j
  let dv : P08BlockVector p b := fun i => d i
  refine ⟨DT, dv, ?_, ?_, ?_⟩
  · funext ⟨i, α⟩
    rw [p08_assemble_mulVec_add]
    change (∑ j : Fin p, Matrix.mulVec (T i j + D i j) (trace.x j) α) =
      v i α + d i α
    exact heq i α
  · apply p08_blockNorm_le_of_blocks DT T
      (p08_gamma_nonneg (by positivity) fp.u_nonneg hvalid)
    intro i j
    exact hD i j
  · apply p08_blockVecNorm_le_of_entrywise dv v
      (p08_gamma_nonneg (Nat.cast_nonneg p) fp.u_nonneg (by
        have hq : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
        have hbu : 0 ≤ ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u := by
          exact mul_nonneg (add_nonneg (Nat.cast_nonneg b) hq) fp.u_nonneg
        nlinarith [hvalid]))
    intro i α
    exact hd i α

end VSCLReuse
