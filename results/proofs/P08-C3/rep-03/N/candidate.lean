import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix Matrix.Norms.Frobenius

private theorem p08_gamma_real_nonneg (u k : ℝ)
    (hu : 0 ≤ u) (hk : 0 ≤ k) (hv : k * u < 1) :
    0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private theorem p08_gamma_real_mono (u a c : ℝ)
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c * u < 1) :
    p08GammaReal a u ≤ p08GammaReal c u := by
  have h1 : 0 < 1 - a * u := by nlinarith
  have h2 : 0 < 1 - c * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ h1 h2).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hac) hu]

private theorem p08_gamma_real_compose (u a b : ℝ)
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : (a + b) * u < 1) :
    p08GammaReal a u + p08GammaReal b u +
      p08GammaReal a u * p08GammaReal b u ≤
      p08GammaReal (a + b) u := by
  have hA : 0 < 1 - a * u := by nlinarith [mul_nonneg hb hu]
  have hB : 0 < 1 - b * u := by nlinarith [mul_nonneg ha hu]
  have hC : 0 < 1 - (a + b) * u := by linarith
  have hden : 1 - (a + b) * u ≤ (1 - a * u) * (1 - b * u) := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (mul_self_nonneg u)]
  have hrec := one_div_le_one_div_of_le hC hden
  have hga : p08GammaReal a u = 1 / (1 - a * u) - 1 := by
    unfold p08GammaReal
    calc
      a * u / (1 - a * u) = (1 - (1 - a * u)) / (1 - a * u) := by ring
      _ = 1 / (1 - a * u) - (1 - a * u) / (1 - a * u) := by rw [sub_div]
      _ = 1 / (1 - a * u) - 1 := by rw [div_self (ne_of_gt hA)]
  have hgb : p08GammaReal b u = 1 / (1 - b * u) - 1 := by
    unfold p08GammaReal
    calc
      b * u / (1 - b * u) = (1 - (1 - b * u)) / (1 - b * u) := by ring
      _ = 1 / (1 - b * u) - (1 - b * u) / (1 - b * u) := by rw [sub_div]
      _ = 1 / (1 - b * u) - 1 := by rw [div_self (ne_of_gt hB)]
  have hleft : p08GammaReal a u + p08GammaReal b u +
      p08GammaReal a u * p08GammaReal b u =
      1 / ((1 - a * u) * (1 - b * u)) - 1 := by
    rw [hga, hgb]
    calc
      _ = (1 / (1 - a * u)) * (1 / (1 - b * u)) - 1 := by ring
      _ = 1 / ((1 - a * u) * (1 - b * u)) - 1 := by rw [one_div_mul_one_div]
  have hright : p08GammaReal (a + b) u =
      1 / (1 - (a + b) * u) - 1 := by
    unfold p08GammaReal
    calc
      (a + b) * u / (1 - (a + b) * u) =
          (1 - (1 - (a + b) * u)) / (1 - (a + b) * u) := by ring
      _ = 1 / (1 - (a + b) * u) - (1 - (a + b) * u) / (1 - (a + b) * u) := by
        rw [sub_div]
      _ = 1 / (1 - (a + b) * u) - 1 := by rw [div_self (ne_of_gt hC)]
  rw [hleft, hright]
  linarith

private theorem p08_relative_error_compose (u a b q₁ q₂ : ℝ)
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : (a + b) * u < 1)
    (h₁ : |q₁ - 1| ≤ p08GammaReal a u)
    (h₂ : |q₂ - 1| ≤ p08GammaReal b u) :
    |q₁ * q₂ - 1| ≤ p08GammaReal (a + b) u := by
  have hga := p08_gamma_real_nonneg u a hu ha (by nlinarith [mul_nonneg hb hu])
  have hgb := p08_gamma_real_nonneg u b hu hb (by nlinarith [mul_nonneg ha hu])
  have hmul : |(q₁ - 1) * (q₂ - 1)| ≤
      p08GammaReal a u * p08GammaReal b u := by
    rw [abs_mul]
    exact mul_le_mul h₁ h₂ (abs_nonneg _) hga
  have hid : q₁ * q₂ - 1 = (q₁ - 1) + (q₂ - 1) + (q₁ - 1) * (q₂ - 1) := by ring
  rw [hid]
  calc
    |(q₁ - 1) + (q₂ - 1) + (q₁ - 1) * (q₂ - 1)| ≤
        |q₁ - 1| + |q₂ - 1| + |(q₁ - 1) * (q₂ - 1)| := by
          calc
            _ ≤ |(q₁ - 1) + (q₂ - 1)| + |(q₁ - 1) * (q₂ - 1)| := abs_add_le _ _
            _ ≤ |q₁ - 1| + |q₂ - 1| + |(q₁ - 1) * (q₂ - 1)| := by
              gcongr
              exact abs_add_le _ _
    _ ≤ p08GammaReal a u + p08GammaReal b u +
          p08GammaReal a u * p08GammaReal b u := by linarith
    _ ≤ p08GammaReal (a + b) u := p08_gamma_real_compose u a b hu ha hb hv

private theorem p08_sqrt_sum_sq_le
    {ι : Type*} [Fintype ι] (s t : ι → ℝ) (g : ℝ)
    (hg : 0 ≤ g) (h : ∀ i, |s i| ≤ g * |t i|) :
    Real.sqrt (∑ i, (s i) ^ 2) ≤
      g * Real.sqrt (∑ i, (t i) ^ 2) := by
  have hterm (i : ι) : (s i) ^ 2 ≤ g ^ 2 * (t i) ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg (s i)) (mul_nonneg hg (abs_nonneg (t i)))).2 (h i)
    simpa [sq_abs, mul_pow] using hsq
  have hsum : (∑ i, (s i) ^ 2) ≤ g ^ 2 * (∑ i, (t i) ^ 2) := by
    calc
      _ ≤ ∑ i, g ^ 2 * (t i) ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
      _ = g ^ 2 * (∑ i, (t i) ^ 2) := by rw [Finset.mul_sum]
  have hsqrt := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq_eq_abs, abs_of_nonneg hg] at hsqrt

private theorem p08_u_le_gamma_one (u : ℝ) (hu : 0 ≤ u) (hv : u < 1) :
    u ≤ p08GammaReal 1 u := by
  have hd : 0 < 1 - u := by linarith
  unfold p08GammaReal
  norm_num
  apply (le_div_iff₀ hd).2
  nlinarith [sq_nonneg u]

private theorem p08_relative_error_one (u δ : ℝ)
    (hu : 0 ≤ u) (hv : u < 1) (hδ : |δ| ≤ u) :
    |(1 + δ) - 1| ≤ p08GammaReal 1 u := by
  simpa using hδ.trans (p08_u_le_gamma_one u hu hv)

private theorem p08_rounded_dot_coeff (fp : StandardFPModel) (n : ℕ) :
    ∀ (a x : Fin n → ℝ), (n : ℝ) * fp.u < 1 →
      ∃ q : Fin n → ℝ,
        (∀ j, |q j - 1| ≤ p08GammaReal (n : ℝ) fp.u) ∧
        Fin.foldl n (fun acc j => fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 =
          ∑ j, (a j * x j) * q j := by
  induction n with
  | zero =>
      intro a x hv
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro j; exact Fin.elim0 j
      · simp
  | succ n ih =>
      intro a x hv
      cases n with
      | zero =>
          obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (a 0) (x 0)
          refine ⟨fun _ => 1 + δ, ?_, ?_⟩
          · intro j
            have hu : fp.u < 1 := by simpa using hv
            simpa using p08_relative_error_one fp.u δ fp.u_nonneg hu hδ
          · simp [Fin.foldl_succ, fp.fl_add_zero, hmul]
      | succ m =>
          let a₀ : Fin (m + 1) → ℝ := fun j => a j.castSucc
          let x₀ : Fin (m + 1) → ℝ := fun j => x j.castSucc
          have hp : ((m + 1 : ℕ) : ℝ) * fp.u < 1 := by
            have hm : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (m + 1)
            nlinarith [mul_nonneg (sub_nonneg.mpr hm) fp.u_nonneg]
          have hu : fp.u < 1 := by
            have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            nlinarith [mul_nonneg (sub_nonneg.mpr hm) fp.u_nonneg]
          obtain ⟨q, hq, heq⟩ := ih a₀ x₀ hp
          let A := Fin.foldl (m + 1)
            (fun acc j => fp.fl_add acc (fp.fl_mul (a₀ j) (x₀ j))) 0
          obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last (m + 1))) (x (Fin.last (m + 1)))
          obtain ⟨δ, hδ, hadd⟩ := fp.model_add A
            (fp.fl_mul (a (Fin.last (m + 1))) (x (Fin.last (m + 1))))
          let q' : Fin (m + 2) → ℝ := Fin.snoc (fun j => q j * (1 + δ)) ((1 + μ) * (1 + δ))
          refine ⟨q', ?_, ?_⟩
          · intro j
            refine Fin.lastCases ?_ ?_ j
            · have htwo : (2 : ℝ) * fp.u < 1 := by
                have hn : (2 : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast Nat.le_add_left 2 m
                nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
              have hcomp := p08_relative_error_compose fp.u 1 1
                (1 + μ) (1 + δ) fp.u_nonneg (by norm_num) (by norm_num)
                (by convert htwo using 1 <;> norm_num)
                (p08_relative_error_one fp.u μ fp.u_nonneg hu hμ)
                (p08_relative_error_one fp.u δ fp.u_nonneg hu hδ)
              have hmono := p08_gamma_real_mono fp.u 2 (m + 2 : ℕ)
                  fp.u_nonneg (by norm_num) (by exact_mod_cast Nat.le_add_left 2 m) hv
              have hbnd : |(1 + μ) * (1 + δ) - 1| ≤
                  p08GammaReal (m + 2 : ℕ) fp.u := by
                exact hcomp.trans (by convert hmono using 1 <;> norm_num)
              simpa [q', Fin.snoc_last, Nat.cast_add, add_assoc] using hbnd
            · intro j
              have hcomp := p08_relative_error_compose fp.u (m + 1 : ℕ) 1
                (q j) (1 + δ) fp.u_nonneg (by exact_mod_cast Nat.zero_le (m + 1))
                (by norm_num) (by convert hv using 1 <;> norm_num [Nat.cast_add]) (hq j)
                (p08_relative_error_one fp.u δ fp.u_nonneg hu hδ)
              simpa [q', Fin.snoc_castSucc, Nat.cast_add] using hcomp
          · rw [Fin.foldl_succ_last]
            change fp.fl_add A (fp.fl_mul (a (Fin.last (m + 1)))
              (x (Fin.last (m + 1)))) = ∑ j, (a j * x j) * q' j
            rw [hadd, hmul]
            rw [Fin.sum_univ_castSucc]
            simp only [q', Fin.snoc_castSucc, Fin.snoc_last]
            have hAeq : A = ∑ j, a j.castSucc * x j.castSucc * q j := heq
            have hsum :
                (∑ j, a j.castSucc * x j.castSucc * (q j * (1 + δ))) =
                (∑ j, a j.castSucc * x j.castSucc * q j) * (1 + δ) := by
              rw [Finset.sum_mul]
              congr 1
              funext j
              ring
            rw [hsum, ← hAeq]
            ring

private theorem p08_rounded_dot_fold (fp : StandardFPModel) (n : ℕ)
    (a x : Fin n → ℝ) :
    roundedDotProduct fp n a x =
      Fin.foldl n (fun acc j => fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 := by
  cases n with
  | zero => simp [roundedDotProduct]
  | succ n =>
      unfold roundedDotProduct
      rw [Fin.foldl_succ]
      simp only [fp.fl_add_zero]

private theorem p08_rounded_rect_matvec_error
    (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hv : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      (∀ i j, |E i j| ≤ p08GammaReal (n : ℝ) fp.u * |A i j|) ∧
      p08RoundedRectMatVec fp A x = p08RectMatVec (p08RectAdd A E) x := by
  classical
  have hrow (i : Fin m) : ∃ q : Fin n → ℝ,
      (∀ j, |q j - 1| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      roundedDotProduct fp n (A i) x = ∑ j, (A i j * x j) * q j := by
    obtain ⟨q, hq, heq⟩ := p08_rounded_dot_coeff fp n (A i) x hv
    exact ⟨q, hq, (p08_rounded_dot_fold fp n (A i) x).trans heq⟩
  choose q hq heq using hrow
  let E : P08RectMatrix m n := fun i j => A i j * (q i j - 1)
  refine ⟨E, ?_, ?_⟩
  · intro i j
    change |A i j * (q i j - 1)| ≤ p08GammaReal (n : ℝ) fp.u * |A i j|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hq i j) (abs_nonneg _)
  · funext i
    change roundedDotProduct fp n (A i) x = ∑ j, (A i j + E i j) * x j
    rw [heq i]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [E]
    ring

private theorem p08_orthonormal_mulvec_sq {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (z : Fin r → ℝ) :
    (∑ i : Fin b, (∑ j : Fin r, X i j * z j) ^ 2) =
      ∑ j : Fin r, z j ^ 2 := by
  have hXX : Xᵀ * X = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext j k
    simpa [Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply, p08OrthonormalColumns] using hX j k
  calc
    (∑ i : Fin b, (∑ j : Fin r, X i j * z j) ^ 2) =
        (X *ᵥ z) ⬝ᵥ (X *ᵥ z) := by simp [dotProduct, Matrix.mulVec, pow_two]
    _ = ((X *ᵥ z) ᵥ* X) ⬝ᵥ z := Matrix.dotProduct_mulVec (X *ᵥ z) X z
    _ = (Xᵀ *ᵥ (X *ᵥ z)) ⬝ᵥ z := by rw [Matrix.mulVec_transpose]
    _ = ((Xᵀ * X) *ᵥ z) ⬝ᵥ z := by rw [Matrix.mulVec_mulVec]
    _ = z ⬝ᵥ z := by rw [hXX]; simp
    _ = ∑ j : Fin r, z j ^ 2 := by simp [dotProduct, pow_two]

private theorem p08_orthonormal_left_mul_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (E : P08RectMatrix r n)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X E) = p08RectFrobNorm E := by
  unfold p08RectFrobNorm p08RectMatMul
  congr 1
  calc
    (∑ i : Fin b, ∑ k : Fin n, (∑ j : Fin r, X i j * E j k) ^ 2) =
        ∑ k : Fin n, ∑ i : Fin b, (∑ j : Fin r, X i j * E j k) ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ j : Fin r, (E j k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact p08_orthonormal_mulvec_sq X hX (fun j => E j k)
    _ = ∑ j : Fin r, ∑ k : Fin n, (E j k) ^ 2 := by rw [Finset.sum_comm]

private theorem p08_rect_transpose_norm {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  unfold p08RectFrobNorm p08RectTranspose
  congr 1
  rw [Finset.sum_comm]

private theorem p08_lowrank_norm {b r : ℕ}
    (X Y : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  unfold p08FrobNorm p08LowRankMatrix
  rw [p08_orthonormal_left_mul_norm X (p08RectTranspose Y) hX,
    p08_rect_transpose_norm]

private theorem p08_rect_norm_eq {m n : ℕ}
    (A : P08RectMatrix m n) : p08RectFrobNorm A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  unfold p08RectFrobNorm
  rw [Real.sqrt_eq_rpow]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]

private theorem p08_rect_entrywise_bound {m n : ℕ}
    (A E : P08RectMatrix m n) (g : ℝ)
    (hg : 0 ≤ g) (h : ∀ i j, |E i j| ≤ g * |A i j|) :
    p08RectFrobNorm E ≤ g * p08RectFrobNorm A := by
  have h' := p08_sqrt_sum_sq_le
    (fun ij : Fin m × Fin n => E ij.1 ij.2)
    (fun ij : Fin m × Fin n => A ij.1 ij.2) g hg
    (fun ij => h ij.1 ij.2)
  simpa only [p08RectFrobNorm, Fintype.sum_prod_type] using h'

private theorem p08_rect_add_bound {m n : ℕ}
    (A E : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectAdd A E) ≤
      p08RectFrobNorm A + p08RectFrobNorm E := by
  rw [p08_rect_norm_eq, p08_rect_norm_eq, p08_rect_norm_eq]
  have h : p08RectAdd A E = A + E := rfl
  rw [h]
  exact norm_add_le A E

private theorem p08_rect_mul_bound {m n k : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n k) :
    p08RectFrobNorm (p08RectMatMul A B) ≤
      p08RectFrobNorm A * p08RectFrobNorm B := by
  rw [p08_rect_norm_eq, p08_rect_norm_eq, p08_rect_norm_eq]
  have h : p08RectMatMul A B = A * B := by
    ext i j
    simp [p08RectMatMul, Matrix.mul_apply, dotProduct]
  rw [h]
  exact Matrix.frobenius_norm_mul A B

private theorem p08_orthonormal_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  have hcol (j : Fin r) : (∑ i : Fin b, (X i j) ^ 2) = 1 := by
    simpa [p08OrthonormalColumns, pow_two] using hX j j
  unfold p08RectFrobNorm
  calc
    Real.sqrt (∑ i : Fin b, ∑ j : Fin r, (X i j) ^ 2) =
        Real.sqrt (∑ j : Fin r, ∑ i : Fin b, (X i j) ^ 2) := by rw [Finset.sum_comm]
    _ = Real.sqrt (∑ j : Fin r, (1 : ℝ)) := by simp_rw [hcol]
    _ = Real.sqrt (r : ℝ) := by simp

private theorem p08_gamma_scaled (u a s : ℝ)
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hs : 1 ≤ s)
    (hv : (s * a) * u < 1) :
    s * p08GammaReal a u ≤ p08GammaReal (s * a) u := by
  have hnum : 0 ≤ (s * a) * u := mul_nonneg (mul_nonneg (by linarith) ha) hu
  have hprod : a * u ≤ (s * a) * u := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hs) ha) hu]
  have hd₁ : 0 < 1 - a * u := by linarith
  have hd₂ : 0 < 1 - (s * a) * u := by linarith
  unfold p08GammaReal
  rw [mul_div_assoc]
  ring_nf at *
  apply (div_le_div_iff₀ hd₁ hd₂).2
  exact mul_le_mul_of_nonneg_left (by linarith : 1 - (s * a) * u ≤ 1 - a * u) hnum

private theorem p08_rank_le_rank_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hs : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrr
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (sub_nonneg.mpr hs)]

private theorem p08_rect_mul_eq {m n k : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n k) :
    p08RectMatMul A B = A * B := by
  ext i j
  simp [p08RectMatMul, Matrix.mul_apply]

private theorem p08_rect_matvec_eq {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ) :
    p08RectMatVec A x = A *ᵥ x := by
  ext i
  simp [p08RectMatVec, Matrix.mulVec, dotProduct]

private theorem p08_rect_add_eq {m n : ℕ}
    (A B : P08RectMatrix m n) : p08RectAdd A B = A + B := rfl

private theorem p08_gamma_rank_sqrt (u : ℝ) (r : ℕ)
    (hu : 0 ≤ u)
    (hv : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  by_cases hr : r = 0
  · simp [hr, p08GammaReal]
  · have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hs : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hrr
    have h := p08_gamma_scaled u (r : ℝ) (Real.sqrt (r : ℝ)) hu
      (by positivity) hs (by simpa [mul_comm] using hv)
    simpa [mul_comm] using h

private theorem p08_lowrank_matvec_error (fp : StandardFPModel)
    {b r : ℕ} (X Y : P08RectMatrix b r) (x : Fin b → ℝ)
    (hX : p08OrthonormalColumns X)
    (hv : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      p08RoundedLowRankMatVec fp X Y x =
        (p08LowRankMatrix X Y + F) *ᵥ x ∧
      p08FrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) := by
  let k : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have hk : 0 ≤ k := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hk fp.u_nonneg]
  have hkvalid : k * fp.u < 1 := by
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) by positivity) fp.u_nonneg]
  have hrvalid : (r : ℝ) * fp.u < 1 := by
    have hrk : (r : ℝ) ≤ k := p08_rank_le_rank_sqrt r
    nlinarith [mul_nonneg (sub_nonneg.mpr hrk) fp.u_nonneg]
  let Yt : P08RectMatrix r b := p08RectTranspose Y
  obtain ⟨E₁, hE₁, hinner⟩ := p08_rounded_rect_matvec_error fp Yt x hbvalid
  let z : Fin r → ℝ := p08RoundedRectMatVec fp Yt x
  obtain ⟨E₂, hE₂, houter⟩ := p08_rounded_rect_matvec_error fp X z hrvalid
  let F : P08Matrix b := X * E₁ + E₂ * (Yt + E₁)
  refine ⟨F, ?_, ?_⟩
  · have hi : z = (Yt + E₁) *ᵥ x := by
      simpa [z, p08_rect_add_eq, p08_rect_matvec_eq] using hinner
    have ho : p08RoundedRectMatVec fp X z = (X + E₂) *ᵥ z := by
      simpa [p08_rect_add_eq, p08_rect_matvec_eq] using houter
    have hmat : (X + E₂) * (Yt + E₁) = p08LowRankMatrix X Y + F := by
      unfold F p08LowRankMatrix
      rw [p08_rect_mul_eq]
      change (X + E₂) * (Yt + E₁) = X * Yt + (X * E₁ + E₂ * (Yt + E₁))
      rw [Matrix.add_mul, Matrix.mul_add]
      abel
    change p08RoundedRectMatVec fp X z = (p08LowRankMatrix X Y + F) *ᵥ x
    rw [ho, hi, Matrix.mulVec_mulVec, hmat]
  · let N : ℝ := p08RectFrobNorm Y
    let gB : ℝ := p08GammaReal (b : ℝ) fp.u
    let gR : ℝ := p08GammaReal (r : ℝ) fp.u
    let gK : ℝ := p08GammaReal k fp.u
    have hN : 0 ≤ N := Real.sqrt_nonneg _
    have hgB : 0 ≤ gB := p08_gamma_real_nonneg fp.u (b : ℝ) fp.u_nonneg (by positivity) hbvalid
    have hgR : 0 ≤ gR := p08_gamma_real_nonneg fp.u (r : ℝ) fp.u_nonneg (by positivity) hrvalid
    have hE₁norm : p08RectFrobNorm E₁ ≤ gB * N := by
      have h := p08_rect_entrywise_bound Yt E₁ gB hgB hE₁
      simpa [N, Yt, p08_rect_transpose_norm, gB] using h
    have hE₂norm : p08RectFrobNorm E₂ ≤ gR * Real.sqrt (r : ℝ) := by
      have h := p08_rect_entrywise_bound X E₂ gR hgR hE₂
      simpa [gR, p08_orthonormal_norm X hX] using h
    have hscale : gR * Real.sqrt (r : ℝ) ≤ gK := by
      simpa [gR, gK, k] using p08_gamma_rank_sqrt fp.u r fp.u_nonneg hkvalid
    have hcomp : gB + gK + gB * gK ≤
        p08GammaReal ((b : ℝ) + k) fp.u := by
      exact p08_gamma_real_compose fp.u (b : ℝ) k fp.u_nonneg
        (by positivity) hk (by simpa [k] using hv)
    have hiso : ‖X * E₁‖ = ‖E₁‖ := by
      calc
        ‖X * E₁‖ = p08RectFrobNorm (p08RectMatMul X E₁) := by
          rw [p08_rect_mul_eq, p08_rect_norm_eq]
        _ = p08RectFrobNorm E₁ := p08_orthonormal_left_mul_norm X E₁ hX
        _ = ‖E₁‖ := p08_rect_norm_eq E₁
    have hF : p08FrobNorm F ≤
        p08RectFrobNorm E₁ + p08RectFrobNorm E₂ * (N + p08RectFrobNorm E₁) := by
      change p08RectFrobNorm F ≤ _
      rw [p08_rect_norm_eq]
      calc
        ‖F‖ ≤ ‖X * E₁‖ + ‖E₂ * (Yt + E₁)‖ := norm_add_le _ _
        _ ≤ ‖E₁‖ + ‖E₂‖ * (‖Yt‖ + ‖E₁‖) := by
          rw [hiso]
          gcongr
          exact (Matrix.frobenius_norm_mul E₂ (Yt + E₁)).trans
            (mul_le_mul_of_nonneg_left (norm_add_le Yt E₁) (norm_nonneg _))
        _ = p08RectFrobNorm E₁ + p08RectFrobNorm E₂ *
            (N + p08RectFrobNorm E₁) := by
          rw [← p08_rect_norm_eq E₁, ← p08_rect_norm_eq E₂,
            ← p08_rect_norm_eq Yt, p08_rect_transpose_norm]
    have hmid : p08RectFrobNorm E₁ + p08RectFrobNorm E₂ *
        (N + p08RectFrobNorm E₁) ≤ (gB + gK + gB * gK) * N := by
      have hsum : 0 ≤ N + p08RectFrobNorm E₁ :=
        add_nonneg hN (Real.sqrt_nonneg _)
      have hsum' : 0 ≤ N + gB * N := add_nonneg hN (mul_nonneg hgB hN)
      have h₂ : p08RectFrobNorm E₂ * (N + p08RectFrobNorm E₁) ≤
          gK * (N + gB * N) := by
        calc
          _ ≤ (gR * Real.sqrt (r : ℝ)) * (N + p08RectFrobNorm E₁) :=
            mul_le_mul_of_nonneg_right hE₂norm hsum
          _ ≤ (gR * Real.sqrt (r : ℝ)) * (N + gB * N) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hE₁norm N)
              (mul_nonneg hgR (Real.sqrt_nonneg _))
          _ ≤ gK * (N + gB * N) := mul_le_mul_of_nonneg_right hscale hsum'
      calc
        _ ≤ gB * N + gK * (N + gB * N) := add_le_add hE₁norm h₂
        _ = (gB + gK + gB * gK) * N := by ring
    have hres : p08FrobNorm F ≤
        p08GammaReal ((b : ℝ) + k) fp.u * N := by
      exact hF.trans (hmid.trans (mul_le_mul_of_nonneg_right hcomp hN))
    simpa [N, k, p08_lowrank_norm X Y hX] using hres

private theorem p08_inverse_rounding_error (u δ : ℝ)
    (hu : 0 ≤ u) (hv : u < 1) (hδ : |δ| ≤ u) :
    |(1 + δ)⁻¹ - 1| ≤ p08GammaReal 1 u := by
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1 |>.trans_eq (by ring)
  have hpos : 0 < 1 + δ := by linarith
  have hden : 0 < 1 - u := by linarith
  have hid : (1 + δ)⁻¹ - 1 = -δ / (1 + δ) := by
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hpos]
  calc
    |δ| / (1 + δ) ≤ u / (1 + δ) :=
      div_le_div_of_nonneg_right hδ (le_of_lt hpos)
    _ ≤ u / (1 - u) :=
      div_le_div_of_nonneg_left hu hden (by linarith)
    _ = p08GammaReal 1 u := by simp [p08GammaReal]

private theorem p08_rounded_sub_fold_coeff (fp : StandardFPModel)
    (n : ℕ) : ∀ (a x : Fin n → ℝ) (rhs : ℝ),
    (n : ℝ) * fp.u < 1 →
    ∃ q : ℝ, ∃ c : Fin n → ℝ,
      |q - 1| ≤ p08GammaReal (n : ℝ) fp.u ∧
      (∀ j, |c j - 1| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      rhs = Fin.foldl n
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) rhs * q +
        ∑ j, (a j * x j) * c j := by
  induction n with
  | zero =>
      intro a x rhs hv
      refine ⟨1, Fin.elim0, ?_, ?_, ?_⟩
      · simp [p08GammaReal]
      · intro j; exact Fin.elim0 j
      · simp
  | succ n ih =>
      intro a x rhs hv
      let a₀ : Fin n → ℝ := fun j => a j.castSucc
      let x₀ : Fin n → ℝ := fun j => x j.castSucc
      have hp : (n : ℝ) * fp.u < 1 := by
        have hn : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
        nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
      have hu : fp.u < 1 := by
        have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
      obtain ⟨q, c, hq, hc, heq⟩ := ih a₀ x₀ rhs hp
      let A := Fin.foldl n
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a₀ j) (x₀ j))) rhs
      let t := a (Fin.last n) * x (Fin.last n)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last n)) (x (Fin.last n))
      obtain ⟨δ, hδ, hsub⟩ := fp.model_sub A
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n)))
      have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
      have hpos : 0 < 1 + δ := by linarith
      let q' : ℝ := q * (1 + δ)⁻¹
      let c' : Fin (n + 1) → ℝ := Fin.snoc c ((1 + μ) * q)
      refine ⟨q', c', ?_, ?_, ?_⟩
      · have h := p08_relative_error_compose fp.u (n : ℝ) 1
          q ((1 + δ)⁻¹) fp.u_nonneg (by positivity) (by norm_num)
          (by convert hv using 1 <;> norm_num [Nat.cast_add]) hq
          (p08_inverse_rounding_error fp.u δ fp.u_nonneg hu hδ)
        simpa [q', Nat.cast_add] using h
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · have h := p08_relative_error_compose fp.u 1 (n : ℝ)
            (1 + μ) q fp.u_nonneg (by norm_num) (by positivity)
            (by simpa [Nat.cast_add, add_comm] using hv)
            (p08_relative_error_one fp.u μ fp.u_nonneg hu hμ) hq
          simpa [c', Fin.snoc_last, Nat.cast_add, add_comm] using h
        · intro j
          have hm : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
          have hmono := p08_gamma_real_mono fp.u (n : ℝ) (n + 1 : ℕ)
            fp.u_nonneg (by positivity) hm hv
          simpa [c', Fin.snoc_castSucc] using (hc j).trans hmono
      · rw [Fin.foldl_succ_last]
        change rhs = fp.fl_sub A (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) * q' +
          ∑ j, (a j * x j) * c' j
        rw [hsub, hmul, Fin.sum_univ_castSucc]
        simp only [c', Fin.snoc_castSucc, Fin.snoc_last]
        have hsum : (∑ j, a j.castSucc * x j.castSucc * c j) =
            ∑ j, (a₀ j * x₀ j) * c j := rfl
        rw [hsum] at *
        have hA : rhs = A * q + ∑ j, (a₀ j * x₀ j) * c j := heq
        rw [hA]
        dsimp [q', t]
        have hinv : (1 + δ) * (1 + δ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
        have hcancel : (1 + δ) * (q * (1 + δ)⁻¹) = q := by
          calc
            _ = q * ((1 + δ) * (1 + δ)⁻¹) := by ring
            _ = q := by rw [hinv]; ring
        calc
          A * q + ∑ j, (a₀ j * x₀ j) * c j =
              ((A - a (Fin.last n) * x (Fin.last n) * (1 + μ)) * (1 + δ)) *
                (q * (1 + δ)⁻¹) +
                (∑ j, (a₀ j * x₀ j) * c j) +
                a (Fin.last n) * x (Fin.last n) * ((1 + μ) * q) := by
                  rw [mul_assoc, hcancel]
                  ring
          _ = _ := by ring

private theorem p08_forward_row_coeff (fp : StandardFPModel) (n : ℕ)
    (L : P08Matrix n) (rhs x : Fin n → ℝ) (i : Fin n)
    (hd : L i i ≠ 0) (hv : (n : ℝ) * fp.u < 1) :
    let a : Fin i.val → ℝ := fun j => L i ⟨j.val, by omega⟩
    let z : Fin i.val → ℝ := fun j => x ⟨j.val, by omega⟩
    let s := Fin.foldl i.val
      (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (z j))) (rhs i)
    ∃ q : ℝ, ∃ c : Fin i.val → ℝ,
      |q - 1| ≤ p08GammaReal (n : ℝ) fp.u ∧
      (∀ j, |c j - 1| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      rhs i = (L i i * fp.fl_div s (L i i)) * q +
        ∑ j, (a j * z j) * c j := by
  dsimp
  let a : Fin i.val → ℝ := fun j => L i ⟨j.val, by omega⟩
  let z : Fin i.val → ℝ := fun j => x ⟨j.val, by omega⟩
  let s : ℝ := Fin.foldl i.val
    (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (z j))) (rhs i)
  have hi : ((i.val : ℕ) : ℝ) * fp.u < 1 := by
    have hn : ((i.val : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
  have his : ((i.val + 1 : ℕ) : ℝ) * fp.u < 1 := by
    have hn : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast i.isLt
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
  have hu : fp.u < 1 := by
    have hn : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
  obtain ⟨q₀, c, hq₀, hc, heq⟩ :=
    p08_rounded_sub_fold_coeff fp i.val a z (rhs i) hi
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (L i i) hd
  have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
  have hpos : 0 < 1 + δ := by linarith
  let q := q₀ * (1 + δ)⁻¹
  refine ⟨q, c, ?_, ?_, ?_⟩
  · have hcomp := p08_relative_error_compose fp.u (i.val : ℝ) 1
      q₀ ((1 + δ)⁻¹) fp.u_nonneg (by positivity) (by norm_num)
      (by simpa [Nat.cast_add] using his) hq₀
      (p08_inverse_rounding_error fp.u δ fp.u_nonneg hu hδ)
    have hmono := p08_gamma_real_mono fp.u (i.val + 1 : ℕ) (n : ℝ)
      fp.u_nonneg (by positivity) (by exact_mod_cast i.isLt) hv
    have hmono' : p08GammaReal ((i.val : ℝ) + 1) fp.u ≤
        p08GammaReal (n : ℝ) fp.u := by simpa [Nat.cast_add] using hmono
    simpa [q, Nat.cast_add] using hcomp.trans hmono'
  · intro j
    have hmono := p08_gamma_real_mono fp.u (i.val : ℝ) (n : ℝ)
      fp.u_nonneg (by positivity) (by exact_mod_cast Nat.le_of_lt i.isLt) hv
    exact (hc j).trans hmono
  · have hsinv : s = (L i i * fp.fl_div s (L i i)) * (1 + δ)⁻¹ := by
      rw [hdiv]
      field_simp [hd, ne_of_gt hpos]
    change rhs i = s * q₀ + ∑ j, (a j * z j) * c j at heq
    change rhs i = (L i i * fp.fl_div s (L i i)) * q +
      ∑ j, (a j * z j) * c j
    have hmul : s * q₀ = (L i i * fp.fl_div s (L i i)) * q := by
      dsimp [q]
      calc
        s * q₀ = ((L i i * fp.fl_div s (L i i)) * (1 + δ)⁻¹) * q₀ :=
          congrArg (· * q₀) hsinv
        _ = (L i i * fp.fl_div s (L i i)) * (q₀ * (1 + δ)⁻¹) := by ring
    calc
      rhs i = s * q₀ + ∑ j, (a j * z j) * c j := heq
      _ = (L i i * fp.fl_div s (L i i)) * q +
          ∑ j, (a j * z j) * c j := by rw [hmul]

private def p08_fin_lt_equiv {n : ℕ} (i : Fin n) :
    Fin i.val ≃ {j : Fin n // j < i} where
  toFun j := ⟨⟨j.val, by omega⟩, by exact Fin.lt_def.mpr j.isLt⟩
  invFun j := ⟨j.1.val, Fin.lt_def.mp j.2⟩
  left_inv j := by apply Fin.ext; rfl
  right_inv j := by apply Subtype.ext; apply Fin.ext; rfl

private theorem p08_fin_sum_prefix {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) =
      ∑ j : Fin n, if j < i then f j else 0 := by
  classical
  let e := p08_fin_lt_equiv i
  calc
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) =
        ∑ j : {j : Fin n // j < i}, f j.1 := by
          apply Fintype.sum_equiv e
          intro j
          rfl
    _ = ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)), f j := by
      symm
      apply Finset.sum_subtype
      intro j
      simp
    _ = ∑ j : Fin n, if j < i then f j else 0 := by
      simp [Finset.sum_ite]

private theorem p08_fin_sum_prefix_dep {n : ℕ} (i : Fin n)
    (f : Fin i.val → ℝ) :
    (∑ j : Fin i.val, f j) =
      ∑ β : Fin n, if h : β < i then f ⟨β.val, Fin.lt_def.mp h⟩ else 0 := by
  classical
  let f' : Fin n → ℝ := fun β =>
    if h : β < i then f ⟨β.val, Fin.lt_def.mp h⟩ else 0
  have h := p08_fin_sum_prefix i f'
  calc
    (∑ j : Fin i.val, f j) = ∑ j : Fin i.val, f' ⟨j.val, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hlt : (⟨j.val, by omega⟩ : Fin n) < i := by exact Fin.lt_def.mpr j.isLt
      simp [f', hlt]
    _ = ∑ β : Fin n, if β < i then f' β else 0 := h
    _ = ∑ β : Fin n, if h : β < i then f ⟨β.val, Fin.lt_def.mp h⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro β hβ
      by_cases hlt : β < i <;> simp [f', hlt]

private theorem p08_forward_row_assemble (n : ℕ)
    (L : P08Matrix n) (i : Fin n) (y rhs : Fin n → ℝ)
    (q : ℝ) (c : Fin i.val → ℝ) (g : ℝ) (hg : 0 ≤ g)
    (hlower : p08LowerTriangular L)
    (hq : |q - 1| ≤ g) (hc : ∀ j, |c j - 1| ≤ g)
    (heq : rhs i = (L i i * y i) * q +
      ∑ j : Fin i.val,
        (L i ⟨j.val, by omega⟩ * y ⟨j.val, by omega⟩) * c j) :
    ∃ Frow : Fin n → ℝ,
      (∀ β, |Frow β| ≤ g * |L i β|) ∧
      rhs i = ∑ β : Fin n, (L i β + Frow β) * y β := by
  classical
  let Frow : Fin n → ℝ := fun β =>
    if h : β < i then L i β * (c ⟨β.val, Fin.lt_def.mp h⟩ - 1)
    else if β = i then L i i * (q - 1) else 0
  refine ⟨Frow, ?_, ?_⟩
  · intro β
    by_cases hlt : β < i
    · simp only [Frow, dif_pos hlt]
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hc ⟨β.val, Fin.lt_def.mp hlt⟩) (abs_nonneg _)
    · by_cases heqβ : β = i
      · subst β
        simp only [Frow, dif_neg (lt_irrefl i), if_true]
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
      · simp only [Frow, dif_neg hlt, if_neg heqβ, abs_zero]
        exact mul_nonneg hg (abs_nonneg _)
  · have hpoint (β : Fin n) :
        (L i β + Frow β) * y β =
          (if h : β < i then (L i β * y β) * c ⟨β.val, Fin.lt_def.mp h⟩ else 0) +
          (if β = i then (L i i * y i) * q else 0) := by
      by_cases hlt : β < i
      · have hne : β ≠ i := ne_of_lt hlt
        simp [Frow, hlt, hne]
        ring
      · by_cases heqβ : β = i
        · subst β
          simp [Frow]
          ring
        · have hgt : i.val < β.val := by omega
          have hz := hlower i β hgt
          simp [Frow, hlt, heqβ, hz]
    calc
      rhs i = (L i i * y i) * q +
          ∑ j : Fin i.val,
            (L i ⟨j.val, by omega⟩ * y ⟨j.val, by omega⟩) * c j := heq
      _ = (∑ β : Fin n,
            if h : β < i then (L i β * y β) * c ⟨β.val, Fin.lt_def.mp h⟩ else 0) +
          ∑ β : Fin n, if β = i then (L i i * y i) * q else 0 := by
            have hprefix :
                (∑ β : Fin n,
                  if h : β < i then (L i β * y β) * c ⟨β.val, Fin.lt_def.mp h⟩ else 0) =
                ∑ j : Fin i.val,
                  (L i ⟨j.val, by omega⟩ * y ⟨j.val, by omega⟩) * c j := by
              exact (p08_fin_sum_prefix_dep i
                (fun j => (L i ⟨j.val, by omega⟩ * y ⟨j.val, by omega⟩) * c j)).symm
            rw [hprefix]
            simp
            ring
      _ = ∑ β : Fin n, (L i β + Frow β) * y β := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro β hβ
        exact (hpoint β).symm

private theorem p08_forward_steps_error (fp : StandardFPModel) (n : ℕ)
    (L : P08Matrix n) (rhs : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hlower : p08LowerTriangular L)
    (hv : (n : ℝ) * fp.u < 1) :
    ∀ k : ℕ, ∀ hk : k ≤ n, ∀ x : Fin n → ℝ,
      ∃ F : P08Matrix n,
        (∀ α β, |F α β| ≤ p08GammaReal (n : ℝ) fp.u * |L α β|) ∧
        (∀ α : Fin n, n - k ≤ α.val →
          ((L + F) *ᵥ (roundedForwardSubSteps fp n L rhs k hk x)) α = rhs α) ∧
        (∀ α : Fin n, α.val < n - k →
          roundedForwardSubSteps fp n L rhs k hk x α = x α) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      refine ⟨0, ?_, ?_, ?_⟩
      · intro α β
        simp only [Matrix.zero_apply, abs_zero]
        exact mul_nonneg
          (p08_gamma_real_nonneg fp.u (n : ℝ) fp.u_nonneg (by positivity) hv)
          (abs_nonneg _)
      · intro α hα
        omega
      · intro α hα
        rfl
  | succ k ih =>
      intro hk x
      have hlt : n - k - 1 < n := by omega
      let i : Fin n := ⟨n - k - 1, hlt⟩
      let a : Fin i.val → ℝ := fun j => L i ⟨j.val, by omega⟩
      let z : Fin i.val → ℝ := fun j => x ⟨j.val, by omega⟩
      let s : ℝ := Fin.foldl i.val
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (z j))) (rhs i)
      let x' : Fin n → ℝ := Function.update x i (fp.fl_div s (L i i))
      let hk' : k ≤ n := Nat.le_of_succ_le hk
      let y := roundedForwardSubSteps fp n L rhs k hk' x'
      have hy : roundedForwardSubSteps fp n L rhs (k + 1) hk x = y := by
        rfl
      obtain ⟨F₀, hF₀, hrows, hpres⟩ := ih hk' x'
      have hprior (j : Fin i.val) : y ⟨j.val, by omega⟩ = x ⟨j.val, by omega⟩ := by
        let jj : Fin n := ⟨j.val, by omega⟩
        have hj : jj.val < n - k := by dsimp [jj, i]; omega
        change y jj = x jj
        have hjpres : y jj = x' jj := hpres jj hj
        rw [hjpres]
        have hne : jj ≠ i := by
          intro he
          have hval := congrArg Fin.val he
          dsimp [jj, i] at hval
          omega
        simp [x', Function.update, hne]

      have hyi : y i = fp.fl_div s (L i i) := by
        have hii : i.val < n - k := by dsimp [i]; omega
        have hipres : y i = x' i := hpres i hii
        rw [hipres]
        simp [x']
      obtain ⟨q, c, hq, hc, hscalar₀⟩ :=
        p08_forward_row_coeff fp n L rhs x i (hdiag i) hv
      have hscalar : rhs i = (L i i * y i) * q +
          ∑ j : Fin i.val,
            (L i ⟨j.val, by omega⟩ * y ⟨j.val, by omega⟩) * c j := by
        rw [hyi]
        simp_rw [hprior]
        exact hscalar₀
      have hg : 0 ≤ p08GammaReal (n : ℝ) fp.u :=
        p08_gamma_real_nonneg fp.u (n : ℝ) fp.u_nonneg (by positivity) hv
      obtain ⟨Frow, hFrow, hrow⟩ :=
        p08_forward_row_assemble n L i y rhs q c
          (p08GammaReal (n : ℝ) fp.u) hg hlower hq hc hscalar
      let F : P08Matrix n := fun α β => if α = i then Frow β else F₀ α β
      refine ⟨F, ?_, ?_, ?_⟩
      · intro α β
        by_cases hα : α = i
        · subst α
          simpa [F] using hFrow β
        · simpa [F, hα] using hF₀ α β
      · intro α hα
        rw [hy]
        by_cases hαi : α = i
        · subst α
          change ((L + F) *ᵥ y) i = rhs i
          have hrow' : ((L + F) *ᵥ y) i = ∑ β : Fin n, (L i β + Frow β) * y β := by
            simp [Matrix.mulVec, dotProduct, F]
          rw [hrow']
          exact hrow.symm
        · have hαk : n - k ≤ α.val := by
            have hival : i.val = n - k - 1 := rfl
            have hneval : α.val ≠ i.val := by
              intro he
              exact hαi (Fin.ext he)
            omega
          have hsame : ((L + F) *ᵥ y) α = ((L + F₀) *ᵥ y) α := by
            simp [Matrix.mulVec, dotProduct, F, hαi]
          rw [hsame]
          exact hrows α hαk
      · intro α hα
        rw [hy]
        have hαk : α.val < n - k := by omega
        have hαpres : y α = x' α := hpres α hαk
        rw [hαpres]
        have hne : α ≠ i := by
          intro he
          subst α
          dsimp [i] at hα
          omega
        simp [x', Function.update, hne]

private theorem p08_forward_sub_error (fp : StandardFPModel) (n : ℕ)
    (L : P08Matrix n) (rhs : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hlower : p08LowerTriangular L)
    (hv : (n : ℝ) * fp.u < 1) :
    ∃ F : P08Matrix n,
      (∀ α β, |F α β| ≤ p08GammaReal (n : ℝ) fp.u * |L α β|) ∧
      (L + F) *ᵥ (roundedForwardSub fp n L rhs) = rhs := by
  obtain ⟨F, hF, hrows, hpres⟩ :=
    p08_forward_steps_error fp n L rhs hdiag hlower hv n (le_refl n) (fun _ => 0)
  refine ⟨F, hF, ?_⟩
  funext α
  exact hrows α (by omega)

private theorem p08_rounded_sub_sum_coeff (fp : StandardFPModel)
    (n : ℕ) : ∀ (w : Fin n → ℝ) (v : ℝ),
    (n : ℝ) * fp.u < 1 →
    ∃ qv : ℝ, ∃ q : Fin n → ℝ,
      |qv - 1| ≤ p08GammaReal (n : ℝ) fp.u ∧
      (∀ j, |q j - 1| ≤ p08GammaReal (n : ℝ) fp.u) ∧
      Fin.foldl n (fun acc j => fp.fl_sub acc (w j)) v =
        v * qv - ∑ j, (w j) * q j := by
  induction n with
  | zero =>
      intro w v hv
      refine ⟨1, Fin.elim0, ?_, ?_, ?_⟩
      · simp [p08GammaReal]
      · intro j; exact Fin.elim0 j
      · simp
  | succ n ih =>
      intro w v hv
      let w₀ : Fin n → ℝ := fun j => w j.castSucc
      have hp : (n : ℝ) * fp.u < 1 := by
        have hn : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
        nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
      have hu : fp.u < 1 := by
        have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
      obtain ⟨qv, q, hqv, hq, heq⟩ := ih w₀ v hp
      let A := Fin.foldl n (fun acc j => fp.fl_sub acc (w₀ j)) v
      obtain ⟨δ, hδ, hsub⟩ := fp.model_sub A (w (Fin.last n))
      let qv' := qv * (1 + δ)
      let q' : Fin (n + 1) → ℝ := Fin.snoc (fun j => q j * (1 + δ)) (1 + δ)
      refine ⟨qv', q', ?_, ?_, ?_⟩
      · have h := p08_relative_error_compose fp.u (n : ℝ) 1
          qv (1 + δ) fp.u_nonneg (by positivity) (by norm_num)
          (by simpa [Nat.cast_add] using hv) hqv
          (p08_relative_error_one fp.u δ fp.u_nonneg hu hδ)
        simpa [qv', Nat.cast_add] using h
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · have hmono := p08_gamma_real_mono fp.u 1 (n + 1 : ℕ)
            fp.u_nonneg (by norm_num)
            (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hv
          simpa [q', Fin.snoc_last] using
            (p08_relative_error_one fp.u δ fp.u_nonneg hu hδ).trans hmono
        · intro j
          have h := p08_relative_error_compose fp.u (n : ℝ) 1
            (q j) (1 + δ) fp.u_nonneg (by positivity) (by norm_num)
            (by simpa [Nat.cast_add] using hv) (hq j)
            (p08_relative_error_one fp.u δ fp.u_nonneg hu hδ)
          simpa [q', Fin.snoc_castSucc, Nat.cast_add] using h
      · rw [Fin.foldl_succ_last]
        change fp.fl_sub A (w (Fin.last n)) =
          v * qv' - ∑ j, w j * q' j
        rw [hsub, Fin.sum_univ_castSucc]
        simp only [qv', q', Fin.snoc_castSucc, Fin.snoc_last]
        have hA : A = v * qv - ∑ j, w₀ j * q j := heq
        rw [hA]
        have hsum : (∑ j, w j.castSucc * (q j * (1 + δ))) =
            (∑ j, w₀ j * q j) * (1 + δ) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [w₀]
          ring
        rw [hsum]
        ring

private theorem p08_vector_sub_fold_eval (fp : StandardFPModel)
    {n b : ℕ} (w : Fin n → Fin b → ℝ)
    (v : Fin b → ℝ) (α : Fin b) :
    (Fin.foldl n (fun acc j => fun β => fp.fl_sub (acc β) (w j β)) v) α =
      Fin.foldl n (fun acc j => fp.fl_sub acc (w j α)) (v α) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      exact congrArg (fun t => fp.fl_sub t (w (Fin.last n) α))
        (ih (fun j => w j.castSucc) v)

private theorem p08_rhs_coeff (fp : StandardFPModel)
    {p b r : ℕ} (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (i : Fin p) (α : Fin b) (hpvalid : (p : ℝ) * fp.u < 1) :
    ∃ qv : ℝ, ∃ q : Fin i.val → ℝ,
      |qv - 1| ≤ p08GammaReal (p : ℝ) fp.u ∧
      (∀ j, |q j - 1| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      trace.rhs i α = v i α * qv -
        ∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩)
            (Y i ⟨j.val, by omega⟩)
            (trace.x ⟨j.val, by omega⟩) α * q j := by
  let W : Fin i.val → Fin b → ℝ := fun j =>
    p08RoundedLowRankMatVec fp
      (X i ⟨j.val, by omega⟩)
      (Y i ⟨j.val, by omega⟩)
      (trace.x ⟨j.val, by omega⟩)
  have hi : (i.val : ℝ) * fp.u < 1 := by
    have hle : (i.val : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) fp.u_nonneg]
  have hfold : trace.rhs i α =
      Fin.foldl i.val (fun acc j => fp.fl_sub acc (W j α)) (v i α) := by
    have h := congrArg (fun w : Fin b → ℝ => w α) (trace.rhs_eq i)
    change trace.rhs i α =
      (Fin.foldl i.val (fun acc j => fun β => fp.fl_sub (acc β) (W j β)) (v i)) α at h
    exact h.trans (p08_vector_sub_fold_eval fp W (v i) α)
  obtain ⟨qv, q, hqv, hq, heq⟩ :=
    p08_rounded_sub_sum_coeff fp i.val (fun j => W j α) (v i α) hi
  have hmono := p08_gamma_real_mono fp.u (i.val : ℝ) (p : ℝ)
    fp.u_nonneg (by positivity) (by exact_mod_cast Nat.le_of_lt i.isLt) hpvalid
  refine ⟨qv, q, hqv.trans hmono, (fun j => (hq j).trans hmono), ?_⟩
  rw [hfold, heq]

private theorem p08_scaled_block_error_bound {b : ℕ}
    (T F : P08Matrix b) (q : Fin b → ℝ)
    (gP gD gC : ℝ) (hgP : 0 ≤ gP) (hgD : 0 ≤ gD)
    (hq : ∀ α, |q α - 1| ≤ gP)
    (hF : p08FrobNorm F ≤ gD * p08FrobNorm T)
    (hcomp : gP + gD + gP * gD ≤ gC) :
    let D : P08Matrix b := fun α β => q α * (T α β + F α β) - T α β
    p08FrobNorm D ≤ gC * p08FrobNorm T := by
  let A : P08Matrix b := fun α β => (q α - 1) * T α β
  let B : P08Matrix b := fun α β => q α * F α β
  let D : P08Matrix b := fun α β => q α * (T α β + F α β) - T α β
  have hD : D = p08RectAdd A B := by
    ext α β
    dsimp [D, A, B, p08RectAdd]
    ring
  have hA : p08FrobNorm A ≤ gP * p08FrobNorm T := by
    apply p08_rect_entrywise_bound T A gP hgP
    intro α β
    dsimp [A]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hq α) (abs_nonneg _)
  have hqabs (α : Fin b) : |q α| ≤ 1 + gP := by
    calc
      |q α| = |(q α - 1) + 1| := by ring
      _ ≤ |q α - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 1 + gP := by simp only [abs_one]; linarith [hq α]
  have hB : p08FrobNorm B ≤ (1 + gP) * p08FrobNorm F := by
    apply p08_rect_entrywise_bound F B (1 + gP) (by linarith)
    intro α β
    dsimp [B]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hqabs α) (abs_nonneg _)
  have hN : 0 ≤ p08FrobNorm T := Real.sqrt_nonneg _
  change p08FrobNorm D ≤ gC * p08FrobNorm T
  calc
    p08FrobNorm D = p08FrobNorm (p08RectAdd A B) := by rw [hD]
    _ ≤ p08FrobNorm A + p08FrobNorm B := p08_rect_add_bound A B
    _ ≤ gP * p08FrobNorm T + (1 + gP) * p08FrobNorm F := add_le_add hA hB
    _ ≤ gP * p08FrobNorm T + (1 + gP) * (gD * p08FrobNorm T) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hF (by linarith)) _
    _ = (gP + gD + gP * gD) * p08FrobNorm T := by ring
    _ ≤ gC * p08FrobNorm T := mul_le_mul_of_nonneg_right hcomp hN

private theorem p08_block_norm_as_sum {p b : ℕ}
    (A : P08BlockMatrix p b) :
    p08BlockFrobNorm A =
      Real.sqrt (∑ i : Fin p, ∑ j : Fin p, (p08FrobNorm (A i j)) ^ 2) := by
  unfold p08BlockFrobNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold p08FrobNorm p08RectFrobNorm
  symm
  exact Real.sq_sqrt (by positivity)

private theorem p08_block_norm_bound {p b : ℕ}
    (A E : P08BlockMatrix p b) (g : ℝ)
    (hg : 0 ≤ g)
    (h : ∀ i j, p08FrobNorm (E i j) ≤ g * p08FrobNorm (A i j)) :
    p08BlockFrobNorm E ≤ g * p08BlockFrobNorm A := by
  rw [p08_block_norm_as_sum E, p08_block_norm_as_sum A]
  have h' := p08_sqrt_sum_sq_le
    (fun ij : Fin p × Fin p => p08FrobNorm (E ij.1 ij.2))
    (fun ij : Fin p × Fin p => p08FrobNorm (A ij.1 ij.2))
    g hg (fun ij => by
      have he : 0 ≤ p08FrobNorm (E ij.1 ij.2) := Real.sqrt_nonneg _
      have ha : 0 ≤ p08FrobNorm (A ij.1 ij.2) := Real.sqrt_nonneg _
      simpa only [abs_of_nonneg he, abs_of_nonneg ha] using h ij.1 ij.2)
  simpa only [Fintype.sum_prod_type] using h'

private theorem p08_block_vec_norm_bound {p b : ℕ}
    (v dv : P08BlockVector p b) (g : ℝ)
    (hg : 0 ≤ g)
    (h : ∀ i α, |dv i α| ≤ g * |v i α|) :
    p08BlockVecNorm dv ≤ g * p08BlockVecNorm v := by
  have h' := p08_sqrt_sum_sq_le
    (fun ia : Fin p × Fin b => dv ia.1 ia.2)
    (fun ia : Fin p × Fin b => v ia.1 ia.2)
    g hg (fun ia => h ia.1 ia.2)
  simpa only [p08BlockVecNorm, Fintype.sum_prod_type] using h'

private theorem p08_sum_lower_diag {p : ℕ} (i : Fin p)
    (f : Fin p → ℝ)
    (hupper : ∀ j : Fin p, i < j → f j = 0) :
    (∑ j : Fin p, f j) =
      (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
  classical
  have hpoint (j : Fin p) : f j =
      (if j < i then f j else 0) + (if j = i then f i else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [h, ne_of_lt h]
    · subst j; simp
    · have hz := hupper j h
      simp [hz, not_lt.mpr (le_of_lt h), ne_of_gt h]
  calc
    (∑ j : Fin p, f j) =
        ∑ j : Fin p, ((if j < i then f j else 0) +
          (if j = i then f i else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hpoint j
    _ = (∑ j : Fin p, if j < i then f j else 0) +
        (∑ j : Fin p, if j = i then f i else 0) := Finset.sum_add_distrib
    _ = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
      rw [← p08_fin_sum_prefix]
      simp

private theorem p08_blr_row_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b)
    (trace : P08BLRTrace fp T X Y v)
    (i : Fin p)
    (hdiag : ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : p08LowerTriangular (T i i))
    (hupper : ∀ j : Fin p, i < j → T i j = 0)
    (hlr : ∀ j : Fin p, j < i → T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    ∃ DTrow : Fin p → P08Matrix b, ∃ dvrow : Fin b → ℝ,
      (∀ j, p08FrobNorm (DTrow j) ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) fp.u *
          p08FrobNorm (T i j)) ∧
      (∀ α, |dvrow α| ≤ p08GammaReal (p : ℝ) fp.u * |v i α|) ∧
      (∀ α, (∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DTrow j α β) * trace.x j β) = v i α + dvrow α) := by
  classical
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let c : ℝ := d + (p : ℝ)
  let gD : ℝ := p08GammaReal d fp.u
  let gP : ℝ := p08GammaReal (p : ℝ) fp.u
  let gC : ℝ := p08GammaReal c fp.u
  have hdnonneg : 0 ≤ d := add_nonneg (by positivity) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hdvalid : d * fp.u < 1 := by
    dsimp [d] at *
    nlinarith [mul_nonneg (show 0 ≤ (p : ℝ) by positivity) fp.u_nonneg]
  have hpvalid : (p : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hdnonneg fp.u_nonneg]
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have hbd : (b : ℝ) ≤ d := by
      dsimp [d]
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity)
        (Real.sqrt_nonneg (r : ℝ))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hbd) fp.u_nonneg]
  have hcvalid : c * fp.u < 1 := hvalid
  have hgD : 0 ≤ gD := p08_gamma_real_nonneg fp.u d fp.u_nonneg hdnonneg hdvalid
  have hgP : 0 ≤ gP := p08_gamma_real_nonneg fp.u (p : ℝ) fp.u_nonneg (by positivity) hpvalid
  have hgC : 0 ≤ gC := p08_gamma_real_nonneg fp.u c fp.u_nonneg (by dsimp [c]; positivity) hcvalid
  have hcomp : gP + gD + gP * gD ≤ gC := by
    have h := p08_gamma_real_compose fp.u (p : ℝ) d fp.u_nonneg
      (by positivity) hdnonneg (by simpa [c, add_comm] using hcvalid)
    simpa [gP, gD, gC, c, add_comm] using h
  obtain ⟨Fd, hFd, hdiagEq₀⟩ :=
    p08_forward_sub_error fp b (T i i) (trace.rhs i) hdiag hlower hbvalid
  have hdiagEq : ((T i i + Fd) *ᵥ trace.x i) = trace.rhs i := by
    rw [trace.x_eq i]
    exact hdiagEq₀
  have hOff (j : Fin p) (hji : j < i) : ∃ F : P08Matrix b,
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) =
        (T i j + F) *ᵥ trace.x j ∧
      p08FrobNorm F ≤ gD * p08FrobNorm (T i j) := by
    obtain ⟨F, hEq, hNorm⟩ :=
      p08_lowrank_matvec_error fp (X i j) (Y i j) (trace.x j)
        (hX j hji) hdvalid
    refine ⟨F, ?_, ?_⟩
    · simpa [hlr j hji] using hEq
    · simpa [gD, d, hlr j hji] using hNorm
  let Foff (j : Fin p) (hji : j < i) : P08Matrix b := Classical.choose (hOff j hji)
  have hOffEq (j : Fin p) (hji : j < i) :
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) =
        (T i j + Foff j hji) *ᵥ trace.x j :=
    (Classical.choose_spec (hOff j hji)).1
  have hOffNorm (j : Fin p) (hji : j < i) :
      p08FrobNorm (Foff j hji) ≤ gD * p08FrobNorm (T i j) :=
    (Classical.choose_spec (hOff j hji)).2
  have hQ (α : Fin b) : ∃ qv : ℝ, ∃ q : Fin i.val → ℝ,
      |qv - 1| ≤ gP ∧
      (∀ j, |q j - 1| ≤ gP) ∧
      trace.rhs i α = v i α * qv -
        ∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩)
            (Y i ⟨j.val, by omega⟩)
            (trace.x ⟨j.val, by omega⟩) α * q j := by
    simpa [gP] using p08_rhs_coeff fp T X Y v trace i α hpvalid
  choose qv q hqv hq hrhs using hQ
  let dvrow : Fin b → ℝ := fun α => v i α * (qv α - 1)
  let DTrow : Fin p → P08Matrix b := fun j =>
    if hji : j < i then
      fun α β => q α ⟨j.val, Fin.lt_def.mp hji⟩ *
          (T i j α β + Foff j hji α β) - T i j α β
    else if j = i then Fd else 0
  refine ⟨DTrow, dvrow, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j < i
    · have hqj (α : Fin b) :
          |q α ⟨j.val, Fin.lt_def.mp hji⟩ - 1| ≤ gP := hq α _
      have hbound := p08_scaled_block_error_bound (T i j) (Foff j hji)
        (fun α => q α ⟨j.val, Fin.lt_def.mp hji⟩)
        gP gD gC hgP hgD hqj (hOffNorm j hji) hcomp
      simpa [DTrow, hji, gC, c, d] using hbound
    · by_cases hjeq : j = i
      · subst j
        have hbc : (b : ℝ) ≤ c := by
          dsimp [c, d]
          nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) by positivity)
            (Real.sqrt_nonneg (r : ℝ))]
        have hmono := p08_gamma_real_mono fp.u (b : ℝ) c fp.u_nonneg
          (by positivity) hbc hcvalid
        have hN : 0 ≤ p08FrobNorm (T i i) := Real.sqrt_nonneg _
        have hFdNorm : p08FrobNorm Fd ≤
            p08GammaReal (b : ℝ) fp.u * p08FrobNorm (T i i) := by
          exact p08_rect_entrywise_bound (T i i) Fd _
            (p08_gamma_real_nonneg fp.u (b : ℝ) fp.u_nonneg (by positivity) hbvalid) hFd
        have hbound := hFdNorm.trans (mul_le_mul_of_nonneg_right hmono hN)
        simpa [DTrow, gC, c, d] using hbound
      · have hij : i < j := by omega
        have hzero := hupper j hij
        simp [DTrow, hji, hjeq, hzero, p08FrobNorm,
          p08RectFrobNorm]
  · intro α
    dsimp [dvrow]
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hqv α) (abs_nonneg _)
  · intro α
    let f : Fin p → ℝ := fun j =>
      ∑ β : Fin b, (T i j α β + DTrow j α β) * trace.x j β
    have habove (j : Fin p) (hij : i < j) : f j = 0 := by
      have hji : ¬j < i := not_lt.mpr (le_of_lt hij)
      have hne : j ≠ i := ne_of_gt hij
      simp [f, DTrow, hji, hne, hupper j hij]
    have hdiagF : f i = trace.rhs i α := by
      have hnot : ¬i < i := lt_irrefl i
      have h := congrArg (fun z : Fin b → ℝ => z α) hdiagEq
      simpa [f, DTrow, hnot, Matrix.mulVec, dotProduct] using h
    have hlowerF (j : Fin i.val) :
        f ⟨j.val, by omega⟩ =
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩)
            (Y i ⟨j.val, by omega⟩)
            (trace.x ⟨j.val, by omega⟩) α * q α j := by
      let jj : Fin p := ⟨j.val, by omega⟩
      have hji : jj < i := Fin.lt_def.mpr j.isLt
      have h := congrArg (fun z : Fin b → ℝ => z α) (hOffEq jj hji)
      change f jj = _
      dsimp [f]
      have hD : ∀ β : Fin b,
          DTrow jj α β = q α j * (T i jj α β + Foff jj hji α β) - T i jj α β := by
        intro β
        have hqidx : (⟨jj.val, Fin.lt_def.mp hji⟩ : Fin i.val) = j := Fin.ext rfl
        simp [DTrow, hji, hqidx]
      simp_rw [hD]
      calc
        (∑ β : Fin b,
            (T i jj α β + (q α j * (T i jj α β + Foff jj hji α β) - T i jj α β)) *
              trace.x jj β) =
            q α j * (∑ β : Fin b,
              (T i jj α β + Foff jj hji α β) * trace.x jj β) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro β hβ
                ring
        _ = p08RoundedLowRankMatVec fp (X i jj) (Y i jj) (trace.x jj) α * q α j := by
          have h' : (∑ β : Fin b,
              (T i jj α β + Foff jj hji α β) * trace.x jj β) =
              p08RoundedLowRankMatVec fp (X i jj) (Y i jj) (trace.x jj) α := by
            simpa only [Matrix.mulVec, dotProduct, Matrix.add_apply] using
              congrArg (· α) (hOffEq jj hji).symm
          rw [h']
          ring
    change (∑ j : Fin p, f j) = v i α + dvrow α
    calc
      (∑ j : Fin p, f j) = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i :=
        p08_sum_lower_diag i f habove
      _ = (∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩)
            (Y i ⟨j.val, by omega⟩)
            (trace.x ⟨j.val, by omega⟩) α * q α j) + trace.rhs i α := by
              rw [hdiagF]
              apply congrArg (· + trace.rhs i α)
              apply Finset.sum_congr rfl
              intro j hj
              exact hlowerF j
      _ = v i α * qv α := by linarith [hrhs α]
      _ = v i α + dvrow α := by dsimp [dvrow]; ring

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
  classical
  dsimp only
  have hrow (i : Fin p) :
      ∃ DTrow : Fin p → P08Matrix b, ∃ dvrow : Fin b → ℝ,
        (∀ j, p08FrobNorm (DTrow j) ≤
          p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) fp.u *
            p08FrobNorm (T i j)) ∧
        (∀ α, |dvrow α| ≤ p08GammaReal (p : ℝ) fp.u * |v i α|) ∧
        (∀ α, (∑ j : Fin p, ∑ β : Fin b,
          (T i j α β + DTrow j α β) * trace.x j β) = v i α + dvrow α) :=
    p08_blr_row_error fp T X Y v trace i (hdiag i) (hlower i)
      (hupper i) (hlr i) (hX i) hvalid
  choose DTrow dvrow hDTnorm hdvnorm hEq using hrow
  let DT : P08BlockMatrix p b := fun i j => DTrow i j
  let dv : P08BlockVector p b := fun i => dvrow i
  have hgC : 0 ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) fp.u := by
    apply p08_gamma_real_nonneg fp.u _ fp.u_nonneg
    · positivity
    · exact hvalid
  have hgP : 0 ≤ p08GammaReal (p : ℝ) fp.u := by
    have hpvalid : (p : ℝ) * fp.u < 1 := by
      have hd : 0 ≤ (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
      nlinarith [mul_nonneg hd fp.u_nonneg]
    exact p08_gamma_real_nonneg fp.u (p : ℝ) fp.u_nonneg (by positivity) hpvalid
  refine ⟨DT, dv, ?_, ?_, ?_⟩
  · funext ⟨i, α⟩
    change (∑ j : Fin p × Fin b,
      (T i j.1 α j.2 + DT i j.1 α j.2) * trace.x j.1 j.2) =
      v i α + dv i α
    rw [Fintype.sum_prod_type]
    exact hEq i α
  · exact p08_block_norm_bound T DT _ hgC (fun i j => hDTnorm i j)
  · exact p08_block_vec_norm_bound v dv _ hgP (fun i α => hdvnorm i α)

end VSCLReuse
