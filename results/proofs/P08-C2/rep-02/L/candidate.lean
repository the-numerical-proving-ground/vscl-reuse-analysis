import VSCLReuse.P08.Definitions
import NumStability.Algorithms.MatVec

namespace VSCLReuse

open scoped BigOperators Matrix Matrix.Norms.Frobenius

private def p08FP (fp : StandardFPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := fp.fl_sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := fp.model_sqrt

private lemma p08_round_eq (fp : StandardFPModel) {m n : ℕ}
    (M : P08RectMatrix m n) (w : Fin n → ℝ) :
    p08RoundedRectMatVec fp M w = NumStability.fl_matVec (p08FP fp) m n M w := rfl

private lemma p08_norm_eq {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = NumStability.frobNormRect M := rfl

private lemma p08_mat_norm_eq {n : ℕ} (M : P08Matrix n) :
    p08FrobNorm M = NumStability.frobNormRect M := rfl

private lemma p08_stage (fp : StandardFPModel) {m n : ℕ}
    (M : P08RectMatrix m n) (w : Fin n → ℝ)
    (hn : (n : ℝ) * fp.u < 1) :
    ∃ D : P08RectMatrix m n,
      p08RectFrobNorm D ≤ p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm M ∧
      p08RoundedRectMatVec fp M w = p08RectMatVec (p08RectAdd M D) w := by
  obtain ⟨D, hD, heq⟩ := NumStability.matVec_backward_error
    (p08FP fp) m n M w hn
  refine ⟨D, ?_, ?_⟩
  · change NumStability.frobNormRect D ≤
      NumStability.gamma (p08FP fp) n * NumStability.frobNormRect M
    simpa [NumStability.frobNormRect_eq_frobNormFn] using
      (NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        D M (NumStability.gamma_nonneg (p08FP fp) hn) hD)
  · funext i
    exact heq i

private lemma p08_X_norm {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  rw [Finset.sum_comm]
  have hdiag (j : Fin r) : (∑ i : Fin b, X i j ^ 2) = 1 := by
    simpa [pow_two] using hX j j
  simp_rw [hdiag]
  simp

private lemma p08_lowrank_norm {b r : ℕ} (X Y : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  have hQ : ∀ j k : Fin r,
      (∑ c : Fin b, (p08RectTranspose X) j c * (p08RectTranspose X) k c) =
        NumStability.idMatrix r j k := by
    intro j k
    exact hX j k
  have hswap :
      NumStability.frobNormSqRect (p08LowRankMatrix X Y) =
        NumStability.frobNormSqRect
          (NumStability.rectMatMul Y (p08RectTranspose X)) := by
    rw [← NumStability.frobNormSqRect_finiteTranspose
      (p08LowRankMatrix X Y)]
    congr 1
    funext i j
    unfold NumStability.finiteTranspose p08LowRankMatrix p08RectMatMul
      p08RectTranspose NumStability.rectMatMul
    apply Finset.sum_congr rfl
    intro k _
    ring
  change NumStability.frobNormRect (p08LowRankMatrix X Y) =
    NumStability.frobNormRect Y
  unfold NumStability.frobNormRect
  rw [hswap]
  congr 1
  exact NumStability.finiteFrobNormSq_rectRightOrthonormal Y
    (p08RectTranspose X) hQ

private lemma p08_norm_std {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = ‖M‖ := by
  rw [p08_norm_eq, NumStability.frobNormRect_eq_frobNormFn]
  rfl

private lemma p08_matvec_std {n : ℕ} (M : P08Matrix n) (w : P08Vector n) :
    p08MatVec M w = M *ᵥ w := rfl

private lemma p08_rectmatvec_std {m n : ℕ}
    (M : P08RectMatrix m n) (w : Fin n → ℝ) :
    p08RectMatVec M w = M *ᵥ w := rfl

private lemma p08_lowrank_std {b r : ℕ} (X Y : P08RectMatrix b r) :
    p08LowRankMatrix X Y = X * Yᵀ := rfl

private lemma p08_left_ortho_norm {b r p : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r p)
    (hX : p08OrthonormalColumns X) : ‖X * M‖ = ‖M‖ := by
  have hQ : ∀ j k : Fin r,
      (∑ c : Fin b, Xᵀ j c * Xᵀ k c) = NumStability.idMatrix r j k := by
    intro j k
    exact hX j k
  have hsq : NumStability.frobNormSqRect (Mᵀ * Xᵀ) =
      NumStability.frobNormSqRect Mᵀ := by
    exact NumStability.finiteFrobNormSq_rectRightOrthonormal Mᵀ Xᵀ hQ
  calc
    ‖X * M‖ = ‖(X * M)ᵀ‖ := (Matrix.frobenius_norm_transpose _).symm
    _ = ‖Mᵀ * Xᵀ‖ := by rw [Matrix.transpose_mul]
    _ = ‖Mᵀ‖ := by
      rw [← p08_norm_std, ← p08_norm_std]
      exact congrArg Real.sqrt hsq
    _ = ‖M‖ := Matrix.frobenius_norm_transpose M

private lemma p08_core {b r : ℕ} (fp : StandardFPModel)
    (X Y : P08RectMatrix b r) (v : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hb : (b : ℝ) * fp.u < 1) (hr : (r : ℝ) * fp.u < 1) :
    ∃ D : P08Matrix b,
      p08RoundedLowRankMatVec fp X Y v =
        p08MatVec (p08RectAdd (p08LowRankMatrix X Y) D) v ∧
      p08FrobNorm D ≤
        (p08GammaReal (b : ℝ) fp.u +
          p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) +
          p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
            Real.sqrt (r : ℝ)) * p08FrobNorm (p08LowRankMatrix X Y) := by
  let B : P08RectMatrix r b := Yᵀ
  let wHat := p08RoundedRectMatVec fp B v
  obtain ⟨DY, hDY, heqY⟩ := p08_stage fp B v hb
  obtain ⟨DX, hDX, heqX⟩ := p08_stage fp X wHat hr
  let D : P08Matrix b := X * DY + DX * B + DX * DY
  have hYnorm : ‖B‖ = p08FrobNorm (p08LowRankMatrix X Y) := by
    calc
      ‖B‖ = ‖Y‖ := by dsimp [B]; exact Matrix.frobenius_norm_transpose Y
      _ = p08RectFrobNorm Y := (p08_norm_std Y).symm
      _ = p08FrobNorm (p08LowRankMatrix X Y) :=
        (p08_lowrank_norm X Y hX).symm
  have hXnorm : ‖X‖ = Real.sqrt (r : ℝ) := by
    rw [← p08_norm_std]
    exact p08_X_norm X hX
  have hDY' : ‖DY‖ ≤ p08GammaReal (b : ℝ) fp.u *
      p08FrobNorm (p08LowRankMatrix X Y) := by
    rw [← p08_norm_std] 
    calc
      p08RectFrobNorm DY ≤ p08GammaReal (b : ℝ) fp.u *
          p08RectFrobNorm B := hDY
      _ = _ := by rw [p08_norm_std, hYnorm]
  have hDX' : ‖DX‖ ≤ p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) := by
    rw [← p08_norm_std]
    calc
      p08RectFrobNorm DX ≤ p08GammaReal (r : ℝ) fp.u *
          p08RectFrobNorm X := hDX
      _ = _ := by rw [p08_norm_std, hXnorm]
  have hterm1 : ‖X * DY‖ ≤ p08GammaReal (b : ℝ) fp.u *
      p08FrobNorm (p08LowRankMatrix X Y) := by
    rw [p08_left_ortho_norm X DY hX]
    exact hDY'
  have hterm2 : ‖DX * B‖ ≤
      (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) *
        p08FrobNorm (p08LowRankMatrix X Y) := by
    calc
      ‖DX * B‖ ≤ ‖DX‖ * ‖B‖ := Matrix.frobenius_norm_mul DX B
      _ ≤ (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right hDX' (norm_nonneg B)
      _ = _ := by rw [hYnorm]
  have hterm3 : ‖DX * DY‖ ≤
      (p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
        Real.sqrt (r : ℝ)) * p08FrobNorm (p08LowRankMatrix X Y) := by
    have hgr : 0 ≤ p08GammaReal (r : ℝ) fp.u :=
      NumStability.gamma_nonneg (p08FP fp) hr
    calc
      ‖DX * DY‖ ≤ ‖DX‖ * ‖DY‖ := Matrix.frobenius_norm_mul DX DY
      _ ≤ (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) *
          (p08GammaReal (b : ℝ) fp.u *
            p08FrobNorm (p08LowRankMatrix X Y)) := by
        gcongr
      _ = _ := by ring
  have hprod : (X + DX) * (B + DY) = X * B + D := by
    change (X + DX) * (B + DY) = X * B + (X * DY + DX * B + DX * DY)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  have heqY' : wHat = (B + DY) *ᵥ v := heqY
  have heqX' : p08RoundedRectMatVec fp X wHat = (X + DX) *ᵥ wHat := heqX
  have hresult : p08RoundedLowRankMatVec fp X Y v =
      p08MatVec (p08RectAdd (p08LowRankMatrix X Y) D) v := by
    change p08RoundedRectMatVec fp X wHat = (X * B + D) *ᵥ v
    rw [heqX', heqY', Matrix.mulVec_mulVec, hprod]
  refine ⟨D, hresult, ?_⟩
  rw [show p08FrobNorm D = ‖D‖ from p08_norm_std D]
  have htri : ‖D‖ ≤ ‖X * DY‖ + ‖DX * B‖ + ‖DX * DY‖ := by
    change ‖(X * DY + DX * B) + DX * DY‖ ≤ _
    calc
      ‖(X * DY + DX * B) + DX * DY‖ ≤
          ‖X * DY + DX * B‖ + ‖DX * DY‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_add_le _ _
  calc
    ‖D‖ ≤ ‖X * DY‖ + ‖DX * B‖ + ‖DX * DY‖ := htri
    _ ≤ p08GammaReal (b : ℝ) fp.u * p08FrobNorm (p08LowRankMatrix X Y) +
        (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) *
          p08FrobNorm (p08LowRankMatrix X Y) +
        (p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
          Real.sqrt (r : ℝ)) * p08FrobNorm (p08LowRankMatrix X Y) := by
          gcongr
    _ = _ := by ring

private lemma p08_r_le_rsqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => simp
  | succ n =>
      have hr : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hs : (1 : ℝ) ≤ Real.sqrt (↑(n + 1) : ℝ) := by
        simpa using (Real.sqrt_le_sqrt hr)
      have hn : (0 : ℝ) ≤ ↑(n + 1) := by positivity
      nlinarith

private lemma p08_gamma_nonneg (x u : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u)
    (hvalid : x * u < 1) : 0 ≤ p08GammaReal x u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hx hu) (by linarith)

private lemma p08_gamma_mono (x y u : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hu : 0 ≤ u) (hy : y * u < 1) :
    p08GammaReal x u ≤ p08GammaReal y u := by
  have hxvalid : x * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxy hu) hy
  have hdx : 0 < 1 - x * u := by linarith
  have hdy : 0 < 1 - y * u := by linarith
  unfold p08GammaReal
  rw [div_le_div_iff₀ hdx hdy]
  nlinarith [mul_le_mul_of_nonneg_right hxy hu]

private lemma p08_gamma_add (x y u : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hvalid : (x + y) * u < 1) :
    p08GammaReal x u + p08GammaReal y u +
      p08GammaReal x u * p08GammaReal y u ≤
        p08GammaReal (x + y) u := by
  let a := x * u
  let b := y * u
  have ha : 0 ≤ a := mul_nonneg hx hu
  have hb : 0 ≤ b := mul_nonneg hy hu
  have hc : a + b < 1 := by dsimp [a, b]; nlinarith [hvalid]
  have hda : 0 < 1 - a := by linarith
  have hdb : 0 < 1 - b := by linarith
  have hdc : 0 < 1 - (a + b) := by linarith
  have hdab : 0 < (1 - a) * (1 - b) := mul_pos hda hdb
  have heq : a / (1 - a) + b / (1 - b) +
      (a / (1 - a)) * (b / (1 - b)) =
        (a + b - a * b) / ((1 - a) * (1 - b)) := by
    field_simp
    ring
  unfold p08GammaReal
  have hab : (x + y) * u = a + b := by dsimp [a, b]; ring
  rw [hab]
  change a / (1 - a) + b / (1 - b) +
    (a / (1 - a)) * (b / (1 - b)) ≤
      (a + b) / (1 - (a + b))
  rw [heq, div_le_div_iff₀ hdab hdc]
  nlinarith [mul_nonneg ha hb]

private lemma p08_gamma_rsqrt_le (r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  let s := Real.sqrt (r : ℝ)
  let a := (r : ℝ) * u
  let b := ((r : ℝ) * s) * u
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hu
  have hab : a ≤ b := by
    dsimp [a, b]
    exact mul_le_mul_of_nonneg_right (p08_r_le_rsqrt r) hu
  have hb : 0 ≤ b := le_trans ha hab
  have hda : 0 < 1 - a := by dsimp [a] at *; linarith
  have hdb : 0 < 1 - b := by dsimp [b] at *; linarith
  have heq : (a / (1 - a)) * s = b / (1 - a) := by
    have hab' : b = a * s := by dsimp [a, b]; ring
    rw [hab']
    ring
  change (a / (1 - a)) * s ≤ b / (1 - b)
  rw [heq, div_le_div_iff₀ hda hdb]
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hab)]

private lemma p08_gamma_coefficient {b r : ℕ} (fp : StandardFPModel)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    p08GammaReal (b : ℝ) fp.u +
      p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) +
      p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
        Real.sqrt (r : ℝ) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
  let y := (r : ℝ) * Real.sqrt (r : ℝ)
  have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have hle : (b : ℝ) * fp.u ≤ ((b : ℝ) + y) * fp.u := by
      exact mul_le_mul_of_nonneg_right (by linarith) fp.u_nonneg
    dsimp [y] at hle
    exact lt_of_le_of_lt hle hvalid
  have hyvalid : y * fp.u < 1 := by
    have hle : y * fp.u ≤ ((b : ℝ) + y) * fp.u := by
      exact mul_le_mul_of_nonneg_right (by linarith) fp.u_nonneg
    dsimp [y] at hle ⊢
    exact lt_of_le_of_lt hle hvalid
  have hgb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
    p08_gamma_nonneg _ _ hb fp.u_nonneg hbvalid
  have hgrs : p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) ≤
      p08GammaReal y fp.u := by
    exact p08_gamma_rsqrt_le r fp.u fp.u_nonneg hyvalid
  have hadd := p08_gamma_add (b : ℝ) y fp.u hb hy fp.u_nonneg
    (by simpa [y] using hvalid)
  calc
    p08GammaReal (b : ℝ) fp.u +
        p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) +
        p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
          Real.sqrt (r : ℝ) ≤
      p08GammaReal (b : ℝ) fp.u + p08GammaReal y fp.u +
        p08GammaReal (b : ℝ) fp.u * p08GammaReal y fp.u := by
          nlinarith [mul_nonneg (show 0 ≤ 1 + p08GammaReal (b : ℝ) fp.u by linarith)
            (sub_nonneg.mpr hgrs)]
    _ ≤ p08GammaReal ((b : ℝ) + y) fp.u := hadd
    _ = _ := rfl

/-- Full Lemma 3.1: low-rank matrix-vector backward error and its A-relative bound. -/
theorem p08_c2_full_low_rank_matvec_error
    {b r : ℕ} (fp : StandardFPModel)
    (A : P08Matrix b) (X Y : P08RectMatrix b r) (v : P08Vector b)
    (ε β : ℝ) (hβ : 0 < β)
    (hX : p08OrthonormalColumns X)
    (happrox : p08FrobNorm (A - p08LowRankMatrix X Y) ≤ ε * β)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    let zHat := p08RoundedLowRankMatVec fp X Y v
    ∃ ΔAtilde ΔA : P08Matrix b,
      zHat = p08MatVec (p08RectAdd (p08LowRankMatrix X Y) ΔAtilde) v ∧
      p08FrobNorm ΔAtilde ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) ∧
      zHat = p08MatVec (p08RectAdd A ΔA) v ∧
      p08FrobNorm ΔA ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm A +
        ε * (1 + p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u) * β := by
  -- PROOF_START P08-C2-H001
  let T : P08Matrix b := p08LowRankMatrix X Y
  let g : ℝ := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  have hcost_nonneg : 0 ≤ (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) := by
    positivity
  have hg : 0 ≤ g := p08_gamma_nonneg _ _ hcost_nonneg fp.u_nonneg hvalid
  have hb : (b : ℝ) * fp.u < 1 := by
    have hcost : (b : ℝ) ≤ (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) := by
      have hrr : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcost fp.u_nonneg) hvalid
  have hr : (r : ℝ) * fp.u < 1 := by
    have hcost : (r : ℝ) ≤ (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) := by
      have h := p08_r_le_rsqrt r
      have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcost fp.u_nonneg) hvalid
  obtain ⟨D, hz, hD⟩ := p08_core fp X Y v hX hb hr
  have hcoeff := p08_gamma_coefficient fp hvalid
  have hTnonneg : 0 ≤ p08FrobNorm T := by
    rw [show p08FrobNorm T = ‖T‖ from p08_norm_std T]
    exact norm_nonneg T
  have hDbound : p08FrobNorm D ≤ g * p08FrobNorm T := by
    exact hD.trans (mul_le_mul_of_nonneg_right hcoeff hTnonneg)
  have happrox' : ‖A - T‖ ≤ ε * β := by
    change p08FrobNorm (A - T) ≤ ε * β at happrox
    rw [← p08_norm_std]
    exact happrox
  have hTbound : ‖T‖ ≤ ‖A‖ + ε * β := by
    calc
      ‖T‖ = ‖A - (A - T)‖ := by congr 1; abel
      _ ≤ ‖A‖ + ‖A - T‖ := norm_sub_le A (A - T)
      _ ≤ ‖A‖ + ε * β := by linarith
  let DA : P08Matrix b := D - (A - T)
  have hmatrix : A + DA = T + D := by
    dsimp [DA]
    abel
  have hzA : p08RoundedLowRankMatVec fp X Y v =
      p08MatVec (p08RectAdd A DA) v := by
    change p08RoundedLowRankMatVec fp X Y v = (T + D) *ᵥ v at hz
    change p08RoundedLowRankMatVec fp X Y v = (A + DA) *ᵥ v
    rw [hmatrix]
    exact hz
  have hDAbound : p08FrobNorm DA ≤
      g * p08FrobNorm A + ε * (1 + g) * β := by
    have hD' : ‖D‖ ≤ g * (‖A‖ + ε * β) := by
      have hd0 : ‖D‖ ≤ g * ‖T‖ := by
        rw [← p08_norm_std]
        rw [← p08_norm_std]
        exact hDbound
      exact hd0.trans (mul_le_mul_of_nonneg_left hTbound hg)
    calc
      p08FrobNorm DA = ‖DA‖ := p08_norm_std DA
      _ ≤ ‖D‖ + ‖A - T‖ := by
        dsimp [DA]
        exact norm_sub_le D (A - T)
      _ ≤ g * (‖A‖ + ε * β) + ε * β := by linarith
      _ = g * p08FrobNorm A + ε * (1 + g) * β := by
        rw [show p08FrobNorm A = ‖A‖ from p08_norm_std A]
        ring
  dsimp
  exact ⟨D, DA, hz, hDbound, hzA, hDAbound⟩

end VSCLReuse
