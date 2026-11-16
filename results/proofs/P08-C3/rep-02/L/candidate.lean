import VSCLReuse.P08.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatVec
import NumStability.Analysis.SubtractionFold
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Source.Higham.Chapter20.Problem05.MGSStability

namespace VSCLReuse

open scoped BigOperators

set_option maxHeartbeats 400000

private def p08ToFP (fp : StandardFPModel) : NumStability.FPModel where
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

private theorem p08_roundedMatVec_eq_fl_matVec (fp : StandardFPModel)
    (m n : ℕ) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    roundedMatVec fp m n A x =
      NumStability.fl_matVec (p08ToFP fp) m n A x := rfl

private theorem p08_steps_eq (fp : StandardFPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (z : Fin n → ℝ),
      roundedForwardSubSteps fp n A x k hk z =
        NumStability.fl_forwardSub_steps (p08ToFP fp) n A x k hk z := by
  intro k
  induction k with
  | zero => intro hk z; rfl
  | succ k ih =>
    intro hk z
    unfold roundedForwardSubSteps NumStability.fl_forwardSub_steps
    exact ih _ _

private theorem p08_forwardSub_eq_fl_forwardSub (fp : StandardFPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    roundedForwardSub fp n A x =
      NumStability.fl_forwardSub (p08ToFP fp) n A x := by
  exact p08_steps_eq fp n A x n (le_refl n) (fun _ => 0)

private theorem p08_orthonormal_to_num {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    NumStability.GramSchmidtOrthonormalColumns X := by
  intro j k
  simpa [NumStability.GramSchmidtOrthonormalColumns,
    NumStability.rectangularGram, NumStability.matMulRect,
    NumStability.finiteTranspose, NumStability.idMatrix] using hX j k

private theorem p08_frob_eq_num {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = NumStability.frobNormRect A := rfl

private theorem p08_orthonormal_frob_sq {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    (∑ i : Fin b, ∑ j : Fin r, X i j ^ 2) = (r : ℝ) := by
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin r, ∑ i : Fin b, X i j ^ 2)
        = ∑ _j : Fin r, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            simpa only [pow_two, if_pos rfl] using hX j j
    _ = r := by simp

private theorem p08_orthonormal_frob {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  simp [p08RectFrobNorm, p08_orthonormal_frob_sq X hX]

private theorem p08_orthonormal_frob_mul {b r n : ℕ}
    (X : P08RectMatrix b r) (Y : P08RectMatrix r n)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X Y) = p08RectFrobNorm Y := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  simp only [p08RectFrobNorm, Real.sq_sqrt (Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin r)))]
  apply Finset.sum_congr rfl
  intro j _
  have h := NumStability.Problem20_5.orthonormal_columns_action_norm_eq X
    (p08_orthonormal_to_num X hX) (fun k => Y k j)
  have hsq := congrArg (fun t : ℝ => t ^ 2) h
  simpa [NumStability.vecNorm2_sq, NumStability.vecNorm2Sq,
    NumStability.rectMatMulVec, p08RectMatMul] using hsq

private theorem p08_frob_transpose {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  unfold p08RectFrobNorm p08RectTranspose
  rw [Finset.sum_comm]

private theorem p08_frob_le_of_rel {m n : ℕ}
    (A E : P08RectMatrix m n) (η : ℝ) (hη : 0 ≤ η)
    (hE : ∀ i j, |E i j| ≤ η * |A i j|) :
    p08RectFrobNorm E ≤ η * p08RectFrobNorm A := by
  rw [p08_frob_eq_num, p08_frob_eq_num]
  have h := NumStability.frobNormRect_le_of_entry_abs_le E
    (fun i j => η * |A i j|)
    (fun i j => mul_nonneg hη (abs_nonneg _)) hE
  convert h using 1
  rw [NumStability.frobNormRect_smul, abs_of_nonneg hη,
    NumStability.frobNormRect_abs]

private theorem p08_gamma_real_sum (a b u : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hvalid : (a + b) * u < 1) :
    p08GammaReal a u + p08GammaReal b u +
      p08GammaReal a u * p08GammaReal b u ≤
        p08GammaReal (a + b) u := by
  have ha0 : 0 ≤ a * u := mul_nonneg ha hu
  have hb0 : 0 ≤ b * u := mul_nonneg hb hu
  have had : 0 < 1 - a * u := by nlinarith
  have hbd : 0 < 1 - b * u := by nlinarith
  have habd : 0 < 1 - (a + b) * u := by linarith
  have hiden : p08GammaReal (a + b) u -
      (p08GammaReal a u + p08GammaReal b u +
        p08GammaReal a u * p08GammaReal b u) =
      (a * u * (b * u)) /
        ((1 - (a + b) * u) * (1 - a * u) * (1 - b * u)) := by
    unfold p08GammaReal
    field_simp
    ring
  have hn : 0 ≤ (a * u * (b * u)) /
      ((1 - (a + b) * u) * (1 - a * u) * (1 - b * u)) := by
    exact div_nonneg (mul_nonneg ha0 hb0)
      (le_of_lt (mul_pos (mul_pos habd had) hbd))
  linarith

private theorem p08_gamma_real_sqrt (r : ℕ) (u : ℝ)
    (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  by_cases hr : r = 0
  · subst r
    simp [p08GammaReal]
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
  have hs : 1 ≤ Real.sqrt (r : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg (r : ℝ)]
  have hru : 0 ≤ (r : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hden1 : 0 < 1 - (r : ℝ) * u := by
    nlinarith [mul_nonneg hru (sub_nonneg.mpr hs)]
  have hden2 : 0 < 1 - ((r : ℝ) * Real.sqrt (r : ℝ)) * u := by linarith
  unfold p08GammaReal
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hden1 hden2).2
  have hnumer : (r : ℝ) * u * Real.sqrt (r : ℝ) =
      ((r : ℝ) * Real.sqrt (r : ℝ)) * u := by ring
  rw [hnumer]
  have hden : 1 - ((r : ℝ) * Real.sqrt (r : ℝ)) * u ≤
      1 - (r : ℝ) * u := by nlinarith [mul_nonneg hru (sub_nonneg.mpr hs)]
  exact mul_le_mul_of_nonneg_left hden
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hu)

private theorem p08_gamma_real_mono (a b u : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u)
    (hvalid : b * u < 1) :
    p08GammaReal a u ≤ p08GammaReal b u := by
  have hau : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
  have hdena : 0 < 1 - a * u := by linarith
  have hdenb : 0 < 1 - b * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ hdena hdenb).2
  nlinarith

private theorem p08_lowrank_matvec_error (fp : StandardFPModel)
    {b r : ℕ} (X Y : P08RectMatrix b r) (x : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hb : (b : ℝ) * fp.u < 1) (hr : (r : ℝ) * fp.u < 1) :
    ∃ F : P08Matrix b,
      (∀ i, p08RoundedLowRankMatVec fp X Y x i =
        ∑ j : Fin b, (p08LowRankMatrix X Y i j + F i j) * x j) ∧
      p08RectFrobNorm F ≤
        (NumStability.gamma (p08ToFP fp) b +
          NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) +
          NumStability.gamma (p08ToFP fp) b *
            (NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ))) *
          p08RectFrobNorm (p08LowRankMatrix X Y) := by
  let Z : P08RectMatrix r b := p08RectTranspose Y
  let z : P08Vector r := p08RoundedRectMatVec fp Z x
  let γb := NumStability.gamma (p08ToFP fp) b
  let γr := NumStability.gamma (p08ToFP fp) r
  obtain ⟨E₁, hE₁, hz⟩ :=
    NumStability.matVec_backward_error (p08ToFP fp) r b Z x hb
  obtain ⟨E₂, hE₂, hw⟩ :=
    NumStability.matVec_backward_error (p08ToFP fp) b r X z hr
  have hγb : 0 ≤ γb := NumStability.gamma_nonneg (p08ToFP fp) hb
  have hγr : 0 ≤ γr := NumStability.gamma_nonneg (p08ToFP fp) hr
  have hE₁norm : p08RectFrobNorm E₁ ≤ γb * p08RectFrobNorm Z :=
    p08_frob_le_of_rel Z E₁ γb hγb hE₁
  have hE₂norm : p08RectFrobNorm E₂ ≤ γr * p08RectFrobNorm X :=
    p08_frob_le_of_rel X E₂ γr hγr hE₂
  let A : P08RectMatrix b r := fun i k => X i k + E₂ i k
  let B : P08RectMatrix r b := fun k j => Z k j + E₁ k j
  let F : P08Matrix b := fun i j => p08RectMatMul A B i j - p08LowRankMatrix X Y i j
  have hz' : z = NumStability.rectMatMulVec B x := by
    funext k
    simpa [z, B, Z, p08RoundedRectMatVec, p08_roundedMatVec_eq_fl_matVec,
      NumStability.rectMatMulVec] using hz k
  have hw' : p08RoundedLowRankMatVec fp X Y x =
      NumStability.rectMatMulVec A z := by
    funext i
    simpa [p08RoundedLowRankMatVec, p08RoundedRectMatVec,
      p08_roundedMatVec_eq_fl_matVec, A, z, Z,
      NumStability.rectMatMulVec] using hw i
  refine ⟨F, ?_, ?_⟩
  · intro i
    calc
      p08RoundedLowRankMatVec fp X Y x i
          = NumStability.rectMatMulVec A z i := congrFun hw' i
      _ = NumStability.rectMatMulVec A (NumStability.rectMatMulVec B x) i := by rw [hz']
      _ = NumStability.rectMatMulVec (NumStability.rectMatMul A B) x i := by
            rw [NumStability.rectMatMulVec_rectMatMul]
      _ = ∑ j : Fin b, (p08LowRankMatrix X Y i j + F i j) * x j := by
            simp only [NumStability.rectMatMulVec, NumStability.rectMatMul,
              p08RectMatMul, F]
            apply Finset.sum_congr rfl
            intro j _
            ring
  · have hF : F = fun i j =>
        NumStability.rectMatMul X E₁ i j +
          (NumStability.rectMatMul E₂ Z i j +
            NumStability.rectMatMul E₂ E₁ i j) := by
      funext i j
      change NumStability.rectMatMul (fun i k => X i k + E₂ i k)
          (fun k j => Z k j + E₁ k j) i j -
          NumStability.rectMatMul X Z i j = _
      rw [NumStability.rectMatMul_add_left,
        NumStability.rectMatMul_add_right,
        NumStability.rectMatMul_add_right]
      ring
    have hXZ : p08RectFrobNorm (p08LowRankMatrix X Y) =
        p08RectFrobNorm Z := by
      exact p08_orthonormal_frob_mul X Z hX
    have hXnorm : p08RectFrobNorm X = Real.sqrt (r : ℝ) :=
      p08_orthonormal_frob X hX
    have hXE : p08RectFrobNorm (NumStability.rectMatMul X E₁) ≤
        γb * p08RectFrobNorm Z := by
      calc
        p08RectFrobNorm (NumStability.rectMatMul X E₁)
            ≤ 1 * p08RectFrobNorm E₁ := by
              exact NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
                X E₁ (by norm_num)
                ((p08_orthonormal_to_num X hX).rectOpNorm2Le_one)
        _ = p08RectFrobNorm E₁ := one_mul _
        _ ≤ γb * p08RectFrobNorm Z := hE₁norm
    have hE₂Z : p08RectFrobNorm (NumStability.rectMatMul E₂ Z) ≤
        (γr * Real.sqrt (r : ℝ)) * p08RectFrobNorm Z := by
      calc
        p08RectFrobNorm (NumStability.rectMatMul E₂ Z)
            ≤ p08RectFrobNorm E₂ * p08RectFrobNorm Z :=
              NumStability.frobNormRect_rectMatMul_le E₂ Z
        _ ≤ (γr * p08RectFrobNorm X) * p08RectFrobNorm Z :=
              mul_le_mul_of_nonneg_right hE₂norm
                (NumStability.frobNormRect_nonneg Z)
        _ = _ := by rw [hXnorm]
    have hE₂E₁ : p08RectFrobNorm (NumStability.rectMatMul E₂ E₁) ≤
        (γb * (γr * Real.sqrt (r : ℝ))) * p08RectFrobNorm Z := by
      calc
        p08RectFrobNorm (NumStability.rectMatMul E₂ E₁)
            ≤ p08RectFrobNorm E₂ * p08RectFrobNorm E₁ :=
              NumStability.frobNormRect_rectMatMul_le E₂ E₁
        _ ≤ (γr * p08RectFrobNorm X) * p08RectFrobNorm E₁ :=
              mul_le_mul_of_nonneg_right hE₂norm
                (NumStability.frobNormRect_nonneg E₁)
        _ ≤ (γr * p08RectFrobNorm X) * (γb * p08RectFrobNorm Z) :=
              mul_le_mul_of_nonneg_left hE₁norm
                (mul_nonneg hγr (NumStability.frobNormRect_nonneg X))
        _ = _ := by rw [hXnorm]; ring
    let U : P08Matrix b := NumStability.rectMatMul X E₁
    let V : P08Matrix b := NumStability.rectMatMul E₂ Z
    let W : P08Matrix b := NumStability.rectMatMul E₂ E₁
    have htri : p08RectFrobNorm (fun i j => U i j + (V i j + W i j)) ≤
        p08RectFrobNorm U + (p08RectFrobNorm V + p08RectFrobNorm W) := by
      calc
        p08RectFrobNorm (fun i j => U i j + (V i j + W i j))
            ≤ p08RectFrobNorm U + p08RectFrobNorm (fun i j => V i j + W i j) :=
              NumStability.frobNormRect_add_le U _
        _ ≤ p08RectFrobNorm U + (p08RectFrobNorm V + p08RectFrobNorm W) :=
              add_le_add_right (NumStability.frobNormRect_add_le V W) _
    have hbound : p08RectFrobNorm U + (p08RectFrobNorm V + p08RectFrobNorm W) ≤
        γb * p08RectFrobNorm Z +
          ((γr * Real.sqrt (r : ℝ)) * p08RectFrobNorm Z +
            (γb * (γr * Real.sqrt (r : ℝ))) * p08RectFrobNorm Z) :=
      add_le_add hXE (add_le_add hE₂Z hE₂E₁)
    rw [hF]
    calc
      p08RectFrobNorm (fun i j => U i j + (V i j + W i j))
          ≤ γb * p08RectFrobNorm Z +
              ((γr * Real.sqrt (r : ℝ)) * p08RectFrobNorm Z +
                (γb * (γr * Real.sqrt (r : ℝ))) * p08RectFrobNorm Z) :=
            le_trans htri hbound
      _ = (γb + γr * Real.sqrt (r : ℝ) +
            γb * (γr * Real.sqrt (r : ℝ))) *
            p08RectFrobNorm (p08LowRankMatrix X Y) := by
            rw [hXZ]
            ring

private theorem p08_lowrank_matvec_gamma_error (fp : StandardFPModel)
    {b r : ℕ} (X Y : P08RectMatrix b r) (x : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      (∀ i, p08RoundedLowRankMatVec fp X Y x i =
        ∑ j : Fin b, (p08LowRankMatrix X Y i j + F i j) * x j) ∧
      p08RectFrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08RectFrobNorm (p08LowRankMatrix X Y) := by
  let s : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hb : (b : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hs fp.u_nonneg]
  have hsvalid : s * fp.u < 1 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg b) fp.u_nonneg]
  have hr : (r : ℝ) * fp.u < 1 := by
    by_cases hr0 : r = 0
    · subst r; simpa using hsvalid
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr0)
      have hsr : 1 ≤ Real.sqrt (r : ℝ) := by
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), Real.sqrt_nonneg (r : ℝ)]
      nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg r) fp.u_nonneg)
        (sub_nonneg.mpr hsr)]
  obtain ⟨F, hEq, hBound⟩ := p08_lowrank_matvec_error fp X Y x hX hb hr
  refine ⟨F, hEq, ?_⟩
  let γb : ℝ := p08GammaReal (b : ℝ) fp.u
  let γr : ℝ := p08GammaReal (r : ℝ) fp.u
  let γs : ℝ := p08GammaReal s fp.u
  have hγb : 0 ≤ γb := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hγs : 0 ≤ γs := by
    exact div_nonneg (mul_nonneg hs fp.u_nonneg) (by linarith)
  have hsr : γr * Real.sqrt (r : ℝ) ≤ γs :=
    p08_gamma_real_sqrt r fp.u fp.u_nonneg hsvalid
  have hγsum : γb + γs + γb * γs ≤
      p08GammaReal ((b : ℝ) + s) fp.u :=
    p08_gamma_real_sum (b : ℝ) s fp.u (Nat.cast_nonneg _) hs fp.u_nonneg hvalid
  have hcoef : γb + γr * Real.sqrt (r : ℝ) +
      γb * (γr * Real.sqrt (r : ℝ)) ≤
      p08GammaReal ((b : ℝ) + s) fp.u := by
    have htmp : γb + γr * Real.sqrt (r : ℝ) +
        γb * (γr * Real.sqrt (r : ℝ)) ≤ γb + γs + γb * γs := by
      nlinarith [mul_nonneg hγb (sub_nonneg.mpr hsr)]
    exact le_trans htmp hγsum
  have hM : 0 ≤ p08RectFrobNorm (p08LowRankMatrix X Y) := Real.sqrt_nonneg _
  calc
    p08RectFrobNorm F ≤
        (γb + γr * Real.sqrt (r : ℝ) + γb * (γr * Real.sqrt (r : ℝ))) *
          p08RectFrobNorm (p08LowRankMatrix X Y) := by
            simpa only [γb, γr, NumStability.gamma, p08ToFP, p08GammaReal] using hBound
    _ ≤ p08GammaReal ((b : ℝ) + s) fp.u *
          p08RectFrobNorm (p08LowRankMatrix X Y) :=
        mul_le_mul_of_nonneg_right hcoef hM
    _ = _ := rfl

private theorem p08_vector_fold_apply (fp : StandardFPModel)
    {m b : ℕ} (f : Fin m → Fin b → ℝ) (v : Fin b → ℝ) (α : Fin b) :
    (Fin.foldl m
      (fun acc j => fun β => fp.fl_sub (acc β) (f j β)) v) α =
      Fin.foldl m (fun acc j => fp.fl_sub acc (f j α)) (v α) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    change fp.fl_sub
        ((Fin.foldl m (fun acc j => fun β => fp.fl_sub (acc β) (f j.castSucc β)) v) α)
        (f (Fin.last m) α) =
      fp.fl_sub
        (Fin.foldl m (fun acc j => fp.fl_sub acc (f j.castSucc α)) (v α))
        (f (Fin.last m) α)
    rw [ih]

private theorem p08_rhs_fold_error (fp : StandardFPModel)
    {p b r : ℕ} (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) (trace : P08BLRTrace fp T X Y v)
    (hvalidp : (p : ℝ) * fp.u < 1) (i : Fin p) (α : Fin b) :
    ∃ Θ : ℝ, ∃ θ : Fin i.val → ℝ,
      |Θ| ≤ p08GammaReal (p : ℝ) fp.u ∧
      (∀ j, |θ j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      trace.rhs i α = v i α * (1 + Θ) -
        ∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
            (trace.x ⟨j.val, by omega⟩) α * (1 + θ j) := by
  let w : Fin i.val → ℝ := fun j =>
    p08RoundedLowRankMatVec fp
      (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
      (trace.x ⟨j.val, by omega⟩) α
  have hvalidi : NumStability.gammaValid (p08ToFP fp) i.val := by
    apply NumStability.gammaValid_mono (p08ToFP fp) (Nat.le_of_lt i.isLt)
    exact hvalidp
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    NumStability.fl_sub_sum_error_init (p08ToFP fp) i.val w (v i α) hvalidi
  have hγmono : NumStability.gamma (p08ToFP fp) i.val ≤
      NumStability.gamma (p08ToFP fp) p :=
    NumStability.gamma_mono (p08ToFP fp) (Nat.le_of_lt i.isLt) hvalidp
  refine ⟨Θ, θ, le_trans hΘ hγmono, (fun j => le_trans (hθ j) hγmono), ?_⟩
  rw [trace.rhs_eq i]
  simpa only [w, NumStability.gamma, p08ToFP, p08GammaReal] using
    (p08_vector_fold_apply fp
      (fun j β => p08RoundedLowRankMatVec fp
        (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
        (trace.x ⟨j.val, by omega⟩) β) (v i) α).trans hfold

private theorem p08_diag_solve_error (fp : StandardFPModel)
    {b : ℕ} (L : P08Matrix b) (rhs : P08Vector b)
    (hdiag : ∀ α : Fin b, L α α ≠ 0)
    (hlower : p08LowerTriangular L)
    (hvalidb : (b : ℝ) * fp.u < 1) :
    ∃ E : P08Matrix b,
      (∀ α, ∑ β : Fin b, (L α β + E α β) *
        roundedForwardSub fp b L rhs β = rhs α) ∧
      p08RectFrobNorm E ≤
        p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm L := by
  obtain ⟨E, hE, hEq⟩ := NumStability.forwardSub_backward_error
    (p08ToFP fp) b L rhs hdiag hlower hvalidb
  have hγ : 0 ≤ NumStability.gamma (p08ToFP fp) b :=
    NumStability.gamma_nonneg (p08ToFP fp) hvalidb
  refine ⟨E, ?_, ?_⟩
  · intro α
    rw [p08_forwardSub_eq_fl_forwardSub]
    exact hEq α
  · simpa only [NumStability.gamma, p08ToFP, p08GammaReal] using
      p08_frob_le_of_rel L E _ hγ hE

private theorem p08_scaled_block_error {b : ℕ}
    (T F : P08Matrix b) (θ : Fin b → ℝ) (a e : ℝ)
    (ha : 0 ≤ a) (he : 0 ≤ e)
    (hθ : ∀ α, |θ α| ≤ e)
    (hF : p08RectFrobNorm F ≤ a * p08RectFrobNorm T) :
    p08RectFrobNorm
      (fun α β => (T α β + F α β) * (1 + θ α) - T α β) ≤
      (a + e + a * e) * p08RectFrobNorm T := by
  let U : P08Matrix b := fun α β => θ α * T α β
  let V : P08Matrix b := fun α β => (1 + θ α) * F α β
  have hUentry : ∀ α β, |U α β| ≤ e * |T α β| := by
    intro α β
    simpa only [U, abs_mul] using
      mul_le_mul_of_nonneg_right (hθ α) (abs_nonneg (T α β))
  have hVentry : ∀ α β, |V α β| ≤ (1 + e) * |F α β| := by
    intro α β
    have habs : |1 + θ α| ≤ 1 + e := by
      calc
        |1 + θ α| ≤ |(1 : ℝ)| + |θ α| := abs_add_le _ _
        _ ≤ 1 + e := by simpa using add_le_add_left (hθ α) 1
    simpa only [V, abs_mul] using
      mul_le_mul_of_nonneg_right habs (abs_nonneg (F α β))
  have hU : p08RectFrobNorm U ≤ e * p08RectFrobNorm T :=
    p08_frob_le_of_rel T U e he hUentry
  have hV : p08RectFrobNorm V ≤ (1 + e) * p08RectFrobNorm F :=
    p08_frob_le_of_rel F V (1 + e) (by linarith) hVentry
  have hnormT : 0 ≤ p08RectFrobNorm T := Real.sqrt_nonneg _
  have hrewrite :
      (fun α β => (T α β + F α β) * (1 + θ α) - T α β) =
      (fun α β => U α β + V α β) := by
    funext α β
    dsimp [U, V]
    ring
  rw [hrewrite]
  calc
    p08RectFrobNorm (fun α β => U α β + V α β)
        ≤ p08RectFrobNorm U + p08RectFrobNorm V :=
          NumStability.frobNormRect_add_le U V
    _ ≤ e * p08RectFrobNorm T + (1 + e) * p08RectFrobNorm F :=
          add_le_add hU hV
    _ ≤ e * p08RectFrobNorm T + (1 + e) * (a * p08RectFrobNorm T) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hF (show 0 ≤ 1 + e by linarith)) _
    _ = (a + e + a * e) * p08RectFrobNorm T := by ring

private theorem p08_rect_frob_sq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
  unfold p08RectFrobNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg _)))

private theorem p08_block_frob_sq {p b : ℕ} (A : P08BlockMatrix p b) :
    p08BlockFrobNorm A ^ 2 =
      ∑ i : Fin p, ∑ j : Fin p, ∑ α : Fin b, ∑ β : Fin b,
        A i j α β ^ 2 := by
  unfold p08BlockFrobNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun α _ =>
        Finset.sum_nonneg (fun β _ => sq_nonneg _)))))

private theorem p08_block_frob_le_of_blocks {p b : ℕ}
    (A E : P08BlockMatrix p b) (g : ℝ) (hg : 0 ≤ g)
    (hblock : ∀ i j, p08RectFrobNorm (E i j) ≤
      g * p08RectFrobNorm (A i j)) :
    p08BlockFrobNorm E ≤ g * p08BlockFrobNorm A := by
  have hsqblock : ∀ i j,
      (∑ α : Fin b, ∑ β : Fin b, E i j α β ^ 2) ≤
        g ^ 2 * (∑ α : Fin b, ∑ β : Fin b, A i j α β ^ 2) := by
    intro i j
    have he := hblock i j
    have hEn : 0 ≤ p08RectFrobNorm (E i j) := Real.sqrt_nonneg _
    have hAn : 0 ≤ g * p08RectFrobNorm (A i j) :=
      mul_nonneg hg (Real.sqrt_nonneg _)
    have hsquare : p08RectFrobNorm (E i j) ^ 2 ≤
        (g * p08RectFrobNorm (A i j)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he) (add_nonneg hEn hAn)]
    rw [p08_rect_frob_sq, mul_pow, p08_rect_frob_sq] at hsquare
    simpa only [pow_two, mul_assoc] using hsquare
  have hsqsum :
      (∑ i : Fin p, ∑ j : Fin p, ∑ α : Fin b, ∑ β : Fin b,
          E i j α β ^ 2) ≤
        g ^ 2 * (∑ i : Fin p, ∑ j : Fin p, ∑ α : Fin b, ∑ β : Fin b,
          A i j α β ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact hsqblock i j
  have hsq : p08BlockFrobNorm E ^ 2 ≤
      (g * p08BlockFrobNorm A) ^ 2 := by
    rw [p08_block_frob_sq, mul_pow, p08_block_frob_sq]
    exact hsqsum
  have hEn : 0 ≤ p08BlockFrobNorm E := Real.sqrt_nonneg _
  have hAn : 0 ≤ g * p08BlockFrobNorm A :=
    mul_nonneg hg (Real.sqrt_nonneg _)
  nlinarith

private theorem p08_sum_fin_lt {p : ℕ} (i : Fin p) (f : Fin p → ℝ) :
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin p => j.val < i.val)), f j := by
  have hinj : ∀ a : Fin i.val, a ∈ Finset.univ →
      ∀ b : Fin i.val, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin p) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simpa using congrArg Fin.val hab)
  have himg : Finset.image (fun (j : Fin i.val) =>
      (⟨j.val, by omega⟩ : Fin p)) Finset.univ =
      Finset.univ.filter (fun j : Fin p => j.val < i.val) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨k, rfl⟩
      simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

private theorem p08_sum_lower_diag {p : ℕ} (i : Fin p) (f : Fin p → ℝ)
    (hupper : ∀ j : Fin p, i.val < j.val → f j = 0) :
    (∑ j : Fin p, f j) =
      (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
  let S : Finset (Fin p) := Finset.univ.filter (fun j => j.val ≤ i.val)
  have hi : i ∈ S := by simp [S]
  have hS : S.erase i = Finset.univ.filter (fun j : Fin p => j.val < i.val) := by
    ext j
    simp only [Finset.mem_erase, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hne : j ≠ i := h.1
      omega
    · intro h
      refine ⟨?_, by omega⟩
      intro heq
      subst j
      omega
  have hupper_sum :
      (∑ j ∈ (Finset.univ.filter (fun j : Fin p => ¬j.val ≤ i.val)), f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
    exact hupper j hj
  calc
    (∑ j : Fin p, f j)
        = (∑ j ∈ S, f j) +
            (∑ j ∈ (Finset.univ.filter (fun j : Fin p => ¬j.val ≤ i.val)),
              f j) := by
          simpa only [S] using
            (Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun j : Fin p => j.val ≤ i.val) f).symm
    _ = (∑ j ∈ S, f j) := by rw [hupper_sum, add_zero]
    _ = (∑ j ∈ S.erase i, f j) + f i := by
          exact (Finset.sum_erase_add _ _ hi).symm
    _ = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
          rw [hS, p08_sum_fin_lt]

private theorem p08_assemble_mulVec_apply {p b : ℕ}
    (T DT : P08BlockMatrix p b) (x : P08BlockVector p b)
    (i : Fin p) (α : Fin b) :
    Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
      (p08AssembleVector x) (i, α) =
      ∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DT i j α β) * x j β := by
  change (∑ q : Fin p × Fin b,
    (T i q.1 α q.2 + DT i q.1 α q.2) * x q.1 q.2) = _
  exact Fintype.sum_prod_type (fun q : Fin p × Fin b =>
    (T i q.1 α q.2 + DT i q.1 α q.2) * x q.1 q.2)

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
  let x : P08BlockVector p b := trace.x
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let c : ℝ := d + (p : ℝ)
  let γb : ℝ := p08GammaReal (b : ℝ) fp.u
  let γd : ℝ := p08GammaReal d fp.u
  let γp : ℝ := p08GammaReal (p : ℝ) fp.u
  let γc : ℝ := p08GammaReal c fp.u
  have hdnonneg : 0 ≤ d := by
    dsimp [d]
    positivity
  have hcvalid : c * fp.u < 1 := hvalid
  have hdvalid : d * fp.u < 1 := by
    dsimp [c] at hcvalid
    nlinarith [mul_nonneg (Nat.cast_nonneg p) fp.u_nonneg]
  have hpvalid : (p : ℝ) * fp.u < 1 := by
    dsimp [c] at hcvalid
    nlinarith [mul_nonneg hdnonneg fp.u_nonneg]
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    dsimp [d] at hdvalid
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg r)
      (Real.sqrt_nonneg (r : ℝ))) fp.u_nonneg]
  have hγb : 0 ≤ γb := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hγd : 0 ≤ γd := by
    exact div_nonneg (mul_nonneg hdnonneg fp.u_nonneg) (by linarith)
  have hγp : 0 ≤ γp := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hγc : 0 ≤ γc := by
    exact div_nonneg (mul_nonneg (add_nonneg hdnonneg (Nat.cast_nonneg _)) fp.u_nonneg)
      (by linarith)
  have hγsum : γd + γp + γd * γp ≤ γc :=
    p08_gamma_real_sum d (p : ℝ) fp.u hdnonneg (Nat.cast_nonneg _)
      fp.u_nonneg hcvalid
  have hγb_le : γb ≤ γc := by
    apply p08_gamma_real_mono (b : ℝ) c fp.u (Nat.cast_nonneg _)
      (by
        have hs : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
        have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
        dsimp [c, d]
        linarith)
      fp.u_nonneg hcvalid
  have hdiag_data : ∀ i : Fin p, ∃ E : P08Matrix b,
      (∀ α, ∑ β : Fin b, (T i i α β + E α β) * x i β = trace.rhs i α) ∧
      p08RectFrobNorm E ≤ γb * p08RectFrobNorm (T i i) := by
    intro i
    obtain ⟨E, hEq, hBound⟩ :=
      p08_diag_solve_error fp (T i i) (trace.rhs i)
        (hdiag i) (hlower i) hbvalid
    refine ⟨E, ?_, hBound⟩
    intro α
    simpa only [x, trace.x_eq i] using hEq α
  let D : Fin p → P08Matrix b := fun i => Classical.choose (hdiag_data i)
  have hD_eq (i : Fin p) (α : Fin b) :
      (∑ β : Fin b, (T i i α β + D i α β) * x i β) = trace.rhs i α :=
    (Classical.choose_spec (hdiag_data i)).1 α
  have hD_norm (i : Fin p) :
      p08RectFrobNorm (D i) ≤ γb * p08RectFrobNorm (T i i) :=
    (Classical.choose_spec (hdiag_data i)).2
  have hlow_data : ∀ i j : Fin p, j < i → ∃ F : P08Matrix b,
      (∀ α, p08RoundedLowRankMatVec fp (X i j) (Y i j) (x j) α =
        ∑ β : Fin b, (T i j α β + F α β) * x j β) ∧
      p08RectFrobNorm F ≤ γd * p08RectFrobNorm (T i j) := by
    intro i j hij
    obtain ⟨F, hEq, hBound⟩ :=
      p08_lowrank_matvec_gamma_error fp (X i j) (Y i j) (x j)
        (hX i j hij) hdvalid
    refine ⟨F, ?_, ?_⟩
    · intro α
      simpa only [hlr i j hij] using hEq α
    · simpa only [hlr i j hij] using hBound
  let F : P08BlockMatrix p b := fun i j =>
    if h : j < i then Classical.choose (hlow_data i j h) else 0
  have hF_eq (i j : Fin p) (hij : j < i) (α : Fin b) :
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (x j) α =
        ∑ β : Fin b, (T i j α β + F i j α β) * x j β := by
    simpa only [F, dif_pos hij] using
      (Classical.choose_spec (hlow_data i j hij)).1 α
  have hF_norm (i j : Fin p) (hij : j < i) :
      p08RectFrobNorm (F i j) ≤ γd * p08RectFrobNorm (T i j) := by
    simpa only [F, dif_pos hij] using
      (Classical.choose_spec (hlow_data i j hij)).2
  have hrhs_data : ∀ i : Fin p, ∀ α : Fin b,
      ∃ Θ : ℝ, ∃ θ : Fin i.val → ℝ,
        |Θ| ≤ γp ∧ (∀ j, |θ j| ≤ γp) ∧
        trace.rhs i α = v i α * (1 + Θ) -
          ∑ j : Fin i.val,
            p08RoundedLowRankMatVec fp
              (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
              (x ⟨j.val, by omega⟩) α * (1 + θ j) := by
    intro i α
    exact p08_rhs_fold_error fp T X Y v trace hpvalid i α
  let Θ : P08BlockVector p b := fun i α => Classical.choose (hrhs_data i α)
  let θ : (i : Fin p) → Fin b → Fin i.val → ℝ := fun i α =>
    Classical.choose (Classical.choose_spec (hrhs_data i α))
  have hΘ_bound (i : Fin p) (α : Fin b) : |Θ i α| ≤ γp :=
    (Classical.choose_spec (Classical.choose_spec (hrhs_data i α))).1
  have hθ_bound (i : Fin p) (α : Fin b) (j : Fin i.val) :
      |θ i α j| ≤ γp :=
    (Classical.choose_spec (Classical.choose_spec (hrhs_data i α))).2.1 j
  have hrhs_eq (i : Fin p) (α : Fin b) :
      trace.rhs i α = v i α * (1 + Θ i α) -
        ∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
            (x ⟨j.val, by omega⟩) α * (1 + θ i α j) :=
    (Classical.choose_spec (Classical.choose_spec (hrhs_data i α))).2.2
  let dv : P08BlockVector p b := fun i α => v i α * Θ i α
  let DT : P08BlockMatrix p b := fun i j =>
    if h : j < i then
      fun α β => (T i j α β + F i j α β) *
        (1 + θ i α ⟨j.val, h⟩) - T i j α β
    else if j = i then D i else 0
  refine ⟨DT, dv, ?_, ?_, ?_⟩
  · funext q
    rcases q with ⟨i, α⟩
    rw [p08_assemble_mulVec_apply]
    change (∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DT i j α β) * x j β) = v i α + dv i α
    have hupper_row (j : Fin p) (hij : i < j) :
        (∑ β : Fin b, (T i j α β + DT i j α β) * x j β) = 0 := by
      have hT : T i j = 0 := hupper i j hij
      have hDT : DT i j = 0 := by simp [DT, not_lt.mpr (le_of_lt hij), ne_of_gt hij]
      rw [hT, hDT]
      simp
    have hbelow (j : Fin i.val) :
        (∑ β : Fin b,
          (T i ⟨j.val, by omega⟩ α β + DT i ⟨j.val, by omega⟩ α β) *
            x ⟨j.val, by omega⟩ β) =
          p08RoundedLowRankMatVec fp
            (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
            (x ⟨j.val, by omega⟩) α * (1 + θ i α j) := by
      let j' : Fin p := ⟨j.val, by omega⟩
      have hij : j' < i := by exact Fin.lt_iff_val_lt_val.mpr j.isLt
      have hsum := hF_eq i j' hij α
      change (∑ β : Fin b, (T i j' α β + DT i j' α β) * x j' β) = _
      calc
        (∑ β : Fin b, (T i j' α β + DT i j' α β) * x j' β)
            = ∑ β : Fin b, ((T i j' α β + F i j' α β) *
                (1 + θ i α j)) * x j' β := by
                  apply Finset.sum_congr rfl
                  intro β _
                  simp only [DT, dif_pos hij]
                  ring
        _ = (∑ β : Fin b, (T i j' α β + F i j' α β) * x j' β) *
              (1 + θ i α j) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro β _
                ring
        _ = p08RoundedLowRankMatVec fp (X i j') (Y i j') (x j') α *
              (1 + θ i α j) := by rw [← hsum]
    have hDTdiag : DT i i = D i := by simp [DT]
    calc
      (∑ j : Fin p, ∑ β : Fin b,
          (T i j α β + DT i j α β) * x j β)
          = (∑ j : Fin i.val,
              ∑ β : Fin b,
                (T i ⟨j.val, by omega⟩ α β +
                    DT i ⟨j.val, by omega⟩ α β) *
                  x ⟨j.val, by omega⟩ β) +
              (∑ β : Fin b, (T i i α β + DT i i α β) * x i β) :=
            p08_sum_lower_diag i _ hupper_row
      _ = (∑ j : Fin i.val,
            p08RoundedLowRankMatVec fp
              (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
              (x ⟨j.val, by omega⟩) α * (1 + θ i α j)) +
              trace.rhs i α := by
            rw [hDTdiag, hD_eq i α]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact hbelow j
      _ = v i α + dv i α := by
            rw [hrhs_eq i α]
            dsimp [dv]
            ring
  · apply p08_block_frob_le_of_blocks T DT γc hγc
    intro i j
    by_cases hij : j < i
    · have hDT : DT i j = fun α β =>
          (T i j α β + F i j α β) *
            (1 + θ i α ⟨j.val, hij⟩) - T i j α β := by
        simp only [DT, dif_pos hij]
      rw [hDT]
      have hscaled := p08_scaled_block_error (T i j) (F i j)
        (fun α => θ i α ⟨j.val, hij⟩) γd γp hγd hγp
        (fun α => hθ_bound i α ⟨j.val, hij⟩) (hF_norm i j hij)
      calc
        p08RectFrobNorm (fun α β =>
            (T i j α β + F i j α β) *
              (1 + θ i α ⟨j.val, hij⟩) - T i j α β)
            ≤ (γd + γp + γd * γp) * p08RectFrobNorm (T i j) := hscaled
        _ ≤ γc * p08RectFrobNorm (T i j) :=
          mul_le_mul_of_nonneg_right hγsum (Real.sqrt_nonneg _)
    · by_cases hji : j = i
      · subst j
        have hDT : DT i i = D i := by simp [DT]
        rw [hDT]
        calc
          p08RectFrobNorm (D i) ≤ γb * p08RectFrobNorm (T i i) := hD_norm i
          _ ≤ γc * p08RectFrobNorm (T i i) :=
            mul_le_mul_of_nonneg_right hγb_le (Real.sqrt_nonneg _)
      · have hij' : i < j := by omega
        have hT : T i j = 0 := hupper i j hij'
        have hDT : DT i j = 0 := by simp [DT, hij, hji]
        rw [hT, hDT]
        simp [p08RectFrobNorm]
  · change p08RectFrobNorm dv ≤ γp * p08RectFrobNorm v
    apply p08_frob_le_of_rel v dv γp hγp
    intro i α
    change |v i α * Θ i α| ≤ γp * |v i α|
    rw [abs_mul, mul_comm |v i α|]
    exact mul_le_mul_of_nonneg_right (hΘ_bound i α) (abs_nonneg _)

end VSCLReuse
