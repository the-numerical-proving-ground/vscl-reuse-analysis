import VSCLReuse.P08.Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p08ToNum (fp : StandardFPModel) : NumStability.FPModel where
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

private lemma p08_dot_bridge (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    roundedDotProduct fp n x y = NumStability.fl_dotProduct (p08ToNum fp) n x y := by
  cases n <;> rfl

private lemma p08_forward_steps_bridge (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      roundedForwardSubSteps fp n L rhs k hk x =
        NumStability.fl_forwardSub_steps (p08ToNum fp) n L rhs k hk x := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro hk x
      unfold roundedForwardSubSteps NumStability.fl_forwardSub_steps
      exact ih _ _

private lemma p08_forward_bridge (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (rhs : Fin n → ℝ) :
    roundedForwardSub fp n L rhs = NumStability.fl_forwardSub (p08ToNum fp) n L rhs := by
  exact p08_forward_steps_bridge fp n L rhs n (le_refl n) _

private lemma p08_orth_bridge {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    NumStability.GramSchmidtOrthonormalColumns X := by
  intro j k
  simpa [NumStability.rectangularGram, NumStability.matMulRect,
    NumStability.finiteTranspose, NumStability.idMatrix] using hX j k

private lemma p08_gamma_nonneg (a u : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hvalid : a * u < 1) : 0 ≤ p08GammaReal a u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg ha hu) (by linarith)

private lemma p08_gamma_add (a b u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hvalid : (a + b) * u < 1) :
    p08GammaReal a u + p08GammaReal b u +
        p08GammaReal a u * p08GammaReal b u ≤
      p08GammaReal (a + b) u := by
  have hau : a * u < 1 := by nlinarith [mul_nonneg hb hu]
  have hbu : b * u < 1 := by nlinarith [mul_nonneg ha hu]
  have hda : 0 < 1 - a * u := by linarith
  have hdb : 0 < 1 - b * u := by linarith
  have hdab : 0 < 1 - (a + b) * u := by linarith
  unfold p08GammaReal
  have heq :
      (a + b) * u / (1 - (a + b) * u) -
          (a * u / (1 - a * u) + b * u / (1 - b * u) +
            a * u / (1 - a * u) * (b * u / (1 - b * u))) =
        a * b * u ^ 2 /
          ((1 - a * u) * (1 - b * u) * (1 - (a + b) * u)) := by
    field_simp
    <;> ring
  rw [← sub_nonneg, heq]
  exact div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg u))
    (le_of_lt (mul_pos (mul_pos hda hdb) hdab))

private lemma p08_gamma_mono (a b u : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hu : 0 ≤ u) (hvalid : b * u < 1) :
    p08GammaReal a u ≤ p08GammaReal b u := by
  have hule : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
  have hva : a * u < 1 := lt_of_le_of_lt hule hvalid
  have hda : 0 < 1 - a * u := by linarith
  have hdb : 0 < 1 - b * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ hda hdb).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hu]

private lemma p08_sqrt_nat_ge_one_or_zero (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  by_cases hr : r = 0
  · subst r; norm_num
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := by
      nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r),
        Real.sqrt_nonneg (r : ℝ)]
    nlinarith

private lemma p08_gamma_sqrt_bound (r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  have hr := p08_sqrt_nat_ge_one_or_zero r
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hu_le : (r : ℝ) * u ≤ ((r : ℝ) * Real.sqrt (r : ℝ)) * u :=
    mul_le_mul_of_nonneg_right hr hu
  have hvr : (r : ℝ) * u < 1 := lt_of_le_of_lt hu_le hvalid
  have hdr : 0 < 1 - (r : ℝ) * u := by linarith
  have hdt : 0 < 1 - ((r : ℝ) * Real.sqrt (r : ℝ)) * u := by linarith
  have ht0 : 0 ≤ ((r : ℝ) * Real.sqrt (r : ℝ)) * u := by positivity
  unfold p08GammaReal
  rw [div_mul_eq_mul_div, mul_assoc]
  apply (div_le_div_iff₀ hdr hdt).2
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hu_le)]

private lemma p08_matvec_bridge (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ) :
    p08RoundedRectMatVec fp A x =
      NumStability.fl_matVec (p08ToNum fp) m n A x := by
  funext i
  exact p08_dot_bridge fp n (A i) x

private lemma p08_row_scale_norm_le {m n : ℕ}
    (A : P08RectMatrix m n) (s : Fin m → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hs : ∀ i, |s i| ≤ c) :
    NumStability.frobNormRect (fun i j => s i * A i j) ≤
      c * NumStability.frobNormRect A := by
  have hraw := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    (A := fun i j => s i * A i j) (B := A) hc (by
      intro i j
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hs i) (abs_nonneg _))
  simpa [NumStability.frobNormRect_eq_frobNormFn] using hraw

private lemma p08_entrywise_norm_le {m n : ℕ}
    (D A : P08RectMatrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |D i j| ≤ c * |A i j|) :
    NumStability.frobNormRect D ≤ c * NumStability.frobNormRect A := by
  simpa [NumStability.frobNormRect_eq_frobNormFn] using
    (NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      D A hc h)

private lemma p08_diag_backward {b : ℕ} (fp : StandardFPModel)
    (L : P08Matrix b) (rhs : P08Vector b)
    (hdiag : ∀ α : Fin b, L α α ≠ 0)
    (hlower : p08LowerTriangular L)
    (hvalid : (b : ℝ) * fp.u < 1) :
    ∃ D : P08Matrix b,
      NumStability.frobNormRect D ≤
        p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect L ∧
      ∀ α : Fin b,
        ∑ β : Fin b, (L α β + D α β) * roundedForwardSub fp b L rhs β =
          rhs α := by
  have hv : NumStability.gammaValid (p08ToNum fp) b := hvalid
  obtain ⟨D, hentry, heq⟩ :=
    NumStability.forwardSub_backward_error (p08ToNum fp) b L rhs
      hdiag hlower hv
  refine ⟨D, ?_, ?_⟩
  · exact p08_entrywise_norm_le D L _
      (p08_gamma_nonneg _ _ (by positivity) fp.u_nonneg hvalid)
      (by simpa [NumStability.gamma, p08GammaReal, p08ToNum] using hentry)
  · intro α
    simpa [p08_forward_bridge] using heq α

private lemma p08_block_norm_le_of_block_norm_le {p b : ℕ}
    (D T : P08BlockMatrix p b) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, NumStability.frobNormRect (D i j) ≤
      c * NumStability.frobNormRect (T i j)) :
    p08BlockFrobNorm D ≤ c * p08BlockFrobNorm T := by
  have hsq : (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, (D i j α β) ^ 2) ≤
      c ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hij := h i j
    have hD0 := NumStability.frobNormRect_nonneg (D i j)
    have hT0 := NumStability.frobNormRect_nonneg (T i j)
    have hcap0 : 0 ≤ c * NumStability.frobNormRect (T i j) := mul_nonneg hc hT0
    have hsqij : NumStability.frobNormRect (D i j) ^ 2 ≤
        (c * NumStability.frobNormRect (T i j)) ^ 2 := by nlinarith
    simpa [NumStability.frobNormRect_sq, NumStability.frobNormSqRect,
      mul_pow] using hsqij
  unfold p08BlockFrobNorm
  have hright0 : 0 ≤ c * Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
      ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) :=
    mul_nonneg hc (Real.sqrt_nonneg _)
  calc
    Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
      ∑ α : Fin b, ∑ β : Fin b, (D i j α β) ^ 2) ≤
        Real.sqrt (c ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = c * Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

private lemma p08_block_vec_norm_le_of_entry {p b : ℕ}
    (d v : P08BlockVector p b) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i α, |d i α| ≤ c * |v i α|) :
    p08BlockVecNorm d ≤ c * p08BlockVecNorm v := by
  have hsq : (∑ i : Fin p, ∑ α : Fin b, (d i α) ^ 2) ≤
      c ^ 2 * (∑ i : Fin p, ∑ α : Fin b, (v i α) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _
    have hi := h i α
    have hcap0 : 0 ≤ c * |v i α| := mul_nonneg hc (abs_nonneg _)
    have hs : (d i α) ^ 2 ≤ (c * |v i α|) ^ 2 := by
      apply (sq_le_sq).2
      simpa [abs_of_nonneg hcap0] using hi
    simpa [mul_pow, sq_abs] using hs
  unfold p08BlockVecNorm
  have hright0 : 0 ≤ c * Real.sqrt (∑ i : Fin p, ∑ α : Fin b, (v i α) ^ 2) :=
    mul_nonneg hc (Real.sqrt_nonneg _)
  calc
    Real.sqrt (∑ i : Fin p, ∑ α : Fin b, (d i α) ^ 2) ≤
        Real.sqrt (c ^ 2 * (∑ i : Fin p, ∑ α : Fin b, (v i α) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = c * Real.sqrt (∑ i : Fin p, ∑ α : Fin b, (v i α) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

private lemma p08_fold_apply (fp : StandardFPModel) {b : ℕ} (m : ℕ)
    (t : Fin m → Fin b → ℝ) (s : Fin b → ℝ) (α : Fin b) :
    (Fin.foldl m (fun acc j => fun β => fp.fl_sub (acc β) (t j β)) s) α =
      Fin.foldl m (fun acc j => fp.fl_sub acc (t j α)) (s α) := by
  induction m generalizing s with
  | zero => simp only [Fin.foldl_zero]
  | succ m ih =>
      rw [Fin.foldl_succ, Fin.foldl_succ]
      exact ih (fun j => t j.succ)
        (fun β => fp.fl_sub (s β) (t 0 β))

private lemma p08_fold_error (fp : StandardFPModel) (m p : ℕ)
    (hm : m ≤ p) (hvalid : (p : ℝ) * fp.u < 1)
    (t : Fin m → ℝ) (s : ℝ) :
    ∃ Θ : ℝ, ∃ θ : Fin m → ℝ,
      |Θ| ≤ p08GammaReal (p : ℝ) fp.u ∧
      (∀ j, |θ j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      Fin.foldl m (fun acc j => fp.fl_sub acc (t j)) s =
        s * (1 + Θ) - ∑ j : Fin m, t j * (1 + θ j) := by
  let gfp := p08ToNum fp
  have hpv : NumStability.gammaValid gfp p := hvalid
  have hmv := NumStability.gammaValid_mono gfp hm hpv
  obtain ⟨Θ, θ, hΘ, hθ, heq⟩ :=
    NumStability.fl_sub_sum_error_init gfp m t s hmv
  have hmono := NumStability.gamma_mono gfp hm hpv
  refine ⟨Θ, θ, ?_, ?_, ?_⟩
  · calc
      |Θ| ≤ NumStability.gamma gfp m := hΘ
      _ ≤ NumStability.gamma gfp p := hmono
      _ = p08GammaReal (p : ℝ) fp.u := rfl
  · intro j
    calc
      |θ j| ≤ NumStability.gamma gfp m := hθ j
      _ ≤ NumStability.gamma gfp p := hmono
      _ = p08GammaReal (p : ℝ) fp.u := rfl
  · exact heq

private lemma p08_assembled_mulVec_apply {p b : ℕ}
    (T D : P08BlockMatrix p b) (x : P08BlockVector p b)
    (i : Fin p) (α : Fin b) :
    Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix D)
      (p08AssembleVector x) (i, α) =
      ∑ j : Fin p, ∑ β : Fin b, (T i j α β + D i j α β) * x j β := by
  simpa only [Matrix.mulVec, dotProduct, p08AssembleMatrix, p08AssembleVector,
    Pi.add_apply] using
    (Fintype.sum_prod_type (fun z : Fin p × Fin b =>
      (T i z.1 α z.2 + D i z.1 α z.2) * x z.1 z.2))

private def p08LowerCast {p : ℕ} (i : Fin p) (j : Fin i.val) : Fin p :=
  ⟨j.val, by omega⟩

private lemma p08_sum_lower {p : ℕ} (i : Fin p) (f : Fin p → ℝ) :
    (∑ j : Fin i.val, f (p08LowerCast i j)) =
      ∑ j ∈ Finset.univ with j < i, f j := by
  have hinj : ∀ a : Fin i.val, a ∈ Finset.univ →
      ∀ b : Fin i.val, b ∈ Finset.univ →
      p08LowerCast i a = p08LowerCast i b → a = b := by
    intro a _ b _ h
    exact Fin.ext (congrArg (fun z : Fin p => z.val) h)
  have himg : Finset.image (p08LowerCast i) Finset.univ =
      Finset.filter (fun j : Fin p => j < i) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      exact t.isLt
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
  rw [← himg, Finset.sum_image hinj]

private lemma p08_sum_tri {p : ℕ} (i : Fin p) (f : Fin p → ℝ)
    (hupper : ∀ j, i < j → f j = 0) :
    (∑ j : Fin p, f j) =
      (∑ j : Fin i.val, f (p08LowerCast i j)) + f i := by
  rw [p08_sum_lower]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin p => j < i)]
  congr 1
  apply Finset.sum_eq_single i
  · intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hij : i < j := by omega
    exact hupper j hij
  · intro hi
    exfalso
    simp at hi

private lemma p08_lowrank_backward {b r : ℕ} (fp : StandardFPModel)
    (X Y : P08RectMatrix b r) (x : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      NumStability.frobNormRect F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          NumStability.frobNormRect (p08LowRankMatrix X Y) ∧
      ∀ α : Fin b, p08RoundedLowRankMatVec fp X Y x α =
        ∑ β : Fin b, (p08LowRankMatrix X Y α β + F α β) * x β := by
  let gfp := p08ToNum fp
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let Yt : Fin r → Fin b → ℝ := fun k β => Y β k
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have htr0 : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := mul_nonneg hr0 hs0
  have hu := fp.u_nonneg
  have hbvalid : NumStability.gammaValid gfp b := by
    change (b : ℝ) * fp.u < 1
    nlinarith [mul_nonneg htr0 hu]
  have hrvalid : NumStability.gammaValid gfp r := by
    change (r : ℝ) * fp.u < 1
    have hrle := p08_sqrt_nat_ge_one_or_zero r
    have hmul := mul_le_mul_of_nonneg_right hrle hu
    nlinarith [mul_nonneg hb0 hu]
  have htvalid : ((r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1 := by
    nlinarith [mul_nonneg hb0 hu]
  have hγb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
    p08_gamma_nonneg _ _ hb0 hu (by simpa [NumStability.gammaValid, gfp, p08ToNum] using hbvalid)
  have hγr : 0 ≤ p08GammaReal (r : ℝ) fp.u :=
    p08_gamma_nonneg _ _ hr0 hu (by simpa [NumStability.gammaValid, gfp, p08ToNum] using hrvalid)
  have hγt : 0 ≤ p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u :=
    p08_gamma_nonneg _ _ htr0 hu htvalid
  have hγd : 0 ≤ p08GammaReal d fp.u :=
    p08_gamma_nonneg _ _ (add_nonneg hb0 htr0) hu hvalid
  obtain ⟨EY, hEYentry, hYrun⟩ :=
    NumStability.matVec_backward_error gfp r b Yt x hbvalid
  let z := p08RoundedRectMatVec fp (p08RectTranspose Y) x
  obtain ⟨EX, hEXentry, hXrun⟩ :=
    NumStability.matVec_backward_error gfp b r X z hrvalid
  let A : Fin b → Fin r → ℝ := fun α k => X α k + EX α k
  let B : Fin r → Fin b → ℝ := fun k β => Yt k β + EY k β
  let F : P08Matrix b := fun α β =>
    NumStability.rectMatMul X EY α β + NumStability.rectMatMul EX B α β
  have hYnorm : NumStability.frobNormRect Yt =
      NumStability.frobNormRect (p08LowRankMatrix X Y) := by
    calc
      NumStability.frobNormRect Yt =
          NumStability.frobNormRect
            (NumStability.rectMatMul X Yt) := by
        symm
        exact NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
          X Yt (p08_orth_bridge X hX)
      _ = NumStability.frobNormRect (p08LowRankMatrix X Y) := rfl
  have hEYnorm : NumStability.frobNormRect EY ≤
      p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect Yt := by
    simpa [NumStability.frobNormRect_eq_frobNormFn, NumStability.gamma,
      p08GammaReal, gfp, p08ToNum] using
      (NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        EY Yt hγb hEYentry)
  have hEXnorm : NumStability.frobNormRect EX ≤
      p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) := by
    have hEX := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        EX X hγr hEXentry
    have hXnorm : NumStability.frobNormRect X = Real.sqrt (r : ℝ) :=
      NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
        (p08_orth_bridge X hX)
    have hXnorm' : NumStability.frobNorm X = Real.sqrt (r : ℝ) := by
      rw [← NumStability.frobNormRect_eq_frobNormFn]
      exact hXnorm
    rw [hXnorm'] at hEX
    simpa [NumStability.frobNormRect_eq_frobNormFn, NumStability.gamma,
      p08GammaReal, gfp, p08ToNum] using hEX
  have hBnorm : NumStability.frobNormRect B ≤
      (1 + p08GammaReal (b : ℝ) fp.u) * NumStability.frobNormRect Yt := by
    calc
      NumStability.frobNormRect B ≤
          NumStability.frobNormRect Yt + NumStability.frobNormRect EY :=
        NumStability.frobNormRect_add_le Yt EY
      _ ≤ NumStability.frobNormRect Yt +
          p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect Yt :=
        add_le_add_right hEYnorm _
      _ = _ := by ring
  have hFnorm : NumStability.frobNormRect F ≤
      p08GammaReal d fp.u * NumStability.frobNormRect Yt := by
    have hXop := NumStability.GramSchmidtOrthonormalColumns.rectOpNorm2Le_one
      (p08_orth_bridge X hX)
    have hfirst : NumStability.frobNormRect (NumStability.rectMatMul X EY) ≤
        NumStability.frobNormRect EY := by
      simpa using NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
        X EY (by norm_num : (0 : ℝ) ≤ 1) hXop
    have hsecond : NumStability.frobNormRect (NumStability.rectMatMul EX B) ≤
        NumStability.frobNormRect EX * NumStability.frobNormRect B :=
      NumStability.frobNormRect_rectMatMul_le EX B
    have hB0 := NumStability.frobNormRect_nonneg B
    have hY0 := NumStability.frobNormRect_nonneg Yt
    have hEXcap0 : 0 ≤ p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) :=
      mul_nonneg hγr hs0
    have hBcap0 : 0 ≤ (1 + p08GammaReal (b : ℝ) fp.u) *
        NumStability.frobNormRect Yt :=
      mul_nonneg (by linarith) hY0
    have hprod : NumStability.frobNormRect EX * NumStability.frobNormRect B ≤
        (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) *
          ((1 + p08GammaReal (b : ℝ) fp.u) *
            NumStability.frobNormRect Yt) :=
      mul_le_mul hEXnorm hBnorm hB0 hEXcap0
    have hrt := p08_gamma_sqrt_bound r fp.u hu htvalid
    have hcomp := p08_gamma_add (b : ℝ)
      ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u hb0 htr0 hu hvalid
    calc
      NumStability.frobNormRect F ≤
          NumStability.frobNormRect (NumStability.rectMatMul X EY) +
            NumStability.frobNormRect (NumStability.rectMatMul EX B) := by
        exact NumStability.frobNormRect_add_le _ _
      _ ≤ NumStability.frobNormRect EY +
          NumStability.frobNormRect EX * NumStability.frobNormRect B :=
        add_le_add hfirst hsecond
      _ ≤ p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect Yt +
          (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) *
            ((1 + p08GammaReal (b : ℝ) fp.u) *
              NumStability.frobNormRect Yt) := add_le_add hEYnorm hprod
      _ ≤ p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect Yt +
          p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
            ((1 + p08GammaReal (b : ℝ) fp.u) *
              NumStability.frobNormRect Yt) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_right hrt hBcap0) _
      _ = (p08GammaReal (b : ℝ) fp.u +
          p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u +
          p08GammaReal (b : ℝ) fp.u *
            p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u) *
            NumStability.frobNormRect Yt := by ring
      _ ≤ p08GammaReal d fp.u * NumStability.frobNormRect Yt := by
        exact mul_le_mul_of_nonneg_right (by simpa [d] using hcomp) hY0
  refine ⟨F, ?_, ?_⟩
  · simpa [d, hYnorm] using hFnorm
  · intro α
    have hz : z = NumStability.rectMatMulVec B x := by
      funext k
      simpa [z, B, NumStability.rectMatMulVec,
        p08_matvec_bridge, gfp, p08ToNum] using hYrun k
    have hout : p08RoundedLowRankMatVec fp X Y x =
        NumStability.rectMatMulVec A z := by
      funext i
      simpa [p08RoundedLowRankMatVec, A, NumStability.rectMatMulVec,
        p08_matvec_bridge, gfp, p08ToNum] using hXrun i
    have hAB : ∀ i j, NumStability.rectMatMul A B i j =
        p08LowRankMatrix X Y i j + F i j := by
      intro i j
      dsimp [NumStability.rectMatMul, A, B, F, p08LowRankMatrix,
        p08RectMatMul, p08RectTranspose, Yt]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    calc
      p08RoundedLowRankMatVec fp X Y x α =
          NumStability.rectMatMulVec A z α := congrFun hout α
      _ = NumStability.rectMatMulVec
          (NumStability.rectMatMul A B) x α := by
        rw [hz, NumStability.rectMatMulVec_rectMatMul]
      _ = ∑ β : Fin b, (p08LowRankMatrix X Y α β + F α β) * x β := by
        unfold NumStability.rectMatMulVec
        apply Finset.sum_congr rfl
        intro β _
        rw [hAB]

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
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let c : ℝ := d + (p : ℝ)
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have htr0 : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := mul_nonneg hr0 hs0
  have hd0 : 0 ≤ d := add_nonneg hb0 htr0
  have hc0 : 0 ≤ c := add_nonneg hd0 hp0
  have hcv : c * fp.u < 1 := hvalid
  have hdv : d * fp.u < 1 := by
    dsimp [c] at hcv
    nlinarith [mul_nonneg hp0 fp.u_nonneg]
  have hbv : (b : ℝ) * fp.u < 1 := by
    dsimp [d] at hdv
    nlinarith [mul_nonneg htr0 fp.u_nonneg]
  have hpv : (p : ℝ) * fp.u < 1 := by
    dsimp [c] at hcv
    nlinarith [mul_nonneg hd0 fp.u_nonneg]
  have hγb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
    p08_gamma_nonneg _ _ hb0 fp.u_nonneg hbv
  have hγp : 0 ≤ p08GammaReal (p : ℝ) fp.u :=
    p08_gamma_nonneg _ _ hp0 fp.u_nonneg hpv
  have hγd : 0 ≤ p08GammaReal d fp.u :=
    p08_gamma_nonneg _ _ hd0 fp.u_nonneg hdv
  have hγc : 0 ≤ p08GammaReal c fp.u :=
    p08_gamma_nonneg _ _ hc0 fp.u_nonneg hcv
  have hdiag_data : ∀ i : Fin p, ∃ D : P08Matrix b,
      NumStability.frobNormRect D ≤
        p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect (T i i) ∧
      ∀ α : Fin b,
        ∑ β : Fin b, (T i i α β + D α β) * trace.x i β = trace.rhs i α := by
    intro i
    obtain ⟨D, hDn, hDeq⟩ :=
      p08_diag_backward fp (T i i) (trace.rhs i)
        (hdiag i) (hlower i) hbv
    refine ⟨D, hDn, ?_⟩
    intro α
    simpa only [trace.x_eq i] using hDeq α
  let D : Fin p → P08Matrix b := fun i => Classical.choose (hdiag_data i)
  have hDnorm : ∀ i, NumStability.frobNormRect (D i) ≤
      p08GammaReal (b : ℝ) fp.u * NumStability.frobNormRect (T i i) := by
    intro i
    exact (Classical.choose_spec (hdiag_data i)).1
  have hDrow : ∀ i α, ∑ β : Fin b,
      (T i i α β + D i α β) * trace.x i β = trace.rhs i α := by
    intro i α
    exact (Classical.choose_spec (hdiag_data i)).2 α
  have hlow_data : ∀ i j : Fin p, j < i → ∃ F : P08Matrix b,
      NumStability.frobNormRect F ≤
        p08GammaReal d fp.u * NumStability.frobNormRect (T i j) ∧
      ∀ α : Fin b, p08RoundedLowRankMatVec fp (X i j) (Y i j)
          (trace.x j) α =
        ∑ β : Fin b, (T i j α β + F α β) * trace.x j β := by
    intro i j hij
    obtain ⟨F, hFn, hFeq⟩ :=
      p08_lowrank_backward fp (X i j) (Y i j) (trace.x j)
        (hX i j hij) hdv
    refine ⟨F, ?_, ?_⟩
    · simpa only [d, ← hlr i j hij] using hFn
    · intro α
      simpa only [← hlr i j hij] using hFeq α
  let F : P08BlockMatrix p b := fun i j =>
    if hij : j < i then Classical.choose (hlow_data i j hij) else 0
  have hFnorm : ∀ i j, j < i → NumStability.frobNormRect (F i j) ≤
      p08GammaReal d fp.u * NumStability.frobNormRect (T i j) := by
    intro i j hij
    simp only [F, dif_pos hij]
    exact (Classical.choose_spec (hlow_data i j hij)).1
  have hFrow : ∀ i j, j < i → ∀ α : Fin b,
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) α =
        ∑ β : Fin b, (T i j α β + F i j α β) * trace.x j β := by
    intro i j hij α
    simp only [F, dif_pos hij]
    exact (Classical.choose_spec (hlow_data i j hij)).2 α
  have hfold_data : ∀ i : Fin p, ∀ α : Fin b,
      ∃ w : ℝ × (Fin i.val → ℝ),
        |w.1| ≤ p08GammaReal (p : ℝ) fp.u ∧
        (∀ j, |w.2 j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
        trace.rhs i α = v i α * (1 + w.1) -
          ∑ j : Fin i.val,
            p08RoundedLowRankMatVec fp
              (X i (p08LowerCast i j)) (Y i (p08LowerCast i j))
              (trace.x (p08LowerCast i j)) α * (1 + w.2 j) := by
    intro i α
    let t : Fin i.val → Fin b → ℝ := fun j =>
      p08RoundedLowRankMatVec fp
        (X i (p08LowerCast i j)) (Y i (p08LowerCast i j))
        (trace.x (p08LowerCast i j))
    obtain ⟨Θ, θ, hΘ, hθ, heq⟩ :=
      p08_fold_error fp i.val p (by omega) hpv (fun j => t j α) (v i α)
    refine ⟨(Θ, θ), hΘ, hθ, ?_⟩
    rw [trace.rhs_eq i]
    exact (p08_fold_apply fp i.val t (v i) α).trans heq
  let w : ∀ i : Fin p, Fin b → ℝ × (Fin i.val → ℝ) :=
    fun i α => Classical.choose (hfold_data i α)
  have hwv : ∀ i α, |(w i α).1| ≤ p08GammaReal (p : ℝ) fp.u := by
    intro i α
    exact (Classical.choose_spec (hfold_data i α)).1
  have hws : ∀ i α j, |(w i α).2 j| ≤ p08GammaReal (p : ℝ) fp.u := by
    intro i α j
    exact (Classical.choose_spec (hfold_data i α)).2.1 j
  have hwrow : ∀ i α, trace.rhs i α = v i α * (1 + (w i α).1) -
      ∑ j : Fin i.val,
        p08RoundedLowRankMatVec fp
          (X i (p08LowerCast i j)) (Y i (p08LowerCast i j))
          (trace.x (p08LowerCast i j)) α * (1 + (w i α).2 j) := by
    intro i α
    exact (Classical.choose_spec (hfold_data i α)).2.2
  let DT : P08BlockMatrix p b := fun i j α β =>
    if hij : j < i then
      let θ := (w i α).2 ⟨j.val, hij⟩
      θ * T i j α β + (1 + θ) * F i j α β
    else if j = i then D i α β else 0
  let dv : P08BlockVector p b := fun i α => (w i α).1 * v i α
  have hγdiag : p08GammaReal (b : ℝ) fp.u ≤ p08GammaReal c fp.u := by
    apply p08_gamma_mono _ _ _ hb0
    · dsimp [c, d]
      nlinarith [htr0, hp0]
    · exact fp.u_nonneg
    · exact hcv
  have hγcomp : p08GammaReal (p : ℝ) fp.u + p08GammaReal d fp.u +
      p08GammaReal (p : ℝ) fp.u * p08GammaReal d fp.u ≤
      p08GammaReal c fp.u := by
    simpa [c, add_comm] using p08_gamma_add (p : ℝ) d fp.u
      hp0 hd0 fp.u_nonneg (by simpa [c, add_comm] using hcv)
  have hDTblock : ∀ i j, NumStability.frobNormRect (DT i j) ≤
      p08GammaReal c fp.u * NumStability.frobNormRect (T i j) := by
    intro i j
    rcases lt_trichotomy j i with hij | heq | hji
    · let θ : Fin b → ℝ := fun α => (w i α).2 ⟨j.val, hij⟩
      have hθ : ∀ α, |θ α| ≤ p08GammaReal (p : ℝ) fp.u := by
        intro α
        exact hws i α _
      have h1θ : ∀ α, |1 + θ α| ≤ 1 + p08GammaReal (p : ℝ) fp.u := by
        intro α
        calc
          |1 + θ α| ≤ |(1 : ℝ)| + |θ α| := abs_add_le _ _
          _ ≤ 1 + p08GammaReal (p : ℝ) fp.u := by norm_num; linarith [hθ α]
      have hform : DT i j = fun α β =>
          θ α * T i j α β + (1 + θ α) * F i j α β := by
        funext α β
        simp only [DT, dif_pos hij, θ]
      rw [hform]
      have hT0 := NumStability.frobNormRect_nonneg (T i j)
      have hF0 := NumStability.frobNormRect_nonneg (F i j)
      calc
        NumStability.frobNormRect
          (fun α β => θ α * T i j α β + (1 + θ α) * F i j α β) ≤
            NumStability.frobNormRect (fun α β => θ α * T i j α β) +
              NumStability.frobNormRect (fun α β => (1 + θ α) * F i j α β) :=
          NumStability.frobNormRect_add_le _ _
        _ ≤ p08GammaReal (p : ℝ) fp.u * NumStability.frobNormRect (T i j) +
            (1 + p08GammaReal (p : ℝ) fp.u) *
              NumStability.frobNormRect (F i j) := by
          exact add_le_add
            (p08_row_scale_norm_le (T i j) θ _ hγp hθ)
            (p08_row_scale_norm_le (F i j) (fun α => 1 + θ α) _
              (by linarith) h1θ)
        _ ≤ p08GammaReal (p : ℝ) fp.u * NumStability.frobNormRect (T i j) +
            (1 + p08GammaReal (p : ℝ) fp.u) *
              (p08GammaReal d fp.u * NumStability.frobNormRect (T i j)) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left (hFnorm i j hij) (by linarith)) _
        _ = (p08GammaReal (p : ℝ) fp.u + p08GammaReal d fp.u +
            p08GammaReal (p : ℝ) fp.u * p08GammaReal d fp.u) *
              NumStability.frobNormRect (T i j) := by ring
        _ ≤ p08GammaReal c fp.u * NumStability.frobNormRect (T i j) :=
          mul_le_mul_of_nonneg_right hγcomp hT0
    · subst j
      have hform : DT i i = D i := by
        funext α β
        simp [DT]
      rw [hform]
      exact (hDnorm i).trans (mul_le_mul_of_nonneg_right hγdiag
        (NumStability.frobNormRect_nonneg (T i i)))
    · have hform : DT i j = 0 := by
        funext α β
        simp [DT, not_lt.mpr (le_of_lt hji), ne_of_gt hji]
      rw [hform, hupper i j hji]
      simp [NumStability.frobNormRect, NumStability.frobNormSqRect]
  have hDTnorm : p08BlockFrobNorm DT ≤
      p08GammaReal c fp.u * p08BlockFrobNorm T :=
    p08_block_norm_le_of_block_norm_le DT T _ hγc hDTblock
  have hdventry : ∀ i α, |dv i α| ≤
      p08GammaReal (p : ℝ) fp.u * |v i α| := by
    intro i α
    simp only [dv, abs_mul]
    exact mul_le_mul_of_nonneg_right (hwv i α) (abs_nonneg _)
  have hdvnorm : p08BlockVecNorm dv ≤
      p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v :=
    p08_block_vec_norm_le_of_entry dv v _ hγp hdventry
  have hFterm : ∀ i : Fin p, ∀ j : Fin i.val, ∀ α : Fin b,
      (∑ β : Fin b, (T i (p08LowerCast i j) α β +
          DT i (p08LowerCast i j) α β) *
          trace.x (p08LowerCast i j) β) =
        p08RoundedLowRankMatVec fp
          (X i (p08LowerCast i j)) (Y i (p08LowerCast i j))
          (trace.x (p08LowerCast i j)) α * (1 + (w i α).2 j) := by
    intro i j α
    let k := p08LowerCast i j
    have hk : k < i := j.isLt
    let θ : ℝ := (w i α).2 j
    have hDT : ∀ β, DT i k α β =
        θ * T i k α β + (1 + θ) * F i k α β := by
      intro β
      simp only [DT, dif_pos hk, θ]
      congr 2
    calc
      (∑ β : Fin b, (T i k α β + DT i k α β) * trace.x k β) =
          ∑ β : Fin b, (1 + θ) * ((T i k α β + F i k α β) * trace.x k β) := by
        apply Finset.sum_congr rfl
        intro β _
        rw [hDT β]
        ring
      _ = (1 + θ) *
          (∑ β : Fin b, (T i k α β + F i k α β) * trace.x k β) := by
        rw [Finset.mul_sum]
      _ = (1 + θ) *
          p08RoundedLowRankMatVec fp (X i k) (Y i k) (trace.x k) α := by
        rw [hFrow i k hk α]
      _ = p08RoundedLowRankMatVec fp (X i k) (Y i k) (trace.x k) α *
          (1 + (w i α).2 j) := by simp [θ, mul_comm]
  have hrow : ∀ i α,
      (∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DT i j α β) * trace.x j β) =
        v i α + dv i α := by
    intro i α
    have hupper_row : ∀ j : Fin p, i < j →
        (∑ β : Fin b,
          (T i j α β + DT i j α β) * trace.x j β) = 0 := by
      intro j hij
      have hDTzero : DT i j = 0 := by
        funext μ ν
        simp [DT, not_lt.mpr (le_of_lt hij), ne_of_gt hij]
      rw [hupper i j hij, hDTzero]
      simp
    have hDTdiag : DT i i = D i := by
      funext μ ν
      simp [DT]
    calc
      (∑ j : Fin p, ∑ β : Fin b,
          (T i j α β + DT i j α β) * trace.x j β) =
        (∑ j : Fin i.val, ∑ β : Fin b,
          (T i (p08LowerCast i j) α β +
            DT i (p08LowerCast i j) α β) *
            trace.x (p08LowerCast i j) β) +
          (∑ β : Fin b,
            (T i i α β + DT i i α β) * trace.x i β) := by
        exact p08_sum_tri i _ hupper_row
      _ = (∑ j : Fin i.val,
          p08RoundedLowRankMatVec fp
            (X i (p08LowerCast i j)) (Y i (p08LowerCast i j))
            (trace.x (p08LowerCast i j)) α *
              (1 + (w i α).2 j)) + trace.rhs i α := by
        rw [Finset.sum_congr rfl (fun j _ => hFterm i j α), hDTdiag,
          hDrow i α]
      _ = v i α * (1 + (w i α).1) := by
        rw [hwrow i α]
        ring
      _ = v i α + dv i α := by
        dsimp [dv]
        ring
  refine ⟨DT, dv, ?_, hDTnorm, hdvnorm⟩
  ext z
  rcases z with ⟨i, α⟩
  simpa only [p08AssembleVector, Pi.add_apply, p08_assembled_mulVec_apply]
    using hrow i α

end VSCLReuse
