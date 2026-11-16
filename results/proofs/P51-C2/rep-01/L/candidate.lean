import VSCLReuse.P51.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p51AsFPModel (fp : P51FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun a b => a - b
  fl_mul := fp.fl_mul
  fl_div := fun a b => a / b
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro a b
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_mul := fp.model_mul
  model_div := by
    intro a b _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro a _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p51Dot_error_bound (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (hk : P51GammaValid fp.u k) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p51Gamma fp.u k * ∑ t : Fin k, |a t| * |x t| := by
  simpa [p51Dot, NumStability.fl_dotProduct, p51Gamma, NumStability.gamma,
    P51GammaValid, NumStability.gammaValid, p51AsFPModel] using
    (NumStability.dotProduct_error_bound (p51AsFPModel fp) k a x hk)

private lemma p51Schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  classical
  let s : Finset (Fin n) := Finset.image (schedule.col i) Finset.univ
  have h₁ : (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j ∈ s, f j := by
    simpa [s] using
      (Finset.sum_image (s := Finset.univ) (f := f)
        (g := schedule.col i) (fun a _ b _ hab => schedule.col_injective i hab)).symm
  have h₂ : (∑ j ∈ s, f j) = ∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro j _ hj
    apply hf j
    by_contra hA
    obtain ⟨t, ht⟩ := schedule.covers i j hA
    exact hj (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)
  exact h₁.trans h₂

/-- Complete componentwise sparse matrix-vector result of Lemma 3.2. -/
theorem p51_c2_lemma32 {m n l : ℕ} (fp : P51FPModel)
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (η : ℝ)
    (hln : 2 ≤ l ∧ l < n) (hvalid : P51GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin m) :
    |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, A i j * x j| ≤
      p51Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
      (η * fp.u + p51Gamma fp.u l * (η * fp.u)) *
        (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
  -- PROOF_START P51-C2-H001
  let d : ℝ := η * fp.u
  let γ : ℝ := p51Gamma fp.u l
  let S : ℝ := ∑ j : Fin n, |A i j| * |x j|
  let T : ℝ := ∑ j : Fin n, |p51Sign (A i j)| * |x j|
  have hsign (j : Fin n) (hA : A i j ≠ 0) : |p51Sign (A i j)| = 1 := by
    have habs : |A i j| ≠ 0 := abs_ne_zero.mpr hA
    simp [p51Sign, hA, abs_div, habs]
  have hpreSign (j : Fin n) :
      |Ahat i j - A i j| ≤ d * |p51Sign (A i j)| := by
    by_cases hA : A i j = 0
    · simp [d, hA, hzero i j hA, p51Sign]
    · simpa [d, hsign j hA] using hpre i j hA
  have hcoef (j : Fin n) :
      |Ahat i j| ≤ |A i j| + d * |p51Sign (A i j)| := by
    have htri : |Ahat i j| ≤ |A i j| + |Ahat i j - A i j| := by
      calc
        |Ahat i j| = |A i j + (Ahat i j - A i j)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    exact le_trans htri (add_le_add_right (hpreSign j) _)
  have hcount : P51GammaValid fp.u (schedule.count i) := by
    unfold P51GammaValid at hvalid ⊢
    have hc : (schedule.count i : ℝ) ≤ (l : ℝ) := by
      exact_mod_cast schedule.count_le i
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hvalid
  have hγmono : p51Gamma fp.u (schedule.count i) ≤ γ := by
    simpa [γ, p51Gamma, NumStability.gamma, p51AsFPModel,
      P51GammaValid, NumStability.gammaValid] using
      (NumStability.gamma_mono (p51AsFPModel fp) (schedule.count_le i) hvalid)
  have hγnonneg : 0 ≤ γ := by
    simpa [γ, p51Gamma, NumStability.gamma, p51AsFPModel,
      P51GammaValid, NumStability.gammaValid] using
      (NumStability.gamma_nonneg (p51AsFPModel fp) hvalid)
  have hrowRound :
      |p51SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
        γ * ∑ j : Fin n, |Ahat i j| * |x j| := by
    have hsumExact :
        (∑ t : Fin (schedule.count i),
          Ahat i (schedule.col i t) * x (schedule.col i t)) =
          ∑ j : Fin n, Ahat i j * x j := by
      exact p51Schedule_sum A schedule i (fun j => Ahat i j * x j) (by
        intro j hA
        simp [hzero i j hA])
    have hsumAbs :
        (∑ t : Fin (schedule.count i),
          |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
          ∑ j : Fin n, |Ahat i j| * |x j| := by
      exact p51Schedule_sum A schedule i (fun j => |Ahat i j| * |x j|) (by
        intro j hA
        simp [hzero i j hA])
    change |p51Dot fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) -
      ∑ j : Fin n, Ahat i j * x j| ≤ _
    rw [← hsumExact, ← hsumAbs]
    calc
      _ ≤ p51Gamma fp.u (schedule.count i) *
          ∑ t : Fin (schedule.count i),
            |Ahat i (schedule.col i t)| * |x (schedule.col i t)| :=
        p51Dot_error_bound fp (schedule.count i) _ _ hcount
      _ ≤ γ * ∑ t : Fin (schedule.count i),
            |Ahat i (schedule.col i t)| * |x (schedule.col i t)| := by
        apply mul_le_mul_of_nonneg_right hγmono
        exact Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hrowPre :
      |(∑ j : Fin n, Ahat i j * x j) -
          ∑ j : Fin n, A i j * x j| ≤ d * T := by
    have hdiff :
        (∑ j : Fin n, Ahat i j * x j) -
          ∑ j : Fin n, A i j * x j =
          ∑ j : Fin n, (Ahat i j - A i j) * x j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdiff]
    calc
      |∑ j : Fin n, (Ahat i j - A i j) * x j| ≤
          ∑ j : Fin n, |(Ahat i j - A i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, (d * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hpreSign j) (abs_nonneg _)
      _ = d * T := by
        simp only [T, mul_assoc, Finset.mul_sum]
  have hrowAbs :
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤ S + d * T := by
    calc
      _ ≤ ∑ j : Fin n,
          (|A i j| + d * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcoef j) (abs_nonneg _)
      _ = S + d * T := by
        simp only [S, T, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  have htri :
      |p51SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, A i j * x j| ≤
        |p51SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| +
        |(∑ j : Fin n, Ahat i j * x j) -
          ∑ j : Fin n, A i j * x j| := by
    have heq : p51SparseMatVec fp A Ahat x schedule i -
        ∑ j : Fin n, A i j * x j =
        (p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, Ahat i j * x j) +
        ((∑ j : Fin n, Ahat i j * x j) - ∑ j : Fin n, A i j * x j) := by
      ring
    rw [heq]
    exact abs_add_le _ _
  calc
    |p51SparseMatVec fp A Ahat x schedule i -
        ∑ j : Fin n, A i j * x j| ≤
      |p51SparseMatVec fp A Ahat x schedule i -
        ∑ j : Fin n, Ahat i j * x j| +
      |(∑ j : Fin n, Ahat i j * x j) -
        ∑ j : Fin n, A i j * x j| := htri
    _ ≤ γ * (∑ j : Fin n, |Ahat i j| * |x j|) + d * T :=
      add_le_add hrowRound hrowPre
    _ ≤ γ * (S + d * T) + d * T := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hrowAbs hγnonneg) _
    _ = p51Gamma fp.u l * S + (d + p51Gamma fp.u l * d) * T := by
      dsimp [γ]
      ring

end VSCLReuse
