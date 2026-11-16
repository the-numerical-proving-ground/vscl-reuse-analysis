import VSCLReuse.P51.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p51AsNumFP (fp : P51FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem p51_sum_schedule {m n l : ℕ}
    (A : Fin m → Fin n → ℝ) (schedule : P51SparseSchedule A l)
    (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  classical
  let s : Finset (Fin n) := Finset.univ.image (schedule.col i)
  have himage : (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j ∈ s, f j := by
    simpa [s] using (Finset.sum_image (schedule.col_injective i).injOn
      (s := Finset.univ) (f := f)).symm
  rw [himage]
  apply Finset.sum_subset (Finset.subset_univ s)
  intro j _ hj
  apply hf j
  by_contra hA
  obtain ⟨t, ht⟩ := schedule.covers i j hA
  exact hj (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)

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
  classical
  let F := p51AsNumFP fp
  let γ := p51Gamma fp.u l
  let E := η * fp.u
  let S := ∑ j : Fin n, |p51Sign (A i j)| * |x j|
  let B := ∑ j : Fin n, |A i j| * |x j|
  let H := ∑ j : Fin n, |Ahat i j| * |x j|
  let y := ∑ j : Fin n, A i j * x j
  let yhat := ∑ j : Fin n, Ahat i j * x j
  have hvalidF : NumStability.gammaValid F l := hvalid
  have hvalidk : NumStability.gammaValid F (schedule.count i) :=
    NumStability.gammaValid_mono F (schedule.count_le i) hvalidF
  have hγmono : NumStability.gamma F (schedule.count i) ≤ γ :=
    NumStability.gamma_mono F (schedule.count_le i) hvalidF
  have hγnonneg : 0 ≤ γ := NumStability.gamma_nonneg F hvalidF
  have hprepoint (j : Fin n) :
      |Ahat i j - A i j| ≤ E * |p51Sign (A i j)| := by
    by_cases hA : A i j = 0
    · simp [E, hA, hzero i j hA, p51Sign]
    · have hsign : |p51Sign (A i j)| = 1 := by
        simp [p51Sign, hA, abs_div, abs_abs]
      simpa [E, hsign] using hpre i j hA
  have hhatpoint (j : Fin n) :
      |Ahat i j| ≤ |A i j| + E * |p51Sign (A i j)| := by
    calc
      |Ahat i j| = |A i j + (Ahat i j - A i j)| := by ring
      _ ≤ |A i j| + |Ahat i j - A i j| := abs_add_le _ _
      _ ≤ |A i j| + E * |p51Sign (A i j)| :=
        by simpa only [add_comm] using (add_le_add_left (hprepoint j) |A i j|)
  have hH : H ≤ B + E * S := by
    calc
      H ≤ ∑ j : Fin n,
          (|A i j| + E * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hhatpoint j) (abs_nonneg _)
      _ = B + E * S := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rfl
  have hpreerr : |yhat - y| ≤ E * S := by
    calc
      |yhat - y| = |∑ j : Fin n, (Ahat i j * x j - A i j * x j)| := by
        simp only [yhat, y, Finset.sum_sub_distrib]
      _ ≤ ∑ j : Fin n, |Ahat i j * x j - A i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |Ahat i j - A i j| * |x j| := by
        congr 1
        ext j
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ j : Fin n, (E * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hprepoint j) (abs_nonneg _)
      _ = E * S := by
        simp only [mul_assoc, ← Finset.mul_sum]
        rfl
  have hrowhat :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) = yhat :=
    p51_sum_schedule A schedule i (fun j => Ahat i j * x j) (by
      intro j hA
      simp [hzero i j hA])
  have hrowhatabs :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) = H :=
    p51_sum_schedule A schedule i (fun j => |Ahat i j| * |x j|) (by
      intro j hA
      simp [hzero i j hA])
  have hdot := NumStability.dotProduct_error_bound F (schedule.count i)
    (fun t => Ahat i (schedule.col i t))
    (fun t => x (schedule.col i t)) hvalidk
  have hround : |p51SparseMatVec fp A Ahat x schedule i - yhat| ≤ γ * H := by
    have hsum : 0 ≤ ∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)| := by
      positivity
    have hdot' :
        |p51SparseMatVec fp A Ahat x schedule i -
          (∑ t : Fin (schedule.count i),
            Ahat i (schedule.col i t) * x (schedule.col i t))| ≤
          γ * (∑ t : Fin (schedule.count i),
            |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) := by
      exact le_trans hdot (mul_le_mul_of_nonneg_right hγmono hsum)
    simpa only [hrowhat, hrowhatabs] using hdot'
  change |p51SparseMatVec fp A Ahat x schedule i - y| ≤
    γ * B + (E + γ * E) * S
  calc
    |p51SparseMatVec fp A Ahat x schedule i - y| =
        |(p51SparseMatVec fp A Ahat x schedule i - yhat) + (yhat - y)| := by
          ring
    _ ≤ |p51SparseMatVec fp A Ahat x schedule i - yhat| + |yhat - y| :=
      abs_add_le _ _
    _ ≤ γ * H + E * S := add_le_add hround hpreerr
    _ ≤ γ * (B + E * S) + E * S :=
      add_le_add (mul_le_mul_of_nonneg_left hH hγnonneg) le_rfl
    _ = γ * B + (E + γ * E) * S := by ring

end VSCLReuse
