import VSCLReuse.P51.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

noncomputable def p51ToFPModel (fp : P51FPModel) : NumStability.FPModel :=
  { NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg with
    fl_add := fp.fl_add
    fl_mul := fp.fl_mul
    fl_add_zero := fp.fl_add_zero
    model_add := fp.model_add
    model_mul := fp.model_mul }

private theorem p51Dot_error (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (hvalid : P51GammaValid fp.u k) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p51Gamma fp.u k * ∑ t : Fin k, |a t| * |x t| := by
  have h := NumStability.dotProduct_error_bound (p51ToFPModel fp) k a x hvalid
  simpa [p51Dot, p51Gamma, p51ToFPModel, NumStability.fl_dotProduct,
    NumStability.gamma, NumStability.gammaValid] using h

private theorem p51_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.univ.image (schedule.col i)
  have hs : (∑ j ∈ s, f j) =
      ∑ t : Fin (schedule.count i), f (schedule.col i t) := by
    apply Finset.sum_image
    intro a _ b _ hab
    exact schedule.col_injective i hab
  rw [← hs]
  apply Finset.sum_subset (Finset.subset_univ s)
  intro j _ hj
  apply hf
  by_contra hne
  obtain ⟨t, ht⟩ := schedule.covers i j hne
  apply hj
  exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩

private theorem p51_abs_sign (a : ℝ) (ha : a ≠ 0) : |p51Sign a| = 1 := by
  simp only [p51Sign, if_neg ha, abs_div, abs_abs]
  exact div_self (abs_ne_zero.mpr ha)

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
  let γ := p51Gamma fp.u l
  let d := η * fp.u
  have hvalid' : NumStability.gammaValid (p51ToFPModel fp) l := hvalid
  have hkvalid' : NumStability.gammaValid (p51ToFPModel fp) (schedule.count i) :=
    NumStability.gammaValid_mono (p51ToFPModel fp) (schedule.count_le i) hvalid'
  have hkvalid : P51GammaValid fp.u (schedule.count i) := hkvalid'
  have hγle : p51Gamma fp.u (schedule.count i) ≤ γ := by
    simpa [γ, p51Gamma, NumStability.gamma, p51ToFPModel] using
      NumStability.gamma_mono (p51ToFPModel fp) (schedule.count_le i) hvalid'
  have hγnonneg : 0 ≤ γ := by
    simpa [γ, p51Gamma, NumStability.gamma, p51ToFPModel] using
      NumStability.gamma_nonneg (p51ToFPModel fp) hvalid'
  have hpreall (j : Fin n) :
      |Ahat i j - A i j| ≤ d * |p51Sign (A i j)| := by
    by_cases haj : A i j = 0
    · simp [haj, hzero i j haj, d, p51Sign]
    · rw [p51_abs_sign _ haj, mul_one]
      exact hpre i j haj
  have hhatabs (j : Fin n) :
      |Ahat i j| ≤ |A i j| + d * |p51Sign (A i j)| := by
    calc
      |Ahat i j| = |A i j + (Ahat i j - A i j)| := by congr 1; ring
      _ ≤ |A i j| + |Ahat i j - A i j| := abs_add_le _ _
      _ ≤ |A i j| + d * |p51Sign (A i j)| :=
        add_le_add (le_refl _) (hpreall j)
  have hhatrow :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) =
        ∑ j : Fin n, Ahat i j * x j := by
    exact p51_schedule_sum A schedule i (fun j => Ahat i j * x j)
      (by intro j haj; simp [hzero i j haj])
  have hhatabsrow :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
        ∑ j : Fin n, |Ahat i j| * |x j| := by
    exact p51_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
      (by intro j haj; simp [hzero i j haj])
  have hround0 := p51Dot_error fp (schedule.count i)
    (fun t => Ahat i (schedule.col i t))
    (fun t => x (schedule.col i t)) hkvalid
  have hround :
      |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, Ahat i j * x j| ≤
        γ * ∑ j : Fin n, |Ahat i j| * |x j| := by
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, |Ahat i j| * |x j| := by
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc
      |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, Ahat i j * x j|
          ≤ p51Gamma fp.u (schedule.count i) *
              (∑ j : Fin n, |Ahat i j| * |x j|) := by
                simpa only [p51SparseMatVec, hhatrow, hhatabsrow] using hround0
      _ ≤ γ * ∑ j : Fin n, |Ahat i j| * |x j| :=
        mul_le_mul_of_nonneg_right hγle hsum_nonneg
  have hpert :
      |(∑ j : Fin n, Ahat i j * x j) - ∑ j : Fin n, A i j * x j| ≤
        d * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin n, (Ahat i j * x j - A i j * x j)|
          ≤ ∑ j : Fin n, |Ahat i j * x j - A i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |Ahat i j - A i j| * |x j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ j : Fin n, (d * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hpreall j) (abs_nonneg _)
      _ = d * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
        simp [Finset.mul_sum, mul_assoc]
  have hsumhat :
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
        (∑ j : Fin n, |A i j| * |x j|) +
          d * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
    calc
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
          ∑ j : Fin n, (|A i j| + d * |p51Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hhatabs j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A i j| * |x j|) +
            d * ∑ j : Fin n, |p51Sign (A i j)| * |x j| := by
        simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  calc
    |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, A i j * x j|
        = |(p51SparseMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, Ahat i j * x j) +
            ((∑ j : Fin n, Ahat i j * x j) -
              ∑ j : Fin n, A i j * x j)| := by congr 1; ring
    _ ≤ |p51SparseMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, Ahat i j * x j| +
          |(∑ j : Fin n, Ahat i j * x j) -
            ∑ j : Fin n, A i j * x j| := abs_add_le _ _
    _ ≤ γ * (∑ j : Fin n, |Ahat i j| * |x j|) +
          d * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) :=
      add_le_add hround hpert
    _ ≤ γ * ((∑ j : Fin n, |A i j| * |x j|) +
          d * (∑ j : Fin n, |p51Sign (A i j)| * |x j|)) +
          d * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsumhat hγnonneg) (le_refl _)
    _ = p51Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
          (η * fp.u + p51Gamma fp.u l * (η * fp.u)) *
            (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
      dsimp [γ, d]
      ring

end VSCLReuse
