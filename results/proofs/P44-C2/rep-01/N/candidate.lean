import VSCLReuse.P44.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p44_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u m) : 0 ≤ p44Gamma u m := by
  unfold p44Gamma P44GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p44_gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) :
    u + (1 + u) * p44Gamma u m ≤ p44Gamma u (m + 1) := by
  let r : ℝ := (m : ℝ) * u
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) hu
  have hv' : r + u < 1 := by
    simpa only [P44GammaValid, Nat.cast_add, Nat.cast_one, add_mul, one_mul, r] using hv
  have hd : 0 < 1 - r := by linarith
  have hd' : 0 < 1 - (r + u) := by linarith
  have hform : u + (1 + u) * (r / (1 - r)) = (r + u) / (1 - r) := by
    field_simp
    ring
  have hcomp : (r + u) / (1 - r) ≤ (r + u) / (1 - (r + u)) := by
    apply (div_le_div_iff₀ hd hd').2
    nlinarith [mul_nonneg (add_nonneg hr hu) hu]
  have hmain : u + (1 + u) * (r / (1 - r)) ≤
      (r + u) / (1 - (r + u)) := hform.le.trans hcomp
  convert hmain using 1;
    simp only [p44Gamma, Nat.cast_add, Nat.cast_one, add_mul, one_mul, r]

private lemma p44_gamma_valid_prev (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) : P44GammaValid u m := by
  unfold P44GammaValid at *
  norm_num only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hv
  nlinarith

private lemma p44_gamma_mul_error (u θ δ : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1))
    (hθ : |θ| ≤ p44Gamma u m) (hδ : |δ| ≤ u) :
    |θ + δ + θ * δ| ≤ p44Gamma u (m + 1) := by
  have hprev := p44_gamma_valid_prev u m hu hv
  have hg := p44_gamma_nonneg u m hu hprev
  have hprod : |θ| * |δ| ≤ p44Gamma u m * u :=
    mul_le_mul hθ hδ (abs_nonneg _) hg
  have hab : |θ + δ + θ * δ| ≤ |θ| + |δ| + |θ| * |δ| := by
    calc
      _ ≤ |θ + δ| + |θ * δ| := abs_add_le _ _
      _ ≤ |θ| + |δ| + |θ| * |δ| := by
        rw [abs_mul]
        linarith [abs_add_le θ δ]
  calc
    _ ≤ |θ| + |δ| + |θ| * |δ| := hab
    _ ≤ u + (1 + u) * p44Gamma u m := by nlinarith
    _ ≤ p44Gamma u (m + 1) := p44_gamma_step u m hu hv

private lemma p44_u_le_gamma_succ (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) : u ≤ p44Gamma u (m + 1) := by
  have hg := p44_gamma_nonneg u m hu (p44_gamma_valid_prev u m hu hv)
  have hs := p44_gamma_step u m hu hv
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 + u by linarith) hg]

private theorem p44_recursive_sum_rep (fp : P44FPModel) :
    ∀ m : ℕ, P44GammaValid fp.u m → ∀ v : Fin (m + 1) → ℝ,
      ∃ θ : Fin (m + 1) → ℝ,
        (∀ t, |θ t| ≤ p44Gamma fp.u m) ∧
        p44RecursiveSum fp (m + 1) v = ∑ t, v t * (1 + θ t) := by
  intro m
  induction m with
  | zero =>
      intro hv v
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro t
        simp [p44Gamma]
      · simp [p44RecursiveSum, Fin.foldl_succ, fp.fl_add_zero]
  | succ m ih =>
      intro hv v
      have hprev := p44_gamma_valid_prev fp.u m fp.u_nonneg hv
      obtain ⟨θ, hθ, hsum⟩ := ih hprev (fun i => v i.castSucc)
      obtain ⟨δ, hδ, hadd⟩ :=
        fp.model_add (p44RecursiveSum fp (m + 1) (fun i => v i.castSucc))
          (v (Fin.last (m + 1)))
      let θ' : Fin ((m + 1) + 1) → ℝ :=
        Fin.snoc (fun i => θ i + δ + θ i * δ) δ
      refine ⟨θ', ?_, ?_⟩
      · intro t
        induction t using Fin.lastCases with
        | last =>
            simpa [θ'] using (hδ.trans (p44_u_le_gamma_succ fp.u m fp.u_nonneg hv))
        | cast i =>
            simpa [θ'] using
              (p44_gamma_mul_error fp.u (θ i) δ m fp.u_nonneg hv (hθ i) hδ)
      · have hfold : p44RecursiveSum fp ((m + 1) + 1) v =
            fp.fl_add (p44RecursiveSum fp (m + 1) (fun i => v i.castSucc))
              (v (Fin.last (m + 1))) := by
          unfold p44RecursiveSum
          rw [Fin.foldl_succ_last]
        calc
          p44RecursiveSum fp ((m + 1) + 1) v =
              ((∑ i : Fin (m + 1), v i.castSucc * (1 + θ i)) +
                v (Fin.last (m + 1))) * (1 + δ) := by
              rw [hfold, hadd, hsum]
          _ = (∑ i : Fin (m + 1),
                v i.castSucc * (1 + (θ i + δ + θ i * δ))) +
                  v (Fin.last (m + 1)) * (1 + δ) := by
              rw [add_mul, Finset.sum_mul]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = ∑ t : Fin ((m + 1) + 1), v t * (1 + θ' t) := by
              conv_rhs => rw [Fin.sum_univ_castSucc]
              simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]

/-- Section 2 multiword-product accumulation representation. -/
theorem p44_c2_multiword_accumulation
    (fp : P44FPModel) (p n : ℕ)
    (pairs : Fin (p * p) ≃ Fin p × Fin p)
    (a b : Fin p → Fin n → ℝ)
    (hp : 0 < p)
    (hvalid : P44GammaValid fp.u (p * p - 1)) :
    ∃ θ : Fin (p * p) → ℝ,
      (∀ t, |θ t| ≤ p44Gamma fp.u (p * p - 1)) ∧
      p44MultiwordDotMany fp p n pairs a b =
        ∑ t : Fin (p * p),
          p44BlockDot fp n (a (pairs t).1) (b (pairs t).2) * (1 + θ t) := by
  -- PROOF_START P44-C2-H001
  have hpos : 0 < p * p := Nat.mul_pos hp hp
  have hm : p * p - 1 + 1 = p * p := by omega
  have hrep := p44_recursive_sum_rep fp (p * p - 1) hvalid
  rw [hm] at hrep
  simpa only [p44MultiwordDotMany] using
    hrep (fun t => p44BlockDot fp n (a (pairs t).1) (b (pairs t).2))

end VSCLReuse
