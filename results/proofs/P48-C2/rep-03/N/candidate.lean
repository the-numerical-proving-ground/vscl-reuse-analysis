import VSCLReuse.P48.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p48_gamma_step_bound (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : (↑(k + 1) : ℝ) * u < 1) :
    p48Gamma u k + u + p48Gamma u k * u ≤ p48Gamma u (k + 1) := by
  have hk : (k : ℝ) * u < 1 := by
    push_cast at hvalid
    nlinarith
  have hkpos : 0 < 1 - (k : ℝ) * u := by linarith
  have hk1pos : 0 < 1 - ((k : ℝ) + 1) * u := by
    push_cast at hvalid
    linarith
  have hident :
      p48Gamma u (k + 1) -
        (p48Gamma u k + u + p48Gamma u k * u) =
      (((k : ℝ) + 1) * u ^ 2) /
        ((1 - ((k : ℝ) + 1) * u) * (1 - (k : ℝ) * u)) := by
    unfold p48Gamma
    push_cast
    field_simp [ne_of_gt hkpos, ne_of_gt hk1pos]
    ring
  have hnum : 0 ≤ ((k : ℝ) + 1) * u ^ 2 := by positivity
  have hden : 0 ≤ (1 - ((k : ℝ) + 1) * u) * (1 - (k : ℝ) * u) := by
    positivity
  have : 0 ≤ p48Gamma u (k + 1) -
      (p48Gamma u k + u + p48Gamma u k * u) := by
    rw [hident]
    exact div_nonneg hnum hden
  linarith

private theorem p48_gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : (k : ℝ) * u < 1) : 0 ≤ p48Gamma u k := by
  unfold p48Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private theorem p48_err_combine (u θ δ : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : (↑(k + 1) : ℝ) * u < 1)
    (hθ : |θ| ≤ p48Gamma u k) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ p48Gamma u (k + 1) := by
  have hk : (k : ℝ) * u < 1 := by
    push_cast at hvalid
    nlinarith
  have hg := p48_gamma_nonneg u k hu hk
  have hprod : |θ| * |δ| ≤ p48Gamma u k * u := by
    exact mul_le_mul hθ hδ (abs_nonneg _) hg
  calc
    |(1 + θ) * (1 + δ) - 1| = |θ + δ + θ * δ| := by ring
    _ ≤ |θ| + |δ| + |θ * δ| := by
      calc
        _ ≤ |θ + δ| + |θ * δ| := abs_add_le _ _
        _ ≤ |θ| + |δ| + |θ * δ| := by linarith [abs_add_le θ δ]
    _ = |θ| + |δ| + |θ| * |δ| := by rw [abs_mul]
    _ ≤ p48Gamma u k + u + p48Gamma u k * u := by linarith
    _ ≤ p48Gamma u (k + 1) := p48_gamma_step_bound u k hu hvalid

private theorem p48_high_factors (fp : P48FPModel) :
    ∀ n : ℕ, ∀ x y : Fin (n + 1) → ℝ,
      P48GammaValid fp.uHigh n →
      ∃ θ : Fin (n + 1) → ℝ,
        (∀ i, |θ i| ≤ p48Gamma fp.uHigh n) ∧
        p48HighDot fp (n + 1) x y =
          ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) := by
  intro n
  induction n with
  | zero =>
      intro x y _
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp [p48Gamma]
      · simp [p48HighDot, Fin.foldl_succ, fp.flHighAdd_zero,
          Fin.foldl_zero]
  | succ k ih =>
      intro x y hvalid
      let x0 : Fin (k + 1) → ℝ := fun i => x i.castSucc
      let y0 : Fin (k + 1) → ℝ := fun i => y i.castSucc
      have hkvalid : P48GammaValid fp.uHigh k := by
        unfold P48GammaValid at hvalid ⊢
        push_cast at hvalid
        nlinarith [fp.uHigh_nonneg]
      obtain ⟨θ, hθ, hsum⟩ := ih x0 y0 hkvalid
      obtain ⟨δ, hδ, hadd⟩ := fp.modelHighAdd
        (p48HighDot fp (k + 1) x0 y0)
        (x (Fin.last (k + 1)) * y (Fin.last (k + 1)))
      let θ' : Fin (k + 2) → ℝ :=
        Fin.snoc (fun i => (1 + θ i) * (1 + δ) - 1) δ
      refine ⟨θ', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [θ', Fin.snoc_last]
          have hgk := p48_gamma_nonneg fp.uHigh k fp.uHigh_nonneg hkvalid
          have hstep := p48_gamma_step_bound fp.uHigh k fp.uHigh_nonneg hvalid
          have hmul : 0 ≤ p48Gamma fp.uHigh k * fp.uHigh :=
            mul_nonneg hgk fp.uHigh_nonneg
          linarith
        · simp only [θ', Fin.snoc_castSucc]
          exact p48_err_combine fp.uHigh (θ j) δ k fp.uHigh_nonneg hvalid
            (hθ j) hδ
      · have hfold : p48HighDot fp (k + 2) x y =
            fp.flHighAdd (p48HighDot fp (k + 1) x0 y0)
              (x (Fin.last (k + 1)) * y (Fin.last (k + 1))) := by
          unfold p48HighDot
          rw [Fin.foldl_succ_last]
        calc
          p48HighDot fp (k + 2) x y =
              (∑ i : Fin (k + 1), (x0 i * y0 i) * (1 + θ i) +
                x (Fin.last (k + 1)) * y (Fin.last (k + 1))) * (1 + δ) := by
                  rw [hfold, hadd, hsum]
          _ = ∑ i : Fin (k + 2), (x i * y i) * (1 + θ' i) := by
            rw [Fin.sum_univ_castSucc (f := fun i : Fin (k + 2) =>
              (x i * y i) * (1 + θ' i))]
            rw [add_mul, Finset.sum_mul]
            simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              dsimp [x0, y0]
              ring

private theorem p48_final_factor_bound (u g θ δ : ℝ)
    (hg : 0 ≤ g) (hθ : |θ| ≤ g) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ (1 + u) * (1 + g) - 1 := by
  have hprod : |θ| * |δ| ≤ g * u :=
    mul_le_mul hθ hδ (abs_nonneg _) hg
  have htri : |θ + δ + θ * δ| ≤ |θ| + |δ| + |θ * δ| := by
    calc
      _ ≤ |θ + δ| + |θ * δ| := abs_add_le _ _
      _ ≤ |θ| + |δ| + |θ * δ| := by linarith [abs_add_le θ δ]
  rw [show (1 + θ) * (1 + δ) - 1 = θ + δ + θ * δ by ring]
  rw [abs_mul] at htri
  nlinarith

theorem p48_c2_mixed_dot_backward_bound
    (fp : P48FPModel) (n : ℕ) (x y : Fin (n + 1) → ℝ)
    (hvalid : P48GammaValid fp.uHigh n) :
    let c := (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1
    ∃ dx dy : Fin (n + 1) → ℝ,
      (∀ i, |dx i| ≤ c * |x i|) ∧
      (∀ i, |dy i| ≤ c * |y i|) ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), (x i + dx i) * y i ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), x i * (y i + dy i) := by
  -- PROOF_START P48-C2-H001
  dsimp only
  obtain ⟨θ, hθ, hsum⟩ := p48_high_factors fp n x y hvalid
  obtain ⟨δ, hδ, hcast⟩ := fp.castDown_model (p48HighDot fp (n + 1) x y)
  let c := (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1
  let ε : Fin (n + 1) → ℝ := fun i => (1 + θ i) * (1 + δ) - 1
  have hg : 0 ≤ p48Gamma fp.uHigh n :=
    p48_gamma_nonneg fp.uHigh n fp.uHigh_nonneg hvalid
  have hε (i : Fin (n + 1)) : |ε i| ≤ c := by
    exact p48_final_factor_bound fp.uLow (p48Gamma fp.uHigh n)
      (θ i) δ hg (hθ i) hδ
  refine ⟨(fun i => x i * ε i), (fun i => y i * ε i), ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      |x i * ε i| = |x i| * |ε i| := abs_mul _ _
      _ ≤ |x i| * c := mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _)
      _ = c * |x i| := mul_comm _ _
  · intro i
    calc
      |y i * ε i| = |y i| * |ε i| := abs_mul _ _
      _ ≤ |y i| * c := mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _)
      _ = c * |y i| := mul_comm _ _
  · change fp.castDown (p48HighDot fp (n + 1) x y) = _
    rw [hcast, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ε]
    ring
  · change fp.castDown (p48HighDot fp (n + 1) x y) = _
    rw [hcast, hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ε]
    ring

end VSCLReuse
