import VSCLReuse.P48.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p48_one_add_gamma_eq (u : ℝ) (n : ℕ)
    (h : P48GammaValid u n) :
    1 + p48Gamma u n = 1 / (1 - (n : ℝ) * u) := by
  have hd : 1 - (n : ℝ) * u ≠ 0 := by
    change (n : ℝ) * u < 1 at h
    linarith
  unfold p48Gamma
  field_simp
  ring

private theorem p48_gamma_step (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (h : P48GammaValid u (n + 1)) :
    (1 + p48Gamma u n) * (1 + u) ≤
      1 + p48Gamma u (n + 1) := by
  have hnext : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    change ((n + 1 : ℕ) : ℝ) * u < 1 at h
    linarith
  have hn : 0 < 1 - (n : ℝ) * u := by
    push_cast at hnext
    nlinarith
  have hvn : P48GammaValid u n := by
    change (n : ℝ) * u < 1
    linarith
  rw [p48_one_add_gamma_eq u n hvn,
    p48_one_add_gamma_eq u (n + 1) h]
  calc
    1 / (1 - (n : ℝ) * u) * (1 + u) =
        (1 + u) / (1 - (n : ℝ) * u) := by ring
    _ ≤ 1 / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
      apply (div_le_div_iff₀ hn hnext).2
      have hp : 0 ≤ (n : ℝ) * u * u :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg u]

private theorem p48_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) :
    ∀ n : ℕ, P48GammaValid u n → (1 + u) ^ n ≤ 1 + p48Gamma u n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [p48Gamma]
  | succ n ih =>
      intro h
      have hn : P48GammaValid u n := by
        change (n : ℝ) * u < 1
        change ((n + 1 : ℕ) : ℝ) * u < 1 at h
        push_cast at h
        nlinarith
      calc
        (1 + u) ^ (n + 1) = (1 + u) ^ n * (1 + u) := pow_succ _ _
        _ ≤ (1 + p48Gamma u n) * (1 + u) :=
          mul_le_mul_of_nonneg_right (ih hn) (by linarith)
        _ ≤ 1 + p48Gamma u (n + 1) := p48_gamma_step u hu n h

private theorem p48_error_extend (u θ δ : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hθ : |θ| ≤ (1 + u) ^ n - 1) (hδ : |δ| ≤ u) :
    |(1 + θ) * (1 + δ) - 1| ≤ (1 + u) ^ (n + 1) - 1 := by
  have hb : 0 ≤ (1 + u) ^ n - 1 := by
    have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + u by linarith) (n := n)
    linarith
  calc
    |(1 + θ) * (1 + δ) - 1| = |θ + δ + θ * δ| := by ring
    _ ≤ |θ| + |δ| + |θ| * |δ| := by
      calc
        |θ + δ + θ * δ| ≤ |θ + δ| + |θ * δ| := abs_add_le _ _
        _ ≤ |θ| + |δ| + |θ| * |δ| := by
          rw [abs_mul]
          linarith [abs_add_le θ δ]
    _ ≤ ((1 + u) ^ n - 1) + u + ((1 + u) ^ n - 1) * u := by
      have hm : |θ| * |δ| ≤ ((1 + u) ^ n - 1) * u :=
        mul_le_mul hθ hδ (abs_nonneg _) hb
      linarith
    _ = (1 + u) ^ (n + 1) - 1 := by rw [pow_succ]; ring

private theorem p48_high_expansion (fp : P48FPModel) :
    ∀ n : ℕ, ∀ x y : Fin (n + 1) → ℝ,
      ∃ θ : Fin (n + 1) → ℝ,
        (∀ i, |θ i| ≤ (1 + fp.uHigh) ^ n - 1) ∧
        p48HighDot fp (n + 1) x y =
          ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) := by
  intro n
  induction n with
  | zero =>
      intro x y
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simp
      · simp [p48HighDot, Fin.foldl_succ_last, fp.flHighAdd_zero]
  | succ n ih =>
      intro x y
      let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
      obtain ⟨θ, hθ, heq⟩ := ih x' y'
      let s : ℝ := p48HighDot fp (n + 1) x' y'
      let z : ℝ := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
      obtain ⟨δ, hδ, hadd⟩ := fp.modelHighAdd s z
      let θ' : Fin (n + 2) → ℝ :=
        Fin.snoc (fun i => (1 + θ i) * (1 + δ) - 1) δ
      refine ⟨θ', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · have hz : |(0 : ℝ)| ≤ (1 + fp.uHigh) ^ n - 1 := by
            have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + fp.uHigh by
              linarith [fp.uHigh_nonneg]) (n := n)
            simp only [abs_zero]
            linarith
          simpa [θ'] using
            (p48_error_extend fp.uHigh 0 δ n fp.uHigh_nonneg hz hδ)
        · intro j
          simpa [θ'] using
            (p48_error_extend fp.uHigh (θ j) δ n fp.uHigh_nonneg (hθ j) hδ)
      · have hfold : p48HighDot fp (n + 2) x y = fp.flHighAdd s z := by
          unfold p48HighDot s z x' y'
          rw [Fin.foldl_succ_last]
          rfl
        rw [hfold, hadd]
        change (s + z) * (1 + δ) = _
        dsimp only [s]
        rw [heq]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          dsimp [x', y']
          ring

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
  dsimp
  obtain ⟨θ, hθ, heq⟩ := p48_high_expansion fp n x y
  obtain ⟨δ, hδ, hcast⟩ :=
    fp.castDown_model (p48HighDot fp (n + 1) x y)
  let γ : ℝ := p48Gamma fp.uHigh n
  let c : ℝ := (1 + fp.uLow) * (1 + γ) - 1
  let e : Fin (n + 1) → ℝ := fun i => (1 + θ i) * (1 + δ) - 1
  let dx : Fin (n + 1) → ℝ := fun i => x i * e i
  let dy : Fin (n + 1) → ℝ := fun i => y i * e i
  have hpow : (1 + fp.uHigh) ^ n ≤ 1 + γ :=
    p48_pow_le_gamma fp.uHigh fp.uHigh_nonneg n hvalid
  have hγ : 0 ≤ γ := by
    have hp : 1 ≤ (1 + fp.uHigh) ^ n :=
      one_le_pow₀ (by linarith [fp.uHigh_nonneg])
    linarith
  have hθγ (i : Fin (n + 1)) : |θ i| ≤ γ := by
    have := hθ i
    linarith
  have he (i : Fin (n + 1)) : |e i| ≤ c := by
    have hm : |θ i| * |δ| ≤ γ * fp.uLow :=
      mul_le_mul (hθγ i) hδ (abs_nonneg _) hγ
    calc
      |e i| = |θ i + δ + θ i * δ| := by dsimp [e]; ring
      _ ≤ |θ i| + |δ| + |θ i| * |δ| := by
        calc
          |θ i + δ + θ i * δ| ≤ |θ i + δ| + |θ i * δ| := abs_add_le _ _
          _ ≤ |θ i| + |δ| + |θ i| * |δ| := by
            rw [abs_mul]
            linarith [abs_add_le (θ i) δ]
      _ ≤ γ + fp.uLow + γ * fp.uLow := by
        linarith [hθγ i, hδ, hm]
      _ = c := by dsimp [c]; ring
  have hmixed : p48MixedDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + e i) := by
    unfold p48MixedDot
    rw [hcast, heq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [e]
    ring
  refine ⟨dx, dy, ?_, ?_, ?_, ?_⟩
  · intro i
    change |dx i| ≤ c * |x i|
    calc
      |dx i| = |x i| * |e i| := by simp [dx, abs_mul]
      _ ≤ |x i| * c := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = c * |x i| := mul_comm _ _
  · intro i
    change |dy i| ≤ c * |y i|
    calc
      |dy i| = |y i| * |e i| := by simp [dy, abs_mul]
      _ ≤ |y i| * c := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = c * |y i| := mul_comm _ _
  · calc
      p48MixedDot fp (n + 1) x y =
          ∑ i : Fin (n + 1), (x i * y i) * (1 + e i) := hmixed
      _ = ∑ i : Fin (n + 1), (x i + dx i) * y i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [dx]
        ring
  · calc
      p48MixedDot fp (n + 1) x y =
          ∑ i : Fin (n + 1), (x i * y i) * (1 + e i) := hmixed
      _ = ∑ i : Fin (n + 1), x i * (y i + dy i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [dy]
        ring

end VSCLReuse
