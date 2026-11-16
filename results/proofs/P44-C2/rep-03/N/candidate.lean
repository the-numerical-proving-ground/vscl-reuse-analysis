import VSCLReuse.P44.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p44_error_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (e d : ℝ) (he : |e| ≤ (1 + u) ^ k - 1) (hd : |d| ≤ u) :
    |e + d + e * d| ≤ (1 + u) ^ (k + 1) - 1 := by
  have hb : 0 ≤ (1 + u) ^ k - 1 := by
    have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + u by linarith) (n := k)
    linarith
  have hmul : |e| * |d| ≤ ((1 + u) ^ k - 1) * u := by
    calc
      |e| * |d| ≤ ((1 + u) ^ k - 1) * |d| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ ((1 + u) ^ k - 1) * u :=
        mul_le_mul_of_nonneg_left hd hb
  calc
    |e + d + e * d| ≤ |e| + |d| + |e| * |d| := by
      calc
        |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
        _ ≤ |e| + |d| + |e| * |d| := by
          rw [abs_mul]
          linarith [abs_add_le e d]
    _ ≤ (1 + u) ^ (k + 1) - 1 := by
      rw [pow_succ]
      nlinarith

private lemma p44_power_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P44GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p44Gamma u k := by
  have hprod : ∀ j : ℕ, (j : ℝ) * u < 1 →
      (1 + u) ^ j * (1 - (j : ℝ) * u) ≤ 1 := by
    intro j
    induction j with
    | zero =>
        intro _
        norm_num
    | succ j ih =>
        intro hj
        have hj' : (j : ℝ) * u < 1 := by
          push_cast at hj ⊢
          nlinarith
        have hstep : (1 + u) * (1 - ((j + 1 : ℕ) : ℝ) * u) ≤
            1 - (j : ℝ) * u := by
          push_cast
          nlinarith [sq_nonneg u, mul_nonneg (Nat.cast_nonneg j) (sq_nonneg u)]
        calc
          (1 + u) ^ (j + 1) * (1 - ((j + 1 : ℕ) : ℝ) * u) =
              (1 + u) ^ j * ((1 + u) * (1 - ((j + 1 : ℕ) : ℝ) * u)) := by
                rw [pow_succ]
                ring
          _ ≤ (1 + u) ^ j * (1 - (j : ℝ) * u) :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg (by linarith) _)
          _ ≤ 1 := ih hj'
  have hden : 0 < 1 - (k : ℝ) * u := by
    dsimp [P44GammaValid] at hk
    linarith
  dsimp [p44Gamma]
  apply (le_div_iff₀ hden).2
  have := hprod k hk
  nlinarith

private lemma p44_foldl_error (fp : P44FPModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ) (x : ℝ),
      ∃ e₀ : ℝ, ∃ e : Fin m → ℝ,
        |e₀| ≤ (1 + fp.u) ^ m - 1 ∧
        (∀ i, |e i| ≤ (1 + fp.u) ^ m - 1) ∧
        Fin.foldl m (fun acc i => fp.fl_add acc (v i)) x =
          x * (1 + e₀) + ∑ i : Fin m, v i * (1 + e i) := by
  intro m
  induction m with
  | zero =>
      intro v x
      refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · simp
      · intro i
        exact i.elim0
      · simp
  | succ m ih =>
      intro v x
      let w : Fin m → ℝ := fun i => v i.castSucc
      obtain ⟨e₀, e, he₀, he, hfold⟩ := ih w x
      obtain ⟨d, hd, hadd⟩ :=
        fp.model_add (Fin.foldl m (fun acc i => fp.fl_add acc (w i)) x)
          (v (Fin.last m))
      let e' : Fin (m + 1) → ℝ :=
        Fin.snoc (fun i => e i + d + e i * d) d
      refine ⟨e₀ + d + e₀ * d, e', ?_, ?_, ?_⟩
      · exact p44_error_step fp.u fp.u_nonneg m e₀ d he₀ hd
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simpa [e'] using le_trans hd (by
              have hb : 0 ≤ (1 + fp.u) ^ m - 1 := by
                have := one_le_pow₀ (show (1 : ℝ) ≤ 1 + fp.u by linarith [fp.u_nonneg])
                  (n := m)
                linarith
              rw [pow_succ]
              nlinarith [mul_nonneg hb fp.u_nonneg])
        | cast i =>
            simpa [e'] using
              p44_error_step fp.u fp.u_nonneg m (e i) d (he i) hd
      · rw [Fin.foldl_succ_last]
        change fp.fl_add
          (Fin.foldl m (fun acc i => fp.fl_add acc (w i)) x)
          (v (Fin.last m)) = _
        rw [hadd, hfold, Fin.sum_univ_castSucc]
        simp only [e', Fin.snoc_castSucc, Fin.snoc_last]
        have hs :
            (∑ i : Fin m, w i * (1 + e i)) * (1 + d) =
              ∑ i : Fin m, v i.castSucc * (1 + (e i + d + e i * d)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [w]
          ring
        calc
          (x * (1 + e₀) + ∑ i : Fin m, w i * (1 + e i) +
              v (Fin.last m)) * (1 + d) =
              (x * (1 + e₀)) * (1 + d) +
              (∑ i : Fin m, w i * (1 + e i)) * (1 + d) +
              v (Fin.last m) * (1 + d) := by ring
          _ = _ := by rw [hs]; ring

private lemma p44_recursive_sum_error (fp : P44FPModel) :
    ∀ (N : ℕ) (v : Fin N → ℝ),
      0 < N → P44GammaValid fp.u (N - 1) →
      ∃ θ : Fin N → ℝ,
        (∀ i, |θ i| ≤ p44Gamma fp.u (N - 1)) ∧
        p44RecursiveSum fp N v = ∑ i : Fin N, v i * (1 + θ i) := by
  intro N
  cases N with
  | zero =>
      intro v hN _
      omega
  | succ m =>
      intro v _ hvalid
      let w : Fin m → ℝ := fun i => v i.succ
      obtain ⟨e₀, e, he₀, he, hfold⟩ := p44_foldl_error fp m w (v 0)
      have hgamma : (1 + fp.u) ^ m - 1 ≤ p44Gamma fp.u m :=
        p44_power_le_gamma fp.u fp.u_nonneg m (by simpa using hvalid)
      let θ : Fin (m + 1) → ℝ := Fin.cons e₀ e
      refine ⟨θ, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero =>
            simpa [θ] using le_trans he₀ hgamma
        | succ i =>
            simpa [θ] using le_trans (he i) hgamma
      · unfold p44RecursiveSum
        rw [Fin.foldl_succ, fp.fl_add_zero]
        change Fin.foldl m (fun acc i => fp.fl_add acc (w i)) (v 0) = _
        rw [hfold, Fin.sum_univ_succ]
        simp only [θ, Fin.cons_zero, Fin.cons_succ]
        rfl

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
  simpa only [p44MultiwordDotMany] using
    p44_recursive_sum_error fp (p * p)
      (fun t => p44BlockDot fp n (a (pairs t).1) (b (pairs t).2))
      (Nat.mul_pos hp hp) hvalid

end VSCLReuse
