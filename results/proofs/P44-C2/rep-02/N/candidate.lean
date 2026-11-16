import VSCLReuse.P44.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p44_gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) :
    p44Gamma u m + u + p44Gamma u m * u ≤ p44Gamma u (m + 1) := by
  let x : ℝ := (m : ℝ) * u
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hxy : x + u < 1 := by
    simpa only [P44GammaValid, Nat.cast_add, Nat.cast_one, add_mul, one_mul, x] using hv
  have hden : 0 < 1 - x := by linarith
  have hden' : 0 < 1 - x - u := by linarith
  have hident : x / (1 - x) + u + x / (1 - x) * u = (x + u) / (1 - x) := by
    field_simp
    ring
  have hdiv : (x + u) / (1 - x) ≤ (x + u) / (1 - x - u) := by
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [mul_nonneg (add_nonneg hx hu) hu]
  simpa only [p44Gamma, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
    sub_add_eq_sub_sub, x, ← hident]
    using hdiv

private theorem p44_valid_prev (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) : P44GammaValid u m := by
  dsimp [P44GammaValid] at *
  have : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
    gcongr
    omega
  linarith

private theorem p44_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u m) : 0 ≤ p44Gamma u m := by
  unfold p44Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private theorem p44_gamma_one_le (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) : u ≤ p44Gamma u (m + 1) := by
  have hg := p44_gamma_nonneg u m hu (p44_valid_prev u m hu hv)
  have hs := p44_gamma_step u m hu hv
  nlinarith [mul_nonneg hg hu]

private theorem p44_compose_error (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P44GammaValid u (m + 1)) (e d : ℝ)
    (he : |e| ≤ p44Gamma u m) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ p44Gamma u (m + 1) := by
  have hg := p44_gamma_nonneg u m hu (p44_valid_prev u m hu hv)
  have hbound : |e + d + e * d| ≤ p44Gamma u m + u + p44Gamma u m * u := by
    calc
      |e + d + e * d| ≤ |e| + |d| + |e * d| := by
        calc
          |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
          _ ≤ |e| + |d| + |e * d| := by linarith [abs_add_le e d]
      _ = |e| + |d| + |e| * |d| := by rw [abs_mul]
      _ ≤ p44Gamma u m + u + p44Gamma u m * u := by gcongr
  convert le_trans hbound (p44_gamma_step u m hu hv) using 1 <;> ring

private theorem p44_foldl_repr (fp : P44FPModel) :
    ∀ (m : ℕ) (v : Fin m → ℝ) (x : ℝ), P44GammaValid fp.u m →
      ∃ (e : ℝ) (θ : Fin m → ℝ),
        |e| ≤ p44Gamma fp.u m ∧
        (∀ i, |θ i| ≤ p44Gamma fp.u m) ∧
        Fin.foldl m (fun acc i => fp.fl_add acc (v i)) x =
          x * (1 + e) + ∑ i : Fin m, v i * (1 + θ i) := by
  intro m
  induction m with
  | zero =>
      intro v x hv
      refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · simp [p44Gamma]
      · intro i
        exact i.elim0
      · simp
  | succ m ih =>
      intro v x hv
      have hvprev := p44_valid_prev fp.u m fp.u_nonneg hv
      obtain ⟨e, θ, he, hθ, heq⟩ := ih (fun i => v i.castSucc) x hvprev
      obtain ⟨d, hd, hfl⟩ := fp.model_add
        (Fin.foldl m (fun acc i => fp.fl_add acc (v i.castSucc)) x)
        (v (Fin.last m))
      let e' : ℝ := (1 + e) * (1 + d) - 1
      let θ' : Fin (m + 1) → ℝ :=
        Fin.snoc (fun i => (1 + θ i) * (1 + d) - 1) d
      refine ⟨e', θ', ?_, ?_, ?_⟩
      · exact p44_compose_error fp.u m fp.u_nonneg hv e d he hd
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [θ'] using le_trans hd (p44_gamma_one_le fp.u m fp.u_nonneg hv)
        · simpa [θ'] using p44_compose_error fp.u m fp.u_nonneg hv (θ j) d (hθ j) hd
      · calc
          Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i)) x =
              fp.fl_add
                (Fin.foldl m (fun acc i => fp.fl_add acc (v i.castSucc)) x)
                (v (Fin.last m)) := Fin.foldl_succ_last _ _
          _ = ((x * (1 + e) + ∑ i : Fin m, v i.castSucc * (1 + θ i)) +
                v (Fin.last m)) * (1 + d) := by rw [hfl, heq]
          _ = x * (1 + e') + ∑ i : Fin (m + 1), v i * (1 + θ' i) := by
            rw [Fin.sum_univ_castSucc]
            simp only [θ', Fin.snoc_castSucc, Fin.snoc_last]
            dsimp [e']
            rw [add_mul, add_mul, Finset.sum_mul]
            simp_rw [mul_assoc]
            ring

private theorem p44_recursive_sum_repr (fp : P44FPModel) (N : ℕ)
    (v : Fin N → ℝ) (hN : 0 < N)
    (hv : P44GammaValid fp.u (N - 1)) :
    ∃ θ : Fin N → ℝ,
      (∀ i, |θ i| ≤ p44Gamma fp.u (N - 1)) ∧
      p44RecursiveSum fp N v = ∑ i : Fin N, v i * (1 + θ i) := by
  cases N with
  | zero => omega
  | succ m =>
      have hv' : P44GammaValid fp.u m := by simpa using hv
      obtain ⟨e, θ, he, hθ, hsum⟩ :=
        p44_foldl_repr fp m (fun i => v i.succ) (v 0) hv'
      refine ⟨Fin.cons e θ, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using he
        · simpa using hθ j
      · change Fin.foldl (m + 1) (fun acc i => fp.fl_add acc (v i)) 0 = _
        rw [Fin.foldl_succ]
        simp only [fp.fl_add_zero]
        rw [hsum, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]

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
  let v : Fin (p * p) → ℝ := fun t =>
    p44BlockDot fp n (a (pairs t).1) (b (pairs t).2)
  have hN : 0 < p * p := Nat.mul_pos hp hp
  obtain ⟨θ, hθ, heq⟩ := p44_recursive_sum_repr fp (p * p) v hN hvalid
  exact ⟨θ, hθ, by simpa only [p44MultiwordDotMany, v] using heq⟩

end VSCLReuse
