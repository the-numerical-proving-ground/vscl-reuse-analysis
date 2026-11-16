import VSCLReuse.P24.Definitions


namespace VSCLReuse

private lemma p24_krylov_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m k : ℕ} (hk : k < m) :
    (A ^ k) b ∈ p24KrylovSpan A b m := by
  apply Submodule.subset_span
  exact ⟨⟨k, hk⟩, rfl⟩

private lemma p24_consecutive_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m k : ℕ} (hk : k < m) :
    v (s + (k : ℕ)) ∈ p24ConsecutiveSpan v s m := by
  apply Submodule.subset_span
  exact ⟨⟨k, hk⟩, rfl⟩

private lemma p24_krylov_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m k : ℕ} (h : m ≤ k) :
    p24KrylovSpan A b m ≤ p24KrylovSpan A b k := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact p24_krylov_mem A b (lt_of_lt_of_le i.isLt h)

private lemma p24_consecutive_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m k : ℕ} (h : m ≤ k) :
    p24ConsecutiveSpan v s m ≤ p24ConsecutiveSpan v s k := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact p24_consecutive_mem v s (lt_of_lt_of_le i.isLt h)

private lemma p24_krylov_map_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) {x : V}
    (hx : x ∈ p24KrylovSpan A b m) :
    A x ∈ p24KrylovSpan A b (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hi : (i : ℕ) + 1 < m + 1 := Nat.succ_lt_succ i.isLt
      have hm := p24_krylov_mem A b hi
      simpa [pow_succ', Module.End.mul_apply] using hm
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (p24KrylovSpan A b (m + 1)).add_mem ihx ihy
  | smul a x hx ih => simpa using (p24KrylovSpan A b (m + 1)).smul_mem a ih

private lemma p24_consecutive_map_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (m : ℕ) {x : V} (hx : x ∈ p24ConsecutiveSpan v s m) :
    A x ∈ p24ConsecutiveSpan v s (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hi : (i : ℕ) < m + 1 := Nat.lt_succ_of_lt i.isLt
      have hi' : (i : ℕ) + 1 < m + 1 := Nat.succ_lt_succ i.isLt
      have h0 := p24_consecutive_mem v s hi
      have h1 := p24_consecutive_mem v s hi'
      have hr : v (s + ((i : ℕ) + 1)) = p24Shift A (p (s + (i : ℕ))) (v (s + (i : ℕ))) := by
        simpa [add_assoc] using hstep (s + (i : ℕ))
      have h1' : v (s + (((i : ℕ) + 1 : ℕ) : ℤ)) ∈ p24ConsecutiveSpan v s (m + 1) := h1
      have h1'' : v (s + ((i : ℕ) + 1)) ∈ p24ConsecutiveSpan v s (m + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1'
      rw [hr] at h1''
      have heq : p24Shift A (p (s + (i : ℕ))) (v (s + (i : ℕ))) =
          A (v (s + (i : ℕ))) + p (s + (i : ℕ)) • v (s + (i : ℕ)) := by
        simp [p24Shift, LinearMap.add_apply]
      rw [heq] at h1''
      have hm := (p24ConsecutiveSpan v s (m + 1)).sub_mem h1''
        ((p24ConsecutiveSpan v s (m + 1)).smul_mem (p (s + (i : ℕ))) h0)
      simpa using hm
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (p24ConsecutiveSpan v s (m + 1)).add_mem ihx ihy
  | smul a x hx ih => simpa using (p24ConsecutiveSpan v s (m + 1)).smul_mem a ih

private lemma p24_consecutive_eq_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (m : ℕ) : p24ConsecutiveSpan v s m = p24KrylovSpan A (v s) m := by
  have hp : ∀ k : ℕ,
      v (s + (k : ℕ)) ∈ p24KrylovSpan A (v s) (k + 1) ∧
      (A ^ k) (v s) ∈ p24ConsecutiveSpan v s (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa using p24_krylov_mem A (v s) (show 0 < 1 by decide)
        · simpa using p24_consecutive_mem v s (show 0 < 1 by decide)
    | succ k ih =>
        constructor
        · have h0 : v (s + (k : ℕ)) ∈ p24KrylovSpan A (v s) (k + 2) :=
            p24_krylov_mono A (v s) (by omega) ih.1
          have hA : A (v (s + (k : ℕ))) ∈ p24KrylovSpan A (v s) (k + 2) := by
            simpa [Nat.add_assoc] using p24_krylov_map_succ A (v s) (k + 1) ih.1
          have hs := hstep (s + (k : ℕ))
          have hsum := (p24KrylovSpan A (v s) (k + 2)).add_mem hA
            ((p24KrylovSpan A (v s) (k + 2)).smul_mem (p (s + (k : ℕ))) h0)
          have hr : v (s + (((k + 1 : ℕ) : ℕ) : ℤ)) =
              A (v (s + (k : ℕ))) + p (s + (k : ℕ)) • v (s + (k : ℕ)) := by
            simpa [Nat.cast_add, p24Shift, LinearMap.add_apply, add_assoc] using hs
          rw [hr]
          exact hsum
        · have hA := p24_consecutive_map_succ A p v s hstep (k + 1) ih.2
          simpa [pow_succ', Module.End.mul_apply, Nat.add_assoc] using hA
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact p24_krylov_mono A (v s) (Nat.succ_le_of_lt i.isLt) (hp i).1
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact p24_consecutive_mono v s (Nat.succ_le_of_lt i.isLt) (hp i).2

private lemma p24_all_powers (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p24KrylovSpan A b n := by
  have hdegree : A.charpoly.natDegree = n := by
    simpa using A.charpoly_natDegree
  have hne : A.charpoly ≠ 1 := by
    intro heq
    have : n = 0 := by simpa [heq] using hdegree.symm
    omega
  let q : Polynomial ℝ := Polynomial.X ^ k %ₘ A.charpoly
  have hq : q.natDegree < n := by
    rw [← hdegree]
    exact Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hne
  have heq : A ^ k = Polynomial.aeval A q := A.pow_eq_aeval_mod_charpoly k
  rw [heq, Polynomial.aeval_eq_sum_range' hq]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i hi
  exact (p24KrylovSpan A b n).smul_mem (q.coeff i)
    (p24_krylov_mem A b (Finset.mem_range.mp hi))

private lemma p24_krylov_invariant (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    A x ∈ p24KrylovSpan A b n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hm := p24_all_powers n hn A b ((i : ℕ) + 1)
      simpa [pow_succ', Module.End.mul_apply] using hm
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (p24KrylovSpan A b n).add_mem ihx ihy
  | smul a x hx ih => simpa using (p24KrylovSpan A b n).smul_mem a ih

private lemma p24_shift_invariant (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (c : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    p24Shift A c x ∈ p24KrylovSpan A b n := by
  have hA := p24_krylov_invariant n hn A b hx
  have hc := (p24KrylovSpan A b n).smul_mem c hx
  simpa [p24Shift, LinearMap.add_apply] using (p24KrylovSpan A b n).add_mem hA hc

private lemma p24_prev_mem (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (j : ℤ) (hy : v (j + 1) ∈ p24KrylovSpan A b n) :
    v j ∈ p24KrylovSpan A b n := by
  let K := p24KrylovSpan A b n
  have hmap : ∀ x ∈ K, p24Shift A (p j) x ∈ K := by
    intro x hx
    exact p24_shift_invariant n hn A b (p j) hx
  let f : K →ₗ[ℝ] K := (p24Shift A (p j)).restrict hmap
  have hinjf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact (hinv j).1 (congrArg Subtype.val hxy)
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinjf ⟨v (j + 1), hy⟩
  have heq : p24Shift A (p j) x.1 = v (j + 1) := congrArg Subtype.val hx
  have hv : x.1 = v j := (hinv j).1 (heq.trans (hstep j))
  exact hv ▸ x.2

private lemma p24_twoSided_eq_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) : p24TwoSidedSpan v = p24KrylovSpan A (v s) n := by
  let K := p24KrylovSpan A (v s) n
  have hs : v s ∈ K := by
    simpa [K] using p24_krylov_mem A (v s) hn
  have hf : ∀ j : ℤ, s ≤ j → v j ∈ K := by
    intro j hj
    induction j, hj using Int.le_induction with
    | base => exact hs
    | succ j hj ih =>
        rw [hstep j]
        exact p24_shift_invariant n hn A (v s) (p j) ih
  have hb : ∀ j : ℤ, j ≤ s → v j ∈ K := by
    intro j hj
    induction j, hj using Int.le_induction_down with
    | base => exact hs
    | pred j hj ih =>
        have hy : v ((j - 1) + 1) ∈ K := by simpa using ih
        exact p24_prev_mem n hn A (v s) p v hstep hinv (j - 1) hy
  have hall : ∀ j : ℤ, v j ∈ K := by
    intro j
    rcases le_total s j with h | h
    · exact hf j h
    · exact hb j h
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact hall j
  · rw [← p24_consecutive_eq_krylov A p v s hstep n]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨s + (i : ℕ), rfl⟩

/-- P24-C1: the shifted-vector spanning equalities in Theorem 6.1. -/
theorem p24_c1_consecutive_shifted_vectors_span
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (hA : Function.Bijective A)
    (B : Fin n → ℝ) (hB : B ≠ 0)
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hv0 : v 0 = B)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) :
    p24TwoSidedSpan v = p24ConsecutiveSpan v s n ∧
      p24ConsecutiveSpan v s n = p24KrylovSpan A (v s) n ∧
      p24KrylovSpan A (v s) n = p24KrylovSpan A B n := by
  -- PROOF_START P24-C1-H001
  have hc := p24_consecutive_eq_krylov A p v s hstep n
  have hs := p24_twoSided_eq_krylov n hn A p v hstep hinv s
  have hz := p24_twoSided_eq_krylov n hn A p v hstep hinv 0
  refine ⟨hs.trans hc.symm, hc, ?_⟩
  calc
    p24KrylovSpan A (v s) n = p24TwoSidedSpan v := hs.symm
    _ = p24KrylovSpan A (v 0) n := hz
    _ = p24KrylovSpan A B n := by rw [hv0]

end VSCLReuse
