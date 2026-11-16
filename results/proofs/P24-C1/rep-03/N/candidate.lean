import VSCLReuse.P24.Definitions

namespace VSCLReuse

private theorem krylov_gen {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m k : ℕ} (hk : k < m) :
    (A ^ k) b ∈ p24KrylovSpan A b m := by
  exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

private theorem krylov_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m l : ℕ} (hml : m ≤ l) :
    p24KrylovSpan A b m ≤ p24KrylovSpan A b l := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact krylov_gen A b (lt_of_lt_of_le k.isLt hml)

private theorem krylov_invariant_of_last {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ)
    (hm : (A ^ m) b ∈ p24KrylovSpan A b m) :
    ∀ x ∈ p24KrylovSpan A b m, A x ∈ p24KrylovSpan A b m := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      change A ((A ^ (k : ℕ)) b) ∈ p24KrylovSpan A b m
      by_cases hk : (k : ℕ) + 1 < m
      · simpa only [pow_succ', Module.End.mul_apply] using (krylov_gen A b hk)
      · have heq : (k : ℕ) + 1 = m := by omega
        have hh : A ((A ^ (k : ℕ)) b) = (A ^ m) b := by
          calc
            A ((A ^ (k : ℕ)) b) = (A ^ ((k : ℕ) + 1)) b := by simp [pow_succ', Module.End.mul_apply]
            _ = (A ^ m) b := congrArg (fun j : ℕ => (A ^ j) b) heq
        rw [hh]
        exact hm
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (Submodule.add_mem _ ihx ihy)
  | smul a x hx ih => simpa using (Submodule.smul_mem (p24KrylovSpan A b m) a ih)

private theorem krylov_later_of_last {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) {m l : ℕ} (hml : m ≤ l)
    (hm : (A ^ m) b ∈ p24KrylovSpan A b m) :
    (A ^ l) b ∈ p24KrylovSpan A b m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hml
  induction t with
  | zero => simpa using hm
  | succ t ih =>
      rw [Nat.add_succ, pow_succ']
      exact krylov_invariant_of_last A b m hm _ (ih (by omega))

private theorem krylov_last_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (A : Module.End ℝ V) (b : V) :
    (A ^ (Module.finrank ℝ V)) b ∈ p24KrylovSpan A b (Module.finrank ℝ V) := by
  let n := Module.finrank ℝ V
  by_contra h
  have hnot (m : ℕ) (hm : m ≤ n) : (A ^ m) b ∉ p24KrylovSpan A b m := by
    intro hmem
    exact h ((krylov_mono A b hm) (krylov_later_of_last A b hm hmem))
  have hstrict (m : ℕ) (hm : m < n + 1) :
      p24KrylovSpan A b m < p24KrylovSpan A b (m + 1) := by
    apply lt_of_le_of_ne (krylov_mono A b (Nat.le_succ m))
    intro heq
    have hmem : (A ^ m) b ∈ p24KrylovSpan A b (m + 1) := krylov_gen A b (Nat.lt_succ_self m)
    exact hnot m (by omega) (heq ▸ hmem)
  have hrank (m : ℕ) (hm : m ≤ n + 1) :
      m ≤ Module.finrank ℝ (p24KrylovSpan A b m) := by
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
        have hs := hstrict m (by omega)
        have hlt := Submodule.finrank_lt_finrank_of_lt hs
        omega
  have hbad := hrank (n + 1) le_rfl
  have hbound := Submodule.finrank_le (p24KrylovSpan A b (n + 1))
  change n + 1 ≤ Module.finrank ℝ (p24KrylovSpan A b (n + 1)) at hbad
  change Module.finrank ℝ (p24KrylovSpan A b (n + 1)) ≤ n at hbound
  omega

private theorem consecutive_gen {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m k : ℕ} (hk : k < m) :
    v (s + (k : ℤ)) ∈ p24ConsecutiveSpan v s m := by
  exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

private theorem consecutive_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) {m l : ℕ} (hml : m ≤ l) :
    p24ConsecutiveSpan v s m ≤ p24ConsecutiveSpan v s l := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact consecutive_gen v s (lt_of_lt_of_le k.isLt hml)

private theorem krylov_map_next {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) :
    ∀ x ∈ p24KrylovSpan A b m, A x ∈ p24KrylovSpan A b (m + 1) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      simpa only [pow_succ', Module.End.mul_apply] using
        (krylov_gen A b (show (k : ℕ) + 1 < m + 1 by omega))
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (Submodule.add_mem _ ihx ihy)
  | smul a x hx ih => simpa using (Submodule.smul_mem (p24KrylovSpan A b (m + 1)) a ih)

private theorem consecutive_map_next {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    ∀ x ∈ p24ConsecutiveSpan v s m,
      A x ∈ p24ConsecutiveSpan v s (m + 1) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k, rfl⟩
      have h₁ : v (s + ((k : ℕ) : ℤ)) ∈ p24ConsecutiveSpan v s (m + 1) :=
        consecutive_gen v s (by omega)
      have h₂ : v (s + (((k : ℕ) + 1 : ℕ) : ℤ)) ∈ p24ConsecutiveSpan v s (m + 1) :=
        consecutive_gen v s (by omega)
      have heq : A (v (s + ((k : ℕ) : ℤ))) =
          v (s + (((k : ℕ) + 1 : ℕ) : ℤ)) - p (s + ((k : ℕ) : ℤ)) • v (s + ((k : ℕ) : ℤ)) := by
        have hs := hstep (s + ((k : ℕ) : ℤ))
        simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply, Int.natCast_add, Int.natCast_one, add_assoc] at hs ⊢
        exact eq_sub_of_add_eq hs.symm
      rw [heq]
      exact Submodule.sub_mem _ h₂ (Submodule.smul_mem _ _ h₁)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (Submodule.add_mem _ ihx ihy)
  | smul a x hx ih => simpa using (Submodule.smul_mem (p24ConsecutiveSpan v s (m + 1)) a ih)

private theorem consecutive_eq_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    p24ConsecutiveSpan v s m = p24KrylovSpan A (v s) m := by
  have hv (k : ℕ) : v (s + (k : ℤ)) ∈ p24KrylovSpan A (v s) (k + 1) := by
    induction k with
    | zero => simpa using (krylov_gen A (v s) (Nat.zero_lt_succ 0))
    | succ k ih =>
        have hA := krylov_map_next A (v s) (k + 1) _ ih
        have hvi := (krylov_mono A (v s) (by omega : k + 1 ≤ (k + 1) + 1)) ih
        have hs := hstep (s + (k : ℤ))
        simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply] at hs
        have hsum : A (v (s + (k : ℤ))) + p (s + (k : ℤ)) • v (s + (k : ℤ)) ∈
            p24KrylovSpan A (v s) ((k + 1) + 1) :=
          Submodule.add_mem _ hA (Submodule.smul_mem _ _ hvi)
        rw [← hs] at hsum
        simpa only [Nat.cast_succ, Int.natCast_add, Int.natCast_one, add_assoc] using hsum
  have hk (k : ℕ) : (A ^ k) (v s) ∈ p24ConsecutiveSpan v s (k + 1) := by
    induction k with
    | zero => simpa using (consecutive_gen v s (Nat.zero_lt_succ 0))
    | succ k ih =>
        have hA := consecutive_map_next A p v hstep s (k + 1) _ ih
        simpa only [pow_succ', Module.End.mul_apply] using hA
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact (krylov_mono A (v s) (by omega : (k : ℕ) + 1 ≤ m)) (hv k)
  · apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact (consecutive_mono v s (by omega : (k : ℕ) + 1 ≤ m)) (hk k)

private theorem twoSided_eq_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V]
    (A : Module.End ℝ V) (p : ℤ → ℝ) (v : ℤ → V)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) (m : ℕ) (hmpos : 0 < m) (hdim : Module.finrank ℝ V = m) :
    p24TwoSidedSpan v = p24KrylovSpan A (v s) m := by
  let K := p24KrylovSpan A (v s) m
  have hlast : (A ^ m) (v s) ∈ K := by
    simpa [K, hdim] using krylov_last_mem A (v s)
  have hAinvar : ∀ x ∈ K, A x ∈ K := krylov_invariant_of_last A (v s) _ hlast
  have hshift (j : ℤ) : ∀ x ∈ K, p24Shift A (p j) x ∈ K := by
    intro x hx
    change A x + p j • x ∈ K
    exact Submodule.add_mem _ (hAinvar x hx) (Submodule.smul_mem _ _ hx)
  have h_all (j : ℤ) : v j ∈ K := by
    refine Int.inductionOn' j s ?_ ?_ ?_
    · simpa [K] using (krylov_gen A (v s) hmpos)
    · intro j hj ih
      rw [hstep j]
      exact hshift j _ ih
    · intro j hj ih
      have hsurj : Set.SurjOn (p24Shift A (p (j - 1))) K K :=
          (LinearMap.injOn_iff_surjOn (hshift (j - 1))).mp
            (fun _ _ _ _ heq => (hinv (j - 1)).injective heq)
      obtain ⟨y, hy, hyeq⟩ := hsurj ih
      have hprev : v j = p24Shift A (p (j - 1)) (v (j - 1)) := by
        simpa using hstep (j - 1)
      have hveq : v (j - 1) = y :=
        (hinv (j - 1)).injective (hprev.symm.trans hyeq.symm)
      simpa [hveq] using hy
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact h_all j
  · rw [← consecutive_eq_krylov A p v hstep s]
    apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact Submodule.subset_span ⟨s + (k : ℕ), rfl⟩

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
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hcon := consecutive_eq_krylov A p v hstep s n
  have hs := twoSided_eq_krylov A p v hstep hinv s n hn hdim
  have hzero := twoSided_eq_krylov A p v hstep hinv 0 n hn hdim
  rw [hv0] at hzero
  constructor
  · exact hs.trans hcon.symm
  constructor
  · exact hcon
  · exact hs.symm.trans hzero

end VSCLReuse
