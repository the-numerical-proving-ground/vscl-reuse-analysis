import VSCLReuse.P24.Definitions

namespace VSCLReuse

private lemma p24_pow_mem_span (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p24KrylovSpan A b n := by
  classical
  have hdeg : (Polynomial.X ^ k %ₘ A.charpoly).degree < n := by
    calc
      _ < A.charpoly.degree :=
        Polynomial.degree_modByMonic_lt (Polynomial.X ^ k) A.charpoly_monic
      _ = n := by simp [Polynomial.degree_eq_natDegree A.charpoly_monic.ne_zero,
        A.charpoly_natDegree]
  have hEnd : A ^ k ∈
      Submodule.span ℝ (Set.range fun i : Fin n => A ^ (i : ℕ)) := by
    apply PowerBasis.mem_span_pow'.mpr
    exact ⟨Polynomial.X ^ k %ₘ A.charpoly, hdeg, A.pow_eq_aeval_mod_charpoly k⟩
  have hApply : ∀ f : Module.End ℝ (Fin n → ℝ),
      f ∈ Submodule.span ℝ (Set.range fun i : Fin n => A ^ (i : ℕ)) →
      f b ∈ p24KrylovSpan A b n := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa using add_mem ihx ihy
    | smul a x hx ih => simpa using (p24KrylovSpan A b n).smul_mem a ih
  exact hApply _ hEnd

private lemma p24_krylov_invariant (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) :
    ∀ x ∈ p24KrylovSpan A b n, A x ∈ p24KrylovSpan A b n := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simpa [pow_succ'] using p24_pow_mem_span n A b ((i : ℕ) + 1)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using add_mem ihx ihy
  | smul a x hx ih => simpa using (p24KrylovSpan A b n).smul_mem a ih

private lemma p24_shift_mem (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (q : ℝ) {x : Fin n → ℝ}
    (hx : x ∈ p24KrylovSpan A b n) :
    p24Shift A q x ∈ p24KrylovSpan A b n := by
  simpa [p24Shift] using
    (p24KrylovSpan A b n).add_mem (p24_krylov_invariant n A b x hx)
      ((p24KrylovSpan A b n).smul_mem q hx)

private lemma p24_shift_preimage_mem (n : ℕ) (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (q : ℝ) (hq : Function.Bijective (p24Shift A q))
    {x : Fin n → ℝ} (hx : p24Shift A q x ∈ p24KrylovSpan A b n) :
    x ∈ p24KrylovSpan A b n := by
  let K := p24KrylovSpan A b n
  let f := p24Shift A q
  have hf : ∀ y ∈ K, f y ∈ K := by
    intro y hy
    exact p24_shift_mem n A b q hy
  let g : K →ₗ[ℝ] K := f.restrict hf
  have hg : Function.Injective g := by
    intro y z h
    apply Subtype.ext
    apply hq.injective
    exact congrArg Subtype.val h
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hg ⟨f x, hx⟩
  have hxy : f y = f x := congrArg Subtype.val hy
  simpa only [hq.injective hxy] using y.property

private lemma p24_all_mem_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s j : ℤ) : v j ∈ p24KrylovSpan A (v s) n := by
  let K := p24KrylovSpan A (v s) n
  have hbase : v s ∈ K := by
    exact Submodule.subset_span ⟨⟨0, hn⟩, by simp⟩
  have hmem : ∀ k : ℤ, v (s + k) ∈ K := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hbase
    | succ i ih =>
        have h := p24_shift_mem n A (v s) (p (s + i)) ih
        have hs := hstep (s + i)
        rw [← hs] at h
        simpa only [Int.natCast_add, Int.natCast_one, add_assoc] using h
    | pred i ih =>
        apply p24_shift_preimage_mem n A (v s)
          (p (s + (-(i : ℤ) - 1))) (hinv (s + (-(i : ℤ) - 1)))
        have hs := hstep (s + (-(i : ℤ) - 1))
        have hidx : s + -(i : ℤ) = (s + (-(i : ℤ) - 1)) + 1 := by omega
        rw [hidx, hs] at ih
        exact ih
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hmem (j - s)

private lemma p24_consecutive_mem {n : ℕ} (v : ℤ → Fin n → ℝ)
    (s : ℤ) (m k : ℕ) (hk : k < m) :
    v (s + (k : ℤ)) ∈ p24ConsecutiveSpan v s m := by
  exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

private lemma p24_consecutive_mono {n : ℕ} (v : ℤ → Fin n → ℝ)
    (s : ℤ) {m l : ℕ} (hml : m ≤ l) :
    p24ConsecutiveSpan v s m ≤ p24ConsecutiveSpan v s l := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact p24_consecutive_mem v s l i (lt_of_lt_of_le i.isLt hml)

private lemma p24_A_consecutive {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) {x : Fin n → ℝ}
    (hx : x ∈ p24ConsecutiveSpan v s m) :
    A x ∈ p24ConsecutiveSpan v s (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hi : (i : ℕ) < m + 1 := by omega
      have hi1 : (i : ℕ) + 1 < m + 1 := by omega
      have hcur := p24_consecutive_mem v s (m + 1) (i : ℕ) hi
      have hnext := p24_consecutive_mem v s (m + 1) ((i : ℕ) + 1) hi1
      have hnext' : v ((s + (i : ℤ)) + 1) ∈
          p24ConsecutiveSpan v s (m + 1) := by
        simpa only [Int.natCast_add, Int.natCast_one, add_assoc] using hnext
      have heq : A (v (s + (i : ℤ))) =
          v ((s + (i : ℤ)) + 1) - p (s + (i : ℤ)) • v (s + (i : ℤ)) := by
        rw [hstep (s + (i : ℤ))]
        simp [p24Shift]
      rw [heq]
      exact (p24ConsecutiveSpan v s (m + 1)).sub_mem hnext'
        ((p24ConsecutiveSpan v s (m + 1)).smul_mem _ hcur)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using add_mem ihx ihy
  | smul a x hx ih => simpa using (p24ConsecutiveSpan v s (m + 1)).smul_mem a ih

private lemma p24_pow_mem_consecutive {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (k : ℕ) :
    (A ^ k) (v s) ∈ p24ConsecutiveSpan v s (k + 1) := by
  induction k with
  | zero =>
      simpa using p24_consecutive_mem v s 1 0 (by omega)
  | succ k ih =>
      have h := p24_A_consecutive A p v hstep s (k + 1) ih
      simpa only [pow_succ', Module.End.mul_apply, Nat.succ_eq_add_one,
        Nat.add_assoc] using h

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
  have hCK (t : ℤ) :
      p24ConsecutiveSpan v t n = p24KrylovSpan A (v t) n := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact p24_all_mem_krylov n hn A p v hstep hinv t (t + (i : ℤ))
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact (p24_consecutive_mono v t (Nat.succ_le_of_lt i.isLt))
        (p24_pow_mem_consecutive A p v hstep t (i : ℕ))
  have hTwo (t : ℤ) :
      p24TwoSidedSpan v = p24KrylovSpan A (v t) n := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact p24_all_mem_krylov n hn A p v hstep hinv t j
    · rw [← hCK t]
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨t + (i : ℤ), rfl⟩
  refine ⟨(hTwo s).trans (hCK s).symm, hCK s, ?_⟩
  calc
    p24KrylovSpan A (v s) n = p24TwoSidedSpan v := (hTwo s).symm
    _ = p24KrylovSpan A (v 0) n := hTwo 0
    _ = p24KrylovSpan A B n := by rw [hv0]

end VSCLReuse
