import VSCLReuse.P24.Definitions

namespace VSCLReuse

private theorem krylov_gen {n m : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) {k : ℕ} (hk : k < m) :
    (A ^ k) b ∈ p24KrylovSpan A b m := by
  apply Submodule.subset_span
  exact ⟨⟨k, hk⟩, rfl⟩

private theorem consecutive_gen {n m : ℕ} (v : ℤ → Fin n → ℝ)
    (s : ℤ) {k : ℕ} (hk : k < m) :
    v (s + k) ∈ p24ConsecutiveSpan v s m := by
  apply Submodule.subset_span
  exact ⟨⟨k, hk⟩, rfl⟩

private theorem krylov_mono {n m m' : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) (h : m ≤ m') :
    p24KrylovSpan A b m ≤ p24KrylovSpan A b m' := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact krylov_gen A b (lt_of_lt_of_le k.isLt h)

private theorem consecutive_mono {n m m' : ℕ} (v : ℤ → Fin n → ℝ)
    (s : ℤ) (h : m ≤ m') :
    p24ConsecutiveSpan v s m ≤ p24ConsecutiveSpan v s m' := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact consecutive_gen v s (lt_of_lt_of_le k.isLt h)

private theorem krylov_map_succ {n m : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (b : Fin n → ℝ) {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b m) :
    A x ∈ p24KrylovSpan A b (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa only [pow_succ', Module.End.mul_apply] using
        (krylov_gen A b (Nat.succ_lt_succ k.isLt))
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

private theorem consecutive_map_succ {n m : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    {x : Fin n → ℝ} (hx : x ∈ p24ConsecutiveSpan v s m) :
    A x ∈ p24ConsecutiveSpan v s (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have h₁ : v (s + (k : ℕ)) ∈ p24ConsecutiveSpan v s (m + 1) :=
        consecutive_gen v s (lt_of_lt_of_le k.isLt (Nat.le_succ m))
      have h₂ : v (s + ((k : ℕ) + 1)) ∈ p24ConsecutiveSpan v s (m + 1) :=
        consecutive_gen v s (Nat.succ_lt_succ k.isLt)
      have h₂' : v (s + (k : ℕ) + 1) ∈ p24ConsecutiveSpan v s (m + 1) := by
        convert h₂ using 1 <;> push_cast <;> ring
      have hs := hstep (s + (k : ℕ))
      simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hs
      change A (v (s + (k : ℕ))) ∈ p24ConsecutiveSpan v s (m + 1)
      have heq : A (v (s + (k : ℕ))) =
          v (s + (k : ℕ) + 1) - p (s + (k : ℕ)) • v (s + (k : ℕ)) := by
        rw [hs]
        abel
      rw [heq]
      exact Submodule.sub_mem _ h₂' (Submodule.smul_mem _ _ h₁)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

private theorem shifted_mem_krylov {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (k : ℕ) : v (s + k) ∈ p24KrylovSpan A (v s) (k + 1) := by
  induction k with
  | zero => simpa using krylov_gen A (v s) (Nat.zero_lt_succ 0)
  | succ k ih =>
      have hA := krylov_map_succ A (v s) ih
      have hp := (krylov_mono A (v s) (Nat.le_succ (k + 1))) ih
      have hs := hstep (s + k)
      simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hs
      have heq : v (s + ((k + 1 : ℕ) : ℤ)) =
          A (v (s + k)) + p (s + k) • v (s + k) := by
        convert hs using 1 <;> push_cast <;> ring
      rw [heq]
      exact Submodule.add_mem _ hA (Submodule.smul_mem _ _ hp)

private theorem power_mem_consecutive {n : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (k : ℕ) : (A ^ k) (v s) ∈ p24ConsecutiveSpan v s (k + 1) := by
  induction k with
  | zero => simpa using consecutive_gen v s (Nat.zero_lt_succ 0)
  | succ k ih =>
      simpa only [pow_succ', Module.End.mul_apply] using
        (consecutive_map_succ A p v s hstep ih)

private theorem consecutive_eq_krylov {n m : ℕ} (A : Module.End ℝ (Fin n → ℝ))
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ) (s : ℤ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j)) :
    p24ConsecutiveSpan v s m = p24KrylovSpan A (v s) m := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact (krylov_mono A (v s) (Nat.succ_le_of_lt k.isLt))
      (shifted_mem_krylov A p v s hstep k)
  · apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    exact (consecutive_mono v s (Nat.succ_le_of_lt k.isLt))
      (power_mem_consecutive A p v s hstep k)

private theorem every_power_mem_krylov {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p24KrylovSpan A b n := by
  have hcp : A.charpoly.natDegree = n := by
    simpa using A.charpoly_natDegree
  have hne : A.charpoly ≠ 1 := by
    intro he
    have : n = 0 := by simpa [he] using hcp.symm
    omega
  have hdeg : (Polynomial.X ^ k %ₘ A.charpoly).natDegree < n := by
    exact (Polynomial.natDegree_modByMonic_lt _ A.charpoly_monic hne).trans_eq hcp
  rw [A.pow_eq_aeval_mod_charpoly]
  rw [Polynomial.aeval_eq_sum_range' hdeg A]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (krylov_gen A b (Finset.mem_range.mp hi))

private theorem krylov_stable {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    A x ∈ p24KrylovSpan A b n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa only [pow_succ', Module.End.mul_apply] using
        (every_power_mem_krylov hn A b ((k : ℕ) + 1))
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

private theorem shift_stable {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (c : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    p24Shift A c x ∈ p24KrylovSpan A b n := by
  simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  exact Submodule.add_mem _ (krylov_stable hn A b hx) (Submodule.smul_mem _ _ hx)

private theorem preimage_mem_stable {n : ℕ} (f : Module.End ℝ (Fin n → ℝ))
    (hf : Function.Injective f) (K : Submodule ℝ (Fin n → ℝ))
    (hstable : ∀ x ∈ K, f x ∈ K) {x : Fin n → ℝ} (hx : x ∈ K) :
    ∃ y ∈ K, f y = x := by
  let g : K →ₗ[ℝ] K := f.restrict hstable
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hab
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hginj ⟨x, hx⟩
  exact ⟨y, y.property, congrArg Subtype.val hy⟩

private theorem all_shifted_mem_krylov {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s j : ℤ) : v j ∈ p24KrylovSpan A (v s) n := by
  let K := p24KrylovSpan A (v s) n
  have hbase : v s ∈ K := by
    simpa [K] using (krylov_gen A (v s) hn)
  have hback (t : ℤ) (ht : v (t + 1) ∈ K) : v t ∈ K := by
    have hstable : ∀ x ∈ K, p24Shift A (p t) x ∈ K := by
      intro x hx
      exact shift_stable hn A (v s) (p t) hx
    obtain ⟨y, hy, hfy⟩ :=
      preimage_mem_stable (p24Shift A (p t)) (hinv t).1 K hstable ht
    have hyt : y = v t := (hinv t).1 (hfy.trans (hstep t))
    simpa [hyt] using hy
  have hall : ∀ d : ℤ, v (s + d) ∈ K := by
    intro d
    induction d using Int.induction_on with
    | zero => simpa using hbase
    | succ i ih =>
        have hnext : v ((s + (i : ℤ)) + 1) ∈ K := by
          rw [hstep (s + i)]
          exact shift_stable hn A (v s) (p (s + i)) ih
        convert hnext using 1 <;> congr 1 <;> omega
    | pred i ih =>
        have hnext : v ((s - (i : ℤ) - 1) + 1) ∈ K := by
          convert ih using 1 <;> congr 1 <;> omega
        have hprev := hback (s - (i : ℤ) - 1) hnext
        convert hprev using 1 <;> congr 1 <;> omega
  convert hall (j - s) using 1 <;> congr 1 <;> omega

private theorem krylov_le_of_mem {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ)
    (hx : x ∈ p24KrylovSpan A b n) :
    p24KrylovSpan A x n ≤ p24KrylovSpan A b n := by
  have hpows : ∀ k : ℕ, (A ^ k) x ∈ p24KrylovSpan A b n := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        simpa only [pow_succ', Module.End.mul_apply] using
          (krylov_stable hn A b ih)
  apply Submodule.span_le.mpr
  rintro y ⟨k, rfl⟩
  exact hpows k

private theorem two_sided_eq_krylov {n : ℕ} (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) : p24TwoSidedSpan v = p24KrylovSpan A (v s) n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact all_shifted_mem_krylov hn A p v hstep hinv s j
  · rw [← consecutive_eq_krylov A p v s hstep]
    apply Submodule.span_le.mpr
    rintro x ⟨k, rfl⟩
    apply Submodule.subset_span
    exact ⟨s + k, rfl⟩

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
  have hfirst : p24TwoSidedSpan v = p24ConsecutiveSpan v s n := by
    rw [two_sided_eq_krylov hn A p v hstep hinv s]
    exact (consecutive_eq_krylov A p v s hstep).symm
  have hsecond : p24ConsecutiveSpan v s n = p24KrylovSpan A (v s) n :=
    consecutive_eq_krylov A p v s hstep
  have hsB : v s ∈ p24KrylovSpan A B n := by
    simpa only [hv0] using
      (all_shifted_mem_krylov hn A p v hstep hinv 0 s)
  have hBs : B ∈ p24KrylovSpan A (v s) n := by
    simpa only [hv0] using
      (all_shifted_mem_krylov hn A p v hstep hinv s 0)
  have hthird : p24KrylovSpan A (v s) n = p24KrylovSpan A B n := by
    apply le_antisymm
    · exact krylov_le_of_mem hn A B (v s) hsB
    · exact krylov_le_of_mem hn A (v s) B hBs
  exact ⟨hfirst, hsecond, hthird⟩

end VSCLReuse
