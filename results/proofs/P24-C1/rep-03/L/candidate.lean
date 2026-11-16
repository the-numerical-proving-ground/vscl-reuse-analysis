import VSCLReuse.P24.Definitions

namespace VSCLReuse

private def p24Prefix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun k : Fin m ↦ w k)

private lemma p24_mem_prefix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) {m k : ℕ} (hk : k < m) : w k ∈ p24Prefix w m := by
  exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

private lemma p24_prefix_mono {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) {m l : ℕ} (hml : m ≤ l) : p24Prefix w m ≤ p24Prefix w l := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact p24_mem_prefix w (lt_of_lt_of_le k.isLt hml)

private lemma p24_map_prefix {V : Type*} [AddCommGroup V] [Module ℝ V]
    (w : ℕ → V) (m : ℕ) (F : Module.End ℝ V) (T : Submodule ℝ V)
    (h : ∀ k : Fin m, F (w k) ∈ T) :
    ∀ x ∈ p24Prefix w m, F x ∈ T := by
  intro x hx
  have hh : Submodule.map F (p24Prefix w m) ≤ T := by
    apply (Submodule.map_span_le F _ T).mpr
    rintro y ⟨k, rfl⟩
    exact h k
  exact hh ⟨x, hx, rfl⟩

private lemma p24_shift_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (q : ℝ) (x : V) :
    p24Shift A q x = A x + q • x := by
  simp [p24Shift]

private lemma p24_prefix_shift_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (q : ℕ → ℝ) (w : ℕ → V)
    (hrec : ∀ k, w (k + 1) = A (w k) + q k • w k) (m : ℕ) :
    p24Prefix w m = p24Prefix (fun k ↦ (A ^ k) (w 0)) m := by
  let u : ℕ → V := fun k ↦ (A ^ k) (w 0)
  have hu (k : ℕ) : u (k + 1) = A (u k) := by
    simp [u, pow_succ', Module.End.mul_apply]
  have hw_mem : ∀ k : ℕ, w k ∈ p24Prefix u (k + 1) := by
    intro k
    induction k with
    | zero =>
        simpa [u] using p24_mem_prefix u (Nat.zero_lt_succ 0)
    | succ k ih =>
        have hA : A (w k) ∈ p24Prefix u (k + 2) := by
          apply p24_map_prefix u (k + 1) A _ _ (w k) ih
          intro i
          rw [← hu]
          exact p24_mem_prefix u (by omega : (i : ℕ) + 1 < k + 2)
        rw [hrec]
        exact (p24Prefix u (k + 2)).add_mem hA
          ((p24Prefix u (k + 2)).smul_mem _
            ((p24_prefix_mono u (by omega : k + 1 ≤ k + 2)) ih))
  have hu_mem : ∀ k : ℕ, u k ∈ p24Prefix w (k + 1) := by
    intro k
    induction k with
    | zero =>
        simpa [u] using p24_mem_prefix w (Nat.zero_lt_succ 0)
    | succ k ih =>
        rw [hu]
        apply p24_map_prefix w (k + 1) A _ _ (u k) ih
        intro i
        have hwi : w ((i : ℕ) + 1) ∈ p24Prefix w (k + 2) :=
          p24_mem_prefix w (by omega)
        have hwi' : w (i : ℕ) ∈ p24Prefix w (k + 2) :=
          p24_mem_prefix w (by omega)
        have hAw : A (w i) = w ((i : ℕ) + 1) - q i • w i := by
          rw [hrec]
          abel
        rw [hAw]
        exact (p24Prefix w (k + 2)).sub_mem hwi
          ((p24Prefix w (k + 2)).smul_mem _ hwi')
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (p24_prefix_mono u (by omega : (i : ℕ) + 1 ≤ m)) (hw_mem i)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (p24_prefix_mono w (by omega : (i : ℕ) + 1 ≤ m)) (hu_mem i)

private lemma p24_krylov_pow_mem (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (k : ℕ) :
    (A ^ k) b ∈ p24KrylovSpan A b n := by
  let r : Polynomial ℝ := Polynomial.X ^ k %ₘ A.charpoly
  have hchar : A.charpoly ≠ 1 := by
    intro heq
    have hd := A.charpoly_natDegree
    rw [heq, Polynomial.natDegree_one, Module.finrank_fin_fun] at hd
    omega
  have hr : r.natDegree < n := by
    simpa only [r, A.charpoly_natDegree, Module.finrank_fin_fun] using
      Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) A.charpoly_monic hchar
  rw [LinearMap.pow_eq_aeval_mod_charpoly]
  change Polynomial.aeval A r b ∈ p24KrylovSpan A b n
  rw [Polynomial.aeval_endomorphism]
  rw [Polynomial.sum_over_range' _ (by simp) n hr]
  apply Submodule.sum_mem
  intro i hi
  exact (p24KrylovSpan A b n).smul_mem _
    (p24_mem_prefix (fun j ↦ (A ^ j) b) (Finset.mem_range.mp hi))

private lemma p24_krylov_stable (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ)
    (hx : x ∈ p24KrylovSpan A b n) :
    A x ∈ p24KrylovSpan A b n := by
  change x ∈ p24Prefix (fun k ↦ (A ^ k) b) n at hx
  change A x ∈ p24Prefix (fun k ↦ (A ^ k) b) n
  apply p24_map_prefix (fun k ↦ (A ^ k) b) n A _ _ x hx
  intro i
  have h : A ((A ^ (i : ℕ)) b) = (A ^ ((i : ℕ) + 1)) b := by
    simp [pow_succ', Module.End.mul_apply]
  rw [h]
  exact p24_krylov_pow_mem n hn A b _

private lemma p24_shift_stable (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ) (q : ℝ)
    (hx : x ∈ p24KrylovSpan A b n) :
    p24Shift A q x ∈ p24KrylovSpan A b n := by
  rw [p24_shift_apply]
  exact (p24KrylovSpan A b n).add_mem (p24_krylov_stable n hn A b x hx)
    ((p24KrylovSpan A b n).smul_mem _ hx)

private lemma p24_shift_preimage_mem (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (b x : Fin n → ℝ) (q : ℝ)
    (hq : Function.Bijective (p24Shift A q))
    (hx : p24Shift A q x ∈ p24KrylovSpan A b n) :
    x ∈ p24KrylovSpan A b n := by
  let K := p24KrylovSpan A b n
  have hstable : ∀ y ∈ K, p24Shift A q y ∈ K :=
    fun y hy ↦ p24_shift_stable n hn A b y q hy
  let F : K →ₗ[ℝ] K := (p24Shift A q).restrict hstable
  have hF : Function.Injective F := by
    intro y z heq
    apply Subtype.ext
    exact hq.1 (congrArg Subtype.val heq)
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hF ⟨p24Shift A q x, hx⟩
  have heq : p24Shift A q y = p24Shift A q x :=
    congrArg Subtype.val hy
  have hxy : (y : Fin n → ℝ) = x := hq.1 heq
  exact hxy ▸ y.property

private lemma p24_consecutive_eq_krylov (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) : p24ConsecutiveSpan v s n = p24KrylovSpan A (v s) n := by
  let w : ℕ → Fin n → ℝ := fun k ↦ v (s + (k : ℤ))
  have hrec (k : ℕ) : w (k + 1) = A (w k) + p (s + (k : ℤ)) • w k := by
    have hs := hstep (s + (k : ℤ))
    rw [p24_shift_apply] at hs
    simpa [w, Nat.cast_add, add_assoc] using hs
  have h := p24_prefix_shift_eq A (fun k ↦ p (s + (k : ℤ))) w hrec n
  simpa [p24ConsecutiveSpan, p24KrylovSpan, p24Prefix, w] using h

private lemma p24_all_mem_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s t : ℤ) : v t ∈ p24KrylovSpan A (v s) n := by
  have hbase : v s ∈ p24KrylovSpan A (v s) n := by
    simpa [p24KrylovSpan, p24Prefix] using
      (p24_mem_prefix (fun k ↦ (A ^ k) (v s)) hn)
  rcases le_total s t with hst | hts
  · induction t, hst using Int.le_induction with
    | base => exact hbase
    | succ j hj ih =>
        rw [hstep j]
        exact p24_shift_stable n hn A (v s) (v j) (p j) ih
  · induction t, hts using Int.le_induction_down with
    | base => exact hbase
    | pred j hj ih =>
        have hs : p24Shift A (p (j - 1)) (v (j - 1)) = v j := by
          simpa using (hstep (j - 1)).symm
        apply p24_shift_preimage_mem n hn A (v s) (v (j - 1)) (p (j - 1))
          (hinv (j - 1))
        rw [hs]
        exact ih

private lemma p24_twoSided_eq_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) : p24TwoSidedSpan v = p24KrylovSpan A (v s) n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨t, rfl⟩
    exact p24_all_mem_krylov n hn A p v hstep hinv s t
  · rw [← p24_consecutive_eq_krylov n A p v hstep s]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
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
  have hs := p24_twoSided_eq_krylov n hn A p v hstep hinv s
  have hzero := p24_twoSided_eq_krylov n hn A p v hstep hinv 0
  have hc := p24_consecutive_eq_krylov n A p v hstep s
  refine ⟨hs.trans hc.symm, hc, ?_⟩
  calc
    p24KrylovSpan A (v s) n = p24TwoSidedSpan v := hs.symm
    _ = p24KrylovSpan A (v 0) n := hzero
    _ = p24KrylovSpan A B n := by rw [hv0]

end VSCLReuse
