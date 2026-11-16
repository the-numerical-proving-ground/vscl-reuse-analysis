import VSCLReuse.P24.Definitions

namespace VSCLReuse

private theorem p24_pow_mem_krylov (n k : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) :
    (A ^ k) b ∈ p24KrylovSpan A b n := by
  open Polynomial in
  have hdeg : ((Polynomial.X : ℝ[X]) ^ k %ₘ A.charpoly).degree < (n : WithBot ℕ) := by
    have h := Polynomial.degree_modByMonic_lt ((Polynomial.X : ℝ[X]) ^ k)
      (LinearMap.charpoly_monic A)
    simpa only [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic A).ne_zero,
      LinearMap.charpoly_natDegree, Module.finrank_fin_fun] using h
  have hEnd : A ^ k ∈ Submodule.span ℝ
      (Set.range fun i : Fin n => A ^ (i : ℕ)) := by
    apply (PowerBasis.mem_span_pow').2
    exact ⟨_, hdeg, LinearMap.pow_eq_aeval_mod_charpoly A k⟩
  have hmap : Submodule.map (LinearMap.applyₗ b)
      (Submodule.span ℝ (Set.range fun i : Fin n => A ^ (i : ℕ))) ≤
      p24KrylovSpan A b n := by
    rw [Submodule.map_span_le]
    intro f hf
    obtain ⟨i, rfl⟩ := hf
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hmap (Submodule.mem_map_of_mem hEnd)

private theorem p24_krylov_A_closed (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    A x ∈ p24KrylovSpan A b n := by
  have hmap : Submodule.map A (p24KrylovSpan A b n) ≤ p24KrylovSpan A b n := by
    change Submodule.map A (Submodule.span ℝ (Set.range fun i : Fin n =>
      (A ^ (i : ℕ)) b)) ≤ p24KrylovSpan A b n
    rw [Submodule.map_span_le]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    simpa only [← Module.End.mul_apply, ← pow_succ'] using
      p24_pow_mem_krylov n (i.val + 1) A b
  exact hmap (Submodule.mem_map_of_mem hx)

private theorem p24_krylov_shift_closed (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (t : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b n) :
    p24Shift A t x ∈ p24KrylovSpan A b n := by
  change A x + t • x ∈ p24KrylovSpan A b n
  exact Submodule.add_mem (p24KrylovSpan A b n)
    (p24_krylov_A_closed n A b hx) (Submodule.smul_mem _ t hx)

private theorem p24_krylov_shift_reflect (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) (t : ℝ)
    (ht : Function.Bijective (p24Shift A t))
    {x : Fin n → ℝ} (hx : p24Shift A t x ∈ p24KrylovSpan A b n) :
    x ∈ p24KrylovSpan A b n := by
  let K := p24KrylovSpan A b n
  let F : K →ₗ[ℝ] K := (p24Shift A t).restrict
    (fun y hy => p24_krylov_shift_closed n A b t hy)
  have hF : Function.Injective F := by
    intro y z hyz
    apply Subtype.ext
    exact ht.injective (congrArg Subtype.val hyz)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hF) ⟨p24Shift A t x, hx⟩
  have heq : p24Shift A t y = p24Shift A t x := congrArg Subtype.val hy
  exact (ht.injective heq).symm ▸ y.property

private theorem p24_range_fin_succ_last {V : Type*} (f : ℕ → V) (m : ℕ) :
    Set.range (fun i : Fin (m + 1) => f i.val) =
      insert (f m) (Set.range fun i : Fin m => f i.val) := by
  ext x
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
    · exact Or.inr ⟨⟨i, h⟩, rfl⟩
    · exact Or.inl (by simp [h])
  · rintro (h | ⟨⟨i, hi⟩, rfl⟩)
    · subst x
      exact ⟨⟨m, Nat.lt_succ_self m⟩, rfl⟩
    · exact ⟨⟨i, Nat.lt_trans hi (Nat.lt_succ_self m)⟩, rfl⟩

private theorem p24_span_insert_congr {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (x y : V) (h : x - y ∈ Submodule.span ℝ S) :
    Submodule.span ℝ (insert x S) = Submodule.span ℝ (insert y S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hzx | hz
    · rw [hzx]
      have hy : y ∈ Submodule.span ℝ (insert y S) :=
        Submodule.subset_span (Set.mem_insert y S)
      have hd : x - y ∈ Submodule.span ℝ (insert y S) :=
        (Submodule.span_mono (Set.subset_insert y S)) h
      convert Submodule.add_mem _ hy hd using 1 <;> abel
    · exact Submodule.subset_span (Set.mem_insert_of_mem y hz)
  · rw [Submodule.span_le]
    intro z hz
    rcases hz with hzy | hz
    · rw [hzy]
      have hx : x ∈ Submodule.span ℝ (insert x S) :=
        Submodule.subset_span (Set.mem_insert x S)
      have hd : x - y ∈ Submodule.span ℝ (insert x S) :=
        (Submodule.span_mono (Set.subset_insert x S)) h
      convert Submodule.sub_mem _ hx hd using 1 <;> abel
    · exact Submodule.subset_span (Set.mem_insert_of_mem x hz)

private theorem p24_krylov_prefix_A (n m : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ p24KrylovSpan A b m) :
    A x ∈ p24KrylovSpan A b (m + 1) := by
  have hmap : Submodule.map A (p24KrylovSpan A b m) ≤
      p24KrylovSpan A b (m + 1) := by
    change Submodule.map A (Submodule.span ℝ (Set.range fun i : Fin m =>
      (A ^ (i : ℕ)) b)) ≤ p24KrylovSpan A b (m + 1)
    rw [Submodule.map_span_le]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨⟨i.val + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt i.isLt)⟩, ?_⟩
    simp only [← Module.End.mul_apply, ← pow_succ']
  exact hmap (Submodule.mem_map_of_mem hx)

private theorem p24_krylov_prefix_mono (n m : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (b : Fin n → ℝ) :
    p24KrylovSpan A b m ≤ p24KrylovSpan A b (m + 1) := by
  unfold p24KrylovSpan
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩, rfl⟩

private theorem p24_shifted_diff_mem_prefix (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    v (s + (m : ℤ)) - (A ^ m) (v s) ∈ p24KrylovSpan A (v s) m := by
  induction m with
  | zero => simp [p24KrylovSpan]
  | succ m ih =>
      have hvm : v (s + (m : ℤ)) ∈ p24KrylovSpan A (v s) (m + 1) := by
        have hdiff := p24_krylov_prefix_mono n m A (v s) ih
        have hpow : (A ^ m) (v s) ∈ p24KrylovSpan A (v s) (m + 1) := by
          apply Submodule.subset_span
          exact ⟨⟨m, Nat.lt_succ_self m⟩, rfl⟩
        have := Submodule.add_mem _ hdiff hpow
        convert this using 1 <;> abel
      have hA := p24_krylov_prefix_A n m A (v s) ih
      have hp := Submodule.smul_mem (p24KrylovSpan A (v s) (m + 1))
        (p (s + (m : ℤ))) hvm
      have hsum := Submodule.add_mem (p24KrylovSpan A (v s) (m + 1)) hA hp
      convert hsum using 1
      · rw [show s + ((m + 1 : ℕ) : ℤ) = (s + (m : ℤ)) + 1 by push_cast; ring,
          hstep (s + (m : ℤ))]
        simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply, pow_succ', Module.End.mul_apply, map_sub]
        abel

private theorem p24_consecutive_eq_krylov (n : ℕ)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (s : ℤ) (m : ℕ) :
    p24ConsecutiveSpan v s m = p24KrylovSpan A (v s) m := by
  induction m with
  | zero => simp [p24ConsecutiveSpan, p24KrylovSpan]
  | succ m ih =>
      have hc : p24ConsecutiveSpan v s (m + 1) =
          Submodule.span ℝ (insert (v (s + (m : ℤ)))
            (Set.range fun i : Fin m => v (s + (i : ℕ)))) := by
        unfold p24ConsecutiveSpan
        rw [p24_range_fin_succ_last (fun k : ℕ => v (s + (k : ℤ))) m]
      have hk : p24KrylovSpan A (v s) (m + 1) =
          Submodule.span ℝ (insert ((A ^ m) (v s))
            (Set.range fun i : Fin m => (A ^ (i : ℕ)) (v s))) := by
        unfold p24KrylovSpan
        rw [p24_range_fin_succ_last (fun k : ℕ => (A ^ k) (v s)) m]
      rw [hc, hk]
      have hd := p24_shifted_diff_mem_prefix n A p v hstep s m
      rw [← ih] at hd
      calc
        _ = Submodule.span ℝ (insert ((A ^ m) (v s))
              (Set.range fun i : Fin m => v (s + (i : ℕ)))) :=
          p24_span_insert_congr
            (Set.range fun i : Fin m => v (s + (i : ℕ)))
            (v (s + (m : ℤ))) ((A ^ m) (v s)) hd
        _ = _ := by
          rw [Submodule.span_insert, Submodule.span_insert]
          change (ℝ ∙ (A ^ m) (v s)) ⊔ p24ConsecutiveSpan v s m =
            (ℝ ∙ (A ^ m) (v s)) ⊔ p24KrylovSpan A (v s) m
          rw [ih]

private theorem p24_two_sided_eq_krylov (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (p : ℤ → ℝ)
    (v : ℤ → Fin n → ℝ)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) :
    p24TwoSidedSpan v = p24KrylovSpan A (v s) n := by
  let K := p24KrylovSpan A (v s) n
  have hbase : v s ∈ K := by
    change v s ∈ p24KrylovSpan A (v s) n
    apply Submodule.subset_span
    exact ⟨⟨0, hn⟩, by simp⟩
  have hall : ∀ j : ℤ, v j ∈ K := by
    have hoffset : ∀ i : ℤ, v (s + i) ∈ K := by
      intro i
      induction i using Int.induction_on with
      | zero => simpa using hbase
      | succ i ih =>
          have h := p24_krylov_shift_closed n A (v s) (p (s + (i : ℤ))) ih
          rw [← hstep (s + (i : ℤ))] at h
          simpa only [add_assoc] using h
      | pred i ih =>
          let j := s + (-(i : ℤ) - 1)
          have hidx : j + 1 = s + -(i : ℤ) := by dsimp [j]; ring
          have hs : v (s + -(i : ℤ)) = p24Shift A (p j) (v j) := by
            rw [← hidx]
            exact hstep j
          have hshift : p24Shift A (p j) (v j) ∈ K := by rw [← hs]; exact ih
          exact p24_krylov_shift_reflect n A (v s) (p j) (hinv j) hshift
    intro j
    have hj : s + (j - s) = j := by ring
    simpa only [hj] using hoffset (j - s)
  have hforward : p24TwoSidedSpan v ≤ K := by
    rw [p24TwoSidedSpan, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact hall j
  have hAclosed : ∀ x ∈ p24TwoSidedSpan v, A x ∈ p24TwoSidedSpan v := by
    intro x hx
    have hmap : Submodule.map A (p24TwoSidedSpan v) ≤ p24TwoSidedSpan v := by
      change Submodule.map A (Submodule.span ℝ (Set.range v)) ≤ p24TwoSidedSpan v
      rw [Submodule.map_span_le]
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      have hnext : v (j + 1) ∈ p24TwoSidedSpan v :=
        Submodule.subset_span ⟨j + 1, rfl⟩
      have hcur : v j ∈ p24TwoSidedSpan v :=
        Submodule.subset_span ⟨j, rfl⟩
      have heq : A (v j) = v (j + 1) - p j • v j := by
        rw [hstep j]
        simp only [p24Shift, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hnext (Submodule.smul_mem _ (p j) hcur)
    exact hmap (Submodule.mem_map_of_mem hx)
  have hpow : ∀ k : ℕ, (A ^ k) (v s) ∈ p24TwoSidedSpan v := by
    intro k
    induction k with
    | zero =>
        simpa using (Submodule.subset_span (R := ℝ) (s := Set.range v) ⟨s, rfl⟩)
    | succ k ih =>
        simpa only [pow_succ', Module.End.mul_apply] using hAclosed _ ih
  have hbackward : K ≤ p24TwoSidedSpan v := by
    change p24KrylovSpan A (v s) n ≤ p24TwoSidedSpan v
    rw [p24KrylovSpan, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hpow i.val
  exact le_antisymm hforward hbackward

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
  have hcon := p24_consecutive_eq_krylov n A p v hstep s n
  have htwo := p24_two_sided_eq_krylov n hn A p v hstep hinv s
  have htwo0 := p24_two_sided_eq_krylov n hn A p v hstep hinv 0
  constructor
  · exact htwo.trans hcon.symm
  constructor
  · exact hcon
  · calc
      p24KrylovSpan A (v s) n = p24TwoSidedSpan v := htwo.symm
      _ = p24KrylovSpan A (v 0) n := htwo0
      _ = p24KrylovSpan A B n := by rw [hv0]

end VSCLReuse
