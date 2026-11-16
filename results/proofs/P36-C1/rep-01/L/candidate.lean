import VSCLReuse.P36.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P36-C1: the exceptional-point construction in Lemma 4.2. -/
theorem p36_c1_exceptional_point_approximation
    (k n : ℕ) (a b epsilon : ℝ)
    (nodes : Fin k → ℝ) (p : Polynomial ℝ)
    (ha : 0 < a) (hab : a < b)
    (hnodes : ∀ i, 0 < nodes i)
    (hinj : Function.Injective nodes)
    (hpdegree : p.natDegree ≤ n)
    (hpapprox : ∀ t, a ≤ t → t ≤ b →
      |t⁻¹ - Polynomial.eval t p| ≤ epsilon) :
    (p36ExtendedApproximant nodes p).natDegree ≤ n + k ∧
      (∀ i, Polynomial.eval (nodes i)
        (p36ExtendedApproximant nodes p) = (nodes i)⁻¹) ∧
      ∀ t, a ≤ t → t ≤ b →
        |t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p)| ≤
          p36IntervalFactor a b nodes * epsilon := by
  -- PROOF_START P36-C1-H001
  let phi := p36NodePolynomial nodes
  let c := Polynomial.eval 0 phi
  have hc : c ≠ 0 := by
    dsimp [c, phi, p36NodePolynomial]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact neg_ne_zero.mpr (ne_of_gt (hnodes i)))
  have hphi (t : ℝ) : Polynomial.eval t phi = ∏ i, (t - nodes i) := by
    simp [phi, p36NodePolynomial, Polynomial.eval_prod]
  have hdiv (t : ℝ) :
      t * Polynomial.eval t phi.divX + c = Polynomial.eval t phi := by
    have h := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
    simpa [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.coeff_zero_eq_eval_zero, c] using h
  have heval (t : ℝ) :
      Polynomial.eval t (p36ExtendedApproximant nodes p) =
        -(c⁻¹ * Polynomial.eval t phi.divX) +
          c⁻¹ * Polynomial.eval t phi * Polynomial.eval t p := by
    simp [p36ExtendedApproximant, p36Correction, phi, c, mul_assoc]
  have herror (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
        c⁻¹ * Polynomial.eval t phi *
          (t⁻¹ - Polynomial.eval t p) := by
    rw [heval]
    field_simp
    nlinarith [hdiv t]
  have hdegphi : phi.natDegree ≤ k := by
    calc
      phi.natDegree ≤ ∑ i : Fin k, (Polynomial.X - Polynomial.C (nodes i)).natDegree := by
        simpa [phi, p36NodePolynomial] using
          (Polynomial.natDegree_prod_le Finset.univ
            (fun i : Fin k => Polynomial.X - Polynomial.C (nodes i)))
      _ = k := by simp
  have hdegcorr : (p36Correction nodes).natDegree ≤ k := by
    calc
      (p36Correction nodes).natDegree =
          (Polynomial.C c⁻¹ * phi.divX).natDegree := by
            simp [p36Correction, phi, c]
      _ ≤ phi.divX.natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ phi.natDegree := Polynomial.natDegree_divX_le
      _ ≤ k := hdegphi
  have hdegext : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    unfold p36ExtendedApproximant
    dsimp only
    apply (Polynomial.natDegree_add_le_of_degree_le
      (hdegcorr.trans (Nat.le_add_left k n)) _)
    calc
      (Polynomial.C c⁻¹ * phi * p).natDegree ≤ (phi * p).natDegree := by
        simpa [mul_assoc] using
          (Polynomial.natDegree_C_mul_le c⁻¹ (phi * p))
      _ ≤ phi.natDegree + p.natDegree := Polynomial.natDegree_mul_le
      _ ≤ n + k := by omega
  refine ⟨hdegext, ?_, ?_⟩
  · intro i
    have hnode : nodes i ≠ 0 := ne_of_gt (hnodes i)
    have hphi_node : Polynomial.eval (nodes i) phi = 0 := by
      rw [hphi]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have h := herror (nodes i) hnode
    rw [hphi_node] at h
    simp only [mul_zero, zero_mul] at h
    linarith
  · intro t hat htb
    have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hat)
    have hfactor (i : Fin k) :
        |t - nodes i| ≤ max (b - nodes i) (nodes i - a) := by
      apply abs_le.mpr
      constructor
      · have h := le_max_right (b - nodes i) (nodes i - a)
        linarith
      · have h := le_max_left (b - nodes i) (nodes i - a)
        linarith
    have hprod :
        |Polynomial.eval t phi| ≤
          ∏ i, max (b - nodes i) (nodes i - a) := by
      rw [hphi, Finset.abs_prod]
      exact Finset.prod_le_prod (by intros; positivity)
        (by intro i hi; exact hfactor i)
    have hnonneg : 0 ≤ |c⁻¹| := abs_nonneg _
    have hbound :
        |c⁻¹| * |Polynomial.eval t phi| *
          |t⁻¹ - Polynomial.eval t p| ≤
          (|c⁻¹| * ∏ i, max (b - nodes i) (nodes i - a)) * epsilon := by
      have h₁ := mul_le_mul_of_nonneg_left hprod hnonneg
      have h₂ :
          (|c⁻¹| * |Polynomial.eval t phi|) *
              |t⁻¹ - Polynomial.eval t p| ≤
            (|c⁻¹| * |Polynomial.eval t phi|) * epsilon :=
        mul_le_mul_of_nonneg_left (hpapprox t hat htb)
          (mul_nonneg hnonneg (abs_nonneg _))
      have heps : 0 ≤ epsilon := le_trans (abs_nonneg _) (hpapprox t hat htb)
      exact h₂.trans (mul_le_mul_of_nonneg_right h₁ heps)
    rw [herror t ht, abs_mul, abs_mul]
    exact hbound

end VSCLReuse
