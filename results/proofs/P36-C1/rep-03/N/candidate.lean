import VSCLReuse.P36.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p36_error_formula {k : ℕ} (nodes : Fin k → ℝ)
    (p : Polynomial ℝ) (t : ℝ)
    (hzero : Polynomial.eval 0 (p36NodePolynomial nodes) ≠ 0)
    (ht : t ≠ 0) :
    t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
      (Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹ *
        Polynomial.eval t (p36NodePolynomial nodes) *
        (t⁻¹ - Polynomial.eval t p) := by
  let phi := p36NodePolynomial nodes
  have hdiv : t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi =
      Polynomial.eval t phi := by
    have h := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
    simpa [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.coeff_zero_eq_eval_zero] using h
  simp only [p36ExtendedApproximant, p36Correction, Polynomial.eval_add,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← hdiv]
  field_simp [ht, hzero]
  ring

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
  have hphi0 : Polynomial.eval 0 (p36NodePolynomial nodes) ≠ 0 := by
    unfold p36NodePolynomial
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simpa using (ne_of_gt (hnodes i))
  have hphi_degree : (p36NodePolynomial nodes).natDegree = k := by
    simp [p36NodePolynomial]
  have hdegree : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    unfold p36ExtendedApproximant p36Correction
    apply (Polynomial.natDegree_add_le_of_degree_le (n := n + k))
    · have h := Polynomial.natDegree_C_mul_le
          (Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹
          (p36NodePolynomial nodes).divX
      simpa only [Polynomial.natDegree_neg] using
        h.trans (Polynomial.natDegree_divX_le.trans (by omega :
          (p36NodePolynomial nodes).natDegree ≤ n + k))
    · have h := Polynomial.natDegree_C_mul_le
          (Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹
          (p36NodePolynomial nodes * p)
      simp only [mul_assoc]
      exact h.trans ((Polynomial.natDegree_mul_le).trans (by omega :
        (p36NodePolynomial nodes).natDegree + p.natDegree ≤ n + k))
  refine ⟨hdegree, ?_, ?_⟩
  · intro i
    have hnode : Polynomial.eval (nodes i) (p36NodePolynomial nodes) = 0 := by
      unfold p36NodePolynomial
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have hi : nodes i ≠ 0 := ne_of_gt (hnodes i)
    have herr := p36_error_formula nodes p (nodes i) hphi0 hi
    rw [hnode, mul_zero, zero_mul, sub_eq_zero] at herr
    exact herr.symm
  · intro t hat htb
    have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hat)
    have hfactor (i : Fin k) :
        |t - nodes i| ≤ max (b - nodes i) (nodes i - a) := by
      apply abs_le.mpr
      constructor
      · have := le_trans (sub_le_sub_left hat _) (le_max_right (b - nodes i) (nodes i - a))
        linarith
      · exact le_trans (sub_le_sub_right htb _) (le_max_left (b - nodes i) (nodes i - a))
    have hprod : |Polynomial.eval t (p36NodePolynomial nodes)| ≤
        ∏ i, max (b - nodes i) (nodes i - a) := by
      have hrewrite : |Polynomial.eval t (p36NodePolynomial nodes)| =
          ∏ i : Fin k, |t - nodes i| := by
        simp [p36NodePolynomial, Polynomial.eval_prod, Finset.abs_prod]
      rw [hrewrite]
      exact Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hfactor i)
    rw [p36_error_formula nodes p t hphi0 ht]
    rw [abs_mul, abs_mul]
    have hmain := mul_le_mul_of_nonneg_left
      (mul_le_mul hprod (hpapprox t hat htb) (abs_nonneg _) (by
        exact le_trans (abs_nonneg _) hprod))
      (abs_nonneg ((Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹))
    simpa [p36IntervalFactor, mul_assoc] using hmain

end VSCLReuse
