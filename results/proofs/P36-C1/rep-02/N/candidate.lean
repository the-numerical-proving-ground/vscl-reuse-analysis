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
  let phi : Polynomial ℝ := p36NodePolynomial nodes
  let c : ℝ := Polynomial.eval 0 phi
  have hphi_eval (t : ℝ) : Polynomial.eval t phi = ∏ i : Fin k, (t - nodes i) := by
    simp [phi, p36NodePolynomial, Polynomial.eval_prod]
  have hc : c ≠ 0 := by
    change Polynomial.eval 0 phi ≠ 0
    rw [hphi_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simpa using (ne_of_gt (hnodes i))
  have hphi_div (t : ℝ) :
      t * Polynomial.eval t phi.divX + c = Polynomial.eval t phi := by
    have h := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.coeff_zero_eq_eval_zero] using h
  have hgeneral (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
        c⁻¹ * Polynomial.eval t phi * (t⁻¹ - Polynomial.eval t p) := by
    have hd := hphi_div t
    simp only [p36ExtendedApproximant, p36Correction, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C]
    change t⁻¹ - (-(c⁻¹ * Polynomial.eval t phi.divX) +
      c⁻¹ * Polynomial.eval t phi * Polynomial.eval t p) =
      c⁻¹ * Polynomial.eval t phi * (t⁻¹ - Polynomial.eval t p)
    field_simp
    nlinarith
  have hphideg : phi.natDegree ≤ k := by
    calc
      phi.natDegree ≤ ∑ i : Fin k,
          ((Polynomial.X : Polynomial ℝ) - Polynomial.C (nodes i)).natDegree := by
            simpa [phi, p36NodePolynomial] using
              (Polynomial.natDegree_prod_le (Finset.univ : Finset (Fin k))
                (fun i => (Polynomial.X : Polynomial ℝ) - Polynomial.C (nodes i)))
      _ = k := by simp [Polynomial.natDegree_X_sub_C]
  have hdegree : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    have hcorrection : (p36Correction nodes).natDegree ≤ k := by
      change (- (Polynomial.C c⁻¹ * phi.divX)).natDegree ≤ k
      simpa only [Polynomial.natDegree_neg] using
        ((Polynomial.natDegree_C_mul_le c⁻¹ phi.divX).trans
          (Polynomial.natDegree_divX_le.trans hphideg))
    have hterm : (Polynomial.C c⁻¹ * phi * p).natDegree ≤ k + n := by
      calc
        (Polynomial.C c⁻¹ * phi * p).natDegree ≤
            (Polynomial.C c⁻¹ * phi).natDegree + p.natDegree := Polynomial.natDegree_mul_le
        _ ≤ phi.natDegree + p.natDegree :=
          Nat.add_le_add_right (Polynomial.natDegree_C_mul_le c⁻¹ phi) _
        _ ≤ k + n := Nat.add_le_add hphideg hpdegree
    change (p36Correction nodes + Polynomial.C c⁻¹ * phi * p).natDegree ≤ n + k
    exact Polynomial.natDegree_add_le_of_degree_le (by omega) (by omega)
  have hnode (i : Fin k) :
      Polynomial.eval (nodes i) (p36ExtendedApproximant nodes p) = (nodes i)⁻¹ := by
    have hzero : Polynomial.eval (nodes i) phi = 0 := by
      rw [hphi_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have h := hgeneral (nodes i) (ne_of_gt (hnodes i))
    rw [hzero, mul_zero, zero_mul, sub_eq_zero] at h
    exact h.symm
  have hinterval (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
      |t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p)| ≤
        p36IntervalFactor a b nodes * epsilon := by
    have hfactor (i : Fin k) :
        |t - nodes i| ≤ max (b - nodes i) (nodes i - a) := by
      apply abs_le.mpr
      constructor
      · have hm := le_max_right (b - nodes i) (nodes i - a)
        linarith
      · have hm := le_max_left (b - nodes i) (nodes i - a)
        linarith
    have hprod : |Polynomial.eval t phi| ≤
        ∏ i : Fin k, max (b - nodes i) (nodes i - a) := by
      rw [hphi_eval, Finset.abs_prod]
      exact Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hfactor i)
    have hprod_nonneg : 0 ≤ ∏ i : Fin k, max (b - nodes i) (nodes i - a) :=
      (abs_nonneg _).trans hprod
    have happ := hpapprox t hat htb
    rw [hgeneral t (ne_of_gt (lt_of_lt_of_le ha hat))]
    simp only [abs_mul]
    change |c⁻¹| * |Polynomial.eval t phi| * |t⁻¹ - Polynomial.eval t p| ≤
      (|c⁻¹| * ∏ i : Fin k, max (b - nodes i) (nodes i - a)) * epsilon
    calc
      |c⁻¹| * |Polynomial.eval t phi| * |t⁻¹ - Polynomial.eval t p| ≤
          |c⁻¹| * (∏ i : Fin k, max (b - nodes i) (nodes i - a)) *
            |t⁻¹ - Polynomial.eval t p| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hprod (abs_nonneg _)) (abs_nonneg _)
      _ ≤ (|c⁻¹| * ∏ i : Fin k, max (b - nodes i) (nodes i - a)) * epsilon := by
            exact mul_le_mul_of_nonneg_left happ
              (mul_nonneg (abs_nonneg _) hprod_nonneg)
  exact ⟨hdegree, hnode, hinterval⟩

end VSCLReuse
