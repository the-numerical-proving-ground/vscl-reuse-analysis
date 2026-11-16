import VSCLReuse.P36.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p36_eval_nodePolynomial {k : ℕ} (nodes : Fin k → ℝ) (t : ℝ) :
    Polynomial.eval t (p36NodePolynomial nodes) = ∏ i, (t - nodes i) := by
  simp [p36NodePolynomial, Polynomial.eval_prod]

private lemma p36_eval_zero_ne {k : ℕ} (nodes : Fin k → ℝ)
    (hnodes : ∀ i, 0 < nodes i) :
    Polynomial.eval 0 (p36NodePolynomial nodes) ≠ 0 := by
  rw [p36_eval_nodePolynomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simpa only [zero_sub, neg_ne_zero] using ne_of_gt (hnodes i)

private lemma p36_eval_node_self {k : ℕ} (nodes : Fin k → ℝ) (i : Fin k) :
    Polynomial.eval (nodes i) (p36NodePolynomial nodes) = 0 := by
  rw [p36_eval_nodePolynomial]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

private lemma p36_nodePolynomial_degree {k : ℕ} (nodes : Fin k → ℝ) :
    (p36NodePolynomial nodes).natDegree ≤ k := by
  calc
    _ ≤ ∑ i : Fin k, (Polynomial.X - Polynomial.C (nodes i)).natDegree := by
      simpa only [p36NodePolynomial] using
        (Polynomial.natDegree_prod_le (s := Finset.univ)
          (fun i : Fin k => Polynomial.X - Polynomial.C (nodes i)))
    _ = k := by simp

private lemma p36_eval_error_identity {k : ℕ} (nodes : Fin k → ℝ)
    (hnodes : ∀ i, 0 < nodes i) (p : Polynomial ℝ)
    (t : ℝ) (ht : t ≠ 0) :
    t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
      (Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹ *
        Polynomial.eval t (p36NodePolynomial nodes) *
        (t⁻¹ - Polynomial.eval t p) := by
  let phi := p36NodePolynomial nodes
  let c := Polynomial.eval 0 phi
  have hc : c ≠ 0 := p36_eval_zero_ne nodes hnodes
  have hdiv : t * Polynomial.eval t phi.divX + c = Polynomial.eval t phi := by
    simpa [c, Polynomial.coeff_zero_eq_eval_zero] using
      congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
  simp only [p36ExtendedApproximant, p36Correction, Polynomial.eval_add,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_C] 
  change t⁻¹ - (- (c⁻¹ * Polynomial.eval t phi.divX) +
    c⁻¹ * Polynomial.eval t phi * Polynomial.eval t p) =
    c⁻¹ * Polynomial.eval t phi * (t⁻¹ - Polynomial.eval t p)
  rw [← hdiv]
  field_simp
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
  have hphi_degree := p36_nodePolynomial_degree nodes
  have hdegree : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    let phi := p36NodePolynomial nodes
    let c := Polynomial.eval 0 phi
    have hcorrection : (p36Correction nodes).natDegree ≤ n + k := by
      change (-(Polynomial.C (c⁻¹) * phi.divX)).natDegree ≤ n + k
      calc
        _ = (Polynomial.C (c⁻¹) * phi.divX).natDegree := by simp
        _ ≤ phi.divX.natDegree := Polynomial.natDegree_C_mul_le _ _
        _ ≤ phi.natDegree := Polynomial.natDegree_divX_le
        _ ≤ k := hphi_degree
        _ ≤ n + k := by omega
    have hproduct : (Polynomial.C (c⁻¹) * phi * p).natDegree ≤ n + k := by
      calc
        _ ≤ (Polynomial.C (c⁻¹) * phi).natDegree + p.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ phi.natDegree + p.natDegree := by
          exact Nat.add_le_add_right (Polynomial.natDegree_C_mul_le _ _) _
        _ ≤ k + n := Nat.add_le_add hphi_degree hpdegree
        _ = n + k := Nat.add_comm _ _
    change (p36Correction nodes + Polynomial.C (c⁻¹) * phi * p).natDegree ≤ n + k
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hcorrection hproduct)
  have hinterp : ∀ i, Polynomial.eval (nodes i)
      (p36ExtendedApproximant nodes p) = (nodes i)⁻¹ := by
    intro i
    have h := p36_eval_error_identity nodes hnodes p (nodes i) (ne_of_gt (hnodes i))
    rw [p36_eval_node_self] at h
    simp only [mul_zero, zero_mul] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨hdegree, hinterp, ?_⟩
  intro t hta htb
  have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hta)
  have hphi_bound : |Polynomial.eval t (p36NodePolynomial nodes)| ≤
      ∏ i, max (b - nodes i) (nodes i - a) := by
    rw [p36_eval_nodePolynomial, Finset.abs_prod]
    apply Finset.prod_le_prod
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      apply abs_le.mpr
      constructor
      · have hm := le_max_right (b - nodes i) (nodes i - a)
        linarith
      · have hm := le_max_left (b - nodes i) (nodes i - a)
        linarith
  have hprod_nonneg : 0 ≤ ∏ i, max (b - nodes i) (nodes i - a) := by
    apply Finset.prod_nonneg
    intro i hi
    have hml := le_max_left (b - nodes i) (nodes i - a)
    have hmr := le_max_right (b - nodes i) (nodes i - a)
    linarith
  have herror := p36_eval_error_identity nodes hnodes p t ht
  calc
    |t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p)| =
        |(Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹| *
          |Polynomial.eval t (p36NodePolynomial nodes)| *
          |t⁻¹ - Polynomial.eval t p| := by rw [herror, abs_mul, abs_mul]
    _ ≤ |(Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹| *
          (∏ i, max (b - nodes i) (nodes i - a)) *
          |t⁻¹ - Polynomial.eval t p| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hphi_bound (abs_nonneg _)) (abs_nonneg _)
    _ ≤ p36IntervalFactor a b nodes * epsilon := by
      change |(Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹| *
        (∏ i, max (b - nodes i) (nodes i - a)) *
        |t⁻¹ - Polynomial.eval t p| ≤
        (|(Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹| *
        (∏ i, max (b - nodes i) (nodes i - a))) * epsilon
      exact mul_le_mul_of_nonneg_left (hpapprox t hta htb)
        (mul_nonneg (abs_nonneg _) hprod_nonneg)

end VSCLReuse
