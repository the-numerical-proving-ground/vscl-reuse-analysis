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
  let c := (Polynomial.eval 0 phi)⁻¹
  have hphi_degree : phi.natDegree = k := by
    change (∏ i : Fin k, (Polynomial.X - Polynomial.C (nodes i))).natDegree = k
    simpa using
      (Polynomial.natDegree_finset_prod_X_sub_C_eq_card
        (Finset.univ : Finset (Fin k)) nodes)
  have hphi_eval (t : ℝ) : Polynomial.eval t phi = ∏ i, (t - nodes i) := by
    simp [phi, p36NodePolynomial, Polynomial.eval_prod]
  have hphi_zero : Polynomial.eval 0 phi ≠ 0 := by
    rw [hphi_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have h := ne_of_gt (hnodes i)
    simpa using h
  have hc : c * Polynomial.eval 0 phi = 1 := inv_mul_cancel₀ hphi_zero
  have hdiv (t : ℝ) :
      t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi =
        Polynomial.eval t phi := by
    have h := congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.coeff_zero_eq_eval_zero] using h
  have hevalext (t : ℝ) :
      Polynomial.eval t (p36ExtendedApproximant nodes p) =
        -(c * Polynomial.eval t phi.divX) +
          c * Polynomial.eval t phi * Polynomial.eval t p := by
    change Polynomial.eval t
      (-(Polynomial.C c * phi.divX) + Polynomial.C c * phi * p) = _
    simp only [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_C]
  have hrec (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ + c * Polynomial.eval t phi.divX =
        c * Polynomial.eval t phi * t⁻¹ := by
    calc
      t⁻¹ + c * Polynomial.eval t phi.divX =
          c * Polynomial.eval t phi.divX + t⁻¹ := by ring
      _ = c * (t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi) * t⁻¹ := by
        calc
          c * Polynomial.eval t phi.divX + t⁻¹ =
              c * Polynomial.eval t phi.divX * (t * t⁻¹) +
                (c * Polynomial.eval 0 phi) * t⁻¹ := by rw [mul_inv_cancel₀ ht, hc]; ring
          _ = c * (t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi) * t⁻¹ := by ring
      _ = c * Polynomial.eval t phi * t⁻¹ := by rw [hdiv]
  have herror (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
        (c * Polynomial.eval t phi) * (t⁻¹ - Polynomial.eval t p) := by
    rw [hevalext]
    calc
      t⁻¹ - (-(c * Polynomial.eval t phi.divX) +
          c * Polynomial.eval t phi * Polynomial.eval t p) =
          (t⁻¹ + c * Polynomial.eval t phi.divX) -
            (c * Polynomial.eval t phi) * Polynomial.eval t p := by ring
      _ = (c * Polynomial.eval t phi) * t⁻¹ -
            (c * Polynomial.eval t phi) * Polynomial.eval t p := by rw [hrec t ht]
      _ = (c * Polynomial.eval t phi) * (t⁻¹ - Polynomial.eval t p) := by ring
  have hdegree : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    have hcorr : (p36Correction nodes).natDegree ≤ k := by
      change (-(Polynomial.C c * phi.divX)).natDegree ≤ k
      rw [Polynomial.natDegree_neg]
      exact (Polynomial.natDegree_C_mul_le c phi.divX).trans
        ((Polynomial.natDegree_divX_le).trans hphi_degree.le)
    have hprod : (Polynomial.C c * phi * p).natDegree ≤ n + k := by
      calc
        (Polynomial.C c * phi * p).natDegree ≤
            (Polynomial.C c * phi).natDegree + p.natDegree := Polynomial.natDegree_mul_le
        _ ≤ phi.natDegree + p.natDegree :=
          Nat.add_le_add_right (Polynomial.natDegree_C_mul_le c phi) _
        _ ≤ k + n := by rw [hphi_degree]; exact Nat.add_le_add_left hpdegree _
        _ = n + k := Nat.add_comm _ _
    change (p36Correction nodes + Polynomial.C c * phi * p).natDegree ≤ n + k
    exact Polynomial.natDegree_add_le_of_degree_le
      (hcorr.trans (by omega)) hprod
  have hnodes_exact : ∀ i, Polynomial.eval (nodes i)
      (p36ExtendedApproximant nodes p) = (nodes i)⁻¹ := by
    intro i
    have hphi_node : Polynomial.eval (nodes i) phi = 0 := by
      rw [hphi_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have h := herror (nodes i) (ne_of_gt (hnodes i))
    rw [hphi_node] at h
    simp only [mul_zero, zero_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hphi_bound (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
      |Polynomial.eval t phi| ≤ ∏ i, max (b - nodes i) (nodes i - a) := by
    rw [hphi_eval, Finset.abs_prod]
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
  have heps : 0 ≤ epsilon :=
    (abs_nonneg (a⁻¹ - Polynomial.eval a p)).trans
      (hpapprox a le_rfl hab.le)
  refine ⟨hdegree, hnodes_exact, ?_⟩
  intro t hat htb
  have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hat)
  rw [herror t ht, abs_mul, abs_mul]
  change |c| * |Polynomial.eval t phi| * |t⁻¹ - Polynomial.eval t p| ≤
    (|c| * ∏ i, max (b - nodes i) (nodes i - a)) * epsilon
  calc
    |c| * |Polynomial.eval t phi| * |t⁻¹ - Polynomial.eval t p| ≤
        |c| * |Polynomial.eval t phi| * epsilon :=
      mul_le_mul_of_nonneg_left (hpapprox t hat htb)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ (|c| * ∏ i, max (b - nodes i) (nodes i - a)) * epsilon := by
      apply mul_le_mul_of_nonneg_right _ heps
      exact mul_le_mul_of_nonneg_left (hphi_bound t hat htb) (abs_nonneg _)

end VSCLReuse
