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
  have hphiDegree : phi.natDegree = k := by
    simp [phi, p36NodePolynomial]
  have hphiZero : Polynomial.eval 0 phi ≠ 0 := by
    simp only [phi, p36NodePolynomial, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact neg_ne_zero.mpr (ne_of_gt (hnodes i)))
  have hdiv (t : ℝ) :
      t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi =
        Polynomial.eval t phi := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.coeff_zero_eq_eval_zero] using
      congrArg (Polynomial.eval t) (Polynomial.X_mul_divX_add phi)
  have herr (t : ℝ) (ht : t ≠ 0) :
      t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p) =
        (Polynomial.eval 0 phi)⁻¹ * Polynomial.eval t phi *
          (t⁻¹ - Polynomial.eval t p) := by
    have hcore : t⁻¹ + (Polynomial.eval 0 phi)⁻¹ *
        Polynomial.eval t phi.divX =
        (Polynomial.eval 0 phi)⁻¹ * Polynomial.eval t phi * t⁻¹ := by
      calc
        t⁻¹ + (Polynomial.eval 0 phi)⁻¹ * Polynomial.eval t phi.divX =
            (Polynomial.eval 0 phi)⁻¹ *
              (t * Polynomial.eval t phi.divX + Polynomial.eval 0 phi) * t⁻¹ := by
                field_simp
                <;> ring
        _ = _ := by rw [hdiv]
    simp only [p36ExtendedApproximant, p36Correction, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C]
    dsimp [phi] at hcore ⊢
    linear_combination hcore
  have hdegreeCorrection : (p36Correction nodes).natDegree ≤ k := by
    change (-(Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi.divX)).natDegree ≤ k
    rw [Polynomial.natDegree_neg]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_divX_le).trans_eq hphiDegree)
  have hdegree : (p36ExtendedApproximant nodes p).natDegree ≤ n + k := by
    change (p36Correction nodes +
      Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi * p).natDegree ≤ n + k
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · omega
    · calc
        (Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi * p).natDegree ≤
            (phi * p).natDegree := by
              simpa only [mul_assoc] using
                (Polynomial.natDegree_C_mul_le ((Polynomial.eval 0 phi)⁻¹) (phi * p))
        _ ≤ phi.natDegree + p.natDegree := Polynomial.natDegree_mul_le
        _ ≤ n + k := by omega
  have hnode (i : Fin k) : Polynomial.eval (nodes i) phi = 0 := by
    simp [phi, p36NodePolynomial, Polynomial.eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ i)]
  have hnodeEval (i : Fin k) :
      Polynomial.eval (nodes i) (p36ExtendedApproximant nodes p) =
        (nodes i)⁻¹ := by
    have hi : nodes i ≠ 0 := ne_of_gt (hnodes i)
    have := herr (nodes i) hi
    rw [hnode i, mul_zero, zero_mul, sub_eq_zero] at this
    exact this.symm
  have hfactor (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (i : Fin k) :
      |t - nodes i| ≤ max (b - nodes i) (nodes i - a) := by
    apply abs_le.mpr
    constructor
    · have := le_max_right (b - nodes i) (nodes i - a)
      linarith
    · have := le_max_left (b - nodes i) (nodes i - a)
      linarith
  have hphiBound (t : ℝ) (hat : a ≤ t) (htb : t ≤ b) :
      |Polynomial.eval t phi| ≤
        ∏ i, max (b - nodes i) (nodes i - a) := by
    have heval : Polynomial.eval t phi = ∏ i, (t - nodes i) := by
      simp [phi, p36NodePolynomial, Polynomial.eval_prod]
    rw [heval, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i hi => abs_nonneg _)
      (fun i hi => hfactor t hat htb i)
  have hprodNonneg :
      0 ≤ ∏ i, max (b - nodes i) (nodes i - a) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (abs_nonneg (a - nodes i)).trans (hfactor a le_rfl hab.le i)
  refine ⟨hdegree, hnodeEval, ?_⟩
  intro t hat htb
  have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hat)
  rw [herr t ht, abs_mul, abs_mul]
  change |(Polynomial.eval 0 phi)⁻¹| *
      |Polynomial.eval t phi| * |t⁻¹ - Polynomial.eval t p| ≤
    |(Polynomial.eval 0 phi)⁻¹| *
      (∏ i, max (b - nodes i) (nodes i - a)) * epsilon
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul (hphiBound t hat htb) (hpapprox t hat htb)
        (abs_nonneg _) hprodNonneg)
      (abs_nonneg ((Polynomial.eval 0 phi)⁻¹)))

end VSCLReuse
