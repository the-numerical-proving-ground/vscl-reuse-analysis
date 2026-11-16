import VSCLReuse.P05.Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace VSCLReuse

private def p05AsNumFormat (fmt : P05RadixFormat) :
    NumStability.FloatingPointFormat where
  beta := fmt.beta
  t := fmt.precision
  emin := fmt.normalEmin
  emax := fmt.normalEmax
  beta_ge_two := fmt.beta_ge_two
  t_pos := fmt.precision_pos
  emin_le_emax := by
    change fmt.emin + (fmt.precision : ℤ) ≤
      fmt.emax + (fmt.precision : ℤ)
    have := fmt.emin_le_emax
    omega

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  let nf := p05AsNumFormat fmt
  have hxf : nf.normalizedExponentRepresentation x ex := by
    exact hx
  have hyf : nf.normalizedExponentRepresentation y ey := by
    exact hy
  have hmagf : |x - y| ≤ nf.betaR ^ min ex ey := hmag
  have hnoOverflowf : min ex ey < nf.emax := hnoOverflow
  have hfinf : nf.finiteSystem (x - y) := by
    rcases lt_or_eq_of_le hmagf with hlt | heq
    · exact nf.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
        ⟨ex, ey, hxf, hyf, hlt⟩
    · have hex : nf.exponentInRange ex := by
        rcases hxf with ⟨_, _, _, he, _⟩
        exact he
      have hey : nf.exponentInRange ey := by
        rcases hyf with ⟨_, _, _, he, _⟩
        exact he
      have he : nf.exponentInRange (min ex ey + 1) := by
        constructor
        · have := hex.1
          have := hey.1
          omega
        · omega
      have hposfin : nf.finiteSystem (nf.betaR ^ min ex ey) := by
        right
        left
        refine ⟨false, nf.minNormalMantissa, min ex ey + 1,
          nf.minNormalMantissa_normalized, he, ?_⟩
        rw [nf.normalizedValue_false_minNormalMantissa_eq]
        congr 1
        omega
      rcases le_total 0 (x - y) with hnonneg | hnonpos
      · rw [abs_of_nonneg hnonneg] at heq
        rw [heq]
        exact hposfin
      · rw [abs_of_nonpos hnonpos] at heq
        have hdiff : x - y = -(nf.betaR ^ min ex ey) := by
          linarith
        rw [hdiff]
        exact nf.finiteSystem_neg hposfin
  have hfin : p05FiniteSystem fmt (x - y) := by
    rcases hfinf with hz | hnorm | hsub
    · exact Or.inl hz
    · exact Or.inr (Or.inl hnorm)
    · rcases hsub with ⟨negative, m, hm, hz⟩
      right
      right
      refine ⟨negative, m, hm, ?_⟩
      rw [hz]
      change
        (p05AsNumFormat fmt).signValue negative * (m : ℝ) *
          (p05AsNumFormat fmt).betaR ^
            ((p05AsNumFormat fmt).emin -
              ((p05AsNumFormat fmt).t : ℤ)) =
        fmt.signValue negative * (m : ℝ) * fmt.betaR ^ fmt.emin
      congr 1
      simp [p05AsNumFormat, P05RadixFormat.normalEmin,
        NumStability.FloatingPointFormat.betaR, P05RadixFormat.betaR]
  refine ⟨hfin, ?_⟩
  rcases hround with ⟨_, hfaithful⟩
  rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
  · exact False.elim (hfaithful (x - y) hfin (Or.inl ⟨hlt, le_refl _⟩))
  · exact heq
  · exact False.elim (hfaithful (x - y) hfin (Or.inr ⟨le_refl _, hgt⟩))

end VSCLReuse
