import VSCLReuse.P05.Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace VSCLReuse

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  let nf : NumStability.FloatingPointFormat := {
    beta := fmt.beta
    t := fmt.precision
    emin := fmt.normalEmin
    emax := fmt.normalEmax
    beta_ge_two := fmt.beta_ge_two
    t_pos := fmt.precision_pos
    emin_le_emax := by
      have h := fmt.emin_le_emax
      dsimp [P05RadixFormat.normalEmin, P05RadixFormat.normalEmax]
      omega
  }
  have hnx : nf.normalizedExponentRepresentation x ex := by
    simpa [nf, P05NormalizedExponentRepresentation,
      NumStability.FloatingPointFormat.normalizedExponentRepresentation,
      P05RadixFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.mantissaInRange,
      P05RadixFormat.normalizedExponentInRange,
      NumStability.FloatingPointFormat.exponentInRange,
      P05RadixFormat.normalizedValue,
      NumStability.FloatingPointFormat.normalizedValue,
      P05RadixFormat.signValue,
      NumStability.FloatingPointFormat.signValue,
      P05RadixFormat.betaR,
      NumStability.FloatingPointFormat.betaR,
      P05RadixFormat.minNormalMantissa,
      NumStability.FloatingPointFormat.minNormalMantissa] using hx
  have hny : nf.normalizedExponentRepresentation y ey := by
    simpa [nf, P05NormalizedExponentRepresentation,
      NumStability.FloatingPointFormat.normalizedExponentRepresentation,
      P05RadixFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.mantissaInRange,
      P05RadixFormat.normalizedExponentInRange,
      NumStability.FloatingPointFormat.exponentInRange,
      P05RadixFormat.normalizedValue,
      NumStability.FloatingPointFormat.normalizedValue,
      P05RadixFormat.signValue,
      NumStability.FloatingPointFormat.signValue,
      P05RadixFormat.betaR,
      NumStability.FloatingPointFormat.betaR,
      P05RadixFormat.minNormalMantissa,
      NumStability.FloatingPointFormat.minNormalMantissa] using hy
  have hmag' : |x - y| ≤ nf.betaR ^ min ex ey := by
    simpa [nf, NumStability.FloatingPointFormat.betaR, P05RadixFormat.betaR] using hmag
  have hfin_nf : nf.finiteSystem (x - y) := by
    by_cases hstrict : |x - y| < nf.betaR ^ min ex ey
    · exact nf.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
        ⟨ex, ey, hnx, hny, hstrict⟩
    · have heq : |x - y| = nf.betaR ^ min ex ey := by
        exact le_antisymm hmag' (le_of_not_gt hstrict)
      obtain ⟨_, _, _, hex, _⟩ := hnx
      obtain ⟨_, _, _, hey, _⟩ := hny
      have he : nf.exponentInRange (min ex ey + 1) := by
        change fmt.normalEmin ≤ min ex ey + 1 ∧ min ex ey + 1 ≤ fmt.normalEmax
        have hlo : fmt.normalEmin ≤ min ex ey := le_min hex.1 hey.1
        omega
      have hend := nf.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow
        (min ex ey)
      by_cases hpos : 0 ≤ x - y
      · rw [abs_of_nonneg hpos] at heq
        exact Or.inr (Or.inl
          ⟨false, nf.minNormalMantissa, min ex ey + 1,
            nf.minNormalMantissa_normalized, he, heq.trans hend.symm⟩)
      · have hneg : x - y < 0 := lt_of_not_ge hpos
        rw [abs_of_neg hneg] at heq
        have hdiff : x - y = nf.normalizedValue true nf.minNormalMantissa
            (min ex ey + 1) := by
          rw [nf.normalizedValue_true_eq_neg_false, hend]
          linarith
        exact Or.inr (Or.inl
          ⟨true, nf.minNormalMantissa, min ex ey + 1,
            nf.minNormalMantissa_normalized, he, hdiff⟩)
  have hfin : p05FiniteSystem fmt (x - y) := by
    simpa [nf, p05FiniteSystem, NumStability.FloatingPointFormat.finiteSystem,
      NumStability.FloatingPointFormat.normalizedSystem,
      NumStability.FloatingPointFormat.subnormalSystem,
      P05RadixFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.mantissaInRange,
      P05RadixFormat.normalizedExponentInRange,
      NumStability.FloatingPointFormat.exponentInRange,
      P05RadixFormat.normalizedValue,
      NumStability.FloatingPointFormat.normalizedValue,
      P05RadixFormat.signValue,
      NumStability.FloatingPointFormat.signValue,
      P05RadixFormat.betaR,
      NumStability.FloatingPointFormat.betaR,
      P05RadixFormat.minNormalMantissa,
      NumStability.FloatingPointFormat.minNormalMantissa,
      P05RadixFormat.subnormalMantissa,
      NumStability.FloatingPointFormat.subnormalMantissa,
      P05RadixFormat.subnormalValue,
      NumStability.FloatingPointFormat.subnormalValue,
      P05RadixFormat.normalEmin] using hfin_nf
  refine ⟨hfin, ?_⟩
  rcases hround with ⟨_, hnone⟩
  rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
  · exact False.elim (hnone (x - y) hfin (Or.inl ⟨hlt, le_rfl⟩))
  · exact heq
  · exact False.elim (hnone (x - y) hfin (Or.inr ⟨le_rfl, hgt⟩))

end VSCLReuse
