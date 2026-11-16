import VSCLReuse.P05.Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace VSCLReuse

private def p05LibraryFormat (fmt : P05RadixFormat) : NumStability.FloatingPointFormat where
  beta := fmt.beta
  t := fmt.precision
  emin := fmt.normalEmin
  emax := fmt.normalEmax
  beta_ge_two := fmt.beta_ge_two
  t_pos := fmt.precision_pos
  emin_le_emax := by
    dsimp [P05RadixFormat.normalEmin, P05RadixFormat.normalEmax]
    have h := fmt.emin_le_emax
    omega

private theorem p05_normalized_to_library
    (fmt : P05RadixFormat) (x : ℝ) (e : ℤ)
    (h : P05NormalizedExponentRepresentation fmt x e) :
    (p05LibraryFormat fmt).normalizedExponentRepresentation x e := by
  rcases h with ⟨negative, m, hm, he, hx⟩
  refine ⟨negative, m, ?_, ?_, ?_⟩
  · exact hm
  · exact he
  · exact hx

private theorem p05_finite_of_library
    (fmt : P05RadixFormat) (x : ℝ)
    (h : (p05LibraryFormat fmt).finiteSystem x) :
    p05FiniteSystem fmt x := by
  rcases h with hz | hn | hs
  · exact Or.inl hz
  · rcases hn with ⟨negative, m, e, hm, he, hx⟩
    exact Or.inr (Or.inl ⟨negative, m, e, hm, he, hx⟩)
  · rcases hs with ⟨negative, m, hm, hx⟩
    right; right
    refine ⟨negative, m, hm, ?_⟩
    simpa [p05LibraryFormat, P05RadixFormat.subnormalValue,
      NumStability.FloatingPointFormat.subnormalValue,
      P05RadixFormat.normalEmin,
      P05RadixFormat.signValue, NumStability.FloatingPointFormat.signValue,
      P05RadixFormat.betaR, NumStability.FloatingPointFormat.betaR] using hx

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  let g := p05LibraryFormat fmt
  have hxg : g.normalizedExponentRepresentation x ex :=
    p05_normalized_to_library fmt x ex hx
  have hyg : g.normalizedExponentRepresentation y ey :=
    p05_normalized_to_library fmt y ey hy
  have hgmag : |x - y| ≤ g.betaR ^ min ex ey := hmag
  have hfin : g.finiteSystem (x - y) := by
    rcases lt_or_eq_of_le hgmag with hlt | heq
    · exact g.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
        ⟨ex, ey, hxg, hyg, hlt⟩
    · have hmin : g.emin ≤ min ex ey := by
        apply le_min
        · exact hxg.choose_spec.choose_spec.2.1.1
        · exact hyg.choose_spec.choose_spec.2.1.1
      have hover : min ex ey < g.emax := hnoOverflow
      have hpow : g.finiteSystem (g.betaR ^ min ex ey) := by
        right; left
        refine ⟨false, g.minNormalMantissa, min ex ey + 1,
          g.minNormalMantissa_normalized, ⟨by omega, by omega⟩, ?_⟩
        rw [g.normalizedValue_false_minNormalMantissa_eq]
        congr 1
        omega
      by_cases hnonneg : 0 ≤ x - y
      · rw [abs_of_nonneg hnonneg] at heq
        rw [heq]
        exact hpow
      · have hneg : x - y < 0 := lt_of_not_ge hnonneg
        rw [abs_of_neg hneg] at heq
        have hval : x - y = -(g.betaR ^ min ex ey) := by linarith
        rw [hval]
        exact g.finiteSystem_neg hpow
  have hfinite : p05FiniteSystem fmt (x - y) :=
    p05_finite_of_library fmt (x - y) hfin
  constructor
  · exact hfinite
  · rcases hround with ⟨_, faithful⟩
    by_contra hne
    rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
    · exact faithful (x - y) hfinite (Or.inl ⟨hlt, le_rfl⟩)
    · exact hne heq
    · exact faithful (x - y) hfinite (Or.inr ⟨le_rfl, hgt⟩)

end VSCLReuse
