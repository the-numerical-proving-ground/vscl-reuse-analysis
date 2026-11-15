import VSCLReuse.P08.Definitions

namespace VSCLReuse

/-- Full Lemma 3.1: low-rank matrix-vector backward error and its A-relative bound. -/
theorem p08_c2_full_low_rank_matvec_error
    {b r : ℕ} (fp : StandardFPModel)
    (A : P08Matrix b) (X Y : P08RectMatrix b r) (v : P08Vector b)
    (ε β : ℝ) (hβ : 0 < β)
    (hX : p08OrthonormalColumns X)
    (happrox : p08FrobNorm (A - p08LowRankMatrix X Y) ≤ ε * β)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    let zHat := p08RoundedLowRankMatVec fp X Y v
    ∃ ΔAtilde ΔA : P08Matrix b,
      zHat = p08MatVec (p08RectAdd (p08LowRankMatrix X Y) ΔAtilde) v ∧
      p08FrobNorm ΔAtilde ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) ∧
      zHat = p08MatVec (p08RectAdd A ΔA) v ∧
      p08FrobNorm ΔA ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm A +
        ε * (1 + p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u) * β := by
  -- PROOF_START P08-C2-H001
  sorry

end VSCLReuse
