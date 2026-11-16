import VSCLReuse.P05.Definitions
import Mathlib

namespace VSCLReuse

private lemma p05_beta_pos (fmt : P05RadixFormat) : 0 < fmt.betaR := by
  unfold P05RadixFormat.betaR
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) fmt.beta_ge_two)

private lemma p05_mantissa_power (fmt : P05RadixFormat) :
    fmt.minNormalMantissa * fmt.beta = fmt.beta ^ fmt.precision := by
  unfold P05RadixFormat.minNormalMantissa
  rw [← pow_succ]
  congr 1
  have hp := fmt.precision_pos
  omega

private lemma p05_small_lattice (fmt : P05RadixFormat) (negative : Bool)
    (n m : ℕ) (hm : m < fmt.beta ^ fmt.precision)
    (hhi : fmt.normalEmin + (n : ℤ) ≤ fmt.normalEmax) :
    p05FiniteSystem fmt
      (fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^ (fmt.normalEmin + (n : ℤ) - (fmt.precision : ℤ))) := by
  induction n generalizing m with
  | zero =>
      by_cases hz : m = 0
      · left
        simp [hz]
      · by_cases hn : fmt.minNormalMantissa ≤ m
        · right; left
          refine ⟨negative, m, fmt.normalEmin, ⟨hn, hm⟩, ⟨le_refl _, ?_⟩, ?_⟩
          · simpa using hhi
          · simp [P05RadixFormat.normalizedValue]
        · right; right
          refine ⟨negative, m, ⟨Nat.pos_of_ne_zero hz, Nat.lt_of_not_ge hn⟩, ?_⟩
          simp [P05RadixFormat.subnormalValue, P05RadixFormat.normalEmin]
  | succ n ih =>
      by_cases hz : m = 0
      · left
        simp [hz]
      · by_cases hn : fmt.minNormalMantissa ≤ m
        · right; left
          refine ⟨negative, m, fmt.normalEmin + ((n + 1 : ℕ) : ℤ),
            ⟨hn, hm⟩, ⟨?_, hhi⟩, ?_⟩
          · omega
          · rfl
        · have hsmall : m < fmt.minNormalMantissa := Nat.lt_of_not_ge hn
          have hmul : m * fmt.beta < fmt.beta ^ fmt.precision := by
            rw [← p05_mantissa_power fmt]
            exact Nat.mul_lt_mul_of_pos_right hsmall
              (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) fmt.beta_ge_two)
          have hhi' : fmt.normalEmin + (n : ℤ) ≤ fmt.normalEmax := by omega
          have hres := ih (m * fmt.beta) hmul hhi'
          convert hres using 1
          have hbne : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
          have hexp : fmt.normalEmin + ((n + 1 : ℕ) : ℤ) - (fmt.precision : ℤ) =
              (fmt.normalEmin + (n : ℤ) - (fmt.precision : ℤ)) + 1 := by
            omega
          rw [hexp, zpow_add₀ hbne, zpow_one]
          simp only [Nat.cast_mul, P05RadixFormat.betaR]
          ring

private lemma p05_lattice (fmt : P05RadixFormat) (negative : Bool)
    (m : ℕ) (e : ℤ) (hlo : fmt.normalEmin ≤ e)
    (hhi : e < fmt.normalEmax) (hm : m ≤ fmt.beta ^ fmt.precision) :
    p05FiniteSystem fmt
      (fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  let n : ℕ := (e - fmt.normalEmin).toNat
  have hn : (n : ℤ) = e - fmt.normalEmin := by
    exact Int.toNat_of_nonneg (by omega)
  by_cases htop : m = fmt.beta ^ fmt.precision
  · right; left
    refine ⟨negative, fmt.minNormalMantissa, e + 1, ⟨le_refl _, ?_⟩,
      ⟨by omega, by omega⟩, ?_⟩
    · have hpow := p05_mantissa_power fmt
      have hbpos : 0 < fmt.beta := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) fmt.beta_ge_two
      have hminpos : 0 < fmt.minNormalMantissa := by
        unfold P05RadixFormat.minNormalMantissa
        exact pow_pos hbpos _
      have hmulge := Nat.mul_le_mul_left fmt.minNormalMantissa fmt.beta_ge_two
      omega
    · have hbne : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
      have hexp : e + 1 - (fmt.precision : ℤ) =
          (e - (fmt.precision : ℤ)) + 1 := by ring
      simp only [P05RadixFormat.normalizedValue, htop]
      rw [hexp, zpow_add₀ hbne, zpow_one]
      have hp : ((fmt.beta ^ fmt.precision : ℕ) : ℝ) =
          (fmt.minNormalMantissa : ℝ) * fmt.betaR := by
        change ((fmt.beta ^ fmt.precision : ℕ) : ℝ) =
          (fmt.minNormalMantissa : ℝ) * (fmt.beta : ℝ)
        exact_mod_cast (p05_mantissa_power fmt).symm
      rw [hp]
      ring
  · have hsmall : m < fmt.beta ^ fmt.precision := Nat.lt_of_le_of_ne hm htop
    have hhi' : fmt.normalEmin + (n : ℤ) ≤ fmt.normalEmax := by omega
    have hres := p05_small_lattice fmt negative n m hsmall hhi'
    have he : fmt.normalEmin + (n : ℤ) = e := by omega
    simpa only [he] using hres

private lemma p05_normal_lattice (fmt : P05RadixFormat) (negative : Bool)
    (m : ℕ) (e base : ℤ) (hbase : base ≤ e) :
    ∃ k : ℤ, fmt.normalizedValue negative m e =
      (k : ℝ) * fmt.betaR ^ (base - (fmt.precision : ℤ)) := by
  let d : ℕ := (e - base).toNat
  let k : ℤ := (if negative then -(m : ℤ) else (m : ℤ)) * (fmt.beta : ℤ) ^ d
  refine ⟨k, ?_⟩
  have hd : (d : ℤ) = e - base := Int.toNat_of_nonneg (by omega)
  have hbne : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
  have hpow : fmt.betaR ^ (e - (fmt.precision : ℤ)) =
      (((fmt.beta : ℤ) ^ d : ℤ) : ℝ) *
        fmt.betaR ^ (base - (fmt.precision : ℤ)) := by
    have hexp : e - (fmt.precision : ℤ) =
        (d : ℤ) + (base - (fmt.precision : ℤ)) := by omega
    rw [hexp, zpow_add₀ hbne, zpow_natCast]
    congr 1
    simp [P05RadixFormat.betaR]
  cases negative <;>
    simp [P05RadixFormat.normalizedValue, P05RadixFormat.signValue, k, hpow] <;>
    ring

private lemma p05_difference_lattice (fmt : P05RadixFormat) (x y : ℝ)
    (ex ey : ℤ) (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey) :
    ∃ k : ℤ, x - y = (k : ℝ) * fmt.betaR ^
      (min ex ey - (fmt.precision : ℤ)) := by
  obtain ⟨nx, mx, _, _, rfl⟩ := hx
  obtain ⟨ny, my, _, _, rfl⟩ := hy
  obtain ⟨kx, hkx⟩ := p05_normal_lattice fmt nx mx ex (min ex ey) (min_le_left _ _)
  obtain ⟨ky, hky⟩ := p05_normal_lattice fmt ny my ey (min ex ey) (min_le_right _ _)
  refine ⟨kx - ky, ?_⟩
  rw [hkx, hky]
  push_cast
  ring

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  let e := min ex ey
  obtain ⟨k, hk⟩ := p05_difference_lattice fmt x y ex ey hx hy
  have hlo : fmt.normalEmin ≤ e := by
    obtain ⟨_, _, _, ⟨hex, _⟩, _⟩ := hx
    obtain ⟨_, _, _, ⟨hey, _⟩, _⟩ := hy
    exact le_min hex hey
  have hbpos : 0 < fmt.betaR := p05_beta_pos fmt
  have hqpos : 0 < fmt.betaR ^ (e - (fmt.precision : ℤ)) := zpow_pos hbpos _
  have hpow : fmt.betaR ^ e =
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    have he : e = (fmt.precision : ℤ) + (e - (fmt.precision : ℤ)) := by ring
    rw [he, zpow_add₀ (ne_of_gt hbpos), zpow_natCast]
    simp [P05RadixFormat.betaR]
  have hboundReal : |(k : ℝ)| ≤ ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
    change |x - y| ≤ fmt.betaR ^ e at hmag
    rw [hk, abs_mul, abs_of_pos hqpos, hpow] at hmag
    exact (mul_le_mul_iff_of_pos_right hqpos).mp hmag
  have hbound : k.natAbs ≤ fmt.beta ^ fmt.precision := by
    have h : (k.natAbs : ℝ) ≤ ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hboundReal
    exact_mod_cast h
  have hrepr : p05FiniteSystem fmt (x - y) := by
    rcases Int.natAbs_eq k with hkpos | hkneg
    · rw [hk, hkpos]
      simpa [P05RadixFormat.signValue] using
        p05_lattice fmt false k.natAbs e hlo hnoOverflow hbound
    · rw [hk, hkneg]
      simpa [P05RadixFormat.signValue] using
        p05_lattice fmt true k.natAbs e hlo hnoOverflow hbound
  refine ⟨hrepr, ?_⟩
  rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
  · exact False.elim (hround.2 (x - y) hrepr (Or.inl ⟨hlt, le_refl _⟩))
  · exact heq
  · exact False.elim (hround.2 (x - y) hrepr (Or.inr ⟨le_refl _, hgt⟩))

end VSCLReuse
