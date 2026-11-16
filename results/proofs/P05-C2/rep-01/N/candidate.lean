import VSCLReuse.P05.Definitions
import Mathlib

namespace VSCLReuse

private theorem p05_grid_small (fmt : P05RadixFormat) (negative : Bool) :
    ∀ (d n : ℕ),
      fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax →
      n < fmt.beta ^ fmt.precision →
      p05FiniteSystem fmt
        (fmt.signValue negative * (n : ℝ) *
          fmt.betaR ^ (fmt.normalEmin + (d : ℤ) - (fmt.precision : ℤ))) := by
  intro d
  induction d with
  | zero =>
      intro n hupper hn
      by_cases hz : n = 0
      · left
        simp [hz]
      by_cases hsmall : n < fmt.minNormalMantissa
      · right
        right
        refine ⟨negative, n, ⟨Nat.pos_of_ne_zero hz, hsmall⟩, ?_⟩
        simp [P05RadixFormat.subnormalValue, P05RadixFormat.normalEmin]
      · right
        left
        refine ⟨negative, n, fmt.normalEmin, ⟨Nat.le_of_not_gt hsmall, hn⟩,
          ⟨le_rfl, ?_⟩, ?_⟩
        · simpa using hupper
        · simp [P05RadixFormat.normalizedValue]
  | succ d ih =>
      intro n hupper hn
      by_cases hz : n = 0
      · left
        simp [hz]
      by_cases hnormal : fmt.minNormalMantissa ≤ n
      · right
        left
        refine ⟨negative, n, fmt.normalEmin + (d + 1 : ℕ),
          ⟨hnormal, hn⟩, ⟨?_, hupper⟩, rfl⟩
        omega
      · have hsmall : n < fmt.minNormalMantissa := Nat.lt_of_not_ge hnormal
        have hmul : n * fmt.beta < fmt.beta ^ fmt.precision := by
          have hpos : 0 < fmt.beta := by have := fmt.beta_ge_two; omega
          have hh := Nat.mul_lt_mul_of_pos_right hsmall hpos
          calc
            n * fmt.beta < fmt.beta ^ (fmt.precision - 1) * fmt.beta := hh
            _ = fmt.beta ^ fmt.precision := by
              rw [← pow_succ]
              congr 1
              have := fmt.precision_pos
              omega
        have hupper' : fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax := by omega
        have hstep := ih (n * fmt.beta) hupper' hmul
        convert hstep using 1
        have hbeta : fmt.betaR ≠ 0 := by
          unfold P05RadixFormat.betaR
          exact_mod_cast (show fmt.beta ≠ 0 by have := fmt.beta_ge_two; omega)
        have hpow :
            fmt.betaR ^ (fmt.normalEmin + ((d + 1 : ℕ) : ℤ) -
              (fmt.precision : ℤ)) =
            fmt.betaR ^ (fmt.normalEmin + (d : ℤ) -
              (fmt.precision : ℤ)) * fmt.betaR := by
          rw [show fmt.normalEmin + ((d + 1 : ℕ) : ℤ) -
              (fmt.precision : ℤ) =
              (fmt.normalEmin + (d : ℤ) - (fmt.precision : ℤ)) + 1 by omega]
          rw [zpow_add₀ hbeta]
          simp
        rw [hpow]
        simp only [Nat.cast_mul, P05RadixFormat.betaR]
        ring

private theorem p05_grid_le (fmt : P05RadixFormat) (negative : Bool)
    (n : ℕ) (e : ℤ)
    (hlo : fmt.normalEmin ≤ e)
    (hhi : e < fmt.normalEmax)
    (hn : n ≤ fmt.beta ^ fmt.precision) :
    p05FiniteSystem fmt
      (fmt.signValue negative * (n : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  by_cases hlt : n < fmt.beta ^ fmt.precision
  · let d : ℕ := (e - fmt.normalEmin).toNat
    have hde : fmt.normalEmin + (d : ℤ) = e := by
      dsimp [d]
      omega
    have hupper : fmt.normalEmin + (d : ℤ) ≤ fmt.normalEmax := by omega
    simpa only [hde] using p05_grid_small fmt negative d n hupper hlt
  · have heq : n = fmt.beta ^ fmt.precision := by omega
    have hprec : fmt.precision - 1 < fmt.precision := by
      have := fmt.precision_pos
      omega
    have hbetagt : 1 < fmt.beta := by
      have := fmt.beta_ge_two
      omega
    have hmant : fmt.minNormalMantissa < fmt.beta ^ fmt.precision := by
      exact Nat.pow_lt_pow_right hbetagt hprec
    right
    left
    refine ⟨negative, fmt.minNormalMantissa, e + 1,
      ⟨le_rfl, hmant⟩, ⟨by omega, by omega⟩, ?_⟩
    have hbeta : fmt.betaR ≠ 0 := by
      unfold P05RadixFormat.betaR
      exact_mod_cast (show fmt.beta ≠ 0 by omega)
    have hp : fmt.beta ^ fmt.precision =
        fmt.minNormalMantissa * fmt.beta := by
      unfold P05RadixFormat.minNormalMantissa
      rw [← pow_succ]
      congr 1
      omega
    have hpow : fmt.betaR ^ ((e + 1) - (fmt.precision : ℤ)) =
        fmt.betaR ^ (e - (fmt.precision : ℤ)) * fmt.betaR := by
      rw [show e + 1 - (fmt.precision : ℤ) =
          (e - (fmt.precision : ℤ)) + 1 by omega]
      rw [zpow_add₀ hbeta]
      simp
    rw [heq, hp]
    simp only [P05RadixFormat.normalizedValue, hpow, Nat.cast_mul]
    unfold P05RadixFormat.betaR
    ring

private theorem p05_signed_value (fmt : P05RadixFormat) (negative : Bool)
    (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e =
      (((if negative then -(m : ℤ) else (m : ℤ)) : ℤ) : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
  cases negative <;>
    simp [P05RadixFormat.normalizedValue, P05RadixFormat.signValue]

private theorem p05_aligned_value (fmt : P05RadixFormat) (negative : Bool)
    (m : ℕ) (e e0 : ℤ) (he : e0 ≤ e) :
    fmt.normalizedValue negative m e =
      (((if negative then -(m : ℤ) else (m : ℤ)) *
        (fmt.beta : ℤ) ^ ((e - e0).toNat) : ℤ) : ℝ) *
        fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
  let d : ℕ := (e - e0).toNat
  have heq : e = e0 + (d : ℤ) := by
    dsimp [d]
    omega
  have hbeta : fmt.betaR ≠ 0 := by
    unfold P05RadixFormat.betaR
    exact_mod_cast (show fmt.beta ≠ 0 by have := fmt.beta_ge_two; omega)
  rw [p05_signed_value, heq]
  have hshift : e0 + (d : ℤ) - (fmt.precision : ℤ) =
      (e0 - (fmt.precision : ℤ)) + (d : ℤ) := by omega
  rw [hshift, zpow_add₀ hbeta]
  have hpow : fmt.betaR ^ (d : ℤ) = ((fmt.beta : ℤ) ^ d : ℝ) := by
    simp [P05RadixFormat.betaR]
  rw [hpow]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  simp
  split_ifs <;> ring

private theorem p05_signed_natAbs (fmt : P05RadixFormat) (k : ℤ) :
    (k : ℝ) =
      fmt.signValue (decide (k < 0)) * (k.natAbs : ℝ) := by
  by_cases hk : k < 0
  · have hnonneg : 0 ≤ -k := by omega
    have habs : (k.natAbs : ℝ) = -(k : ℝ) := by
      have hh := Int.natAbs_of_nonneg hnonneg
      rw [Int.natAbs_neg] at hh
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z : ℝ)) hh
    simp [P05RadixFormat.signValue, hk, habs]
  · have hnonneg : 0 ≤ k := by omega
    have habs : (k.natAbs : ℝ) = (k : ℝ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg hnonneg)
    simp [P05RadixFormat.signValue, hk, habs]

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  rcases hx with ⟨nx, mx, hmx, hex, hxv⟩
  rcases hy with ⟨ny, my, hmy, hey, hyv⟩
  let e0 : ℤ := min ex ey
  let ix : ℤ :=
    (if nx then -(mx : ℤ) else (mx : ℤ)) *
      (fmt.beta : ℤ) ^ ((ex - e0).toNat)
  let iy : ℤ :=
    (if ny then -(my : ℤ) else (my : ℤ)) *
      (fmt.beta : ℤ) ^ ((ey - e0).toNat)
  let k : ℤ := ix - iy
  have hlo : fmt.normalEmin ≤ e0 := by
    dsimp [e0]
    exact le_min hex.1 hey.1
  have hxe : e0 ≤ ex := min_le_left _ _
  have hye : e0 ≤ ey := min_le_right _ _
  have hxgrid :
      x = (ix : ℝ) * fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
    rw [hxv]
    exact p05_aligned_value fmt nx mx ex e0 hxe
  have hygrid :
      y = (iy : ℝ) * fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
    rw [hyv]
    exact p05_aligned_value fmt ny my ey e0 hye
  have hgrid :
      x - y = (k : ℝ) * fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
    rw [hxgrid, hygrid]
    dsimp [k]
    push_cast
    ring
  have hbeta : fmt.betaR ≠ 0 := by
    unfold P05RadixFormat.betaR
    exact_mod_cast (show fmt.beta ≠ 0 by have := fmt.beta_ge_two; omega)
  have hbeta_pos : 0 < fmt.betaR := by
    unfold P05RadixFormat.betaR
    exact_mod_cast (show 0 < fmt.beta by have := fmt.beta_ge_two; omega)
  have hunit_pos :
      0 < fmt.betaR ^ (e0 - (fmt.precision : ℤ)) :=
    zpow_pos hbeta_pos _
  have hpowbound :
      fmt.betaR ^ e0 =
        (fmt.beta ^ fmt.precision : ℕ) *
          fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
    rw [show e0 = (fmt.precision : ℤ) +
        (e0 - (fmt.precision : ℤ)) by omega]
    rw [zpow_add₀ hbeta]
    simp [P05RadixFormat.betaR]
  have hmag' :
      |(k : ℝ)| * fmt.betaR ^ (e0 - (fmt.precision : ℤ)) ≤
        (fmt.beta ^ fmt.precision : ℕ) *
          fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
    calc
      _ = |x - y| := by
        rw [hgrid, abs_mul, abs_of_pos hunit_pos]
      _ ≤ fmt.betaR ^ e0 := hmag
      _ = _ := hpowbound
  have hkboundR : |(k : ℝ)| ≤ (fmt.beta ^ fmt.precision : ℕ) :=
    le_of_mul_le_mul_right hmag' hunit_pos
  have hkbound : k.natAbs ≤ fmt.beta ^ fmt.precision := by
    have hh : (k.natAbs : ℝ) ≤ (fmt.beta ^ fmt.precision : ℕ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hkboundR
    exact_mod_cast hh
  have hfinite : p05FiniteSystem fmt (x - y) := by
    rw [hgrid, p05_signed_natAbs fmt k]
    exact p05_grid_le fmt (decide (k < 0)) k.natAbs e0 hlo hnoOverflow hkbound
  constructor
  · exact hfinite
  · rcases hround with ⟨_, hfaithful⟩
    rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
    · exact False.elim (hfaithful (x - y) hfinite (Or.inl ⟨hlt, le_rfl⟩))
    · exact heq
    · exact False.elim (hfaithful (x - y) hfinite (Or.inr ⟨le_rfl, hgt⟩))

end VSCLReuse
