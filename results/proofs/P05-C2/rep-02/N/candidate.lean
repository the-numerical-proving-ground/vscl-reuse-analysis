import VSCLReuse.P05.Definitions
import Mathlib

namespace VSCLReuse

private lemma p05_beta_pos (fmt : P05RadixFormat) : 0 < fmt.betaR := by
  dsimp [P05RadixFormat.betaR]
  exact_mod_cast (show 0 < fmt.beta by have h := fmt.beta_ge_two; omega)

private lemma p05_pow_prec (fmt : P05RadixFormat) :
    fmt.beta ^ fmt.precision = fmt.minNormalMantissa * fmt.beta := by
  dsimp [P05RadixFormat.minNormalMantissa]
  rw [← pow_succ]
  congr 1
  have h := fmt.precision_pos
  omega

private lemma p05_mantissa_lt (fmt : P05RadixFormat) :
    fmt.minNormalMantissa < fmt.beta ^ fmt.precision := by
  rw [p05_pow_prec]
  have hpos : 0 < fmt.minNormalMantissa := by
    dsimp [P05RadixFormat.minNormalMantissa]
    exact pow_pos (by have h := fmt.beta_ge_two; omega) _
  have hbeta : 1 < fmt.beta := by have h := fmt.beta_ge_two; omega
  nlinarith

private lemma p05_finite_small_lattice (fmt : P05RadixFormat)
    (negative : Bool) (t n : ℕ)
    (hn : n < fmt.beta ^ fmt.precision)
    (ht : fmt.normalEmin + (t : ℤ) ≤ fmt.normalEmax) :
    p05FiniteSystem fmt
      (fmt.signValue negative * (n : ℝ) *
        fmt.betaR ^ (fmt.normalEmin + (t : ℤ) - (fmt.precision : ℤ))) := by
  induction t generalizing n with
  | zero =>
      simp only [Nat.cast_zero, add_zero] at ht ⊢
      by_cases hn0 : n = 0
      · left
        simp [hn0]
      by_cases hlarge : fmt.minNormalMantissa ≤ n
      · right; left
        refine ⟨negative, n, fmt.normalEmin, ⟨hlarge, hn⟩, ?_, ?_⟩
        · exact ⟨le_refl _, ht⟩
        · rfl
      · right; right
        refine ⟨negative, n, ⟨Nat.pos_of_ne_zero hn0, Nat.lt_of_not_ge hlarge⟩, ?_⟩
        simp only [P05RadixFormat.subnormalValue]
        congr 1
        dsimp [P05RadixFormat.normalEmin]
        congr 1
        omega
  | succ t ih =>
      by_cases hn0 : n = 0
      · left
        simp [hn0]
      by_cases hlarge : fmt.minNormalMantissa ≤ n
      · right; left
        refine ⟨negative, n, fmt.normalEmin + ((t + 1 : ℕ) : ℤ),
          ⟨hlarge, hn⟩, ?_, ?_⟩
        · constructor <;> omega
        · rfl
      · have hsmall : n < fmt.minNormalMantissa := Nat.lt_of_not_ge hlarge
        have hmul : n * fmt.beta < fmt.beta ^ fmt.precision := by
          rw [p05_pow_prec]
          exact Nat.mul_lt_mul_of_pos_right hsmall (by have h := fmt.beta_ge_two; omega)
        have hrec := ih (n * fmt.beta) hmul (by omega)
        convert hrec using 1
        have hb : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
        have he : fmt.normalEmin + ((t + 1 : ℕ) : ℤ) - (fmt.precision : ℤ) =
            (fmt.normalEmin + (t : ℤ) - (fmt.precision : ℤ)) + 1 := by push_cast; omega
        rw [he, zpow_add₀ hb]
        simp only [zpow_one]
        push_cast
        dsimp [P05RadixFormat.betaR]
        ring

private lemma p05_finite_nat_lattice (fmt : P05RadixFormat)
    (negative : Bool) (e : ℤ) (n : ℕ)
    (hemin : fmt.normalEmin ≤ e)
    (hemax : e < fmt.normalEmax)
    (hn : n ≤ fmt.beta ^ fmt.precision) :
    p05FiniteSystem fmt
      (fmt.signValue negative * (n : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  rcases lt_or_eq_of_le hn with hsmall | htop
  · let t : ℕ := (e - fmt.normalEmin).toNat
    have ht : e = fmt.normalEmin + (t : ℤ) := by
      dsimp [t]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hemin)]
      omega
    have hfin := p05_finite_small_lattice fmt negative t n hsmall
      (by simpa only [← ht] using le_of_lt hemax)
    simpa only [← ht] using hfin
  · right; left
    refine ⟨negative, fmt.minNormalMantissa, e + 1,
      ⟨le_refl _, p05_mantissa_lt fmt⟩, ?_, ?_⟩
    · constructor <;> omega
    · simp only [P05RadixFormat.normalizedValue]
      have hb : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
      have hpow : (fmt.beta ^ fmt.precision : ℝ) =
          (fmt.minNormalMantissa : ℝ) * fmt.betaR := by
        dsimp [P05RadixFormat.betaR]
        exact_mod_cast p05_pow_prec fmt
      rw [← Nat.cast_pow] at hpow
      rw [htop, hpow]
      have he : e + 1 - (fmt.precision : ℤ) =
          (e - (fmt.precision : ℤ)) + 1 := by omega
      rw [he, zpow_add₀ hb]
      simp only [zpow_one]
      ring

private lemma p05_normalized_on_lattice (fmt : P05RadixFormat)
    (x : ℝ) (e e0 : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x e)
    (hle : e0 ≤ e) :
    ∃ z : ℤ, x = (z : ℝ) * fmt.betaR ^ (e0 - (fmt.precision : ℤ)) := by
  rcases hx with ⟨negative, m, hm, he, rfl⟩
  let d : ℕ := (e - e0).toNat
  let z : ℤ := (if negative then -(m : ℤ) else (m : ℤ)) * (fmt.beta : ℤ) ^ d
  refine ⟨z, ?_⟩
  have hd : (d : ℤ) = e - e0 := by
    dsimp [d]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
  have heq : e - (fmt.precision : ℤ) =
      (e0 - (fmt.precision : ℤ)) + (e - e0) := by omega
  simp only [P05RadixFormat.normalizedValue]
  rw [heq, zpow_add₀ hb, ← hd, zpow_natCast]
  have hz : (z : ℝ) = fmt.signValue negative * (m : ℝ) * fmt.betaR ^ d := by
    dsimp [z, P05RadixFormat.betaR]
    cases negative <;> simp [P05RadixFormat.signValue]
  rw [hz]
  ring

private lemma p05_finite_int_lattice (fmt : P05RadixFormat)
    (e z : ℤ)
    (hemin : fmt.normalEmin ≤ e)
    (hemax : e < fmt.normalEmax)
    (hmag : |(z : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ))| ≤ fmt.betaR ^ e) :
    p05FiniteSystem fmt ((z : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ))) := by
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p05_beta_pos fmt)
  have hk : 0 < fmt.betaR ^ (e - (fmt.precision : ℤ)) := zpow_pos (p05_beta_pos fmt) _
  have he : e = (fmt.precision : ℤ) + (e - (fmt.precision : ℤ)) := by omega
  rw [he, zpow_add₀ hb] at hmag
  have hineq : |(z : ℝ)| * fmt.betaR ^ (e - (fmt.precision : ℤ)) ≤
      fmt.betaR ^ (fmt.precision : ℤ) * fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    simpa [abs_mul, abs_of_pos hk] using hmag
  have hcoeffR : |(z : ℝ)| ≤ fmt.betaR ^ (fmt.precision : ℤ) :=
    (mul_le_mul_iff_of_pos_right hk).mp hineq
  have hcoeff : z.natAbs ≤ fmt.beta ^ fmt.precision := by
    have h : (z.natAbs : ℝ) ≤ (fmt.beta ^ fmt.precision : ℝ) := by
      simpa [Nat.cast_natAbs, P05RadixFormat.betaR] using hcoeffR
    exact_mod_cast h
  by_cases hz : 0 ≤ z
  · have hzcast : (z.natAbs : ℝ) = (z : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg hz]
    have hfin := p05_finite_nat_lattice fmt false e z.natAbs hemin hemax hcoeff
    simpa [P05RadixFormat.signValue, hzcast] using hfin
  · have hzcast : (z.natAbs : ℝ) = -(z : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg (lt_of_not_ge hz)]
      push_cast
      ring
    have hfin := p05_finite_nat_lattice fmt true e z.natAbs hemin hemax hcoeff
    simpa [P05RadixFormat.signValue, hzcast] using hfin

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  let e : ℤ := min ex ey
  have hemin : fmt.normalEmin ≤ e := by
    rcases hx with ⟨_, _, _, hxe, _⟩
    rcases hy with ⟨_, _, _, hye, _⟩
    exact le_min hxe.1 hye.1
  obtain ⟨zx, hxlat⟩ := p05_normalized_on_lattice fmt x ex e hx (min_le_left _ _)
  obtain ⟨zy, hylat⟩ := p05_normalized_on_lattice fmt y ey e hy (min_le_right _ _)
  let z : ℤ := zx - zy
  have hd : x - y = (z : ℝ) * fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    rw [hxlat, hylat]
    dsimp [z]
    push_cast
    ring
  have hfin : p05FiniteSystem fmt (x - y) := by
    rw [hd]
    apply p05_finite_int_lattice fmt e z hemin hnoOverflow
    simpa only [← hd] using hmag
  refine ⟨hfin, ?_⟩
  rcases hround with ⟨_, hfaith⟩
  by_cases hlt : rounded < x - y
  · exact False.elim (hfaith (x - y) hfin (Or.inl ⟨hlt, le_refl _⟩))
  by_cases hgt : x - y < rounded
  · exact False.elim (hfaith (x - y) hfin (Or.inr ⟨le_refl _, hgt⟩))
  exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

end VSCLReuse
