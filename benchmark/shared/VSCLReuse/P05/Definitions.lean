import Mathlib.Data.Real.Basic

namespace VSCLReuse

structure P05RadixFormat where
  beta : ℕ
  precision : ℕ
  emin : ℤ
  emax : ℤ
  beta_ge_two : 2 ≤ beta
  precision_pos : 0 < precision
  emin_le_emax : emin ≤ emax

namespace P05RadixFormat

def betaR (fmt : P05RadixFormat) : ℝ :=
  fmt.beta

def minNormalMantissa (fmt : P05RadixFormat) : ℕ :=
  fmt.beta ^ (fmt.precision - 1)

def normalizedMantissa (fmt : P05RadixFormat) (m : ℕ) : Prop :=
  fmt.minNormalMantissa ≤ m ∧ m < fmt.beta ^ fmt.precision

def subnormalMantissa (fmt : P05RadixFormat) (m : ℕ) : Prop :=
  0 < m ∧ m < fmt.minNormalMantissa

def normalEmin (fmt : P05RadixFormat) : ℤ :=
  fmt.emin + (fmt.precision : ℤ)

def normalEmax (fmt : P05RadixFormat) : ℤ :=
  fmt.emax + (fmt.precision : ℤ)

def normalizedExponentInRange (fmt : P05RadixFormat) (e : ℤ) : Prop :=
  fmt.normalEmin ≤ e ∧ e ≤ fmt.normalEmax

def signValue (_fmt : P05RadixFormat) (negative : Bool) : ℝ :=
  if negative then -1 else 1

noncomputable def normalizedValue
    (fmt : P05RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ) : ℝ :=
  fmt.signValue negative * (m : ℝ) *
    fmt.betaR ^ (e - (fmt.precision : ℤ))

noncomputable def subnormalValue
    (fmt : P05RadixFormat) (negative : Bool) (m : ℕ) : ℝ :=
  fmt.signValue negative * (m : ℝ) * fmt.betaR ^ fmt.emin

end P05RadixFormat

def P05NormalizedExponentRepresentation
    (fmt : P05RadixFormat) (x : ℝ) (e : ℤ) : Prop :=
  ∃ negative m,
    fmt.normalizedMantissa m ∧
    fmt.normalizedExponentInRange e ∧
    x = fmt.normalizedValue negative m e

def p05FiniteSystem (fmt : P05RadixFormat) (x : ℝ) : Prop :=
  x = 0 ∨
    (∃ negative m e,
      fmt.normalizedMantissa m ∧
      fmt.normalizedExponentInRange e ∧
      x = fmt.normalizedValue negative m e) ∨
    ∃ negative m,
      fmt.subnormalMantissa m ∧
      x = fmt.subnormalValue negative m

def p05Faithful (representable : ℝ → Prop) (exact rounded : ℝ) : Prop :=
  representable rounded ∧
    ∀ candidate, representable candidate →
      ¬ ((rounded < candidate ∧ candidate ≤ exact) ∨
        (exact ≤ candidate ∧ candidate < rounded))

def p05FaithfulInFormat
    (fmt : P05RadixFormat) (exact rounded : ℝ) : Prop :=
  p05Faithful (p05FiniteSystem fmt) exact rounded

end VSCLReuse
