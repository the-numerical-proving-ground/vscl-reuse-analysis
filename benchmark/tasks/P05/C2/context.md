A floating-point number system with base β, mantissa length p, and exponent range
[e_min, e_max] may be defined by

F := {m · β^e : m, e ∈ ℤ, −β^p < m < β^p, e_min ≤ e ≤ e_max}. (1)

Let F be accompanied by floating-point operations that approximate their real
counterparts according to a map fl : ℝ → F. An operation is faithfully rounded
when no other floating-point number lies between its rounded result and the exact
real result.

For f ∈ F, let e(f) denote the exponent in a representation
f = m_f · β^e(f) satisfying (1). Definition (1) permits multiple representations
of many elements. For example, with β = 2 and p = 4, the value 3 has the
representations

3 = 12 · β^−2 = 6 · β^−1 = 3 · β^0.

In the proof of Theorem 2, the paper uses the following exact-subtraction
implication. By definition (1), the difference of two floating-point numbers a
and b is a multiple of β^min{e(a),e(b)}. In the absence of overflow,

|a − b| ≤ β^p β^min{e(a),e(b)}  ⟹  a ⊖ b = a − b. (8)

The paper then applies (8) to the two faithful subtractions in FastTwoSum. Its
proof justification for (8) is precisely that the difference lies on the common
radix lattice and that the displayed magnitude bound keeps its mantissa within
the floating-point system; faithful rounding must therefore return the exact
difference. The paper notes that an analogous statement holds for addition.
