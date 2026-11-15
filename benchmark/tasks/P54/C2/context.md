Langlois and Louvet, “How to Ensure a Faithful Polynomial Evaluation with the Compensated Horner Algorithm,” ARITH 2007, Section 2.2, Lemma 1 (PDF page 3).

The paper's equation (3) assumes that, when underflow and overflow do not occur, a rounded addition or multiplication has both the forward form `fl(v) = v(1+δ)` and the inverse form `v = fl(v)(1+ε)`, where `|δ|, |ε| ≤ u`. It writes `γ_k = ku/(1-ku)` when `ku < 1`. Algorithm 1 evaluates a degree-`n` polynomial by starting with its leading coefficient and then, in descending order, rounding one multiplication by `x` and one addition of the next coefficient. In the Lean definitions, coefficient lists are in descending order and have length `n+1`.

Lemma 1 takes two degree-`n` polynomials `p(x) = Σ a_i x^i` and `q(x) = Σ b_i x^i` with floating point coefficients. The coefficients of `p ⊕ q` are the rounded sums `a_i ⊕ b_i`; the coefficients of `p+q` are the exact sums `a_i+b_i`. Its first conclusion, equation (7), is

    |(p+q)(x) − Horner(p ⊕ q, x)| ≤ γ_(2n+1) · overline(p+q)(|x|),

where the overline means the polynomial formed from the absolute values of the exact coefficient sums. Its second conclusion, equation (8), is

    overline(p+q)(|x|) ≤ (1+u)^(2n+1) Horner(|p ⊕ q|, |x|).

For (7), the printed proof says to adapt the standard Horner error argument cited there. For (8), it starts with `r_n = |a_n ⊕ b_n|` and follows Algorithm 1 on absolute coefficient sums. Its induction bounds the absolute-coefficient polynomial formed from the processed coefficients by `(1+u)^(2i+1)|r_(n−i)|` after `i` steps, yielding (8) when `i=n`.
