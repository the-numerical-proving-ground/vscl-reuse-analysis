Section 2 studies powers of the shifted upper-triangular matrix used in the
Taylor expansion.  Lemma 2.1 writes this matrix as `D + N`, where `D` is
diagonal, every diagonal entry of `D` has absolute value at most `delta`, and
`N` is strictly upper triangular.  Absolute values and inequalities in the
lemma are componentwise.

For every natural number `k`, the lemma bounds the absolute value of
`(D + N)^k` by

\[
  \sum_{r=0}^{\min(k,n-1)} {k \choose r}
    \delta^{k-r}|N|^r.
\]

The paper obtains the bound by dominating products componentwise by products
of absolute values, replacing `|D|` by `delta I`, and expanding the resulting
power.  Because a strictly upper-triangular `n`-by-`n` matrix has zero `r`th
power for `r >= n`, all later terms vanish.  The Lean definition
`p23PowerMajorant` represents the displayed truncated sum by ranging through
`0,...,k` and assigning zero to terms with `r >= n`.
