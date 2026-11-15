The paper computes a residual for iterative refinement in the same arithmetic
precision used by the factorization and solution. Its arithmetic model is

\[
  \operatorname{fl}(a\mathbin{\mathrm{op}}b)
  =(a\mathbin{\mathrm{op}}b)(1+\delta),
  \qquad |\delta|\leq u,
\]

for the four basic operations, with no overflow or underflow. Let

\[
  \gamma_k=\frac{ku}{1-ku}, \qquad ku<1.
\]

Near the end of Section 2.2, the paper states that standard error analysis
bounds the error in a computed residual component by

\[
  \gamma_{s+1}
  \left(|b_i|+\sum_{j:a_{ij}\ne0}|a_{ij}|\,|x_j|\right),
\]

where (s) is an upper bound on the number of nonzero entries in a row. This
is the sparse replacement for the dense dimension-dependent residual bound.
The paper uses it to explain why the computed componentwise backward error can
differ from the true value by only about this rounding level.

The Lean statement considers one stored sparse row. The vectors `a` and `x`
contain its (s) stored coefficients and the matching solution components.
`p20RoundedSparseRowProduct` performs one rounded multiplication per stored
entry and accumulates the products in order; `p20RoundedResidual` then performs
the final rounded subtraction from (b_i).
