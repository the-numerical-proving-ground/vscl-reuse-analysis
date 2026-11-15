Section 6 studies how much the condition number of the diagonally normalized
matrix can grow during exact two-sided Jacobi iteration.  For a symmetric
positive definite matrix `H`, Proposition 6.2 defines its Hadamard measure by

\[
  \mathcal H(H)=\frac{\det(H)}{\prod_i H_{ii}}.
\]

The proposition proves five properties.  First, the measure is at most one,
with equality exactly for diagonal `H`.  If `H=L L^T` is its Cholesky
factorization, then `H_{ii}` is the squared row energy of `L`, while
`det(H)` is the product of the squared diagonal entries of `L`.  Each row
energy is at least its diagonal square, and equality in their product occurs
exactly when every entry below the diagonal of `L` is zero.

Second, the measure is unchanged by nonsingular diagonal congruence.  In
Cholesky coordinates this multiplies both the determinant contribution and
the corresponding diagonal contribution by the same product of squared row
scales.

Third, write `H=DAD`, where `D` is diagonal and `A` has unit diagonal.  If
the dimension is `n+1`, write the smallest eigenvalue as `lambdaMin` and the
other `n` positive eigenvalues as `tailEigen`.  Their total is at most the
trace `n+1`, and

\[
  \mathcal H(H)=\det(A)
    =\lambda_{\min}(A)\prod_i \mathtt{tailEigen}_i.
\]

The paper equalizes the tail eigenvalues to maximize their product, obtaining

\[
  \prod_i \mathtt{tailEigen}_i
    \le \left(\frac{n+1}{n}\right)^n \le e,
  \qquad
  \lambda_{\min}(A)\ge \frac{\mathcal H(H)}e.
\]

Fourth, an exact Jacobi rotation with normalized pivot entry `a` preserves
the determinant and multiplies the product of diagonal entries by `1-a^2`.
Consequently

\[
  \mathcal H(H')=\frac{\mathcal H(H)}{1-a^2}
    \ge \mathcal H(H).
\]

Finally, apply the preceding two facts to every matrix in a finite prefix of
an exact Jacobi sequence.  Unit diagonal gives
`lambdaMax <= n+1`; together with the lower bound on `lambdaMin` and the
monotonicity of the measure, this yields

\[
  \kappa(A_m)\le
  \frac{(n+1)e}{\mathcal H(H_0)}
\]

for every step in the prefix.  The Lean statement uses `diagProduct` to
record the product of the diagonal entries along the sequence and uses
`measure`, `lambdaMin`, `lambdaMax`, and `kappa` for exactly these scalar
quantities.
