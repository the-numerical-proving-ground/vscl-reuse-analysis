For a symmetric matrix `B` with spectral decomposition

\[
  B=Q\,\operatorname{diag}(\lambda_i)Q^T,
\]

where `Q` is orthogonal, define its positive part by

\[
  B_+=Q\,\operatorname{diag}(\max(\lambda_i,0))Q^T.
\]

The weighted Frobenius norm in equation (1.2) is

\[
  \lVert M\rVert_W=\lVert W^{1/2}MW^{1/2}\rVert_F.
\]

Theorem 3.2 states that the projection of `A` onto the positive semidefinite
matrices in this norm is

\[
  P_S(A)=W^{-1/2}(W^{1/2}AW^{1/2})_+W^{-1/2}. \tag{3.3}
\]

Moreover,

\[
  \operatorname{diag}(P_S(A))\geq \operatorname{diag}(A).
\]

For the proof, the paper writes the difference between `A` and the proposed
projection as the congruence of the negative spectral part of
`W^{1/2}AW^{1/2}`.  This difference is negative semidefinite.  The positive
and negative spectral parts have zero product, which gives the normal-cone
orthogonality condition and hence proves that the proposed matrix is the
projection.  Finally,

\[
  (W^{1/2}AW^{1/2})_+-W^{1/2}AW^{1/2}\succeq0.
\]

Congruence by `W^{-1/2}` preserves positive semidefiniteness, and every
diagonal entry of a positive semidefinite matrix is nonnegative, giving the
diagonal inequality.

In the formal statement, `S` and `Sinv` denote `W^{1/2}` and `W^{-1/2}`,
respectively.  Their symmetry and two inverse identities are supplied
explicitly, and `Q`, `lambda` supply the displayed spectral decomposition of
`S*A*S`.  The squared weighted Frobenius objective has the same minimizers as
the norm itself.
