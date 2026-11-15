Appendix B considers a symmetric indefinite factorization (A=LDL^T), where
(D) has one-by-one and two-by-two diagonal blocks and the entries of the unit
lower triangular factor (L) are bounded. The paper assumes that the small
block systems used during factorization and solution are solved by a normwise
backward-stable method. Dimension-dependent constants and second-order terms
are suppressed.

For the first elimination step, whether the pivot has order one or two, the
computed partial factorization contains a computed Schur complement
\(\widehat S\). The paper writes its computed update as

\[
  \widehat S=A_{22}-\widehat L_{11}A_{12}-\Delta S.
\]

It then gives the first-step rounding-error estimate

\[
  \|\Delta S\|\leq c_r\epsilon
  \bigl(\|A_{22}\|+\|\widehat L_{11}\|\,\|A_{12}\|\bigr)
  +O(\epsilon^2),
\]

where the small constant (c_r) depends on the number of operations in the
rank-one or rank-two update. This local estimate is the input to the recursive
factorization argument that follows.
