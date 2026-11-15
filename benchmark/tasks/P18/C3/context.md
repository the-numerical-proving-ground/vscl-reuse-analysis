Appendix B starts with a symmetric indefinite matrix factored as (A=LDL^T),
where (D) is made of one-by-one and two-by-two blocks and (L) is unit lower
triangular with bounded entries. It assumes that the small block systems in
the factorization and solution phases are solved by a normwise
backward-stable method. Under these assumptions, the paper states that both
the factorization and the linear equation solution are normwise backward
stable. In particular, for the computed solution (widehat x),

\[
  (A+F)\widehat x=b, \qquad
  \|F\|\leq d'(n)\epsilon\|A\|+O(\epsilon^2).
\]

The preceding part of Appendix B obtains a factorization perturbation
(A+\Delta A=\widehat L\widehat D\widehat L^T). For the solution phase, the
paper combines the perturbations from the forward triangular solve, the
block-diagonal solve, and the transposed back solve. It records the resulting
first-order equation as

\[
 b=\bigl(A+\Delta A+\Delta L\,D L^T
       +L\,\Delta D L^T+LD\,\Delta L^T\bigr)\widehat x.
\]

Substituting the bounds for (L) and (D) leaves a bound involving only
(\|A\|), the unit roundoff, and a modest function of the dimension. Terms
containing products of two or more perturbations are absorbed into the
paper's (O(\epsilon^2)) term.
