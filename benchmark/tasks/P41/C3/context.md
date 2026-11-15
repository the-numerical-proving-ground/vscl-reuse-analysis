Algorithm 1 recursively solves a block Hessenberg system. At an interior node, it first obtains a URV decomposition of the southwest block. It then computes the two pieces of \(G\) by

\[
 G_s:=\operatorname{solve}(A_{se},U),\qquad
 G_n:=\operatorname{solve}(A_{nw},A_{ne}G_s).
\]

At the bottom of the recursion, Algorithm 1 solves each child system by Gaussian elimination. Section 3 describes the rounded matrix product as \(\operatorname{fl}(AB)=AB+E\) with a small product error, and a Gaussian-elimination solution by \(AX=B+\Delta B\) with a small residual. Section 4.2 writes the three computations of the \(G\) stage as

\[
 A_{se}G_s=U+\Delta G_s,\qquad
 U_n=A_{ne}G_s+\Delta U_n,\qquad
 A_{nw}G_n=U_n+\Delta G_n.
\]

Equation (20) bounds the matrix-product error \(\Delta U_n\), and equations (21)–(22) combine the three stage errors into the block residual \(AG=EU+\Delta G\). The selected result is the one-right-hand-side case at a node whose two child solves are Gaussian-elimination leaves. Its displayed residuals retain the individual factorization, solve, and product errors before combining the north and south block rows.
