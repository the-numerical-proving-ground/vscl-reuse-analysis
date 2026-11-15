# Yalamov and Paprzycki (1999), complete Lemma 1

The published paper is *Stability and performance analysis of a block elimination solver for bordered linear systems*, IMA Journal of Numerical Analysis 19(3), pp. 335–348. The selected result and proof are on printed pages 338–339 (physical PDF pages 4–5). The source uses the standard relative floating-point model without exceptional arithmetic.

The paper partitions the bordered system as

\[
 M=\begin{pmatrix}A&B\\ C&D\end{pmatrix},\qquad
 L=\begin{pmatrix}A&0\\ C&I\end{pmatrix},\qquad
 \widetilde U=\begin{pmatrix}I&\widetilde V\\0&\widetilde\Delta\end{pmatrix}.
\]

Algorithm steps 3–4 solve each column of \(A\widetilde V=B\) by a backward-stable solver and compute \(\widetilde\Delta=\operatorname{fl}(D-\operatorname{fl}(C\widetilde V))\). Section 4, equation (3), gives the solver contract

\[
 (A+\varepsilon_A)\widetilde x=c,
 \qquad |\varepsilon_A|\le K_1\rho_0|A|.
\]

It applies separately to every computed column of \(\widetilde V\); each column may have its own perturbation matrix. The paper defines \(\gamma_{n+1}=(n+1)\rho_0/(1-(n+1)\rho_0)\).

**Lemma 1 (complete claim).** The computed factorization satisfies

\[
 L\widetilde U=M+E,\qquad
 |E|\le \mu_1|M|
   \begin{pmatrix}0&|\widetilde V|\\0&I\end{pmatrix},
 \qquad \mu_1=\max\{K_1\rho_0,\gamma_{n+1}\}.
\]

The proof multiplies the two block factors and identifies the only nonzero error blocks as

\[
 E_{12}=A\widetilde V-B,
 \qquad E_{22}=C\widetilde V+\widetilde\Delta-D.
\]

For each column \(j\), equation (3) gives \((A+\varepsilon_A^{(j)})\widetilde V_{:,j}=B_{:,j}\), so

\[
 |E_{12}|\le K_1\rho_0|A||\widetilde V|.
\]

The proof then analyzes the one rounded matrix product and the final matrix subtraction in \(\widetilde\Delta\):

\[
 |E_{22}|\le\gamma_{n+1}\bigl(|D|+|C||\widetilde V|\bigr).
\]

These block bounds imply the lemma's displayed \(|M|\)-majorant. The Lean task uses finite real matrices with arbitrary positive or zero dimensions, a relative-rounding operation model, columnwise instances of equation (3), the actual block product \(L\widetilde U\), and the complete componentwise \(|M|\)-majorant. The computed Schur complement is exactly the two source operations above.
