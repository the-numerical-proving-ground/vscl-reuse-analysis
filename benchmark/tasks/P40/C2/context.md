Algorithm 1.1 computes the residual for iterative refinement in a higher precision with unit roundoff \(\bar u\), then stores it in working precision with unit roundoff \(u\), where \(\bar u\leq u\). In Section 2, Carson and Higham analyze these two stages separately. For a current iterate \(x_i\), the high-precision stage gives

\[
 s_i=\operatorname{fl}_{\bar u}(b-Ax_i)=b-Ax_i+\Delta s_i,
 \qquad |\Delta s_i|\leq\bar\gamma_{n+1}(|b|+|A||x_i|).
\]

The stored residual is \(r_i=\operatorname{fl}_u(s_i)=s_i+f_i\), with \(|f_i|\leq u|s_i|\). Combining these two rounding stages, equation (2.3) states

\[
 r_i=b-Ax_i+\Delta r_i,\qquad
 |\Delta r_i|\leq u|b-Ax_i|+(1+u)\bar\gamma_{n+1}(|b|+|A||x_i|).
\]

All vector and matrix absolute values in this display are componentwise.
