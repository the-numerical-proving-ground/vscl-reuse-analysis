Section 6 analyzes a divide-and-conquer inverse of a lower triangular matrix partitioned as

\[
 L=\begin{bmatrix}L_{11}&0\\L_{21}&L_{22}\end{bmatrix},\qquad
 L^{-1}=\begin{bmatrix}L_{11}^{-1}&0\\
 -L_{22}^{-1}L_{21}L_{11}^{-1}&L_{22}^{-1}\end{bmatrix}.
\]

The paper lists seven ways of evaluating the off-diagonal inverse block. Method B computes
\(X_{21}=-L_{22}\backslash(L_{21}X_{11})\): it forms the block product and then solves a lower triangular system. The proof of the componentwise right-residual bound (6.1) states the rounded-operation relations \(\operatorname{fl}(AB)=AB+\Delta(A,B)\) and, for a triangular solve \(X=\operatorname{fl}(T\backslash B)\), \(TX+\Delta(T,X)=B\). Their perturbations are bounded componentwise by a dimension-dependent factor times unit roundoff and, respectively, \(|A||B|\) and \(|T||X|\), up to terms of order \(u^2\).

For Method B, the paper's off-diagonal calculation is

\[
 L_{22}X_{21}+\Delta(L_{22},X_{21})
       =-L_{21}X_{11}+\Delta(L_{21},X_{11}),
\]

and thus bounds \(|L_{22}X_{21}+L_{21}X_{11}|\) by the sum of the two componentwise perturbation bounds. The paper then combines this calculation with the diagonal-block induction to obtain (6.1), \(|L\widehat X-I|\leq c_nu|L||\widehat X|+O(u^2)\).
