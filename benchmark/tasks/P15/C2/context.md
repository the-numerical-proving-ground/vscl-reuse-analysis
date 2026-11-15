### 3.1.4. Bounding \(\|\Delta \widehat R_i\|_2\)

Let \(R\in\mathbb R^{n\times n}\) be a nonsingular upper triangular matrix. The computed solution \(\widehat x\) obtained by solving an upper triangular linear system \(Rx=b\) by back substitution in floating-point arithmetic satisfies [11, Theorem 8.5]

\[
\tag{3.25}
(R+\Delta R)\widehat x=b,
\qquad
|\Delta R|\leq \gamma_n |R|.
\]

We have for \(1\leq i\leq m\)

\[
\tag{3.26}
\|\Delta \widehat R_i\|_2
\leq \||\Delta \widehat R_i|\|_F
\leq \gamma_n\sqrt n\,\|\widehat R\|_2.
\]

From (3.7), (3.4), and (3.21) we obtain

\[
\tag{3.27}
\|\widehat R\|_2^2
\leq \|X\|_2^2+s+\|E_1\|_2+\|E_2\|_2
\leq \|X\|_2^2+1.1s
\leq 1.1\|X\|_2^2.
\]

Substituting this into (3.26) gives

\[
\tag{3.28}
\|\Delta \widehat R_i\|_2
\leq 1.02nu\sqrt n\sqrt{1.1}\,\|X\|_2
\leq 1.1n\sqrt n\,u\|X\|_2.
\]

### 3.1.6. Bounding \(\|\widehat Q\|_2\)

Lemma 3.1. Suppose that \(X\in\mathbb R^{m\times n}\) with \(m\geq n\) satisfies (3.2) and (3.3). Then the matrix \(\widehat Q\) obtained by applying the shiftedCholeskyQR algorithm in floating-point arithmetic to \(X\) satisfies

\[
\|\widehat Q^T\widehat Q-I\|_2<2,
\]

and hence

\[
\tag{3.33}
\|\widehat Q\|_2<\sqrt 3.
\]

### 3.1.7. Bounding the residual in shiftedCholeskyQR

Lemma 3.2. Under the assumptions in Lemma 3.1, \(\widehat Q\widehat R\) computed by shiftedCholeskyQR satisfies

\[
\frac{\|\widehat Q\widehat R-X\|_F}{\|X\|_2}
\leq 2n^2u.
\]

Proof. First note that

\[
\|\widehat q_i^T\widehat R-x_i^T\|
=\|\widehat q_i^T\widehat R-
\widehat q_i^T(\widehat R+\Delta\widehat R_i)\|
\leq \|\widehat q_i^T\Delta\widehat R_i\|
\leq \|\widehat q_i^T\|\,\|\Delta\widehat R_i\|.
\]

Substituting (3.28) into this gives

\[
\tag{3.38}
\|\widehat q_i^T\widehat R-x_i^T\|
\leq \|\widehat q_i^T\|\,1.1n\sqrt n\,u\|X\|_2.
\]

On the other hand, from (3.33) we have

\[
\tag{3.39}
\|\widehat Q\|_F<\sqrt{3n}.
\]

Hence it follows that

\[
\begin{aligned}
\tag{3.40}
\|\widehat Q\widehat R-X\|_F
&=\sqrt{\sum_{i=1}^m
  \|\widehat q_i^T\widehat R-x_i^T\|^2}\\
&\leq \sqrt{\sum_{i=1}^m\|\widehat q_i^T\|^2}
  \,1.1n\sqrt n\,u\|X\|_2\\
&=\|\widehat Q\|_F\,1.1n\sqrt n\,u\|X\|_2
\leq 2n^2u\|X\|_2.
\end{aligned}
\]

By (3.13) we have \(\Delta X=\widehat Q\widehat R-X\), so (3.40) in fact provides a bound for \(\|\Delta X\|_F\) that is tighter than the previous bound (3.32):

\[
\tag{3.41}
\|\Delta X\|_F\leq 2n^2u\|X\|_2.
\]
