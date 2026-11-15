Let

\[
R=\begin{pmatrix}A_k&B_k\\&C_k\end{pmatrix}=\mathcal R(M\Pi)
\]

and define

\[
p(R,k)=\max_{\substack{1\leq i\leq k\\1\leq j\leq n-k}}
\sqrt{(A_k^{-1}B_k)_{i,j}^{,2}+
\left(\frac{\gamma_j(C_k)}{\omega_i(A_k)}\right)^2}.
\]

Theorem 3.2. Let

\[
R=\begin{pmatrix}A_k&B_k\\&C_k\end{pmatrix}=\mathcal R(M\Pi)
\]

satisfy \(p(R,k)<f\). Then

\[
\sigma_i(A_k)\geq
\frac{\sigma_i(M)}{\sqrt{1+f^2k(n-k)}},
\qquad 1\leq i\leq k,
\tag{8}
\]

and

\[
\sigma_j(C_k)\leq
\sigma_{j+k}(M)\sqrt{1+f^2k(n-k)},
\qquad 1\leq j\leq n-k.
\tag{9}
\]

Proof. For simplicity we assume that \(M\), and therefore \(R\), has full
column rank. Let

\[
\alpha=\frac{\sigma_{\max}(C_k)}{\sigma_{\min}(A_k)},
\]

and write

\[
R=
\begin{pmatrix}A_k&0\\0&C_k/\alpha\end{pmatrix}
\begin{pmatrix}I_k&A_k^{-1}B_k\\0&\alpha I_{n-k}\end{pmatrix}
=\widehat A_k W_1.
\]

By [29, Thm. 3.3.16],

\[
\sigma_i(R)\leq\sigma_i(\widehat A_k)\|W_1\|_2,
\qquad 1\leq i\leq n.
\tag{10}
\]

Since \(\sigma_{\min}(A_k)=\sigma_{\max}(C_k/\alpha)\), we have
\(\sigma_i(\widehat A_k)=\sigma_i(A_k)\) for \(1\leq i\leq k\).
Moreover,

\[
\begin{aligned}
\|W_1\|_2^2
&\leq 1+\|A_k^{-1}B_k\|_2^2
       +\|C_k\|_2^2\|A_k^{-1}\|_2^2\\
&\leq 1+\|A_k^{-1}B_k\|_F^2
       +\|C_k\|_F^2\|A_k^{-1}\|_F^2\\
&=1+\sum_{i=1}^k\sum_{j=1}^{n-k}
\left\{(A_k^{-1}B_k)_{i,j}^{,2}
+\frac{\gamma_j(C_k)^2}{\omega_i(A_k)^2}\right\}\\
&\leq1+f^2k(n-k).
\end{aligned}
\]

Thus \(\|W_1\|_2\leq\sqrt{1+f^2k(n-k)}\). Plugging these
relations into (10) gives (8). Similarly, let

\[
\begin{pmatrix}\alpha A_k&0\\0&C_k\end{pmatrix}
=
\begin{pmatrix}A_k&B_k\\0&C_k\end{pmatrix}
\begin{pmatrix}\alpha I_k&-A_k^{-1}B_k\\0&I_{n-k}\end{pmatrix}
=RW_2.
\]

Then

\[
\sigma_j(C_k)=\sigma_{j+k}(\widehat A_k)
\leq\sigma_{j+k}(R)\|W_2\|_2
\leq\sigma_{j+k}(M)\sqrt{1+f^2k(n-k)},
\]

which is (9).
