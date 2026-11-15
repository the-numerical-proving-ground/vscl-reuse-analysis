Theorem 1.1. Let

\[
h_\ell(x)=\sum_{k=\ell}^{\infty}c_kx^k
\]

be a power series with radius of convergence \(\omega\), and let

\[
\widetilde h_\ell(x)=\sum_{k=\ell}^{\infty}|c_k|x^k.
\]

For any \(A\in\mathbb C^{n\times n}\) with \(\rho(A)<\omega\),

\[
\|h_\ell(A)\|\leq
\widetilde h_\ell\bigl(\|A^t\|^{1/t}\bigr),
\]

where

\[
\|A^t\|^{1/t}=
\max\{\|A^k\|^{1/k}:k\geq\ell\text{ and }c_k\ne0\}.
\]

Proof. The existence of \(t\) is guaranteed because the sequence
\(\{\|A^k\|^{1/k}\}\) is bounded above and convergent. Moreover,

\[
\begin{aligned}
\|h_\ell(A)\|
&\leq\sum_{k=\ell}^{\infty}|c_k|\|A^k\|\\
&=\sum_{k=\ell}^{\infty}|c_k|
  \bigl(\|A^k\|^{1/k}\bigr)^k\\
&\leq\sum_{k=\ell}^{\infty}|c_k|
  \bigl(\|A^t\|^{1/t}\bigr)^k
=\widetilde h_\ell\bigl(\|A^t\|^{1/t}\bigr).
\end{aligned}
\]

Lemma 4.1. If \(k\geq1\) and
\(k=pm_1+qm_2\), where \(p,q\) are positive integers and
\(m_1,m_2\) are nonnegative integers, then

\[
\|A^k\|^{1/k}
\leq\max\bigl(\|A^p\|^{1/p},\|A^q\|^{1/q}\bigr).
\]

Proof. Let
\(\delta=\max(\|A^p\|^{1/p},\|A^q\|^{1/q})\). Then

\[
\begin{aligned}
\|A^k\|
&\leq\|A^{pm_1}\|\|A^{qm_2}\|\\
&\leq\bigl(\|A^p\|^{1/p}\bigr)^{pm_1}
       \bigl(\|A^q\|^{1/q}\bigr)^{qm_2}\\
&\leq\delta^{pm_1}\delta^{qm_2}=\delta^k.
\end{aligned}
\]

Theorem 4.2. Define \(h_\ell\) and \(\widetilde h_\ell\) as in
Theorem 1.1, suppose \(\rho(A)<\omega\), and let \(p\) be a positive
integer. Then

\[
\|h_\ell(A)\|\leq
\widetilde h_\ell\left(
\max\bigl(\|A^p\|^{1/p},\|A^{p+1}\|^{1/(p+1)}\bigr)
\right)
\]

if \(\ell\geq p(p-1)\), and

\[
\|h_\ell(A)\|\leq
\widetilde h_\ell\left(
\max\bigl(\|A^{2p}\|^{1/(2p)},
          \|A^{2p+2}\|^{1/(2p+2)}\bigr)
\right)
\]

if \(\ell\geq2p(p-1)\) and \(h_\ell\) is even.

Proof. For the first part, let

\[
X_p=\{m\in\mathbb N:m\geq p(p-1)\}
\]

and

\[
Y_p=\{(p+1)m_1+pm_2:m_1,m_2\in\mathbb N\cup\{0\}\}.
\]

We have \(X_p\subset Y_p\), since any \(k\in X_p\) can be written as
\(k=pq+r\), where \(q\geq p-1\) and \(0\leq r<p\). Then

\[
k=(p+1)r+p(q-r)\in Y_p,
\]

because \(q-r\geq p-r-1\geq0\). Hence Lemma 4.1 gives

\[
\|A^k\|^{1/k}
\leq\max\{\|A^{p+1}\|^{1/(p+1)},\|A^p\|^{1/p}\},
\qquad k\geq p(p-1),
\]

and the result follows from Theorem 1.1. The even case follows similarly
from

\[
\{\ell:\ell\text{ even},\ \ell\geq2p(p-1)\}
=2X_p\subset2Y_p
=\{(2p+2)m_1+2pm_2:m_1,m_2\in\mathbb N\cup\{0\}\}.
\]
