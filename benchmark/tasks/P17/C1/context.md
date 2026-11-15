In this paper, \(\epsilon\) denotes a matrix or scalar satisfying
\(\|\epsilon\|\leq f(n)u\) for a modest dimension-dependent function and a
fixed norm. Modest constants and higher-order terms in \(u\) are suppressed.

Let \(X=P\Sigma Q^*\) be an SVD. For a nonnegative scalar function \(f\)
that vanishes only at zero, define

\[
f(X)=Pf(\Sigma)Q^*.
\]

This mapping preserves the unitary polar factor.

Lemma 4.1. Let \(X\in\mathbb C^{s\times n}\), \(s\geq n\), and suppose that
a computed approximation \(\widehat Y\) to \(f(X)\) is mixed
backward--forward stable:

\[
\widehat Y=f(\widetilde X)+\epsilon\|\widehat Y\|_2,
\qquad
\widetilde X=X+\epsilon\|X\|_2. \tag{4.1}
\]

Write the positive singular values of \(\widetilde X\) as
\(M=\sigma_1\geq\cdots\geq\sigma_r=m>0\). Suppose

\[
\frac{f(x)}{\max_{m\leq t\leq M}f(t)}\geq\frac{x}{dM},
\qquad x\in[m,M], \tag{4.2}
\]

where \(d\geq1\), and suppose \(f(0)=0\) in the rank-deficient case. If
\(U\) is any unitary polar factor of \(\widehat Y\) and

\[
\widehat H=\frac12\bigl(U^*X+(U^*X)^*\bigr),
\]

then

\[
U\widehat H=X+d\epsilon\|X\|_2, \tag{4.3}
\]

and

\[
\widehat H=H+d\epsilon\|H\|_2, \tag{4.4}
\]

where \(H\) is the Hermitian polar factor of \(X\).

For the square case, take an SVD
\(\widetilde X=P\Sigma Q^*\). Its Hermitian polar factor is
\(\widetilde H=Q\Sigma Q^*\), while the Hermitian polar factor of
\(f(\widetilde X)\) is \(f(\widetilde H)=Qf(\Sigma)Q^*\). Stability of the
Hermitian polar factor gives

\[
H_{\widehat Y}=f(\widetilde H)+\epsilon\|\widehat Y\|_2.
\]

Using \(\widehat Y=UH_{\widehat Y}\), the two representations of
\(\widehat Y\), and
\(\|\widehat Y\|_2=(1+\epsilon)\|f(\Sigma)\|_2\), gives

\[
Pf(\Sigma)Q^*=UQf(\Sigma)Q^*+epsilon\|f(\Sigma)\|_2. \tag{4.5}
\]

Right-multiply by

\[
Qf(\Sigma)^+\Sigma Q^*
=Q\operatorname{diag}\left(
\frac{\sigma_1}{f(\sigma_1)},\ldots,
\frac{\sigma_r}{f(\sigma_r)},0,\ldots,0\right)Q^*.
\]

Condition (4.2) implies that the norm of this multiplier is at most
\(d\|\widetilde X\|_2/\|f(\Sigma)\|_2\). Therefore

\[
\widetilde X=U\widetilde H+d\epsilon\|\widetilde X\|_2. \tag{4.6}
\]

Left multiplication by \(U^*\), followed by (4.1), yields

\[
U^*X=\widetilde H+d\epsilon\|X\|_2. \tag{4.7}
\]

Finally, substitute (4.7) into the symmetrized definition of
\(\widehat H\). The self-adjoint part of the error is still of size
\(d\epsilon\|X\|_2\), which gives the residual (4.3). Combining the same
identity with the perturbation bound for the Hermitian polar factor from
\(\widetilde X=X+\epsilon\|X\|_2\) gives (4.4).
