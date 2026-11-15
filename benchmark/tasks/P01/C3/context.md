For the error analysis we will make use of the standard model of floating point arithmetic, in which (u) is the unit roundoff:

\[
\tag{1.2}
fl(x\mathbin{\mathrm{op}}y)=(x\mathbin{\mathrm{op}}y)(1+\delta),
\qquad |\delta|\leq u,
\qquad \mathrm{op}=+,-,*,/.
\]

Our task is to evaluate \(S_n=\sum_{i=1}^{n}x_i\), where \(x_1,\ldots,x_n\) are real numbers. In this section we consider the standard recursive summation technique in which \(S_n\) is evaluated according to

\[
s=0;\qquad
\text{for }i=1:n,\quad s=s+x_i,\quad\text{end}.
\]

In general, each different ordering of the \(x_i\) will yield a different computed sum \(\widehat S_n\) in floating point arithmetic, and it is of interest to determine how the ordering affects the error \(E_n=\widehat S_n-S_n\).

To begin, we make no assumption on the ordering and obtain a standard bound for \(E_n\). By a direct application of the model (1.2) we have, with \(S_k=\sum_{i=1}^{k}x_i\),

\[
\tag{2.1}
\widehat S_k=fl(\widehat S_{k-1}+x_k)
  =(\widehat S_{k-1}+x_k)(1+\delta_k),
\qquad |\delta_k|\leq u,\quad k=2:n.
\]

By repeated use of this relation it follows that

\[
\tag{2.2}
\widehat S_n=(x_1+x_2)\prod_{k=2}^{n}(1+\delta_k)
  +\sum_{i=3}^{n}x_i\prod_{k=i}^{n}(1+\delta_k).
\]

To simplify the product terms we use the result that if \(|\delta_i|\leq u\) for \(i=1:n\) then

\[
\prod_{i=1}^{n}(1+\delta_i)=1+\theta_n,
\qquad |\theta_n|\leq\frac{nu}{1-nu}\equiv\gamma_n.
\]

Thus we rewrite (2.2) as

\[
\tag{2.3}
\widehat S_n=(x_1+x_2)(1+\theta_{n-1})
  +\sum_{i=3}^{n}x_i(1+\theta_{n-i+1}),
\]

which yields

\[
\tag{2.4}
|E_n|=\left|(x_1+x_2)\theta_{n-1}
  +\sum_{i=3}^{n}x_i\theta_{n-i+1}\right|
\]

and

\[
\tag{2.5}
|E_n|\leq(|x_1|+|x_2|)\gamma_{n-1}
  +\sum_{i=3}^{n}|x_i|\gamma_{n-i+1}.
\]

We can weaken (2.5) to obtain the bound

\[
\tag{2.6}
|E_n|\leq\gamma_{n-1}\sum_{i=1}^{n}|x_i|
  =(n-1)u\sum_{i=1}^{n}|x_i|+O(u^2),
\]

which is independent of the ordering.

First, we derive a sharper error bound. From (2.1) the error introduced on
the \(k\)th step is

\[
(\widehat S_{k-1}+x_k)\delta_k
  = \frac{\widehat S_k\delta_k}{1+\delta_k}.
\]

Summing these individual errors gives

\[
\tag{2.7}
E_n=\sum_{k=2}^{n}\frac{\widehat S_k\delta_k}{1+\delta_k},
\]

which shows that, to first order, the overall error is the sum of the
relative rounding errors weighted by the partial sums. Hence

\[
\tag{2.8}
|E_n|\leq \frac{u}{1-u}\sum_{k=2}^{n}|\widehat S_k|.
\]

This bound involves the computed partial sums but not the individual terms.
If it is weakened by bounding the partial sums in terms of the input
magnitudes, it recovers (2.5) to within second-order terms.

The first method we consider is pairwise summation (also known as cascade summation). In this method the \(x_i\) are summed in pairs, and this pairwise summation process is repeated recursively. The sum is obtained in \(\lceil\log_2 n\rceil\) stages.

The error expression (3.3) holds for pairwise summation, but it is easy to derive a useful error bound independently. Assume for simplicity that \(n=2^r\). Unlike in recursive summation each addend takes part in the same number of additions, \(\log_2 n\). Therefore, analogously to (2.2), we have a relation of the form

\[
\widehat S_n=\sum_{i=1}^{n}x_i
  \prod_{k=1}^{\log_2 n}(1+\delta_k^{(i)}),
\qquad |\delta_k^{(i)}|\leq u,
\]

which leads to the bound

\[
\tag{3.6}
|E_n|\leq\gamma_{\log_2 n}\sum_{i=1}^{n}|x_i|.
\]

This is a smaller bound than (2.6) for recursive summation, since it is proportional to \(\log_2 n\) rather than \(n\).
