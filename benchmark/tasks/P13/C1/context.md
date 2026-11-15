6.3. Repeated outside-inside scaling. Next, we consider repeatedly applying
outside and inside scaling in alternating order, as shown in Algorithm 3. This
process can only improve the error bounds, and it eventually converges.

Theorem 13. The sequence

\[
r_i^{(t)}s_j^{(t)}\|A^{(t)}\|\|B^{(t)}\|,
\qquad t=0,1,\ldots,
\]

is monotonically nonincreasing and converges linearly.

Appendix D. Convergence analysis of alternating scaling. In this appendix we
prove Theorem 13.

The intermediate scaling factors rapidly converge to 1. With

\[
w^{(t)}=\max\left(\max_i|\log r_i^{\prime(t)}|,
                         \max_j|\log s_j^{\prime(t)}|\right),
\qquad
w^{(t+1)}=\max_k|\log p_k^{\prime(t+1)}|,
\]

Lemma 20 gives

\[
w^{(t)}\leq w^{(t-1)},
\qquad
w^{(t+1)}\leq 0.5w^{(t)},
\qquad t=t_0+2,t_0+4,\ldots.
\]

The following lemma proves linear convergence, and therefore completes the
proof of Theorem 13.

Lemma 21. There is a sequence \(\nu^{(t)}\) so that

\[
\mu_{ij}^{(t)}\leq\nu^{(t)},\qquad
\mu_{ij}^{(t+1)}\leq\nu^{(t+1)},
\]

and

\[
\nu^{(t+1)}=\nu^{(t)},\qquad
\nu^{(t+2)}\leq 0.5\nu^{(t)},
\qquad t=t_0,t_0+2,\ldots.
\]

Proof. Assume that \(t=t_0,t_0+2,\ldots\). Rearranging the definition of
\(\mu_{ij}^{(t)}\), and substituting the products of the intermediate outside
scaling factors, gives

\[
\mu_{ij}^{(t)}
=\left(r_i^{\prime(t+2)}s_j^{\prime(t+2)}
       r_i^{\prime(t+4)}s_j^{\prime(t+4)}\cdots\right)^{-1}-1.
\]

Applying the definition of \(w^{(t)}\) to this expression gives

\[
\mu_{ij}^{(t)}
\leq
\exp\left(2w^{(t+2)}+2w^{(t+4)}+\cdots\right)-1.
\]

Define

\[
\nu^{(t)}=
\exp\left(2w^{(t+2)}+2w^{(t+4)}+\cdots\right)-1,
\qquad
\nu^{(t+1)}=\nu^{(t)}.
\]

This guarantees \(\mu_{ij}^{(t)}\leq\nu^{(t)}\). Since
\(r_i^{(t)}s_j^{(t)}\|A^{(t)}\|\|B^{(t)}\|\) is monotonically nonincreasing,
so is its relative distance to its limit. Thus

\[
\mu_{ij}^{(t+1)}\leq\mu_{ij}^{(t)}
\leq\nu^{(t)}=\nu^{(t+1)}.
\]

It remains to prove \(\nu^{(t+2)}\leq0.5\nu^{(t)}\). By Lemma 20,

\[
\begin{aligned}
w^{(t+3)}&\leq0.5w^{(t+2)},
&w^{(t+4)}&\leq w^{(t+3)}\leq0.5w^{(t+2)},\\
w^{(t+5)}&\leq0.5w^{(t+4)},
&w^{(t+6)}&\leq w^{(t+5)}\leq0.25w^{(t+2)},
\end{aligned}
\]

and so on. Therefore

\[
w^{(t+2)}
=(0.5+0.25+\cdots)w^{(t+2)}
\geq w^{(t+4)}+w^{(t+6)}+\cdots.
\]

It follows that

\[
\exp\left(2w^{(t+2)}\right)
\geq
\exp\left(2w^{(t+4)}+2w^{(t+6)}+\cdots\right).
\]

Applying this inequality to the definition of \(\nu^{(t)}\),

\[
\nu^{(t)}
\geq
\left(\exp\left(2w^{(t+4)}+2w^{(t+6)}+\cdots\right)\right)^2-1.
\]

Let

\[
x=\exp\left(2w^{(t+4)}+2w^{(t+6)}+\cdots\right),
\]

so that \(\nu^{(t+2)}=x-1\). Then

\[
\nu^{(t)}\geq x^2-1
=(2+\nu^{(t+2)})\nu^{(t+2)}
\geq2\nu^{(t+2)},
\]

which proves \(\nu^{(t+2)}\leq0.5\nu^{(t)}\).
