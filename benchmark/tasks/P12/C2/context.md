2. Rounding error analysis and evaluation scheme. We use the standard
model of floating-point arithmetic [12, sect. 2.2]

\[
\operatorname{fl}(x\mathbin{\mathrm{op}}y)=(x\mathbin{\mathrm{op}}y)(1+\delta),
\qquad |\delta|\leq u, \tag{2.1}
\]

where $x$ and $y$ are floating-point numbers and op denotes addition,
subtraction, multiplication, or division. We give rounding error analysis for
real arithmetic, but the bounds remain valid for complex arithmetic with
appropriately increased constants [12, sect. 3.6]. In our results, when we
write $A\in\mathbb{R}^{n\times n}$ it is understood that $A$ is a matrix
of floating-point numbers.

For matrix multiplication, we have [12, sect. 3.5]

\[
\operatorname{fl}(AB)=AB+E, \qquad |E|\leq \gamma_n |A||B|, \tag{2.2}
\]

where $\gamma_n:=nu/(1-nu)$, assuming $nu<1$.

2.1. Powers and polynomials of matrices. We first derive an upper bound on
the rounding errors in the computation of $X^k$ in a fixed precision.

Lemma 2.2. For $X\in\mathbb{R}^{n\times n}$ and $X_t=X^t$ with
$t\in\mathbb{N}_+$, the computed matrix
$\widehat X_t=\operatorname{fl}(X^t)$ obtained by repeated multiplication
$\widehat X_k=\operatorname{fl}(\widehat X_{k-1}X)$, $k=1:t$,
$\widehat X_0=X$, in precision $u$ satisfies

\[
|\widehat X_t-X^t|\leq \gamma_{(t-1)n}|X|^t.
\]

Proof. For $t=2$ the bound holds by (2.2). Suppose the bound holds for
$t=k-1$:

\[
|\widehat X_{k-1}-X^{k-1}|\leq
\gamma_{(k-2)n}|X|^{k-1}.
\]

We have, for $t=k$,

\[
\begin{aligned}
|\widehat X_k-X^k|
&\leq |\widehat X_k-\widehat X_{k-1}X|
   +|\widehat X_{k-1}X-X^k| \\
&\leq \gamma_n|\widehat X_{k-1}||X|
   +|\widehat X_{k-1}-X^{k-1}||X| \\
&\leq \gamma_n(1+\gamma_{(k-2)n})|X|^{k-1}|X|
   +\gamma_{(k-2)n}|X|^k \\
&\leq \gamma_{(k-1)n}|X|^k,
\end{aligned}
\]

where in the last inequality we have used [12, Lem. 3.3], and so the proof is
completed by induction.
