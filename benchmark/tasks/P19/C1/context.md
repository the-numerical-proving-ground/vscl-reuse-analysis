Let (A=A[p]) be a nonsingular real (n\times n) matrix whose entries
depend linearly on parameters (p\in\mathbb R^t), and let (Ax=b).
Write the parameterization in vector form as

\[
  \operatorname{vec}(\Delta A^T)=B\Delta p,
\]

and put (X=I_n\otimes x^T). For a perturbed system in the structured
condition-number definition, the paper obtains

\[
  \Delta x
  = A^{-1}\Delta b-A^{-1}\Delta A x+O(\epsilon^2),                 \tag{3.2}
\]

with (Delta A x=XB\Delta p). If the componentwise perturbations satisfy

\[
  |\Delta p|\leq \epsilon g,
  \qquad
  |\Delta b|\leq \epsilon f,
\]

then

\[
 \left\|A^{-1}\Delta A x+A^{-1}\Delta b\right\|_\infty
 \leq
 \epsilon\left\||A^{-1}XB|g+|A^{-1}|f\right\|_\infty .           \tag{3.3}
\]

The paper states that suitable choices of the signs of (Delta p) and
(Delta b) attain equality in this bound. It therefore obtains the sharp
structured condition formula

\[
 \operatorname{cond}_\infty^S(A,x)
 =
 \frac{\left\||A^{-1}XB|g+|A^{-1}|f\right\|_\infty}
        {\|x\|_\infty}.                                           \tag{3.4}
\]

In the Lean statement, (K) denotes (A^{-1}XB), (H) denotes
(A^{-1}), and `xNorm` denotes the positive scalar (|x|_\infty).
The attainable-value set contains the relative infinity norms of

\[
  H\Delta b-K\Delta p
\]

over the same componentwise boxes. Its supremum is
`p19LinearizedCondition`, while the right side of (3.4) is
`p19ConditionFormula`.
