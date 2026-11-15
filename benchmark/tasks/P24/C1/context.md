Section 6 treats the one-column case.  Let `A` be an invertible real
`n`-dimensional linear map, let `B` be nonzero, and let every shifted map
`A + p_j I` be invertible.  The paper defines a two-sided sequence by
`v_0 = B` and

\[
  v_{j+1}=(A+p_j I)v_j.
\]

For negative indices this recurrence uses the inverse shifted maps.  The
subspace `L(A,B,p)` is the span of all vectors in this two-sided sequence.

Theorem 6.1, equations (6.3)--(6.4), states that for every integer `s`, the
span of the full sequence equals the span of the `n` consecutive vectors
from `v_s` through `v_{s+n-1}`.  This is also the order-`n` ordinary Krylov
subspace generated from `v_s`, and it equals the order-`n` Krylov subspace
generated from `B`.

For forward indices, Lemma 6.2 uses the recurrence to identify consecutive
shifted-vector spans with ordinary Krylov spans and then uses stabilization
after dimension `n`.  For backward indices, Lemma 6.3 first puts
`(A+p_{s-1}I)^{-1}v_s` in the span of `v_s,Av_s,...,A^{n-1}v_s` by a linear
dependence argument in dimension `n`.  It then repeats this containment to
reach every earlier vector.  The proof of Theorem 6.1 combines the two
lemmas and takes `s=0` to obtain the Krylov span based on `B`.
