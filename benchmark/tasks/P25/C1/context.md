Choice 2 in Section 2 sets the forcing term to

\[
  \eta_k=\gamma
    \left(\frac{\lVert F(x_k)\rVert}{\lVert F(x_{k-1})\rVert}\right)^\alpha,
  \qquad 0\leq\gamma\leq 1,\quad 1<\alpha\leq 2.
\]

After proving that sufficiently local iterates remain in the chosen
neighborhood, Theorem 2.3 uses Lemma 1.4 to obtain equation (2.8):

\[
 \lVert F(x_{k+1})\rVert \leq
 \left[
   \gamma\left(
     \frac{\lVert F(x_k)\rVert}{\lVert F(x_{k-1})\rVert}
   \right)^\alpha
   +B\lVert F(x_k)\rVert
 \right]\lVert F(x_k)\rVert .
\]

For the case `gamma = 1`, the paper proves R-order `alpha`.  It writes
`tau_k = ||F(x_k)|| / ||F(x_(k-1))||`, chooses a sufficiently late index,
and reindexes it to zero so that

\[
  (2\tau_1)^{\alpha-1}+2B\lVert F(x_0)\rVert\leq 1.
\]

It then sets `D = 1/(2 tau_1)` and `beta_k = D tau_k`.  Thus `D > 1`
and `beta_1 = 1/2`.  From equation (2.8) it derives

\[
  \tau_{k+1}\leq \tau_k^\alpha
    +B\tau_k\cdots\tau_1\lVert F(x_0)\rVert
\]

and proves by induction that

\[
  \beta_k\leq \beta_1^{\alpha^{k-1}}.
\]

The formal task is the paper's `alpha = 2` specialization after this exact
reindexing.  Its sequence `residual k` represents `||F(x_k)||`; its index-zero
ratio is the paper's `tau_1`.  Consequently the displayed estimate becomes
`beta_k <= (1/2)^(2^k)`, which also tends to zero.
