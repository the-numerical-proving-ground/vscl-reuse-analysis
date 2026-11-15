Section 4.1 studies the product of two unit lower-bidiagonal matrices `B`
and `C`, with nonnegative subdiagonal entries `b_i` and `c_i`. The paper
assumes that `b_i = 0` whenever `c_(i-1) = 0`.

Lemma 4.1 constructs new nonnegative unit lower-bidiagonal matrices
`B'` and `C'` such that

\[
  B'C'=BC, \qquad b'_1=0.
\]

Comparing the first two subdiagonals gives

\[
  c'_1=b_1+c_1, \qquad
  b'_i=\frac{b_i c_{i-1}}{c'_{i-1}}, \qquad
  c'_i=b_i+c_i-b'_i.
\]

To remove the subtraction, the proof introduces `d_i=b_i-b'_i` and derives

\[
  d_1=b_1, \qquad
  d_i=\frac{b_i d_{i-1}}{c'_{i-1}}, \qquad
  c'_i=c_i+d_i.
\]

The recurrence stops at the first later zero in `b`; entries after that index
are unchanged. Algorithm 4.1 implements this recurrence using no subtraction
and at most four arithmetic operations per processed index. The paragraph
after the algorithm also records that no other zero is introduced in `B`, no
zero is lost from `C`, and at most one zero of `C` can become nonzero, at the
returned stopping index.

In the Lean statement, `n` counts the stored subdiagonal positions, `q` is the
stopping index, and `p21UnitLowerBidiagonal` is the corresponding exact matrix.
The hypotheses `hbefore` and `hstop` state that `q` is the first later zero of
`b`, with `q=n` when there is no such zero.
