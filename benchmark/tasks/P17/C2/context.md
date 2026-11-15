In this paper, \(\epsilon\) denotes a matrix or scalar satisfying
\(\|\epsilon\|\leq f(n)u\) for a modest function \(f\) depending only on
the dimension and for a fixed norm. Constants depending modestly on the
dimension and higher-order terms in \(u\) are suppressed.

For the Newton--Schulz iteration, first consider the computed approximation
\(\widehat Y\) to

\[
Y=\frac12 X(3I-X^*X), \qquad \|X\|_2<\sqrt3.
\]

If \(\widehat Y\) is computed by first forming \(XX^*X\) and then performing
the subtraction, then

\[
\widehat Y=\frac32X-\frac12(XX^*X+\epsilon_1)+\epsilon_2. \tag{6.6}
\]

Here \(\epsilon_1\) is the forward error in forming \(XX^*X\), while
\(\epsilon_2\) is the error from the subtraction. Since
\(\|X\|_2<\sqrt3\) and \(\|XX^*X\|_2=\|X\|_2^3<3\sqrt3\), both errors can
be written as \(\epsilon\|X\|_2\). Consequently,

\[
\widehat Y=\frac12X(3I-X^*X)+\epsilon\|X\|_2,
\]

so this evaluation has a small forward error and satisfies the mixed
backward--forward condition (4.10).
