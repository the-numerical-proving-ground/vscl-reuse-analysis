# Absence of poles, Theorem 1

For ordered interpolation points

```text
x_0 < x_1 < ... < x_n
```

the paper rewrites the rational interpolant with denominator

```text
s(x) = sum_{i=0}^{n-d} mu_i(x),

mu_i(x) = product_{j=0}^{i-1} (x-x_j)
          product_{k=i+d+1}^{n} (x_k-x).
```

Theorem 1 states that, for every `0 <= d <= n`, the rational function has
no real poles. Its proof shows that `s(x)` is positive.

For the part selected here, suppose

```text
x_alpha < x < x_{alpha+1},    0 <= alpha <= n-1,
```

and split the index set into

```text
I_1 = {i : i <= alpha-d},
I_2 = {i : alpha-d+1 <= i <= alpha},
I_3 = {i : alpha+1 <= i}.
```

The paper writes `s=s_1+s_2+s_3`, where `s_k` is the sum over `I_k`.
When `d >= 1`, every term in the nonempty middle block is positive. In the
right block, the first term is positive, signs alternate, and absolute values
decrease because

```text
x_{i+d+1}-x > x_i-x.
```

Pairing successive terms therefore makes the right-block sum nonnegative
(and positive when nonempty). Reading the left block in reverse gives the
same alternating, decreasing argument. Thus the positive middle block plus
the two nonnegative tails gives `s(x)>0`.
