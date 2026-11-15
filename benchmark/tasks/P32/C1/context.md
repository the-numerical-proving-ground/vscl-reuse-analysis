# Lemma 3.4: multiplier for the first companion form

Section 3.2 studies the homogeneous first companion pencil
`C1(alpha,beta) = alpha X1 + beta Y1`.  Lemma 3.4 states that, for every
polynomial degree `m`, there is an `m`-by-`m` block matrix `E(alpha,beta)` such
that

```text
E(alpha,beta) C1(alpha,beta) = I_m tensor P(alpha,beta).       (3.7)
```

Using the paper's one-based block indices, its first column is

```text
E_i1 = alpha^(m-i) beta^(i-1) I_n,             1 <= i <= m.
```

For `j > 1`, the proof defines the remaining blocks by

```text
E_ij = -(alpha/beta)^(j-i)
         sum_(k=0)^(m-j) alpha^(k-1) beta^(m-k) A_k,
                                                    1 <= i < j,

E_ij =  (alpha/beta)^(j-i)
         sum_(k=m-j+1)^m alpha^(k-1) beta^(m-k) A_k,
                                                    1 < j <= i <= m.
```

The paper's proof consists of directly verifying that this explicit
`E(alpha,beta)` satisfies equation (3.7).
