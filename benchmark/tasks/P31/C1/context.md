# Proposition 3.4: rank loss implies an invariant subspace

Section 3.2 considers the vector case.  After `m-1` K-PIK iterations,

```text
Range(V_m) = K_(2m)(A, A^(-m) B)
           = span{A^(-m)B, ..., A^(-1)B, B, AB, ..., A^(m-1)B}.
```

At iteration `m`, the two new directions before normalization are represented
by `A^m B` and `A^(-m-1) B`, after their components in `Range(V_m)` have been
removed.  Proposition 3.4 states that if this new two-column block has rank
less than two, then the space obtained by adjoining it to `V_m` is invariant
under `A` (with respect to `B`).

The proof writes rank loss as a nontrivial relation

```text
alpha_(-m) A^(-m)B + ... + alpha_(-1) A^(-1)B + alpha_0 B
  + alpha_1 AB + ... + alpha_(m-1) A^(m-1)B
  + alpha_m A^m B + alpha_(-m-1) A^(-m-1)B = 0.
```

If the coefficient of `A^(-m-1)B` is zero, the relation expresses the upper
new direction in the old space, which is therefore invariant.  If both end
coefficients are nonzero, multiplying the relation by `A` expresses the next
positive power in the enlarged space, again proving invariance.
