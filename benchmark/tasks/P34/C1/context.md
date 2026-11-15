# Inverse secular construction, equations (3.2)--(3.3)

The paper reduces the rank-one modification problem to a diagonal matrix
`D = diag(d_1,...,d_n)` with `d_1 < ... < d_n` and a positive vector. Its
eigenvalues interlace the diagonal entries:

```text
d_1 < lambda_1 < d_2 < lambda_2 < ... < d_n < lambda_n.
```

For proposed interlacing eigenvalues `lambda_tilde_j`, Section 3 compares
their characteristic product with the determinant of
`D + z_tilde z_tilde^T`:

```text
product_j (lambda_tilde_j - lambda)
  = (1 + sum_i z_tilde_i^2 / (d_i - lambda))
      product_j (d_j - lambda).
```

Setting `lambda = d_i` gives

```text
z_tilde_i^2
  = product_j (lambda_tilde_j - d_i)
      / product_(j != i) (d_j - d_i).                     (3.2)
```

Interlacing makes the right-hand side positive, and equation (3.3) chooses
`z_tilde_i` as its positive square root. The paper then works backward:
with `z_tilde` defined by (3.3), the proposed values
`lambda_tilde_1,...,lambda_tilde_n` are exactly the eigenvalues of
`D + z_tilde z_tilde^T`.
