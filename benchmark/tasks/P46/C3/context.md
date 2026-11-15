# Higham and Pranesh (2019), Section 3.2, equations (3.1)–(3.8)

Simulation 3.2 carries out a kernel in a higher precision and rounds its result once
into a lower precision. The respective unit roundoffs are `u_h` and `u_l`; the
analysis uses the standard relative-error model without overflow or underflow.

For `C = AB`, let `C_hat` be the high-precision computed matrix product and
`C_tilde` its entrywise low-precision rounding. Equations (3.1) and (3.2) give

```text
|C - C_hat| ≤ gamma_h(n) |A| |B|,
|C_tilde - C_hat| ≤ u_l |C_hat|,
gamma_h(n) = n u_h / (1 - n u_h).
```

The paper combines these to obtain its componentwise product bound

```text
|C - C_tilde| ≤ 2 u_l |A| |B|                              (3.3)
```

under the size condition

```text
n ≤ u_l / (u_h (1 + 2 u_l)).                              (3.4)
```

For a triangular system `T x = b`, Section 3.2 also analyzes the solution
`x_hat` computed by high-precision substitution. Equation (3.6) gives a
perturbation `Delta T` with

```text
(T + Delta T) x_hat = b,   |Delta T| ≤ gamma_h(n) |T|.     (3.6)
```

The stored solution `x_tilde` is the entrywise low-precision rounding of
`x_hat`, so `|x_tilde - x_hat| ≤ u_l |x_hat|` by (3.7). Immediately before
(3.8), the paper bounds its componentwise residual by

```text
|T x_tilde - b| ≤ (gamma_h(n) + u_l) |T| |x_hat|.
```

For the triangular kernel, the Lean target takes `T` upper triangular and
models high-precision substitution explicitly. Matrix and vector inequalities
are componentwise.
