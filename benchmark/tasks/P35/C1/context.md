# Convergence versus loss of biorthogonality, Theorem 4.1

At the end of Lanczos step `j`, the paper writes the loss matrix as

```text
P_j^T Q_j - I_j = C_j + Delta_j + D_j,
```

where `C_j` is strictly lower triangular, `Delta_j` is diagonal, and `D_j`
is strictly upper triangular. Local biorthogonality makes the relevant
neighboring entries zero. If `T_j z_i = theta_i z_i` and
`w_i^H T_j = theta_i w_i^H`, define

```text
Delta_j T_j - T_j Delta_j = K_j - L_j,
P_j^T F_j - G_j^T Q_j = N_j - M_j,
```

with `K_j,N_j` strictly lower triangular and `L_j,M_j` strictly upper
triangular. Theorem 4.1 states

```text
p_{j+1}^T x_i = phi_ji / gamma_ji,
y_i^H q_{j+1} = psi_ji / beta_ji,

phi_ji   = w_i^H (K_j + N_j) z_i,
psi_ji   = w_i^H (L_j + M_j) z_i,
gamma_ji = gamma_{j+1} (w_i^H e_j),
beta_ji  = beta_{j+1} (e_j^T z_i).
```

The proof subtracts the two projected Lanczos relations and obtains (4.10):

```text
gamma_{j+1} e_j p_{j+1}^T Q_j
  - beta_{j+1} P_j^T q_{j+1} e_j^T
= C_j T_j - T_j C_j
  + Delta_j T_j - T_j Delta_j
  + D_j T_j - T_j D_j
  + P_j^T F_j - G_j^T Q_j.
```

The first rank-one term and `C_j T_j - T_j C_j` are strictly lower
triangular; the second rank-one term and `D_j T_j - T_j D_j` are strictly
upper triangular. Taking the strictly lower and strictly upper parts gives
(4.11)--(4.12):

```text
gamma_{j+1} e_j p_{j+1}^T Q_j
  = C_j T_j - T_j C_j + K_j + N_j,

-beta_{j+1} P_j^T q_{j+1} e_j^T
  = D_j T_j - T_j D_j - L_j - M_j.
```

Multiplication on the left by `w_i^H` and on the right by `z_i` cancels
both commutators by the two eigenvector equations. Dividing by the displayed
nonzero factors gives (4.6) and (4.7).
