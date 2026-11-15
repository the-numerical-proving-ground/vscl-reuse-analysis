# Simoncini and Szyld (2003), Lemma 5.1

The published paper studies GMRES after `m` inexact Arnoldi iterations in exact arithmetic. The Arnoldi vectors are orthonormal, the `(m+1) × m` Hessenberg matrix is `H_m`, and `βe₁` represents the initial residual in Arnoldi coordinates. GMRES chooses coefficients by minimizing `‖βe₁ − H_m y‖₂`.

**Lemma 5.1 (complete claim).** For every `k = 1, …, m`, the `k`th component of the GMRES coefficient vector at iteration `m` obeys

```text
|(y_m)_k| ≤ ‖r̃_(k−1)‖₂ / σ_m(H_m),
```

where the preceding computed residual is `r̃_(k−1) = r₀ − V_(k−1)H_(k−1)y_(k−1)`.

The printed proof uses a QR factorization of `H_m`. Its orthogonal factor is the ordered product of adjacent Givens rotations, and its upper-triangular factor is `R_m`. The transformed initial residual has first `m` components `g_m`. The paper identifies component `k` of `g_m` as a cosine times the product of the preceding sines and `β`. The norm of the transformed tail beginning at `k` is therefore at most the preceding computed residual norm. Because `y_m = R_m⁻¹g_m`, upper-triangular support restricts component `k` to that tail. Cauchy–Schwarz bounds it by the tail norm times the norm of row `k` of `R_m⁻¹`. The latter is at most `1/σ_m(H_m)`, completing the proof.
