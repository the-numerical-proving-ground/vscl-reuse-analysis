# Theorem 3.6: CALU multiplier growth

Theorem 3.6 considers CALU with reduction-tree height H and panel width b. It states that every element of the factor L is bounded in absolute value by 2^(bH).

For a row first used at a leaf of the reduction tree, the proof writes the row of the CALU L factor as a product involving the inverses of the successive b-by-b GEPP unit-lower factors Lbar_0 through Lbar_(H-1). Entries of each Lbar_h are bounded by one in absolute value. The vectors Abar_h * Ubar_(h+1)^(-1) entering these inverse actions are also bounded componentwise by one.

The paper states that the elements in zero-based row i of

```text
abs(Lbar_h^(-1)) * abs(Abar_h * Ubar_(h+1)^(-1))
```

are bounded by 2^i. Repeating this argument through all H levels gives the componentwise factor 2^(bH). The same reasoning applies at later CALU factorization steps.

In the formal statement, `ell h` is Lbar_h. The vectors `probeIn h` and `probeOut h` represent one bounded vector and its inverse action:

```text
ell h * probeOut h = probeIn h.
```

The vectors `z h` record the successive inverse actions along the whole reduction-tree path:

```text
ell h * z (h+1) = z h.
```

The structure `P29CALUMultiplierProcess b H ell probeIn probeOut z` records these full entrywise matrix equations, unit diagonal, zeros above the diagonal, the strict-lower absolute bound of one, and the two input bounds. It does not assume either conclusion.

The conclusion is exactly the one-level 2^i inverse-action estimate stated in the proof and the final multiplier bound 2^(bH).
