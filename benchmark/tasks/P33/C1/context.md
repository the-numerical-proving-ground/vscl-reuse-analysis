# Theorem 4.5: nontrivial core transformations

Section 4.1 represents the factorized companion matrix using descending core
transformations `C1,...,Cn` and `B1,...,Bn`. If the active part of `Ci` is
`[ui vi; wi zi]`, Theorem 4.1 sets `gamma_i = |wi| = |vi|` and states

```text
gamma_1 ... gamma_n = 1 / ||x||_2.                         (4.6)
```

Its proof uses the persistent relations `C x = alpha e1`, `x_(n+1) = -1`, and
`||x||_2 = |alpha|`. Successively applying the adjoints of the cores to `e1`
gives

```text
x_(n+1) = alpha v_n ... v_1,
```

and taking absolute values gives (4.6).

Theorem 4.5 considers the active parts `[ui vi; wi zi]` of `Bi` and defines
`beta_i = |wi| = |vi|`. It states that every `beta_i` is positive and that

```text
beta_1 ... beta_n = |a0| / ||x||_2.                        (4.9)
```

In the proof, the subdiagonal entries of `B` are the main-diagonal entries of
the upper-triangular tail `Htilde`, while the corresponding subdiagonal entries
of `C` are the main-diagonal entries of the upper-triangular tail `Ctilde`.
The identity `Htilde = Ctilde Rtilde` therefore gives
`beta_i = gamma_i |r_ii|`. Taking products, applying Theorem 4.1, and using
`|det Rtilde| = |det Atilde| = |a0|` proves (4.9). Since `a0` is nonzero, all
the factors `beta_i` are positive.
