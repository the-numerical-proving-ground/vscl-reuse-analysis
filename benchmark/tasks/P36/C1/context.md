# Exceptional spectral points, Lemma 4.2

Let

```text
D = [a,b] union {x_1,...,x_k}
```

be a subset of the positive real axis and let `f(x)=1/x`. Lemma 4.2 states
that there is a constant `R`, depending only on the exceptional points and
the interval, such that

```text
e_n(D) <= R q^(n-k+1),
```

where `q=q(b/a)` is the interval approximation rate from Proposition 2.1.

The proof chooses a polynomial `r` of degree at most `k-1` that interpolates
`f` at `x_1,...,x_k` and sets

```text
phi(x) = (x-x_1)...(x-x_k).
```

The reciprocal interpolation identity expresses `f-r` as `phi` times a
constant multiple of `f`. Hence, for an interval approximant `p`, the
polynomial

```text
r + phi p
```

after incorporating that constant into `phi p`, agrees with `f` at every
exceptional point. On `[a,b]` its error is bounded by the interval error of
`p` times a constant depending only on `a`, `b`, and the exceptional points.
Taking `p` of degree `n-k` and applying Proposition 2.1 gives the displayed
bound.
