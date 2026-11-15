# Yang, Fox, and Sanders (2021), Section 2, MP Setting 2.3 and equation (2.10)

The paper studies a dot product of two vectors held in a low precision format. In MP Setting 2.3, each input product is exact in the high precision format. The products are then added sequentially in high precision, and the accumulated scalar is rounded once to the low precision format. The analysis assumes the standard relative rounding model and excludes overflow and underflow in the final conversion.

For an input with `m` terms, the first product enters the accumulator without an addition error. The expansion in equation (2.8) assigns to every product a factor made from at most `m - 1` rounded high precision additions. Lemma 2.1 bounds each factor by `1 + θ_i`, where `|θ_i| ≤ γᵸ_(m-1)` and `γᵸ_k = k u_h / (1 - k u_h)` under `k u_h < 1`. Thus the high precision sum can be written as the exact sum of the products multiplied by their individual factors.

The final low precision conversion contributes a common factor `1 + δ_l`, with `|δ_l| ≤ u_l`. Distributing that factor into the summands gives the two backward representations in equation (2.10): the computed mixed precision dot product is both the exact dot product with componentwise perturbed first inputs and the exact dot product with componentwise perturbed second inputs. For each component, the perturbation magnitude is at most

```text
((1 + u_l) (1 + γᵸ_(m-1)) - 1) times the magnitude of that input component.
```

The Lean task uses `m = n + 1`. Its model represents exact products, high precision rounded additions, and one low precision cast directly.
