Plonka and Tasche, “Numerical stability of fast trigonometric and orthogonal wavelet transforms,” Section 2, Theorem 2 and proof (author PDF, pp. 5–6).

The paper uses a floating-point model with unit roundoff u: each computed basic operation is the exact result times 1+ε, where |ε|≤u, with underflow and overflow ignored. For k u<1, γ_k=k u/(1−k u). The preceding Lemma 1 treats recursive and cascade inner products. Under the standard arithmetic model, adding zero to a representable value is exact.

Theorem 2 takes a real n×n matrix A, n≥2, whose rows each have at most l nonzero entries, 2≤l≤n and l u<1. Every nonzero coefficient is precomputed as an entry of Ahat with |Ahat_jk−A_jk|≤ηu for some η>0. An exact zero coefficient remains zero in Ahat. For any real vector x, the componentwise error of the computed product obeys

    |fl(Ahat x)−A x| ≤ γ_{l̃}|A||x| + (ηu+γ_{l̃}ηu)|sign A||x|,

where l̃=l for recursive summation and l̃=⌈log₂ l⌉+1 for cascade summation. The paper also gives the corresponding first-order expression with O(u²) terms.

The preceding Lemma 1 treats arbitrary inner-product vectors. Each matrix row uses the corresponding recursive or cascade evaluation of its nonzero terms.

The proof first obtains |Ahat−A|≤ηu|sign A|. It separates the computed-product error into the floating-point evaluation error relative to Ahat x and the coefficient-precomputation error. Lemma 1 bounds each row's evaluation error by γ_{l̃}|Ahat||x|. Finally, the entrywise bound |Ahat|≤|A|+|Ahat−A| gives the displayed result for both summation choices.
