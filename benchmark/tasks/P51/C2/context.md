Plonka, Schumacher, and Tasche, “Numerical stability of biorthogonal wavelet transforms,” Section 3, Lemma 3.2 (author preprint, pp. 7–8).

The paper uses a floating-point model with unit roundoff u: a computed basic operation is the exact result multiplied by 1+ε, with |ε|≤u, and it ignores underflow and overflow. For k u<1 it writes γ_k=k u/(1−k u). Recursive inner-product summation obeys the γ_k absolute-product bound of Lemma 3.1.

Lemma 3.2 considers an m×n matrix A with at most l nonzero entries in each row, 2≤l<n, and l u<1. Its nonzero coefficients are precomputed as entries of Ahat with absolute error at most ηu for some η>0; zero entries of A remain zero in Ahat. For machine-number input x, the recursively computed matrix-vector product satisfies, componentwise,

    |fl(Ahat x) − A x| ≤ γ_l |A| |x| + (ηu + γ_l ηu) |sign A| |x|.

The paper's proof first bounds |Ahat−A| by ηu |sign A|. It splits the final error into the rounded product error relative to Ahat x and the precomputation difference (Ahat−A)x. For each row, recursive summation over its nonzero entries bounds the first part by γ_l |Ahat| |x|. The triangle inequality for |Ahat| completes the stated bound.
