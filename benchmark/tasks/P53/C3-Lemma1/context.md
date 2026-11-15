Plonka and Tasche, “Numerical stability of fast trigonometric and orthogonal wavelet transforms,” Section 2, complete Lemma 1 (author PDF, p. 4).

The paper uses the standard relative-error floating-point model, with unit roundoff u and no overflow or underflow. It defines gamma_k = k u/(1−k u) for k u<1. Its inner product is computed either recursively, accumulating the n rounded products in sequence, or by cascade summation, combining the rounded products in a balanced tree.

Lemma 1 states both bounds for arbitrary real n-vectors a and b when n u<1. The recursive result is |aᵀb−fl(aᵀb)| ≤ gamma_n |a|ᵀ|b|. The cascade result is |aᵀb−fl(aᵀb)| ≤ gamma_{ceil(log₂ n)+1} |a|ᵀ|b|. The printed proof says these follow by induction over n and cites the standard roundoff analysis for inner products.

The Lean target uses n>0 and the paper’s n u<1 guard. Its `Nat.clog 2 n` is ceil(log₂ n), and `p53Dot` and `p53CascadeDot` are the recursive and balanced algorithms defined in the common paper model.
