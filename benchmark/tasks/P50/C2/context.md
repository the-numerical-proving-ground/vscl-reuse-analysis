# Bientinesi and van de Geijn (2011), Theorem 3.5

The published paper is *Goal-Oriented and Modular Stability Analysis*, SIAM Journal on Matrix Analysis and Applications 32(1), pp. 286–308. Section 3 gives the left-to-right dot-product algorithm in Figure 3.1(left), the local rounding model, the diagonal perturbation pattern (3.3), and the complete Theorem 3.5 with two presentations of its proof on printed pages 290–292 (physical PDF pages 5–7).

For vectors (x,y\in\mathbb R^n), the algorithm starts at zero and visits the products in index order. It rounds each product (x_jy_j), then adds it to the accumulator. The first addition from zero is exact. The standard arithmetic model writes every other rounded addition and multiplication as its exact result multiplied by (1+\delta), where (|\delta|\le u). The paper assumes (nu<1) and writes (\gamma_k=ku/(1-ku)).

**Theorem 3.5 (complete claim).** The computed dot product has an exact diagonal backward-error representation

\[
\widehat\kappa=x^\mathsf T(I+\Sigma^{(n)})y
 =\sum_{j=0}^{n-1}x_jy_j(1+\theta_j).
\]

For (n=0) the sum is empty. For (n=1), (|\theta_0|\le\gamma_1). For (n\ge2), the paper's diagonal pattern is (\operatorname{diag}(\theta_n,\theta_n,\theta_{n-1},\ldots,\theta_2)): the first two coefficients have bounds (\gamma_n), and the coefficient at position (j\ge2) has bound (\gamma_{n-j+1}). The symbols at different positions denote independent error factors, even when they share a subscript. The paper's statement and equation (3.3) together specify this position-dependent content.

The printed induction proves the whole representation. At the first product, only multiplication contributes a local factor. At each later step, the new multiplication factor and addition factor attach to the new product, while the addition factor also multiplies every coefficient already in the accumulated dot product. The proof combines these local factors into the position-dependent (\gamma_k) bounds. The accompanying error worksheet proves the same invariant over every loop iteration.

The Lean definitions use zero-based `Fin` indices and the exact same operation order. `p50SourceBudget n j` is (n) for (j=0) and (n-j+1) otherwise; in particular it is (n) at (j=1) and (2) at the last index when (n\ge2). This makes the complete printed diagonal pattern explicit for all lengths.
