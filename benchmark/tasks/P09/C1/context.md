In order to prove our main result, we need a technical lemma to rewrite a product of binomials as a sum of monomials. In the result, we denote by P(S) the power set of the set S. It can be defined recursively by

P(empty) = {empty},

P(S union {ell}) = {T union {ell} : T in P(S)} union P(S).                 (3.5)

Lemma 3.9. Let m,n be natural numbers with m <= n, let I = {k : m <= k <= n}, and let x_k,y_k be real for every k in I. Then

prod_{k=m}^n (x_k+y_k)
= prod_{k=m}^n x_k
+ sum_{K in P(I), K != I}
    (prod_{i in K} x_i)(prod_{j in I setminus K} y_j).                    (3.6)

Proof. First prove by induction on the size of I that

prod_{k=m}^n (x_k+y_k)
= sum_{K in P(I)}
    (prod_{i in K} x_i)(prod_{j in I setminus K} y_j).                    (3.7)

For K empty, use that the empty product is 1. The formula is immediate when m=n. For the induction step, extend the set by incrementing n. Multiply the induction hypothesis by x_{n+1}+y_{n+1} and distribute it into two sums. The first sum is indexed by the subsets containing n+1 and the second by those not containing n+1. The recursive description (3.5) combines them into the power set of the extended interval. Finally, extract the term K=I, which is prod x_k, to obtain (3.6).

Equation (3.1) shows that limited-precision stochastic rounding is biased, and Lemma 3.2 shows that it does not satisfy mean independence. The following general model separates each error into a centered part and a deterministic-rounding bias.

Lemma 3.10. Let delta_1,...,delta_n be random errors produced by a sequence of elementary operations using SR_{p,r}, and let beta_1,...,beta_n be their corresponding errors incurred by fl_{p+r}. Define alpha_k=delta_k-beta_k. Then the alpha_k are mean independent:

E(alpha_k | alpha_1,...,alpha_{k-1}) = E(alpha_k) = 0.

Moreover, for every 1 <= i <= n,

prod_{k=i}^n (1+delta_k)
= prod_{k=i}^n (1+alpha_k) + B_i,                                         (3.8)

where I_i={k : i <= k <= n} and

B_i = sum_{K in P(I_i), K != I_i}
        (prod_{k in K}(1+alpha_k))
        (prod_{j in I_i setminus K} beta_j).

It satisfies

|B_i| <= gamma_{n-i+1}(u_p+u_{p+r}) - gamma_{n-i+1}(u_p),                 (3.9)

where gamma_m(x)=(1+x)^m-1.

Proof. Equation (3.3) gives E(alpha_k)=E(delta_k)-E(beta_k)=0. The variable beta_k is determined by the preceding errors, and Lemma 3.2 gives E(delta_k | alpha_1,...,alpha_{k-1})=beta_k. Therefore

E(alpha_k | alpha_1,...,alpha_{k-1})
= E(delta_k | alpha_1,...,alpha_{k-1})
  - E(beta_k | alpha_1,...,alpha_{k-1})
= beta_k-beta_k=0.

Apply Lemma 3.9 with x_k=1+alpha_k and y_k=beta_k to obtain (3.8). Since |alpha_k|<=u_p and |beta_k|<=u_{p+r}, the absolute value of the remainder is at most

sum_{K in P(I_i), K != I_i}
  (1+u_p)^{|K|} u_{p+r}^{n-i+1-|K|}.

Grouping by subset size and applying the binomial theorem gives

(1+u_p+u_{p+r})^{n-i+1}-(1+u_p)^{n-i+1}
= gamma_{n-i+1}(u_p+u_{p+r})-gamma_{n-i+1}(u_p),

which proves (3.9).
