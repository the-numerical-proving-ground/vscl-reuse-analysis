                                                                                                                                            Throughout this work we will use the following model of rounding errors, which
                                                                                                                                        was also used in [7] and [16].
                                                                                                                                            Model 1.5 (probabilistic model of rounding errors). Let the computation of
                                                                                                                                        interest generate rounding errors \delta 1 , \delta 2 , . . . (in that order) satisfying (1.4). The \delta k are
                                                                                                                                        mean independent random variables of mean zero.
                                                                                                                                              For the round to nearest rounding mode (the default in IEEE arithmetic) the
                                                                                                                                        error bounds obtained under Model 1.5 often reflect the behavior of the actual errors
                                                                                                                                        obtained, but in some circumstances the model is not valid because the rounding
                                                                                                                                        errors are highly dependent or have nonzero mean, and the bound can then be violated
                                                                                                                                        [7, sec. 7], [8, sec. 8], [15, sec. 4.2]. For stochastic rounding [7], [8], the rounding errors
                                                                                                                                        always satisfy the model. For further discussion of the applicability of the model see
                                                                                                                                        [7], [15].
                                                                                                                                              In our probabilistic rounding error analysis it is more difficult than in worst-case
                                                                                                                                        rounding error analysis to bound terms of all orders in u so we will state the bounds
                                                                                                                                        to first order in u. We will, however, show that the higher order terms do not change
                                                                                                                                        the conclusions of the analysis. We also give explicit bounds for the probabilities with
                                                                                                                                        which the error bounds hold, and these show that the analysis does not introduce
                                                                                                                                        exponential worsening of probabilities with the dimensions. All our probabilistic
                                                                                                                                        results can informally be stated as saying that the given backward error bound holds
                                                                                                                                        with \lambda  a modest constant with high probability.
                                                                                                                                             In the first two lemmas we consider the application of the Householder matrices
                                                                                                                                        to a vector b. In Lemma 4.3 and Theorem 4.4, b is taken to be each of the columns
                                                                                                                                        of A in turn. In the first three lemmas we take the Householder vectors to be exact.
                                                                                                                                                Lemma 4.1. Consider the (given) Householder matrices

                                                                                                                                                                                Pi = I  -  vi viT \in  \BbbR m\times m ,                       viT vi = 2,                                i = 1 : r,

                                                                                                                                        and the product

                                                                                                                                                                                            br+1 = Pr . . . P2 P1 b,                                   b = b1 \in  \BbbR m ,

                                                                                                                                         computed as bj+1 = Pj bj = bj  -  (vjT bj )vj , j = 1 : r. Under Model 1.5, the computed
                                                                                                                                        \widehat br+1 satisfies

                                                                                                                                        (4.1)                                              \widehat br+1 = (Pr + \Delta Pr ) . . . (P1 + \Delta P1 )b,

                                                                                                                                        where

                                                                                                                                        (4.2)                                                                \| \Delta Pj \| 2 \leq  c5 \gamma
                                                                                                                                                                                                                                        \widetilde m (\lambda )

                                                                                                                                        holds for all j with probability at least p2 (\lambda , m, r) = 1  -  2rm exp( - \lambda 2 /2).
                                                                                                                                             Proof. Define the scalars sj = vjT bj . From standard rounding error analysis
                                                                                                                                        [12, sec. 3.1], [15, Proof of Thm. 3.1], the computed sj satisfy s\widehat j = vjT Dj\widehat bj , where
                                                                                                                                                                   \Bigl(      \Bigr)                               m \Bigl(                   \Bigr)                     \bigm|            \bigm|
                                                                                                                                                                           (j)                         (j)                                 (j)                            \bigm|  (j) \bigm|
                                                                                                                                                                                                                   \prod
                                                                                                                                                          Dj = diag dk ,                            dk =                        1 + \delta k,i ,                          \bigm| \delta k,i \bigm|  \leq  u,   i, k = 1 : m.
                                                                                                                                                                                                                   i=1

                                                                                                                                        Then we form
                                                                                                                                                                                                                         \Bigl(          \Bigr)  \Bigl(  \Bigl(          \Bigr)         \Bigr)
                                                                                                                                                                    \widehat bj+1 = fl(\widehat bj  -  s\widehat j vj ) = I + \Lambda (j) \widehat bj  -  I + \Lambda (j) s\widehat j vj ,
                                                                                                                                                                                                                                      1                               2

                                                                                                                                        where
                                                                                                                                                                                                     \Bigl(  \Bigr)                    \bigm|  \bigm|
                                                                                                                                                                                             (j)               (j)                     \bigm|  (j) \bigm|
                                                                                                                                                                                     \Lambda k = diag \epsilon k,i ,                   \bigm| \epsilon k,i \bigm|  \leq  u,        k = 1,2.

                                                                                                                                                                (j)                                 (j)                                                                                                                        (j)
                                                                                                                                        Note that \Lambda 1 depends on \Lambda 2 , and that since we are using Model 1.5 the \delta k,i and
                                                                                                                                                 (j)
                                                                                                                                        \epsilon k,i are mean independent random variables of mean zero. Hence
                                                                                                                                                                 \Bigl(              \Bigr)  \Bigl(               \Bigl(          \Bigr)                    \Bigr)
                                                                                                                                                  \widehat bj+1 = I + \Lambda (j) \widehat bj  -  I + \Lambda (j) v T Dj\widehat bj \cdot  vj
                                                                                                                                                                                 1                                         2              j
                                                                                                                                                                 \Bigl(              \Bigr)  \Bigl(           \Bigl(          \Bigr)        \Bigr)
                                                                                                                                                                                 (j)                                      (j)
                                                                                                                                                                = I + \Lambda 1                     I  -  I + \Lambda 2 vj vjT Dj \widehat bj
                                                                                                                                                                 \Bigl[  \Bigl(                       \Bigr)                                                            \Bigl(  \Bigl(      \Bigr)  \Bigr) \Bigr]
                                                                                                                                                                                                 (j) \bigl(                                                         (j)                 (j)
                                                                                                                                                                                                                  vj vjT + vj vjT (Dj  -  I) + \Lambda 1 I  -  I + \Lambda 2 vj vjT Dj \widehat bj
                                                                                                                                                                                                                                                    \bigr)
                                                                                                                                                                = I  -  I + \Lambda 2
                                                                                                                                        (4.3) = (Pj + \Delta Pj )\widehat bj ,




                                                                                                                                             Copyright © by SIAM. Unauthorized reproduction of this article is prohibited.

1152                         MICHAEL P. CONNOLLY AND NICHOLAS J. HIGHAM


                                                                                                                                        where
                                                                                                                                                                                 \Bigl(             \Bigr)                     \Bigl(  \Bigl(      \Bigr)  \Bigr)
                                                                                                                                                                     (j)                        (j)                        (j)                 (j)
                                                                                                                                        (4.4) \Delta Pj =  - \Lambda 2 vj vjT  -  I + \Lambda 2 vj vjT (Dj  -  I) +\Lambda 1 I  -  I + \Lambda 2 vj vjT Dj ,
Downloaded 08/05/26 to 129.97.125.159 . Redistribution subject to SIAM license or copyright; see https://epubs.siam.org/terms-privacy




                                                                                                                                                                                 \underbrace{}              \underbrace{}
                                                                                                                                                                                                                 (\ast )

                                                                                                                                        and so

                                                                                                                                                              \| \Delta Pj \| 2 \leq  2u + 2(1 + u)\| Dj  -  I\| 2 + u (1 + 2(1 + u)\| Dj \| 2 )
                                                                                                                                                                              = 3u + 2(1 + u)\| Dj  -  I\| 2 + 2u(1 + u)\| Dj \| 2 .

                                                                                                                                            From Lemma 1.4 we have that for any constant \lambda  > 0 and any particular j,
                                                                                                                                                                                 \bigm|        \bigm|
                                                                                                                                                                (j)          (k) \bigm|  (k) \bigm|
                                                                                                                                        (4.5)                  dk = 1 + \psi j , \bigm| \psi j \bigm|  \leq  \gamma
                                                                                                                                                                                                             \widetilde m (\lambda ),

                                                                                                                                        holds for any particular k and j with probability at least p(\lambda ) = 1  -  2 exp( - \lambda 2 /2),
                                                                                                                                        or equivalently it fails to hold with probability at most 1  -  p(\lambda ). By the inclusion-
                                                                                                                                        exclusion principle [21, p. 39] (4.5) fails to hold for at least one of the pairs (j, k)
                                                                                                                                        with probability at most rm(1  -  p(\lambda )), which means that it holds for all j and k with
                                                                                                                                        probability at least p2 (\lambda , m, r) = 1  -  rm(1  -  p(\lambda )) = 1  -  2rm exp( - \lambda 2 /2).
                                                                                                                                            Hence \| I  -  Dj \| 2 \leq  \gamma
                                                                                                                                                                         \widetilde m (\lambda ) holds for all j with probability at least p2 (\lambda , m, r) and
                                                                                                                                        hence

                                                                                                                                        (4.6)           \| \Delta Pj \| 2 \leq  3u + 2(1 + u)\widetilde                          \widetilde m (\lambda )) \leq  c5 \gamma
                                                                                                                                                                                             \gamma m (\lambda ) + 2u(1 + u)(1 + \gamma                            \widetilde m (\lambda )
                                                                                                                                            Lemma 4.2. With the same notation as in Lemma 4.1, assume that the bound
                                                                                                                                        (4.2) holds with probability 1 for all j. Then the computed \widehat br+1 satisfies
                                                                                                                                                                                                                           \surd
                                                                                                                                        (4.7)          \widehat br+1 = QT (b + \Delta b), \| \Delta b\| 2 \leq  c6 \lambda  r \gamma
                                                                                                                                                                                                                                  \widetilde m (\lambda )\| b\| 2 + O(u2 )

                                                                                                                                        with probability at least p3 (\lambda , m) = 1  -  2m exp( - \lambda 2 ), where Q = (Pr . . . P2 P1 )T .
                                                                                                                                              Proof. We can rewrite (4.1) as
                                                                                                                                                                             \left(                                                       \right)
                                                                                                                                                                                      r
                                                                                                                                                                                    \sum
                                                                                                                                                      \widehat br+1 = br+1 +              Pr . . . Pj+1 \Delta Pj Pj - 1 . . . P1 + O(u2 ) b
                                                                                                                                                                                               j=1
                                                                                                                                                                                                  \left(                            \right)
                                                                                                                                                                                                           r
                                                                                                                                                                                                         \sum
                                                                                                                                        (4.8)                           = br+1 + QT                              Fj + O(u2 )                   b,
                                                                                                                                                                                                      j=1

                                                                                                                                        where

                                                                                                                                        (4.9)                                              Fj = P1 . . . Pj \Delta Pj Pj - 1 . . . P1 .

                                                                                                                                        Our aim is to show that \BbbE (Fj |  Fj - 1 , . . . , F1 ) = 0, so that we can apply Theorem 3.2
                                                                                                                                        with Xk = Fk . When we substitute the expressions for Fj and then \Delta Pj into this
                                                                                                                                        expression and use the linearity of the expectation we obtain a sum of expectations,
                                                                                                                                        each of which we need to show is zero. We will just consider two of the terms, which
                                                                                                                                        come from (\ast ) in (4.4), as the other terms are treated similarly.
                                                                                                                                            Theorem 4.4 bounds the backward error to first order, while the analogous worst-
                                                                                                                                        case result, Theorem 1.1, bounds all orders. We argue that the exclusion of higher-
                                                                                                                                        order terms is inconsequential. Set r = n in Lemma 4.2. The O(u2 ) term that we
                                                                                                                                        dropped from the analysis\bigl(  after    the expansion of (4.1) at the beginning of the proof
                                                                                                                                        of Lemma 4.2 comprises n2 terms of order u2 and in view of (4.2) is bounded by
                                                                                                                                                                          \bigr)
