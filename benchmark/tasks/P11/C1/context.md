                                                                                                                                            Model 1 (mixed precision MMA unit). We consider a mixed precision matrix
                                                                                                                                        multiply-accumulate (MMA) unit with the following specifications to compute a given
                                                                                                                                        matrix product C = AB. The input matrices A and B must be rounded to a floating-
                                                                                                                                        point format, called the input format, which uses t bits of precision and an exponent
                                                                                                                                        range [emin , emax ], leading to
                                                                                                                                              \bullet  a unit roundoff equal to u = 2 - t ;
                                                                                                                                              \bullet  a range of normalized numbers equal to \pm [fmin , fmax ], with fmin = 2e\mathrm{m}\mathrm{i}\mathrm{n}
                                                                                                                                                       and fmax = 2e\mathrm{m}\mathrm{a}\mathrm{x} (2  -  2u). If subnormal numbers are available, the interval
                                                                                                                                                       [ - fmin , fmin ] contains representable values uniformly spaced by 2ufmin . The
                                                                                                                                                       maximum distance between any real number in [ - fmin , fmin ] and the nearest
                                                                                                                                                       floating-point number is therefore
                                                                                                                                                                                                   \Biggl\{
                                                                                                                                                                                                            fmin /2 if subnormals are not available,
                                                                                                                                                       (2.1)         gmin =
                                                                                                                                                                                                            ufmin with subnormals (gradual underflow).

                                                                                                                                        The computation of the inner products are performed in a floating-point format, called
                                                                                                                                        the accumulation format, which uses T \geq  t bits of precision and an exponent range
                                                                                                                                        [Emin , Emax ] \supseteq  [emin , emax ], leading to
                                                                                                                                               \bullet  a unit roundoff equal to U = 2 - T ;
                                                                                                                                               \bullet  a range of normalized numbers equal to \pm [Fmin , Fmax ], with Fmin = 2E\mathrm{m}\mathrm{i}\mathrm{n}
                                                                                                                                                        and Fmax = 2E\mathrm{m}\mathrm{a}\mathrm{x} (2  -  2U ). If subnormal numbers are available, the interval
                                                                                                                                                        [ - Fmin , Fmin ] contains representable values uniformly spaced by 2U Fmin . The
                                                                                                                                                        maximum distance between any real number in [ - Fmin , Fmin ] and the nearest
                                                                                                                                                        floating-point number is therefore
                                                                                                                                                                                                   \Biggl\{
                                                                                                                                                                                                            Fmin /2 if subnormals are not available,
                                                                                                                                                        (2.2)         Gmin =
                                                                                                                                                                                                            U Fmin with subnormals (gradual underflow).

                                                                                                                                             For both the input and accumulation formats, we use the following model of
                                                                                                                                        floating-point arithmetic [6, eqn. 2]. Assuming overflow does not occur,

                                                                                                                                        (2.3)                  fl(x) = x(1 + \delta ) + \eta ,   | \delta |  \leq  u,   | \eta |  \leq  gmin ,   \eta \delta  = 0,
                                                                                                                                        where fl(x) refers to the operator that rounds x \in  \BbbR  to the nearest number repre-
                                                                                                                                        sentable in the input format. Similarly,

                                                                                                                                        (2.4)                    FL(x op y) = (x op y)(1 + \delta ) + \eta ,                                                                 | \delta |  \leq  U,                              | \eta |  \leq  Gmin ,                     \eta \delta  = 0,

                                                                                                                                        where FL(x op y) refers to the operator rounding x op y to the accumulation format
                                                                                                                                        with op \in  \{ +,  - , \times , \div \} . In the above, the condition \eta \delta  = 0 refers to the fact that each
                                                                                                                                        error can only be affected by either rounding or underflow, but not both at the same
                                                                                                                                        time.
                                                                                                                                            The models (2.3) and (2.4) assume round-to-nearest mode [11, sect. 4.3]. How-
                                                                                                                                        ever, these models continue to hold with directed rounding modes (such as round-to-
                                                                                                                                        zero, etc.) by replacing u and gmin (resp., U and Gmin ) with 2u and 2gmin (resp., 2U
                                                                                                                                        and 2Gmin ). This remark is particularly of interest for NVIDIA tensor cores, which
                                                                                                                                        where the max() is componentwise and where we have taken \ell  = p  -  1. Hence
                                                                                                                                                                                                                       p - 1
Downloaded 08/05/26 to 129.97.125.159 . Redistribution subject to SIAM license or copyright; see https://epubs.siam.org/terms-privacy




                                                                                                                                                                                                                       \sum
                                                                                                                                        (4.14)                                                                x=               \lambda  - 1 ui x(i) + \Delta x,
                                                                                                                                                                                                                       i=0

                                                                                                                                        where since \lambda  - 1 \leq  2\theta  - 1 \| x\| \infty
                                                                                                                                        (4.15)                            | \Delta x|  = | \lambda  - 1 \Delta x(p - 1) |  \leq  max(up | x| , \lambda  - 1 up - 1 gmin )
                                                                                                                                        (4.16)                                                                          \leq  max(up | x| , 2up - 1 \theta  - 1 gmin \| x\| \infty  ).
                                                                                                                                        Similarly we have for y
                                                                                                                                                                                p - 1
                                                                                                                                                                                \sum
                                                                                                                                        (4.17)                    y=                    \mu  - 1 uj y (j) + \Delta y,           | \Delta y|  \leq  max(up | y| , 2up - 1 \theta  - 1 gmin \| y\| \infty  ).
                                                                                                                                                                                j=0

                                                                                                                                                Going back to the full matrices A and B, we have therefore proven
                                                                                                                                                                                             p - 1
                                                                                                                                                                                             \sum
                                                                                                                                        (4.18)                                      A=                ui \Lambda  - 1 A(i) + \Delta A,               \| \Delta A\| \infty  \leq  \zeta \| A\| \infty  ,
                                                                                                                                                                                             i=0
                                                                                                                                                                                             p - 1
                                                                                                                                                                                             \sum
                                                                                                                                        (4.19)                                     B=                 uj B (j) M  - 1 + \Delta B,                        \| \Delta B\| \infty  \leq  \zeta \| B\| \infty
                                                                                                                                                                                             j=0

                                                                                                                                        with

                                                                                                                                        (4.20)                                                            \zeta  = max(up , 2nup - 1 \theta  - 1 gmin ).

                                                                                                                                        This generalizes the multiword decomposition error bound of order up by taking into
                                                                                                                                        account possible underflows, which add the error term 2nup - 1 \theta  - 1 gmin .
                                                                                                                                             It now remains to bound the accuracy of the product C = AB approximated with
                                                                                                                                        (4.7) and computed in the accumulation format. Denoting by \Delta C the errors in the
                                                                                                                                        computation of the products A(i) B (j) in the accumulation format, the computed C   \widehat
                                                                                                                                        satisfies                          \left(                                  \right)
                                                                                                                                                                                   \sum
                                                                                                                                        (4.21) C  \widehat  = \Lambda  - 1               ui+j A(i) B (j) + \Delta C M  - 1
                                                                                                                                                                                    i+j<p
                                                                                                                                                                                \left(                                                                                                                      \right)
                                                                                                                                                                                        p - 1 \sum
                                                                                                                                                                                       \sum   p - 1                                     \sum
                                                                                                                                                                          - 1
                                                                                                                                        (4.22)              = \Lambda                                 ui+j
                                                                                                                                                                                                              A B(i)     (j)
                                                                                                                                                                                                                                  -                   u  i+j           (i)
                                                                                                                                                                                                                                                                     A B         (j)
                                                                                                                                                                                                                                                                                         + \Delta C                    M  - 1
                                                                                                                                                                                    i=0 j=0                                            i+j\geq p
                                                                                                                                                                                                                                                           \left(                                                               \right)
                                                                                                                                                                 p - 1
                                                                                                                                                                 \sum                                 p - 1
                                                                                                                                                                                                      \sum                                                                          \sum
                                                                                                                                        (4.23)              =               ui \Lambda  - 1 A(i)              uj B (j) M  - 1 + \Lambda  - 1                     \Delta C  -                     ui+j A(i) B (j)                           M  - 1
                                                                                                                                                                  i=0                                 j=0                                                                         i+j\geq p
                                                                                                                                                                                                                                                                     \sum
                                                                                                                                                                                                                           - 1                   - 1
                                                                                                                                        (4.24)              = (A  -  \Delta A)(B  -  \Delta B) + \Lambda                         \Delta CM                -                    ui+j \Lambda  - 1 A(i) B (j) M  - 1
                                                                                                                                                                                                                                                                 i+j\geq p
                                                                                                                                        (4.25)              = AB + E.
                                                                                                                                        Since by construction | A(i) |  \leq  (1 + u)| \Lambda A|  and | B (j) |  \leq  (1 + u)| BM | , we have
                                                                                                                                                      \bigm\|                                      \bigm\|
                                                                                                                                                      \bigm\|                                      \bigm\|
                                                                                                                                                      \bigm\|  \sum  i+j  - 1 (i) (j)  - 1 \bigm\|                              p
                                                                                                                                        (4.26)                          u \Lambda  A B M \bigm\|   \bigm\|  \lesssim  (p  -  1)u \| A\| \infty  \| B\| \infty  .
                                                                                                                                                      \bigm\|
                                                                                                                                                      \bigm\|
                                                                                                                                                      \bigm\| i+j\geq p                            \bigm\|
                                                                                                                                                                                                                                           \infty




                                                                                                                                             Copyright © by SIAM. Unauthorized reproduction of this article is prohibited.

MATRIX MULTIPLICATION WITH NARROW RANGE ARITHMETIC                                                                                                   B795

                                                                                                                                        To bound the error \Delta C, [7, Thm. 2.1] obtains a relative error bound of order (n+p2 )U ,
                                                                                                                                        to which we must add the accumulation underflows. Proceeding identically to the
Downloaded 08/05/26 to 129.97.125.159 . Redistribution subject to SIAM license or copyright; see https://epubs.siam.org/terms-privacy




                                                                                                                                        single word analysis of the previous section, we obtain
                                                                                                                                                                                        \Bigl(                           \Bigr)
                                                                                                                                        (4.27)           \| \Delta C\| \infty  \lesssim  (n + p2 )U + 4rn\theta  - 2 Gmin \| A\| \infty  \| B\| \infty  ,

                                                                                                                                        where r bounds the maximum number of possible underflows in the computation of
                                                                                                                                        any coefficient of C: for the same reason as in the p = 1 case, we have the bound
                                                                                                                                        r \leq  np(p + 1)/2. In conclusion we have proven
                                                                                                                                                                                  \Bigl(
                                                                                                                                                          \| E\| \infty  \lesssim  2\zeta  + \zeta  2 + (p  -  1)up
                                                                                                                                        (4.28)                                                                               \Bigr)
                                                                                                                                                                                  + (n + p2 )U + 2p(p + 1)n2 \theta  - 2 Gmin \| A\| \infty  \| B\| \infty  ,

                                                                                                                                        where \zeta  is defined in (4.20).
                                                                                                                                            4.2. Summary and discussion. We summarize the extension of Theorem 3.1
                                                                                                                                        to multiword arithmetic in the following theorem.
                                                                                                                                            Theorem 4.1. Let A \in  \BbbR m\times n and B \in  \BbbR n\times q and consider a mixed precision MMA
                                                                                                                                        unit as specified in Model 1. Let \Lambda  and M be diagonal matrices whose coefficients are
                                                                                                                                        powers of two such that the elements of \Lambda A and BM are all bounded by
                                                                                                                                                                                      \Bigl(        \sqrt{}         \Bigr)
                                                                                                                                                                         \theta  = min fmax , Fmax /n .
                                                                                                                                                                                                                \sum p - 1 i (i)
                                                                                                                                                                                                                                                                                           \sum p - 1
                                                                                                                                                                                                                                                                                                    j (j)
                                                                                                                                        Let the p-word decompositions \Lambda A \approx                               i=0 u A    and BM \approx                                                j=0 u B    be com-
                                                                                                                                        puted as
                                                                                                                                                                        \Biggl( \Biggl(                                    i - 1
                                                                                                                                                                                                                                                  \Biggr)              \Biggr)
                                                                                                                                                                                                                           \sum
                                                                                                                                                                               (i)                                                  k       (k)                    i
                                                                                                                                        (4.29)                             A         = fl                  \Lambda A  -            u A                       /u                   ,
                                                                                                                                                                                                                           k=0
                                                                                                                                                                                                                            j - 1
                                                                                                                                                                                            \Biggl( \Biggl(                                            \Biggr)              \Biggr)
                                                                                                                                                                                                                            \sum
                                                                                                                                                                               (j)                                                      k    (k)                        j
                                                                                                                                        (4.30)                             B         = fl                  BM  -                    u B                           /u                   ,
                                                                                                                                                                                                                            k=0

                                                                                                                                        where fl(\cdot ) denotes the rounding operator to the input format. Let C = AB be computed
                                                                                                                                        as
                                                                                                                                                                                         \left(                     \right)
                                                                                                                                                                                                 \sum
                                                                                                                                                                                     - 1
                                                                                                                                        (4.31)                         C = \Lambda                      i+j (i) (j)
                                                                                                                                                                                                       u A B                 M  - 1 ,
                                                                                                                                                                                                        i+j<p


                                                                                                                                        where the inner products in the matrix products A(i) B (j) are all computed in the
                                                                                                                                        accumulation format. Then the computed C                           \widehat  satisfies
                                                                                                                                                                                            \Bigl(
                                                                                                                                                        \widehat   -  AB\| \infty  \lesssim  (p + 1)up + 4nup - 1 \theta  - 1 gmin
                                                                                                                                                     \| C
                                                                                                                                        (4.32)                                                                                          \Bigr)
                                                                                                                                                                                             + (n + p2 )U + 2p(p + 1)n2 \theta  - 2 Gmin \| A\| \infty  \| B\| \infty  .

                                                                                                                                             Bound (4.32) is to be compared with the bound obtained by Fasi et al. [7, Thm.
                                                                                                                                        2.1] without taking into account range limitations:
                                                                                                                                                                                                \Bigl(                 \Bigr)
                                                                                                                                        (4.33)              \widehat   -  AB\| \infty  \lesssim  (p + 1)up + (n + p2 )U \| A\| \infty  \| B\| \infty  .
                                                                                                                                                         \| C




                                                                                                                                           Copyright © by SIAM. Unauthorized reproduction of this article is prohibited.

B796                            THEO MARY AND MANTAS MIKAITIS


                                                                                                                                        The comparison shows that we recover the same two terms of order up and U , and
                                                                                                                                        we have two new terms of order up - 1 \theta  - 1 gmin and \theta  - 2 Gmin to account for the input
Downloaded 08/05/26 to 129.97.125.159 . Redistribution subject to SIAM license or copyright; see https://epubs.siam.org/terms-privacy




                                                                                                                                        and accumulation underflows, respectively.
                                                                                                                                             More importantly, we should compare bound (4.32) with bound (3.26) obtained
                                                                                                                                        by Theorem 3.1, to check whether the conclusions of the previous sections continue
                                                                                                                                        to hold with multiword arithmetic. The comparison shows that the error terms as-
                                                                                                                                        sociated with the input format, 2u and 4n\theta  - 1 gmin in (3.26), are both reduced with
                                                                                                                                        multiword arithmetic by a factor of order up - 1 , giving (p + 1)up and 4nup - 1 \theta  - 1 gmin
                                                                                                                                        in (4.32). Therefore, the main conclusion of Theorem 4.1 is that the use of multiword
                                                                                                                                        arithmetic reduces in equal measure the rounding errors and the underflow errors as-
                                                                                                                                        sociated with the input format; hence we can expect the latter to remain dominated
                                                                                                                                        by the former even when p > 1.
                                                                                                                                             If the number of words p is large enough so that up \lesssim  U + \theta  - 2 Gmin , the errors
                                                                                                                                        associated with the accumulation format will dominate. However, for the same reasons
                                                                                                                                        as discussed in the previous section, we can expect the accumulation underflow errors
                                                                                                                                        of order \theta  - 2 Gmin to be insignificant and remain dominated by the rounding errors of
                                                                                                                                        order U .
                                                                                                                                             Overall, we conclude once more that underflows should not be a cause for concern,
