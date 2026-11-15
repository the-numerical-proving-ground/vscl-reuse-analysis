3. Basic algorithms and error analysis
Algorithm 3.1 gives a naive implementation of (1.1) and (1.2).
                                                                            n
Algorithm 3.1      Given x ∈ Rn this algorithm computes f (x) = log            i=1 e
                                                                                    xi   and the gradient
g(x) = ∇f (x).
       1   s=0
       2   for i = 1 : n
       3      wi = exp(xi )
       4      s = s + wi
       5   end
       6   f = log(s)
       7   for i = 1 : n
       8      gi = wi /s
       9   end


    What can be said about the accuracy of this algorithm when it is implemented in floating-point
arithmetic? To answer this question we carry out a rounding error analysis. Throughout this section we
assume that there is no overflow or underflow.

ACCURATELY COMPUTING THE LOG-SUM-EXP AND SOFTMAX FUNCTIONS                                           2317

    First we consider the error in evaluating the sum of positive terms

                                                       
                                                       n             
                                                                     n
                                                  s=         exi ≡          wi .
                                                       i=1            i=1




                                                                                                                             Downloaded from https://academic.oup.com/imajna/article/41/4/2311/5893596 by Lorna Rourke user on 05 August 2026
Evaluating wi = exi yields a computed result satisfying

                                                    wi = exi (1 + δ1 ),
                                                                                                                   (3.1)

where, as noted in Section 2, we can expect the relative error from the exponential evaluation to satisfy
|δ1 | ⩽ u. Therefore
                                                     wi − wi | ⩽ wi u.
                                                    |
Write the (exact) sum of computed quantities as

                                                              
                                                              n
                                                       
                                                       s=           
                                                                    wi .
                                                              i=1

The rounding error analysis in Higham (1993) and Higham (2002, sec. 4.2) shows that the computed
sums satisfies6
                                                             
                                                             n−1
                                            |
                                             s −
                                                s| ⩽ u             |ti | + O(u2 ),
                                                             i=1
             i+1
where ti =      j=1 
                    wj , so that, since 
                                        wi ≥ 0,

                                                                     
                                                                     n
                         |
                          s −
                             s| ⩽ u(n − 1)(
                                           w1 + 
                                                w2 ) + u                   (n + 1 − i)
                                                                                      wi + O(u2 ).
                                                                     i=3


Here and throughout this paper, the O(u2 ) term is innocuous in that it becomes significant only when the
corresponding first-order term is already so large that it provides no useful information; see Blanchard
et al. (2020, sec. 2.1.2) for details of these terms for summation. Writing s −
                                                                               s = s −s +
                                                                                          s −s we obtain
                                            
                                            n
                                |s −
                                    s| ⩽           wi − wi | + |
                                                  |            s −
                                                                   s|
                                            i=1

                                             
                                             n               
                                                             n
                                        ⩽u          wi + u     (n + 1 − i)
                                                                          wi + O(u2 )
                                              i=1            i=1

                                            
                                            n
                                        =         (n + 2 − i)wi + O(u2 ),                                           (3.2)
                                            i=1


   6
     We note that more refined error bounds for summation are available under additional assumptions on the floating-point
arithmetic (Rump, 2012; Lange & Rump, 2019).

2318                             P. BLANCHARD, D. J. HIGHAM AND N. J. HIGHAM


since 
      wi = wi + O(u). Hence

                               
                               s = s + Δs,       |Δs| ⩽ (n + 1)us + O(u2 ).                           (3.3)


    Turning to the evaluation of the softmax function g from its definition (1.2), by (3.1) we have

        g_hat_j = exp(x_j)(1 + δ_1) / s_hat · (1 + δ_2),     |δ_2| ≤ u,

    where δ_2 accounts for the division, and so by (3.3),

        g_hat_j = exp(x_j) / [s(1 + η)] · (1 + δ_1)(1 + δ_2),
        |η| ≤ (n + 1)u + O(u²).

    Therefore

        g_hat_j = g_j(1 + τ_j),     |τ_j| ≤ (n + 3)u + O(u²).

    This bound guarantees a relative error of order at most nu in every component of g. We weaken the
    bound into a normwise bound for the next theorem.

    Theorem 3.3 (Basic softmax algorithm). In the absence of overflow and underflow the computed
    softmax g_hat from Algorithm 3.1 satisfies

        ‖g − g_hat‖_∞ / ‖g‖_∞ ≤ (n + 3)u + O(u²).           (3.6)
