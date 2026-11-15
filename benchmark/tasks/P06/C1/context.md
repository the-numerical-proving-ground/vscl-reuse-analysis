4. Barycentric formula

          values f i ≡ 1 are obviously interpolated by pn (x) = 1, and hence (3.1) gives
The function
1 = (x) nj=0 w j /(x − x j ). Using this equation to eliminate (x) in (3.1) yields

                                              
                                              n
                                                    wj
                                                         fj
                                              j=0
                                                  x − xj
                                   pn (x) =                   ,                             (4.1)
                                               
                                               n
                                                     wj
                                               j=0
                                                   x − xj

which is called the ‘second (proper) form of the barycentric formula’ by Rutishauser
(1990).
   Since this formula is obtained by using a mathematical identity that does not
necessarily hold in floating point arithmetic, this second formula might be expected to
have different stability properties to the first.
   Working in the same way as in the proof of Theorem 3.2, we find that
                                       
                                       n
                                         w j 2n j
                                                      f j n + 3 j
                                    j=0
                                            x − xj
                            
                            pn (x) = n                                    1
                                           w j 2n j
                                                       n + 2 j
                                        j=0
                                             x − xj
                                       
                                       n
                                             wj
                                                  f j 3n + 4 j
                                       j=0
                                           x − xj
                                   =                                  ·
                                        
                                        n
                                              wj
                                                   3n + 2 j
                                        j=0
                                            x − xj

This result does not admit any useful interpretation in terms of backward error. But it does
lead readily to a forward error bound, which is stated in the next result. We note first that
the equality (2.2) can be rewritten
                                                 n          
                                                               
                                                      wj f j 
                                                     x − x 
                                                j=0          j
                              cond(x, n, f ) =  n             ·
                                                 w f 
                                                        j j 
                                                              
                                                 j=0 x − x j 

552                                        N . J . HIGHAM


T HEOREM 4.1 The computed      pn (x) from (4.1) satisfies
                                               n  w j           
                                                                   
             | pn (x) −  pn (x)|                      
                                                   j=0 x−x j   f j 
                                  ⩽ (3n + 4)u                    
                   | pn (x)|                    n        w        
                                                j=0 x−xj j f j 
                                                     n  w j 
                                                        j=0  x−x j 




                                                                                                Downloaded from https://academic.oup.com/imajna/article/24/4/547/687371 by Lorna Rourke user on 05 August 2026
                                        +(3n + 2)u                  + O(u 2 )
                                                      n       wj 
                                                      j=0 x−x j 
                                    = (3n + 4)u cond(x, n, f )
                                                    n  w j 
                                                       j=0  x−x j 
                                        +(3n + 2)u                + O(u 2 )          (4.2)
                                                     n       wj 
                                                     j=0 x−x j 
                                    = (3n + 4)u cond(x, n, f )
                                        +(3n + 2)u cond(x, n, 1) + O(u 2 ),             (4.3)
where the argument ‘1’ denotes the function with constant value 1. There exist rounding
errors such that this bound is attained to within a constant factor.
