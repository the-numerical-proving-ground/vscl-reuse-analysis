3.2 LR matrix times LR matrix
Next we analyse the product of two LR matrices   A = XA YAT and 
                                                                 B = YB XBT , where XA and XB have
                                               
orthonormal columns. Note that we consider B of the form YB XB rather than XB YBT because of the
                                                                 T

representation (2.3) whose usefulness is made clear below.
Lemma 3.3 (LR matrix times LR matrix). Let A, B ∈ Rb×b and

                                    
                                    A = XA YAT ,      
                                                      B = YB XBT ,
                                                  
                                          b×r r×b           b×r r×b


where XA and XB have orthonormal columns and

                                   A − 
                                        A ⩽ εβA ,     B − 
                                                            B ⩽ εβB .

If the product C =   A
                       B is computed as C = (XA (YAT YB ))XBT or C = XA ((YAT YB )XBT ), where the
parentheses indicate the order in which the intermediate products are performed, then the computed

C satisfies

                                        
                                         C −B ⩽ γc 
                                            A        A
                                                         B,                                        (3.10)

where c = b + 2r3/2 , and therefore

                   
                    C − AB ⩽ γc AB + ε(1 + γc ) βA B + AβB + εβA βB .                      (3.11)

Proof. We consider the case where the product is computed as (
                                                              AYB )XBT = (XA (YAT YB ))XBT , the other
case being analogous. Let W = 
                              AYB ; by Lemma 3.2, the computed W satisfies

                    =
                   W  AYB + ΔW,         ΔW ⩽ γb+r3/2 
                                                        AYB  = γb+r3/2 
                                                                           A
                                                                              B.

960                                        N. J. HIGHAM AND T. MARY


         T ; the computed 
Let C = WX                 C satisfies
          B

                     BT + ΔC,
                 C = WX                         
                                     ΔC ⩽ γr WX                            
                                                    B  ⩽ γr3/2 (1 + γb+r3/2 )AB,

                   =
                    A
                     B + ΔWXBT + ΔC = 
                                      A
                                       B + F.




                                                                                                             Downloaded from https://academic.oup.com/imajna/article/42/2/951/6238550 by Lorna Rourke user on 05 August 2026
Bounding F ⩽ γc 
                   A
                      B, with c = b + 2r3/2 , proves (3.10). We then replace 
                                                                              A by A + EA and 
                                                                                              B by
B + EB to obtain

           
           C = AB + F + G,      F ⩽ γc AB + γc ε βA B + AβB + εβA βB ,
                               G = EA B + AEB + EA EB  ⩽ ε βA B + AβB + εβA βB ,

which yields (3.11).                                                                                   
