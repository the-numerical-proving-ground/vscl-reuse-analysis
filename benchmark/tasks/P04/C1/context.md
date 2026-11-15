      Let x' = (x(0), ■■■,x(N-l)),y'          = O(0), ■■■,y(N-l))          and fl(y) be the floating-
point representation of y and let

              Nina          = ((C   \z(k)\2)/ N) '     and      ||z||.    = max \z(k)\.

Then we have the following:
   Theorem l.Ify=Txis        computed by a floating-point fast Fourier transform of
order N = NiN2 • • • AV, then
   a. ||fl(y)- ylUs/llyllRMs< K(N,y)e + 0(e2)and
   b. ||fl(y)- ylMlylUs < VNK(N, y)e + 0(e2),where
                                          M
                            K(N, y) = 22 «W) + (.M - 1)(3 + 27)
                                      i-i
and
                             a(N,) = V2                      (IV, = 2),
                                    = 5                      (TV,= 4),

                                    = 2-s/Ni (Ni + y)        otherwise.

   (In the case of radix-2 or radix-A algorithms the important constants are

                    K(2M, y) = (3 + V2 + 27)M - (3 + 27),                    and

                    K(AM,y) = (8 + 2T)M - (3 + 2T).

These constants include the effect of separate multiplications by Dx (I = 1, 2, • • • ,
M - 1).)
    4. Roundoff Errors in Multidimensional Transformations.      The efficiency of the
fast Fourier transform has made it economically feasible to compute higher-dimen-
sional Fourier transformations in applications such as picture processing and x-ray
diffraction studies. In this section, bounds on roundoff errors in multidimensional
FFT's are derived.
   The problem is to bound roundoff errors in computing

      Y(h, t2, ■■■,tm)= 22 Z • • • 12 e(MiM + s2t2/N2+ • • ■ + smtjNm)

                                                       X(Si, s2, • • • , sm)

                                             (s„ U = 0, 1, • • • , Ni - 1; / = 1, 2, • • • , m).

764                                                     GEORGE U. RAMOS

Let
   E(h, t2, ■■• , tj               = fl(Y(h,           t2, ■■■ , tm)) -           Y(ti, t2, ■■■ , tm),

        [ñ(Y)~ y]RMS
                   = {(£                              S • • S \E(h, t2, ■■■ , fjfJM/v,                            • • • Nmy/2,
and
                      [ñ(Y)         -      y]MAx =               max          \E(ti,    t2, ■■■ , fj|.
                                                          li.l..¡m


Then we have
    Theorem 2. The RMS and maximum error due to roundoff in a multidimensional
fast Fourier transform are bounded by
    a. [ñ(Y) - y]RMS/TRM8á « J2T-1 Wi, 7) + 0(e2) and
    b. [ñ(Y) - y]MAx/TRMS g e(NN2 ■■■Nmf'2 £7-i Wu y) + 0(e2), where
 K(Nt, y) (I = 1,2, • • • , m) is the error constant given in Theorem 1.
    Proof. Let (4.1) be rewritten as the system of equations

•^I-lCSl»   ■ ■ ' » sl-l<   ti.         ■ ■ ■ > t„)

                     = }2 e(Sltt/N¡)Z,(si,                       ■■■ ,s,, ti +i, •■■ ,tm)                    (I = 1, 2, • • • , m)
                              si


with Z0 = Y and Zm = X, and describe this system of equations by the notation
                                        Z,_, = r,Z,                   (/ = 1, 2, ••• , m).
Then by adding and subtracting identical terms to the equation
               fl( Y) -        Y = ñ(Ti ñ(T2 • • • fl(TmX)                             ■))-    TiT2          ■■ TmX,
one gets
                  fl( Y)-           Y = ñ(Ti fl(Z,)) -                  Ti ñ(Zi)

                                              +   Ti ñ(T2 Ü(Z2)) -               TiT2ñ(Z2)
                                              +   TiT2 ñ(T3 fl(Z3)) -                  TiT2T3 ñ(Z3)

                                             + • • • + TiT2 ■■■ Tm-i ñ(TmX) -                            TiT2 ■■■ TmX.
Now take the RMS value of both sides and use the Cauchy-Schwarz inequality
to get

                [fl( Y) -           y]RMS g [fl(7\ fl(Zi))                -      Ti fl(Z1)]RMS

(4.2)                                             + [TiW(T2 fl(Z2)) -                   T2 fl(Z2)]]RMS

                                                  +    ••• + [TiT2 ■■■ Tm.i[f\(TmX)                      -     rmZ]]RMS.
Using Theorem 1, it is not difficult to prove that

(4.3)              LTKZ,-,)- Z^Ws/lZJbms                                 Ú eVNtKW,               y) + 0(e2).
Nor is it difficult to prove
(4-4)                                             [Z^Lms             = VN, [Z,]RM8.
Therefore, by (4.2), (4.3) and (4.4),

ROUNDOFF ERROR ANALYSISOF FAST FOURIER TRANSFORM                                765

 \ñ(Y)    -   y]RMS ú   e{(Ni)w2K(Ni,y)[ñ(Zi)]RK8

                           +   (NiN2)1/2K(N2,y)[ñ(Z2)]RMS


                           +   •••   +   (NiN2   •••   Nm)1/2K(Nm,y)[ñ(X)]aMa}        + 0(t2).

But by (4.3), [ñ(Zt)]RU8 = [Z,]RMS + 0(e) (I = 1, 2, • ■• , m -                  1), and by (4.4),
[Z,]RMS   = (N,+iNl+2    •■• Nm)1/2[X]RMa. Assuming          that   fl[(Z)]RMS   = [X]RliS,   or at
least [fl(X)]RMs = [I]ems + 0(e), the proof of part a is complete.
   Part b is proved by arguments identical to those used in the proof of part b of
Theorem 1.
