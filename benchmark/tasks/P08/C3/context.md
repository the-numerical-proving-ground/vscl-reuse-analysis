Theorem 4.4 (BLR triangular system). Let
\(\widetilde T\in\mathbb{R}^{n\times n}\) be a triangular BLR matrix
partitioned into \(p^2\) LR blocks
\(\widetilde T_{ij}\in\mathbb{R}^{b\times b}\), and let
\(v\in\mathbb{R}^n\). If the solution of
\(\widetilde T x=v\) is computed by solving

\[
 T_{ii}x_i=v_i-\sum_{j=1}^{i-1}\widetilde T_{ij}x_j
\]

for each block \(x_i=x((i-1)b+1:ib)\), then the computed
\(\widehat x\) satisfies

\[
 (\widetilde T+\Delta\widetilde T)\widehat x=v+\Delta v,
 \qquad
 \|\Delta\widetilde T\|\leq\gamma_c\|\widetilde T\|,
 \qquad
 \|\Delta v\|\leq\gamma_p\|v\|,                                  \tag{4.21}
\]

where \(c=b+r^{3/2}+p\).

Proof. Let \(w_i^{(j)}=\widetilde T_{ij}\widehat x_j\), where
\(\widehat x_j\) is the \(j\)-th block row of the computed solution from
the previous \(i-1\) steps. By Lemma 3.1, the computed
\(\widehat w_i^{(j)}\) satisfies

\[
 \widehat w_i^{(j)}=(\widetilde T_{ij}+F_{ij})\widehat x_j,
 \qquad \|F_{ij}\|\leq\gamma_d\|\widetilde T_{ij}\|,
 \qquad d=b+r^{3/2}.
\]

Let \(w_i=v_i-\sum_{j=1}^{i-1}w_i^{(j)}\). The computed
\(\widehat w_i\) satisfies

\[
 \widehat w_i=v_i\circ(e+\Delta e_i)
 -\sum_{j=1}^{i-1}\widehat w_i^{(j)}\circ(e+\Delta e_j),
 \qquad |\Delta e_j|\leq\gamma_p e,
\]

where \(e=[1,\ldots,1]^T\). By Lemma 2.2, the computed solution
\(\widehat x_i\) of \(T_{ii}x_i=\widehat w_i\) satisfies

\[
 (T_{ii}+F_{ii})\widehat x_i=\widehat w_i,
 \qquad \|F_{ii}\|\leq\gamma_b\|T_{ii}\|.
\]

Therefore, since \(\widetilde T_{ii}=T_{ii}\),

\[
 \sum_{j=1}^{i}(\widetilde T_{ij}+\Delta\widetilde T_{ij})
   \widehat x_j
 =v_i\circ(e+\Delta e_i),                                         \tag{4.22}
\]

where
\(\Delta\widetilde T_{ij}=\Theta_j\circ\widetilde T_{ij}
 +F_{ij}\circ(J+\Theta_j)\), and hence
\(\|\Delta\widetilde T_{ij}\|
 \leq\gamma_{d+p+O(u)}\|\widetilde T_{ij}\|\).
Gathering (4.22) over all block rows gives
\((\widetilde T+\Delta\widetilde T)\widehat x=v+\Delta v\), with
\(\|\Delta v\|\leq\gamma_p\|v\|\), and

\[
 \|\Delta\widetilde T\|
 \leq\gamma_{d+p+O(u)}
 \left(\sum_{i=1}^p\sum_{j=1}^i
       \|\widetilde T_{ij}\|^2\right)^{1/2}
 \leq\gamma_{d+p}\|\widetilde T\|+O(u^2),
\]

as required.
