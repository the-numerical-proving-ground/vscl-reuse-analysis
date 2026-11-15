Lemma 3.1 (LR matrix times vector). Let \(A \in \mathbb{R}^{b\times b}\),
\(X,Y \in \mathbb{R}^{b\times r}\), and \(v\in\mathbb{R}^b\), where \(X\)
has orthonormal columns and \(\widetilde A=XY^T\) is an LR approximation of
\(A\) satisfying \(\|A-\widetilde A\|\leq \varepsilon\beta\) for some
\(\beta>0\). If the matrix-vector product \(Av\) is computed as
\(z=X(Y^Tv)\), the computed \(\widehat z\) satisfies

\[
 \widehat z=(\widetilde A+\Delta\widetilde A)v,
 \qquad \|\Delta\widetilde A\|\leq \gamma_c\|\widetilde A\|,
 \qquad c=b+r^{3/2},                                                \tag{3.1}
\]

and therefore

\[
 \widehat z=(A+\Delta A)v,
 \qquad \|\Delta A\|\leq
 \gamma_c\|A\|+\varepsilon(1+\gamma_c)\beta.                      \tag{3.2}
\]

Proof. Let \(w=Y^Tv\). The computed \(\widehat w\) satisfies

\[
 \widehat w=(Y+\Delta Y)^Tv,
 \qquad \|\Delta Y\|\leq\gamma_b\|Y\|=\gamma_b\|\widetilde A\|. \tag{3.3}
\]

Let \(z=X\widehat w\). The computed \(\widehat z\) satisfies

\[
 \widehat z=(X+\Delta X)\widehat w,
 \qquad \|\Delta X\|\leq\gamma_r\|X\|=\gamma_r\sqrt r.           \tag{3.4}
\]

Here \(\|X\|=\sqrt r\) because \(X\) has orthonormal columns.
Combining (3.3) and (3.4) gives

\[
 \widehat z=(X+\Delta X)(Y+\Delta Y)^Tv
            =(\widetilde A+\Delta\widetilde A)v,
\]

with

\[
 \|\Delta\widetilde A\|
 \leq (\gamma_b+\gamma_r\sqrt r+\gamma_b\gamma_r\sqrt r)
       \|\widetilde A\|
 \leq \gamma_c\|\widetilde A\|,
\]

which proves (3.1). Bound (3.2) follows on replacing
\(\widetilde A\) by \(A+E\), where \(\|E\|\leq\varepsilon\beta\).
