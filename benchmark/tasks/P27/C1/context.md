The paper defines the phi-functions by the convergent series

\[
  \phi_\ell(z)=\sum_{k=0}^{\infty}\frac{z^k}{(k+\ell)!},
  \qquad \ell\geq 0,
\]

with \(\phi_0(z)=e^z\). Let

\[
  A\in\mathbb C^{n\times n},\qquad
  W=[w_1,\ldots,w_p]\in\mathbb C^{n\times p},\qquad
  \widetilde A=
  \begin{bmatrix}A&W\\0&J\end{bmatrix},
\]

where \(J\in\mathbb C^{p\times p}\) has ones on its first
superdiagonal and zeros elsewhere.

Theorem 2.1 states that, for \(X=\phi_\ell(\tau\widetilde A)\),
\(\tau\in\mathbb C\), and \(j=1,\ldots,p\),

\[
  X(1:n,n+j)=
  \sum_{k=1}^{j}\tau^k\phi_{\ell+k}(\tau A)w_{j-k+1}.
  \tag{2.7}
\]

For the proof, the paper first establishes

\[
  \widetilde A^k=
  \begin{bmatrix}A^k&M_k\\0&J^k\end{bmatrix},
  \qquad
  M_k=A^{k-1}W+M_{k-1}J,
\]

with \(M_1=W\) and \(M_0=0\). Since multiplication by a column of
\(J\) shifts the columns of \(W\) and of earlier powers of \(J\),
the \(j\)-th column satisfies

\[
  M_k(:,j)=\sum_{r=1}^{\min(k,j)}A^{k-r}w_{j-r+1}.
\]

Substituting this block-power formula into the defining series for
\(\phi_\ell(\tau\widetilde A)\), taking the \(j\)-th column of
the upper-right block, and reindexing the convergent sums gives

\[
  \sum_{r=1}^{j}\tau^r
    \left(\sum_{q=0}^{\infty}
      \frac{(\tau A)^q}{(q+\ell+r)!}\right)w_{j-r+1},
\]

which is equation (2.7).
