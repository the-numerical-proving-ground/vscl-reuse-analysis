Du Croz and Higham, “Stability of Methods for Matrix Inversion,” IMA Journal of Numerical Analysis 12(1), 1992, Section 2.1, Method 2 and complete Lemma 2.1 with proof (printed pp. 4–5).

The paper uses the standard floating-point model: a rounded arithmetic operation is the exact operation multiplied by 1+δ with |δ|≤u, ignoring underflow and overflow. Its constants c_n are of order n, and it retains terms through first order in u.

Method 2 computes the columns of the inverse of a nonsingular lower triangular matrix L in descending order. At column j it forms the reciprocal of L_jj, multiplies the already computed trailing inverse X_(j+1:n,j+1:n) by L_(j+1:n,j), and scales the resulting vector by the negative computed reciprocal.

Lemma 2.1 states that the complete computed inverse X has a componentwise left-residual bound of the form |XL−I| ≤ c_n u |X||L| + O(u²). Its proof partitions L and X into a leading scalar and a trailing (n−1)×(n−1) block. The diagonal reciprocal gives a scalar relative error δ with |δ|≤u. The newly computed lower column is the exact negative scaled trailing product plus the rounding error of the multiplication and matrix-vector product. Substitution into the first column of XL−I bounds it by the corresponding entries of |X||L|. The induction hypothesis supplies the same bound for the trailing block; the above-diagonal entries are zero.
