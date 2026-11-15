Section 3. Superblocked dot product. Figure 3.1(a) gives the t-level superblock
algorithm: it accumulates products at the lowest of t temporary levels and, after
every block of N_b terms, carries a partial sum into the next level. The same
blocking factor N_b is used at each level, with N_b = N^(1/t). The paper assumes
this is an integer.

Proposition 3.1. For a t-temporary superblock summation, equal blocking factors
N^(1/t) minimize the worst-case error counter. The counter is

    t (N^(1/t) - 1),

and the associated summation error bound uses gamma at that counter. The proof
inducts on t. At the next level it adds N_b - 1 for the lowest block to the
counter for the remaining t levels on N/N_b partial sums. Minimizing that sum
gives N_b = N^(1/(t+1)), hence the same block size at all levels.

Proposition 3.2. The t-temporary superblock dot-product computation satisfies

    |s_n - s_hat_n| <= gamma_(t(N^(1/t)-1)+1) |x|^T |y|.       (3.2)

Proof. Compared with superblock summation, the dot product has one additional
factor (1 + delta) from each multiplication. Adding one to the summation error
counter in Proposition 3.1 gives (3.2).
