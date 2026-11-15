# Higham and Kim (2001), Theorem 2.1 and equation (2.1)

For the quadratic matrix polynomial Q(z) = z²A + zB + C, assume there are p distinct eigenvalues with n ≤ p ≤ 2n. The corresponding eigenvectors satisfy the Haar condition: every selection of n of them is linearly independent.

Theorem 2.1 states that there are at least (p choose n) different right solvents of AX² + BX + C = 0. They are obtained by selecting n eigenpairs (μᵢ,wᵢ), forming W with columns wᵢ, and taking X = W diag(μᵢ) W⁻¹ as in equation (2.1).

The paper's proof uses the selected eigenpair equations to get A W diag(μᵢ)² + B W diag(μᵢ) + C W = 0; postmultiplication by W⁻¹ gives the solvent equation. The selections yield different solvents because their eigenvalue sets differ.
