# Lemma 3.1 and Appendix A

The paper applies three sequences of plane rotations while deriving the LSMR residual estimate. It writes
\(\bar\beta_1=\alpha_1\beta_1\), \(\bar\alpha_1=\alpha_1\), \(\bar c_0=1\), and \(\bar s_0=0\).

The first rotation uses

\[
 \rho_i^2=\bar\alpha_i^2+\beta_{i+1}^2,
 \qquad c_i=\bar\alpha_i/\rho_i,
 \qquad s_i=\beta_{i+1}/\rho_i,
 \qquad \theta_{i+1}=s_i\alpha_{i+1},
 \qquad \bar\alpha_{i+1}=c_i\alpha_{i+1}.
\]

The next rotation uses

\[
 \bar\rho_i^2=(\bar c_{i-1}\rho_i)^2+\theta_{i+1}^2,
 \qquad \bar c_i=\bar c_{i-1}\rho_i/\bar\rho_i,
 \qquad \bar s_i=\theta_{i+1}/\bar\rho_i,
 \qquad \bar\theta_i=\bar s_{i-1}\rho_i.
\]

The final rotation, with \(\dot\rho_1=\bar\rho_1\), uses

\[
 \widetilde\rho_i^2=\dot\rho_i^2+\bar\theta_{i+1}^2,
 \qquad \widetilde c_i=\dot\rho_i/\widetilde\rho_i,
 \qquad \widetilde s_i=\bar\theta_{i+1}/\widetilde\rho_i,
 \qquad \widetilde\theta_{i+1}=\widetilde s_i\bar\rho_{i+1},
 \qquad \dot\rho_{i+1}=\widetilde c_i\bar\rho_{i+1}.
\]

Let \(s^{(i)}=s_1\cdots s_i\) and \(\bar s^{(i)}=\bar s_1\cdots\bar s_i\), with an empty product equal to one. Appendix A obtains

\[
 \widetilde\tau_1=\widetilde\rho_1^{-1}\bar c_1\bar\beta_1,
 \qquad \widetilde\tau_{i+1}=\widetilde\rho_{i+1}^{-1}\bigl((-1)^{i+2}\bar s^{(i)}\bar c_{i+1}\bar\beta_1-\widetilde\theta_{i+1}\widetilde\tau_i\bigr),
 \qquad \dot\beta_1=c_1\beta_1,
 \qquad \dot\beta_{i+1}=-\widetilde s_i\dot\beta_i+\widetilde c_i(-1)^i s^{(i)}c_{i+1}\beta_1,
 \qquad \widetilde\beta_i=\widetilde c_i\dot\beta_i+\widetilde s_i(-1)^i s^{(i)}c_{i+1}\beta_1.
\]

Lemma 3.1 states that the transformed right-hand-side components and the forward-substitution components agree: \(\widetilde\beta_i=\widetilde\tau_i\). In the iteration described by equations (3.2)--(3.3), this identifies the first \(k-1\) components.

For the base case, Appendix A expands \(\widetilde\beta_1\), substitutes the three rotations, and uses \(\bar\rho_1^2=\rho_1^2+\theta_2^2\) to obtain \(\widetilde\beta_1=\bar c_1\bar\beta_1/\widetilde\rho_1=\widetilde\tau_1\).

For the induction step, the paper first proves the product identity

\[
 s^{(i-1)}c_i\bar\rho_i^{-1}\bar c_{i-1}^{\,2}\rho_i^2\beta_1
   =\bar c_i\bar s^{(i-1)}\bar\beta_1.
 \tag{A.7}
\]

Combining the rotation identities also gives

\[
 \frac{c_i}{\bar\rho_i}\bigl(\bar c_{i-1}^{\,2}\rho_i^2-\widetilde s_{i-1}^{\,2}\bar\rho_i^2\bigr)
 =\dot\rho_i\widetilde c_{i-1}c_i
  -\bar\theta_{i+1}s_i c_{i+1}.
\]

Substituting the induction hypothesis into the forward-substitution recurrence, applying (A.7) and the last rotation identity, and then using the recurrence for \(\dot\beta_i\) reduces the result to the displayed formula for \(\widetilde\beta_i\). Hence \(\widetilde\tau_i=\widetilde\beta_i\) for every positive index.
