# BMM22: scope of the formalization

Sergey G. Bobkov, Arnaud Marsiglietti, James Melbourne, *Concentration functions and entropy bounds for discrete log-concave distributions*, Combinatorics, Probability and Computing 31 (2022), DOI 10.1017/S096354832100016X; arXiv:2007.11030v2.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1, symmetric upper bound; Proposition 7.3 | Central atom estimate for finite hypergeometric convolutions in KPZ Appendix A.3. | [`Critical2DKPZ.WalkTails.symmetricProfile_maxAtom_le_of_logConcave`](../../Critical2DKPZ/WalkTails/SymmetricMaxAtom.lean); [`Critical2DKPZ.WalkTails.symmetricHalfProfile_maxAtom_le`](../../Critical2DKPZ/WalkTails/SymmetricMaxAtom.lean) | Adapted to finite strictly positive interval-supported symmetric profiles, with integer or half-integer centre. The proved bound is M²(1 + 2 Σ k²p(k)) ≤ 487, with k + 1/2 in the half-centred case; the sum is one side of the symmetric second moment. The proved constant is 487; no sharp-constant theorem is claimed. See [BMM22-D1](../ERRATA-AND-DEVIATIONS.md#bmm22-d1). |
| Proposition 4.2; Corollary 4.3 | Closure under the finite convolutions producing the hypergeometric sum. | [`Critical2DKPZ.WalkTails.finiteConvolution_toeplitzTP2`](../../Critical2DKPZ/WalkTails/DiscreteConvolution.lean); [`Critical2DKPZ.WalkTails.squaredBinomialConvolution_logConcave`](../../Critical2DKPZ/WalkTails/LogConcavity.lean) | Adapted: finite convolution with explicit Toeplitz TP₂ hypotheses; adjacent log-concavity established for squared-binomial convolutions. Direct 2×2-minor proof, not an import of Hoggar’s theorem. See [BMM22-D2](../ERRATA-AND-DEVIATIONS.md#bmm22-d2). |
| Theorem 1.1, sharp lower and nonsymmetric upper bounds; Lemmas 7.1–7.2 in their general majorization form | Not required once a relaxed finite symmetric central bound suffices. | — | Outside the formalized scope as these full statements: the finite profile argument and Gaussian-tail combination supply the needed C/√n estimate without the sharp constants, arbitrary infinite supports, or the entropy branch. |

## Scope

Lean proves a relaxed finite symmetric log-concave maximum-atom estimate, including the half-integer repair, and the finite convolution machinery sufficient for the KPZ walk estimate.

The sharp symmetric branch of Theorem 1.1, the full two-sided theorem, and the general infinite-support and entropy results are not formalized verbatim.

## Source version

[Source version](https://arxiv.org/abs/2007.11030v2). PDF SHA-256: `d283cadfb929494ae1275ac1f99f03ab349a7906b67a388dbeba05d3a785f41e`.
