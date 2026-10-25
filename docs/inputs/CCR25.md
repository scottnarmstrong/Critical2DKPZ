# CCR25: scope of the formalization

Francesco Caravenna, Francesca Cottini and Maurizia Rossi, *Quasi-critical fluctuations for 2D directed polymers*, Annals of Applied Probability 35 (2025), no. 4, 2604–2643; arXiv:2307.02453v3.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 4.5; Theorem 4.8 | Full-support collision-word expansion underlying CSZ25 Theorem 5.7. | [`Critical2DKPZ.MomentBounds.wordRunsBound_four`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundFour.lean); [`Critical2DKPZ.MomentBounds.wordRunsBound_six`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundSix.lean) | Specialized to finite nonnegative initial profiles, terminal profile 1, orders h = 4 and 6, planar simple random walk and Gaussian disorder. These results prove the collision-word upper estimate, rather than the full general two-test moment-expansion theorem. The flat-terminal horizon shift accounts for the endpoint-disorder convention. See [CCR25-D2](../ERRATA-AND-DEVIATIONS.md#ccr25-d2), [CCR25-D3](../ERRATA-AND-DEVIATIONS.md#ccr25-d3). |
| Theorem 4.11 | Bound finite operator words by boundary norms and interacting/free operator bounds. | [`Critical2DKPZ.MomentBounds.ccr25_finite_word_operator_bound`](../../Critical2DKPZ/MomentBounds/CCR25WordCounting.lean) | Special case, proved conditionally on its explicit partition-moment, boundary-norm and free/interacting operator bounds. Finite configuration cutoff; h arbitrary in this algebraic helper. It is not a proof that those operator assumptions hold for every source environment. |
| Propositions 4.23–4.24 | Analytic closure of the h=4,6 moment estimate. | [`Critical2DKPZ.MomentBounds.ccrMomentBound_four_of_wordRuns`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundFour.lean); [`Critical2DKPZ.MomentBounds.ccrMomentBound_six`](../../Critical2DKPZ/MomentBounds/CCR25MomentBoundSix.lean) | The combined fourth- and sixth-moment application is proved for the Gaussian polymer with terminal profile 1. The fourth-moment helper’s WordRunsBound 4 hypothesis is supplied by wordRunsBound_four. Constants depend on h; the individual source propositions are not asserted verbatim. See [CCR25-D4](../ERRATA-AND-DEVIATIONS.md#ccr25-d4), [CCR25-D5](../ERRATA-AND-DEVIATIONS.md#ccr25-d5), [CCR25-D6](../ERRATA-AND-DEVIATIONS.md#ccr25-d6). |
| Theorems 1.1–1.2 | Background quasi-critical Edwards–Wilkinson limits. | — | Outside the formalized scope: the KPZ proof needs the moment/operator estimates, not these quasi-critical CLTs. |

## Scope

The CCR25 collision-word/operator method is implemented for the Gaussian planar terminal-profile-one fourth and sixth moment bounds, but neither its full general-environment operator theorem nor its quasi-critical CLTs may be claimed formalized.

## Source version

[Source version](https://arxiv.org/abs/2307.02453v3). PDF SHA-256: `9aab2173be6d6d8a036dce3bc33f1eb08e9883cec89b647e37f384263c8792df`.
