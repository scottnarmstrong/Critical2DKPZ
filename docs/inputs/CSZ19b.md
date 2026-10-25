# CSZ19b — On the moments of the (2+1)-dimensional directed polymer and stochastic heat equation in the critical window

**Citation:** Francesco Caravenna, Rongfeng Sun and Nikos Zygouras, *On the moments of the (2+1)-dimensional directed polymer and stochastic heat equation in the critical window*, Communications in Mathematical Physics **372** (2019), 385–440. DOI: 10.1007/s00220-019-03527-z. **arXiv:** 1808.03586v2.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Equations (3.2)–(3.3) | The first-collision covariance decomposition for two probability starting profiles, then heat-distributed starts (the KPZ paper). | [`Critical2DKPZ.Polymer.probability_profile_firstCollision_absolute`](../../Critical2DKPZ/Polymer/ProbabilityProfiles.lean); [`Critical2DKPZ.Polymer.smoothedP2Plane_firstCollision`](../../Critical2DKPZ/Polymer/SmoothedCovariance.lean) | **Adapted:** Lean proves the polarized first-selected-chaos-point identity actually used by KPZ, for two deterministic probability profiles and heat profiles, in Gaussian disorder and the period-two SRW on `Z²`. It holds for every real coupling and finite horizon, with `s ≤ n`; no critical-window limit is assumed. Lean includes terminal disorder on `(s,n]`, whereas CSZ19b's partition function excludes both endpoint slices. The printed equations are averaged variances, not literally this two-profile identity. See [CSZ19b-D1](../ERRATA-AND-DEVIATIONS.md#csz19b-d1), [CSZ19b-D2](../ERRATA-AND-DEVIATIONS.md#csz19b-d2), [CSZ19b-D3](../ERRATA-AND-DEVIATIONS.md#csz19b-d3). |
| Theorem 1.9 and the polymer third-moment theorem | Historical discussion of critical-window moments (the KPZ paper). | — | **Outside the formalized scope** as CSZ19b's third-moment theorem for the mollified SHE or its printed polymer limit. This citation is background. The chosen formal KPZ argument obtains polymer moment inputs through the DHP26 adaptation and CSZ25 moment bounds, rather than invoking this continuum-SHE theorem. |

## Scope

Lean proves the KPZ adaptation of CSZ19b's finite chaos decomposition: the first-collision covariance identity for arbitrary probability starting profiles and its heat-profile specialization in the Gaussian planar SRW model.

The finite chaos identity is adapted to the KPZ conventions rather than formalized verbatim as Equations (3.2)–(3.3). The source’s general-disorder continuum variance and third-moment limit theorems and its mollified-SHE results are not formalized here.

## Source version

[Source version](https://arxiv.org/abs/1808.03586v2). PDF SHA-256: `6f7621782df63ac27613f3165dceb3c3e3813e5fc3b9f7ad4e42b4fdd9efe589`.
