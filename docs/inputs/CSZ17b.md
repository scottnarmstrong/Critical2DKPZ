# CSZ17b — Universality in marginally relevant disordered systems

**Citation:** Francesco Caravenna, Rongfeng Sun and Nikos Zygouras, *Universality in marginally relevant disordered systems*, Annals of Applied Probability **27** (2017), no. 5, 3050–3112. DOI: 10.1214/17-AAP1276. **arXiv:** 1510.06287.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.8; Theorem 1.15 | Historical phase-transition and log-normal/zero-limit discussion for intermediate disorder (the KPZ paper). | — | **Outside the formalized scope:** these fixed-`β̂` universality and regularized-SHE limits are background, not inputs to the KPZ proof. The formalization studies the finer critical window directly. |
| Theorem 1.13; Theorem 1.17 | The grouped literature citation for Edwards–Wilkinson Gaussian fluctuations below criticality (the KPZ paper). | — | **Outside the formalized scope:** the subcritical field limit is not invoked in the critical KPZ construction or convergence proof.  |
| Theorem 1.12, and the exponential-scale heuristics in §2.2 | Historical origin of decompositions on exponential time scales (the KPZ paper). The citation does not invoke this multi-scale correlation theorem. | — | The source multi-scale correlation theorem is not formalized. The critical KPZ proof establishes its own block estimates and does not use the source’s monotonicity argument. |

## Scope

CSZ17b supplies historical and methodological context. Its universality, subcritical field-limit, multi-scale correlation and general polymer/pinning theorems are outside the scope of this formalization; the selected proof does not use its monotonicity argument.

## Source version

[Source version](https://arxiv.org/abs/1510.06287). PDF SHA-256: `e1552f8ad70e49c432179bf66e5e163decb3df33f35cf6c455f7f39408134d9a`.
