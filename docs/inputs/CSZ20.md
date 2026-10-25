# CSZ20 — The two-dimensional KPZ equation in the entire subcritical regime

**Citation:** Francesco Caravenna, Rongfeng Sun and Nikos Zygouras, *The two-dimensional KPZ equation in the entire subcritical regime*, Annals of Probability **48** (2020), no. 3, 1086–1127. DOI: 10.1214/19-AOP1383. **arXiv:** 1812.03911v3.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1.1; model review in §1.2 | Background on subcritical Edwards–Wilkinson fluctuations and regularization conventions (the KPZ paper). | — | **Outside the formalized scope:** the fixed subcritical range `0 < β̂ < 1` is not the critical window of the target theorem. These citations supply background, and the formal critical construction does not invoke the subcritical limit theorem. |
| Proposition 2.2; local-window decomposition in §2.1 | Methodological precedent for localization (the KPZ paper), a heuristic analogy, and acknowledgment of the local/remainder decomposition. | — | The source localization estimate has subcritical tuning and its own time window, spatial window and normalization. The critical KPZ local estimate instead uses Gaussian covariance, variance-defect and replica-Green bounds; global fluctuations are handled by block factorization. |

## Scope

The cited CSZ20 subcritical convergence and localization results are methodological context for the KPZ proof and are not formalized here.

The source’s Edwards–Wilkinson theorem and subcritical Proposition 2.2 are not formalized here. The critical KPZ local estimate is a different theorem.

## Source version

[Source version](https://arxiv.org/abs/1812.03911v3). PDF SHA-256: `1494d6430e486e5ae1e93ae46d57eb3ff9276f32be417530cc78999a6ef29294`.
