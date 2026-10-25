# CSZ26: what is formalized

**Citation.** F. Caravenna, R. Sun, and N. Zygouras, “The critical 2d stochastic heat flow and related models,” lecture notes, arXiv:2412.10311v3 (25 May 2026).

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Centred disorder and finite-product identity | KPZ uses centered Gaussian disorder and the identity `exp(H·1_A) = 1 + (exp(H)-1)·1_A` to expand the partition function. | [`Critical2DKPZ.Polymer.integral_xi`](../../Critical2DKPZ/Polymer/Chaos.lean); [`Critical2DKPZ.Polymer.integral_xi_sq`](../../Critical2DKPZ/Polymer/Chaos.lean) | **Special case:** the Lean disorder is standard Gaussian, so the centered factor is `exp(βω−β²/2)−1` with variance `exp(β²)−1`; CSZ26 allows general disorder with a finite log-MGF. |
| Point-to-point chaos expansion | KPZ cites CSZ26 §2 for the finite expansion of its point-to-point partition function (the KPZ paper). | [`Critical2DKPZ.Polymer.pathWeight_chaos`](../../Critical2DKPZ/Polymer/Chaos.lean); [`Critical2DKPZ.Polymer.pointToPoint_chaos`](../../Critical2DKPZ/Polymer/Chaos.lean) | **Adapted:** Lean proves the exact finite subset expansion for the KPZ period-2 walk and its terminal-disorder convention. CSZ26 excludes disorder at both endpoint times (`n_r < L`); KPZ includes the terminal layer (`n_k ≤ n`), with the terminal endpoint enforced by an indicator (the `q₀` pinning in kernel notation). The source’s aperiodic covariance-identity walk is also specialized to the KPZ walk. See [CSZ26-D1](../ERRATA-AND-DEVIATIONS.md#csz26-d1), [CSZ26-D2](../ERRATA-AND-DEVIATIONS.md#csz26-d2). |
| Point-to-plane expansion | Background identity for the same finite product expansion; the KPZ proof’s cited application is the point-to-point version above. | [`Critical2DKPZ.Polymer.pointToPlane_chaos`](../../Critical2DKPZ/Polymer/Chaos.lean) | **Adapted:** finite subset expansion for the KPZ endpoint convention and walk; the source has noise only at times `1,…,N−1`, while the target convention includes the terminal layer. |
| Section 2 subcritical moment transition and later SHF construction | Background asymptotic results, distinct from the finite point-to-point identity used by KPZ. | — | **Outside the formalized scope:** the KPZ use is limited to the finite chaos algebra; no CSZ26 asymptotic transition or SHF construction theorem is imported as a Lean result. |

## Scope

Lean proves the finite polynomial-chaos expansions for the KPZ polymer’s Gaussian disorder and exact period-2 endpoint convention.

The source’s general-walk asymptotic theorems are not formalized here. No identification with the SHF constructed in those notes is asserted.

## Source version

[Source version](https://arxiv.org/abs/2412.10311v3). PDF SHA-256: `5922d7f49028e00777919d52493a896c2f5fd019a67fef0a893d2568238246a1`.
