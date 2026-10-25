# Ivan16: scope of the formalization

Paata Ivanisvili, *A boundary value problem and the Ehrhard inequality*, Studia Mathematica 246 (2019), DOI 10.4064/sm170730-22-1; arXiv:1605.04840. The pinned source title omits the initial “A”.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| Theorem 1 (mth1); essential-supremum inequality | Alternative argument to Ehrhard, not selected. | — | Outside the formalized scope: no general H differential-inequality/essential-supremum equivalence; the NP16 sufficient interpolation argument avoids it. |
| Ehrhard application in Section 3, discussion | Only the convex-set consequence is needed by KPZ. | [`Critical2DKPZ.Ehrhard.gaussian_set_ehrhard`](../../Critical2DKPZ/Ehrhard/GaussianSetInequality.lean) | Special case of the Ehrhard consequence: convex A,B, weights 1-t,t with 0≤t≤1, arbitrary finite-dimensional Gaussian. Proved through NP16, not Ivanisvili’s boundary-value problem. Not the general measurable-set weighted Borell inequality. |
| Theorem 2 (theorem2); characterization of eligible measures | Not used. | — | Outside the formalized scope: no necessity characterization of measures or general boundary-value PDE solution is needed. |

## Scope

The convex-set Ehrhard consequence relevant to KPZ is proved by a different argument; Ivanisvili’s general boundary-value theorem is not formalized.

The boundary-value problem, essential-supremum criterion, necessity direction and characterization of eligible measures are not formalized here.

## Source version

[Source version](https://arxiv.org/abs/1605.04840). PDF SHA-256: `e52e5cb8c9832c482415cb8dfef9016af8cff35b8e1693e76e49e018dd7a0e37`.
