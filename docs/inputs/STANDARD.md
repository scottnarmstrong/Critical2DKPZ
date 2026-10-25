# STANDARD: scope of the formalization

G. F. Lawler and V. Limic, *Random Walk: A Modern Introduction*, Cambridge University Press (2010), DOI 10.1017/CBO9780511750854 (LL10); W. Hebisch and L. Saloff-Coste, *Gaussian estimates for Markov chains and random walks on groups*, Annals of Probability 21 (1993), 673–709, DOI 10.1214/aop/1176989263 (HS93); M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis, Self-Adjointness*, Academic Press (1975) (RS75); A. Ehrhard, *Symétrisation dans l’espace de Gauss*, Mathematica Scandinavica 53 (1983), DOI 10.7146/math.scand.a-12035 (E83). No arXiv IDs for these cited originals.

The table distinguishes specializations and adaptations from the full source statements. Each linked Lean result has the hypotheses stated in its declaration.

| Paper result | Use in the KPZ proof | Lean result | Scope |
|---|---|---|---|
| LL10 Theorem 2.3.5, equation (2.23); compare Theorem 2.3.11 | Additive planar local CLT; heat-kernel approximations in KPZ and input moment papers. | [`Critical2DKPZ.srwKernel_localCLT`](../../Critical2DKPZ/RandomWalk/Estimates.lean) | For planar nearest-neighbour simple symmetric walk at positive integer times and reachable parity, the additive local CLT has uniform error C/n² against 2g_(n/2). This is not the general-walk relative moderate-deviation expansion. See [LL10-D1](../ERRATA-AND-DEVIATIONS.md#ll10-d1). |
| LL10 Propositions 2.1.2 and 2.4.6; HS93 Theorem 5.1, equation (13) | Gaussian upper bound for the planar walk. | [`Critical2DKPZ.srwKernel_gaussianBound`](../../Critical2DKPZ/RandomWalk/Estimates.lean) | Special case: n≥1 and all z∈ℤ², q_n(z)≤C/n exp(-c∥z∥²/n); proof uses the ported simple-walk estimates, not a formalization of arbitrary-walk maximal tails or all polynomial-growth groups. |
| HS93 Theorem 5.1, equation (14) | Same-parity displacement estimate in KPZ Appendix A.3. | [`Critical2DKPZ.WalkTails.srwKernel_sameParity_sq_diff_le`](../../Critical2DKPZ/WalkTails/SameParityGradient.lean) | For planar simple walk and same-parity z,z′, the squared difference is bounded by C‖z − z′‖²/n³ times the two Gaussian tails. The direct planar proof replaces the source generating-neighbourhood first-difference estimate on groups. See [HS93-D1](../ERRATA-AND-DEVIATIONS.md#hs93-d1). |
| RS75 Theorem IX.10 | Positive-type covariance kernel admits a positive spectral measure in KPZ Section 8. | [`Critical2DKPZ.Spectral.exists_spectralMeasure_of_positiveType`](../../Critical2DKPZ/Spectral/BochnerSchwartzTestPairing.lean) | Special case: real even kernels on Plane=ℝ², locally L², with an explicit polynomial bound on integrals of absolute values over balls and nonnegative compact-test quadratic forms; conclusion is locally finite positive spectral measure with polynomial growth, covariance pairing and symmetry inheritance. Not arbitrary distributions in arbitrary dimension; the book deduces temperedness from positive type. Angular-frequency normalization is explicit. See [RS75-D1](../ERRATA-AND-DEVIATIONS.md#rs75-d1). |
| E83 convex-set Ehrhard inequality; FMP25 Theorem 2.1 | Ehrhard inequality, used in Gaussian convexity and Ehrhard-law closure. | [`Critical2DKPZ.Ehrhard.gaussian_set_ehrhard`](../../Critical2DKPZ/Ehrhard/GaussianSetInequality.lean) | Adapted: finite-threshold CDF formulation for convex sets and all finite-dimensional Gaussian laws, including singular covariance and outer-measure sets; proved via NP16 rather than original symmetrization. This is an attribution to the inequality, not a claim about E83’s entire development. |

## Scope

Lean proves the planar simple-walk local CLT, Gaussian and same-parity difference estimates, a planar locally-L² positive-kernel spectral representation, and the finite-dimensional convex-set Ehrhard inequality needed by KPZ.

The general Lawler–Limic random-walk theory, Hebisch–Saloff-Coste group theorem, full distributional Bochner–Schwartz equivalence and Ehrhard’s original symmetrization theory are not formalized here.

## Source version

The sources are Lawler and Limic, *Random Walk: A Modern Introduction* (2010), DOI 10.1017/CBO9780511750854; Hebisch and Saloff-Coste, *Gaussian estimates for Markov chains and random walks on groups* (1993), DOI 10.1214/aop/1176989263; and Reed and Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis, Self-Adjointness* (1975). The checksums below identify the PDF copies used. LL10 and HS93 were read by PDF text extraction; RS75 printed p.14 was checked visually.

- **LL10:** Lawler and Limic (2010), DOI 10.1017/CBO9780511750854; author’s prepublication PDF SHA-256: `cb10ab9e665913f5041fd12511c2492c41d3e4bbebcf2d6ba7162c78acfbd9ea`.
- **HS93:** Hebisch and Saloff-Coste (1993), DOI 10.1214/aop/1176989263; author-hosted PDF SHA-256: `6a2483bb4b1bf765848cf5cad2061063b12ad661d4fd249ef42df3046be86d59`.
- **RS75:** Reed and Simon (1975), *Methods of Modern Mathematical Physics II*; scanned original PDF SHA-256: `860c253c1801841fc10ff3fccde9db647924ad70ad92e91dab9f5bb4eedda405`.
- **E83:** Ehrhard, *Symétrisation dans l’espace de Gauss* (1983), DOI 10.7146/math.scand.a-12035. The original was not available for this review, so no original-source checksum is claimed. The formulation and proof were checked through FMP25 and NP16.
