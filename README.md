# The Critical 2D KPZ Process in Lean

[![Build and verify](https://github.com/scottnarmstrong/Critical2DKPZ/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/Critical2DKPZ/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/Critical2DKPZ/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/Critical2DKPZ/actions/workflows/comparators.yml)

A Lean 4 and Mathlib formalization of

> Quentin Berger, Francesco Caravenna, Jeremy Clark, Alexander Dunlap, Yu Gu, Ziyang Liu, Shuta Nakajima,
> Rongfeng Sun, Li-Cheng Tsai, Zuodi Xie and Nikos Zygouras, *The Critical 2D KPZ Process*,
> [arXiv:2610.31614](https://arxiv.org/abs/2610.31614).

The paper studies directed polymers on $\mathbb Z^2$ in a Gaussian environment at critical disorder. Their partition
functions converge to the critical 2D stochastic heat flow (SHF), and their centred logarithms converge to a random
distribution, the critical 2D KPZ process. The paper proves a comparison principle in the initial data and then shows
that, for flat initial data, this process is Gaussian at small scales (its averages at scale $\varepsilon$ divided by
$\sqrt{\log\log(1/\varepsilon)}$ converge in law to a centred Gaussian), has a radial covariance kernel behaving like
$\log\log(1/\lvert z\rvert)$ at the diagonal, is not a signed measure and is not Gaussian, is invariant under
translations and rotations, is covariant under scaling (with the parameter $\vartheta$ shifted), and that its pairing
with any nonnegative test function has a law of Ehrhard type, that is, the law of $h(G)$ for a standard Gaussian
$G$ and a finite nondecreasing convex function $h$.

The formalization proves all of these results, together with the results from other papers that their proofs use. The
libraries `Critical2DKPZ` and `Critical2DKPZStatements` contain no `sorry` and use no axiom beyond Lean's standard
`propext`, `Classical.choice` and `Quot.sound`.

## The main result

The model is the directed polymer on $\mathbb Z^2$: a simple random walk rewarded by an i.i.d. standard Gaussian
environment, at the inverse temperature $\beta_N$ fixed by $\sigma_N^2 R_N = 1+\vartheta/\log N$, where
$\sigma_N^2=e^{\beta_N^2}-1$, $R_N$ is the expected number of returns of the walk to the origin by time $2N$, and
$\vartheta\in\mathbb R$ is a fixed parameter. A macroscopic point $x\in\mathbb R^2$ is represented by the nearest site to
$\sqrt{N/2}\,x$ of the even sublattice $\lbrace z\in\mathbb Z^2:\ z_1+z_2\in2\mathbb Z\rbrace$, and a macroscopic time
$t\ge0$ by the even integer $2\lceil Nt/2\rceil$. For a measure $Z_{s,t}$ on $\mathbb R^2\times\mathbb R^2$ write
$Z_{s,t}(f,g)=\int f(x)g(y)\,Z_{s,t}(dx,dy)$, and let $g_\delta^{(x)}$ be the heat kernel of variance $\delta$ centred
at $x$.

**Theorem (Theorem A and Theorem 1.2 of the paper).** For every $\vartheta$ there is a critical 2D stochastic heat flow
$Z$: the joint limit in law of the rescaled point-to-point and point-to-plane partition functions. For every such $Z$
there is a random field $H$, measurable with respect to $Z$, such that for every time $t>0$ and every bounded continuous
initial condition $h_0$:

- $H_t(h_0)$ is almost surely a distribution in the local Sobolev space $H^{-a}_{\mathrm{loc}}(\mathbb R^2)$ for every
  $a>0$;
- it is the limit, as $\delta\downarrow0$, of the temporally regularized fields
  $x\mapsto\log Z_{0,t-\delta}(e^{h_0},g_\delta^{(x)})-\mathbb E\log Z_{0,t-\delta}(1,g_\delta^{(0)})$, in probability in
  $H^{-a}_{\mathrm{loc}}$, and in every $L^p$, $1\le p\lt\infty$, when tested against a smooth compactly supported
  function;
- the lattice fields $x\mapsto\log Z^{(N)}_t(e^{h_0},x)-\mathbb E\log Z^{(N)}_t(1,0)$, where
  $Z^{(N)}_t(e^{h_0},x)=\int e^{h_0(y)}Z^{(N)}_{0,t}(y,x)\,dy$ integrates the rescaled point-to-point partition function
  against the initial weight, converge in law to $H_t(h_0)$ in $H^{-a}_{\mathrm{loc}}$, jointly for finitely many times
  and initial conditions.

$H$ is the critical 2D KPZ process. The list of formalized statements has 22 entries: Theorem A and Theorem 1.2; the
paper's other main
results (the comparison principle and, for flat initial data, small-scale Gaussianity, the covariance kernel, the facts
that $H$ is neither a signed measure nor Gaussian, its symmetries, and the Ehrhard property of its tested laws); and
results, from the paper and
from the literature, on which their proofs rest. All 22 are stated, with their exact hypotheses and links to the Lean
statements, in [docs/main-results.md](docs/main-results.md).

## Results from other papers

The paper builds on a large literature: the construction and characterization of the critical SHF, moment formulas for
the two-dimensional stochastic heat equation, renewal theory for the planar random walk, Gaussian convexity and
Ehrhard's inequality, among others. To prove its theorems from first principles, we formalized the parts of these
papers that the argument uses. Each such result is proved in the form the argument needs, which is sometimes a special
case or an adaptation of the published statement. The [input-paper index](docs/inputs/README.md) lists the papers and
books involved and says, for each, which of its results are formalized and how.

## Scope

- **The model.** Everything is proved for the paper's model: an i.i.d. standard Gaussian environment, the simple random
  walk on $\mathbb Z^2$ and the paper's critical scaling at a fixed parameter $\vartheta$. The paper's extension of the
  convergence to deterministic $\vartheta_N\to\vartheta$ is not part of the formalized statements, and universality in
  the environment or the walk is not claimed.
- **Other papers.** Their results are formalized as far as the argument uses them, not in full; the input-paper index
  gives the details.
- **Modes of convergence.** The convergence statements are those of the paper: in law, in $H^{-a}_{\mathrm{loc}}$, jointly
  at finitely many times and initial conditions. Convergence as a process in time and almost sure continuity in time are
  not claimed.
- **Differences from the printed statements.** Where a Lean statement differs from the printed one, for instance by an
  added hypothesis that the printed statement needs, the difference is recorded in
  [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).
- **Review.** The authors of the paper have not reviewed this formalization.

## How to verify

Install [elan](https://github.com/leanprover/elan). The file [`lean-toolchain`](lean-toolchain) selects Lean
4.35.0-rc2 and [`lake-manifest.json`](lake-manifest.json) pins Mathlib; do not run `lake update`. From the repository
root:

```sh
lake exe cache get
lake build Critical2DKPZ Critical2DKPZStatements
python3 scripts/print_axioms
```

The first command downloads the compiled Mathlib. The second builds the library and the 22 statements. The third runs
`#print axioms` on each of the 22 theorems and checks that every one depends only on `propext`, `Classical.choice` and
`Quot.sound`, so that no proof relies on `sorry` or on an added axiom. A successful build alone does not show this,
since Lean compiles a theorem proved by `sorry` with only a warning.

Reading the statements against the paper is the part of the check that a computer cannot do. The
[paper-to-Lean correspondence](docs/correspondence.md) lists, for each numbered result of the paper, the Lean
declaration that proves it, the declaration that covers it, or a note that it is not formalized separately.

## Single-file restatement of the main theorem

[`Critical2DKPZAudit/Challenge.lean`](Critical2DKPZAudit/Challenge.lean) restates Theorem 1.2 in a single file that
imports only Mathlib and defines every object the statement uses: the planar simple random walk and the Gaussian
environment, the critical tuning $\beta_N$, the point-to-point and point-to-plane partition functions, the critical SHF,
the critical KPZ process and its regularized and lattice approximations, and the local negative Sobolev energies.
Its only `sorry` is the proof of the theorem.
[`Critical2DKPZAudit/Solution.lean`](Critical2DKPZAudit/Solution.lean) proves the same statement from this library,
and [comparator](https://github.com/leanprover/comparator) checks, with both the Lean kernel and the NanoDa kernel,
that the two statements and all 40 definitions agree and that the proof uses only the standard axioms:

```sh
lake build Critical2DKPZAudit
lake env lean Critical2DKPZAudit/AxiomsAudit.lean
scripts/verify_comparator.sh
```

The comparator script runs on Linux. It needs `landrun` and `nanoda_bin` on `PATH`, or located through
`COMPARATOR_LANDRUN` and `COMPARATOR_NANODA`; it builds pinned, toolchain-compatible copies of `comparator` and
`lean4export` itself, unless existing ones are supplied through `COMPARATOR_BIN` and `COMPARATOR_LEAN4EXPORT`. When
reading the Challenge, keep in mind:

- The hypothesis of the theorem is that $Z$ is a critical SHF in the sense of the Challenge. This class is not empty:
  the library proves Theorem A, the existence of such an SHF for every $\vartheta$, but that theorem is not part of the
  comparator check.
- The critical SHF is characterized by the joint finite-dimensional limits of the point-to-point and point-to-plane
  polymer pairings on their common disorder space; existence for this exact predicate is proved in the library. Its
  identification with the SHF constructed by Caravenna, Sun and Zygouras rests on the literature.
- Convergence in law is stated on the space of all distributions, with the topology generated by the local negative
  Sobolev energies; its finite-energy part is $H^{-a}_{\mathrm{loc}}$ with its usual topology. The limit lies almost
  surely in $H^{-a}_{\mathrm{loc}}$ (part of the theorem) and the lattice fields lie in it too (proved in the library),
  so this is convergence in law in $H^{-a}_{\mathrm{loc}}$; see [KPZ-D114](docs/ERRATA-AND-DEVIATIONS.md#kpz-d114).
- Both approximations are centred by a flat-data mean evaluated at the spatial point $0$: the regularized field
  subtracts $\mathbb E\log Z_{0,t-\delta}(1,g_\delta^{(0)})$ and the lattice field subtracts
  $\mathbb E\log Z^{(N)}_t(1,0)$. The paper's centring constants do not depend on the point, by translation invariance,
  and each is shared by all initial data.
- The statement covers times $t>0$ and bounded continuous initial data, and gives convergence in probability in
  $H^{-a}_{\mathrm{loc}}$ for each localizing test function and each threshold.

## Errata and deviations

Formalizing the paper and the papers it uses turned up errors in the printed texts. About half are typos; the others
are wrong constants or signs, missing hypotheses, restricted domains, false intermediate steps, and statements that are
false as printed (all of the latter in the input papers). None changes the conclusions of the paper's main results.
Where the proofs need an input that is wrong as printed, they use a proved correction, a restricted statement or a
different argument; errata in results that the proofs do not use come without a replacement theorem. The errata, and the
places where the Lean statements differ from the printed ones, are listed per source, with counts, in
[docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).

## Documentation

- [The 22 results](docs/main-results.md): each result proved here, with its hypotheses and a link to its Lean statement.
- [Paper-to-Lean correspondence](docs/correspondence.md): every numbered result of the paper and its Lean counterpart,
  or a note that it is not formalized separately.
- [Input papers](docs/inputs/README.md): which results of other papers are formalized, and how.
- [Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md): errors found in the papers, and differences between the
  printed and the formalized statements.
- [Exact statements](Critical2DKPZStatements/) and [definitions](Critical2DKPZ/Definitions/).

## How this formalization was made

The proofs were written by AI agents (GPT-6.1 Sol and GPT-6 Luna in Codex, Claude Opus 5.5 and Claude Sonnet 5.5 in
Claude Code) under the supervision of Scott Armstrong. Each completed main statement received a separate audit
(statement against the paper, hypotheses, axioms, and use of the intended results). The Lean kernel checks every proof.
See [formalization.yaml](formalization.yaml) for details.

## Author, citation and license

The Lean development is by **Scott Armstrong**, CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant
Institute School of Mathematics, Computing, and Data Science, New York University. Scott Armstrong was supported by the
European Research Council (ERC) under the European Union's Horizon Europe research and innovation programme, grant
agreement No. 101200828.

To cite this formalization, use [CITATION.cff](CITATION.cff), together with the paper it formalizes. The Lean code is
licensed under the Apache License 2.0; see [LICENSE](LICENSE).
