# Lean formalization of the Atiyah–Singer index theorem

This project formalizes the classical Atiyah–Singer index theorem and its cohomological and
twisted spin Dirac formulations in Lean 4, using mathlib and a library of supporting results.
The main proof follows the embedding and K-theory approach in Lawson and Michelsohn's
*Spin Geometry*, with supplementary arguments from the references below.

The repository contains the production library in `AtiyahSinger/`, its public entry
`AtiyahSinger.lean`, and the independent Comparator harness in `Comparator/`.
The current toolchain is Lean v4.35.0 with its bundled Lake and mathlib v4.35.0.
The complete production build has passed. The full seven-target Comparator run completed
successfully, with acceptance by both Lean's default kernel and Nanoda.

## No mathematical novelty

This is a formalization of established mathematics. No new mathematical theorem is claimed.

## AI usage and human responsibility

AI assistance was used for literature analysis, dependency refinement, Lean statements and
proof development, debugging, and review support. Human maintainers take responsibility for
the mathematical scope, assumptions, interpretation of references, code, documentation,
and release decisions.

Kernel checking verifies proof terms against the encoded statements and their dependencies.
Human reviewers remain responsible for establishing that those statements and definitions
faithfully represent the intended mathematics.

## Main results

Let $`X`$ be a compact Hausdorff second-countable smooth manifold without boundary,
with $`n=\dim X`$, and let $`P`$ be an elliptic complex pseudodifferential operator of
real order between finite-rank smooth complex bundles. Write $`\mathrm{ind}_a(P)`$,
also denoted $`\mathrm{ind}\,P`$, for its analytic index on smooth sections. Let
$`u=[\sigma_{\mathrm{full}}(P)]\in K_c^0(T^*X)`$ be its intrinsic full-symbol class,
and let $`u_T\in K_c^0(TX)`$ be the class transported by the chosen metric identification.
The cohomological pairings below use rational coefficients and evaluate the appropriate
top-degree components.

**T01 — Analytic and topological indices.** For arbitrary real operator order,

$$
\mathrm{ind}_a(P) = \mathrm{ind}_t(u).
$$

The differential-operator version is also provided.

**T02 — Cohomological formula on the tangent bundle.** With $`\pi:TX\to X`$,

$$
\mathrm{ind}\\,P = (-1)^n \left\langle
  \mathrm{ch}(u_T) \smile \pi^* \widehat{A}(TX)^2,
  [TX]_{\mathrm{lf}}
\right\rangle.
$$

The pairing uses compactly supported cohomology and locally finite homology. The tangent
total space has its canonical interleaved complex orientation; the base need not be orientable.

**T03 — Oriented-base cohomological formula.** For a given integral orientation $`O`$,

$$
\mathrm{ind}\\,P = (-1)^{n(n+1)/2} \left\langle
  \pi_{!} \mathrm{ch}(u_T) \smile \widehat{A}(TX)^2,
  [X]_O
\right\rangle.
$$

The same orientation determines the fundamental class and the inverse Thom map $`\pi_!`$.

**T04 — Twisted spin Dirac index.** On a compact Riemannian spin manifold of dimension
$`2m`$, for a smooth finite-rank complex coefficient bundle $`W`$ and any smooth complex
connection on $`W`$,

$$
\mathrm{ind}\\,D_W^+ = \left\langle
  \mathrm{ch}(W) \smile \widehat{A}(TX), [X]
\right\rangle.
$$

Here $`[X]`$ uses the supplied spin orientation. The dimension-zero case uses the
positive empty-frame orientation and identifies $`D_W^+`$ with the zero map
$`\Gamma^\infty(W)\to0`$.

T01–T03 have both locally varying finite-rank atlas presentations and native fixed-rank
bundle presentations. The native versions retain the supplied smooth positive density.
The conventions, model comparisons, and project supplements are specified in the technical report.

For example, T01 can be applied to an elliptic operator presented by smooth bundle
atlases `A` and `B`. After building the library, the following Lean example gives
the required manifold and bundle assumptions explicitly:

```lean
import AtiyahSinger.Analysis.FullSymbolIndexTheorem

open AtiyahSinger Bundle
open scoped Manifold ContDiff

universe u v w a b

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 30 in
example {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    {E : X → Type v} {F : X → Type w}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)]
    (A : SmoothComplexBundleAtlas.{a, u, v} (n := n) E)
    (B : SmoothComplexBundleAtlas.{b, u, w} (n := n) F)
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m) (hP : P.IsElliptic) :
    P.toLinearMap.index = cotangentTopologicalIndex n X (P.fullSymbolKClass hP) := by
  exact P.index_eq_cotangentTopologicalIndex_fullSymbol hP
```

Here `P.toLinearMap.index` is the analytic index on smooth sections, and
`P.fullSymbolKClass hP` is the compactly supported K-class of its full symbol.

## Mathematical coverage and reuse

| Area | Supporting interfaces |
| --- | --- |
| Functional and elliptic analysis | Fredholm operators, kernel–cokernel comparisons, real-order Sobolev spaces, Fourier estimates, pseudodifferential calculus, parametrices, and elliptic regularity |
| Differential geometry | Smooth complex bundles, densities, metrics, connections, principal and associated bundles, and tubular neighborhoods |
| K-theory | Relative and compactly supported complex K-theory in degree zero, products, Bott periodicity, Thom isomorphisms, and tangent-bundle pushforwards for proper smooth embeddings |
| Algebraic topology | Relative and compactly supported singular cohomology, locally finite singular homology, orientations, Thom–Gysin comparisons, and characteristic classes |
| Clifford and spin geometry | Clifford modules, half-spinor bundles, twisted Dirac operators, and their symbol classes |
| Representation theory and equivariant constructions | Representation rings, equivariant K-classes, representation-valued Fredholm indices, and associated sphere bundles |

These supporting definitions and theorems can support further formalizations beyond the
index theorem. We aim to contribute suitable results to mathlib, subject to human review
of their mathematical statements and proofs, interfaces, and code style.

The [public dependency catalog](dependencies/dependencies.public.json) identifies 14 specific mathlib analysis interfaces and three
adapted bundle compactness interfaces from the Poincaré Conjecture project, in addition to
module-level library dependencies. The latter concern fiber norms and compact disk and sphere
bundles.

## Build

Install Lean through [elan](https://github.com/leanprover/elan). The toolchain and dependency
lock pin Lean v4.35.0 and mathlib v4.35.0. From the repository root, run:

```sh
lake exe cache get
lake build
```

The default `AtiyahSinger` library target covers every retained production module,
including modules outside the public entry's import closure. Comparator environments
are compiled separately.

All 2,370 production modules compiled successfully; `lake build` exited with code 0.
The recorded run reached 16 concurrent Lean compiler processes and took approximately
5 hours 39 minutes, with a sampled peak aggregate resident set size (RSS) of 37.08 GB
across build processes. Lower build concurrency may reduce aggregate memory use.

## Comparator

The harness is configured to check seven independently written propositions: atlas and
native versions of T01–T03, and the uniform native even-dimensional T04. Separate Challenge
and Solution environments use the reviewed production definitions; Solution applies the
production proofs. The configuration permits no definition holes and only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. It compares the statements and reachable
definitions and replays the solution with both Lean's kernel and Nanoda.

The [harness README](Comparator/README.md) describes the target interfaces and the
separate Challenge and Solution environments.

Use Linux with Python 3.11 or newer, Bubblewrap (`bwrap`) with namespace creation permitted,
Git, `env`, and `which`. Build the production imports first. The selected
toolchain supplies Comparator, the exporters, and the kernel executables.

Run the build, preparation, and Comparator stages sequentially.

From the repository root, choose an output directory that does not exist:

```sh
python3 Comparator/prepare.py --output .lake/comparator/run01
lake env lake comparator \
  --config .lake/comparator/run01/config.json \
  --challenge-from-export .lake/comparator/run01/Challenge.ndjson \
  --solution-from-export .lake/comparator/run01/Solution.ndjson
```

Preparation compiles the three harness modules, reuses built production imports, and saves
source and configuration snapshots with the exports. Keep Bubblewrap enabled. Preparation
alone is not a passing verdict. A successful run must exit with code zero and print all of:

```text
Lean default kernel accepts the solution
nanoda kernel accepts the solution
Your solution is okay!
```

The complete seven-target run exited with code 0 and printed all three acceptance messages.
Checking took approximately 13 hours 43 minutes, with a sampled peak aggregate RSS of 142.19 GB.
Allow memory headroom above the measured checking peak for other processes and variation between runs.

Retain the preparation records and source/type review: supplied exports do not independently
establish their provenance from the current source files. Correspondence between production
objects and textbook mathematics remains a matter of mathematical source review.

## Main references

- **SG:** H. B. Lawson, Jr., and M.-L. Michelsohn. *Spin Geometry*.
  Princeton Mathematical Series, vol. 38. Princeton University Press, Princeton, NJ, 1989.
  [DOI](https://doi.org/10.1515/9781400883912).
- **TA:** M. E. Taylor. *Pseudodifferential Operators*. Princeton Mathematical Series,
  vol. 34. Princeton University Press, Princeton, NJ, 1981.
  [DOI](https://doi.org/10.1515/9781400886104).
- **KA:** M. Karoubi. *K-Theory: An Introduction*. Grundlehren der mathematischen
  Wissenschaften, vol. 226. Springer-Verlag, Berlin, 1978.
  [DOI](https://doi.org/10.1007/978-3-540-79890-3).
- **MS:** J. W. Milnor and J. D. Stasheff. *Characteristic Classes*.
  Annals of Mathematics Studies, vol. 76. Princeton University Press, Princeton, NJ, 1974.
  [DOI](https://doi.org/10.1515/9781400881826).
- **HU:** D. Husemoller. *Fibre Bundles*. 3rd ed. Graduate Texts in Mathematics, vol. 20.
  Springer-Verlag, New York, 1994.
  [DOI](https://doi.org/10.1007/978-1-4757-2261-1).
- **ASI:** M. F. Atiyah and I. M. Singer. “The Index of Elliptic Operators: I.”
  *Annals of Mathematics*, Second Series, **87**(3) (1968), 484–530.
  [DOI](https://doi.org/10.2307/1970715).
- **ASIII:** M. F. Atiyah and I. M. Singer. “The Index of Elliptic Operators: III.”
  *Annals of Mathematics*, Second Series, **87**(3) (1968), 546–604.
  [DOI](https://doi.org/10.2307/1970717).

The formalization uses [mathlib4](https://github.com/leanprover-community/mathlib4)
and adapts bundle compactness results from the
[Poincaré Conjecture project](https://github.com/frenzymath/Poincare-Conjecture).

## Technical report

| Item | Location |
| --- | --- |
| Technical report | [docs/technical_report.md](docs/technical_report.md) |

## License

The project is released under the [Apache License 2.0](LICENSE). Reused material retains
its source attribution and applicable license notices.
