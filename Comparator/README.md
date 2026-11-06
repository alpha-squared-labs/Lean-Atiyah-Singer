# Atiyah–Singer Comparator

This harness is configured to check the T01–T04 theorem interfaces using the
Comparator bundled with the project's Lean toolchain. It uses the production
definitions and spells out the seven propositions in `Statements.lean`.
Standardness of the objects is established by the project's mathematical source
review; this harness does not reconstruct those objects using only mathlib.

| Node | Targets in `AtiyahSinger.ComparatorTargets` | Scope |
| --- | --- | --- |
| T01 | `t01_atlas`, `t01_native` | The original elliptic PDO of real order and its intrinsic full-symbol K-class |
| T02 | `t02_atlas`, `t02_native` | The tangent-bundle cohomological formula, without orienting the base |
| T03 | `t03_atlas`, `t03_native` | The base-space formula with the same given integral orientation |
| T04 | `t04` | The original twisted positive Dirac operator in every native even dimension |

The atlas versions allow locally varying finite rank. The native versions retain
their fixed ranks and original positive density. T04 retains the supplied spin
input, metric, coefficient bundle and smooth coefficient connection. Its native
zero-dimensional endpoint uses the positive empty-frame orientation; independent
signed or stabilized zero-dimensional models are separate statements.

Sources: Lawson and Michelsohn, *Spin Geometry* (SG), Princeton University Press,
1989: III.13.2, p.244; the two III.13.8 formulas (13.18) and (13.24), pp.254–256;
III.13.10, formula (13.26), pp.256–257. The native zero-dimensional continuation
is the separately proved project extension documented in production module M2303.

## Two separate environments

`Challenge.lean` intentionally admits exactly the seven expected targets.
`Solution.lean` imports the independent propositions and applies the actual
production theorems. Neither the production library nor Solution imports Challenge.
These environments must be compiled separately because they declare the same
target names with different proof values.

`definition_names` is empty. It is the list of permitted definition holes,
not a list of all definitions used by the theorems. All reachable definitions
remain subject to comparison. The configuration permits only `propext`,
`Classical.choice` and `Quot.sound`, and requires both Lean's kernel and Nanoda.
Changing a definition, weakening a statement or admitting a solution proof does
not count as a successful check against the frozen challenge.

## Run

Run the build, preparation, and Comparator stages sequentially.

Choose a new output directory and run the following commands from the repository root:

```sh
python3 Comparator/prepare.py --output .lake/comparator/run01
lake env lake comparator \
  --config .lake/comparator/run01/config.json \
  --challenge-from-export .lake/comparator/run01/Challenge.ndjson \
  --solution-from-export .lake/comparator/run01/Solution.ndjson
```

Preparation compiles only the three harness modules with the actual project
options and imports the compiled production dependencies from `.lake`. It
exports the seven roots plus the bundled comparator's required kernel primitives.
The output directory contains source/configuration snapshots and actual commands.
It must not already exist.

The export options avoid a full production rebuild. Comparator itself does not
check that supplied exports came from the current source tree: retain the
preparation receipt, its source snapshots and the independent source/type review.
`PREPARED_NOT_YET_COMPARATOR_ACCEPTED` is not a kernel verdict.

Execution keeps Comparator's Bubblewrap sandbox enabled. `lake env` also exposes
the bundled `nanoda_bin` on PATH. A passing run has exit code zero and all three
messages: `Lean default kernel accepts the solution`,
`nanoda kernel accepts the solution`, and `Your solution is okay!`.

The mathematical source register does not inventory compiler products. The
comparator declarations are validation interfaces, not additional mathematical
DAG nodes or replacements for T01–T04.

## Verification status

The complete seven-target Comparator run finished with exit code 0.
Both Lean's default kernel and Nanoda accepted the solution,
and Comparator printed `Your solution is okay!`.

| Validation stage | Elapsed time | Sampled peak aggregate RSS |
| --- | --- | --- |
| Preparation and export | Approximately 10 minutes | 16.85 GB |
| Complete seven-target validation | Approximately 13 hours 43 minutes | 142.19 GB |

Allow memory headroom above the measured checking peak for other
processes and variation between runs.
