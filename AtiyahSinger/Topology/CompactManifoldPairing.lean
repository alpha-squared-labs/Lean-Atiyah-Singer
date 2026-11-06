/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing

/-!
# Ordinary top-degree evaluation on the original compact oriented manifold

Public module ID: M1641.

The inverse of the existing compact-support comparison sends an ordinary
class to its unique compact-support class. The existing LF integral then
evaluates it on the rational image of the same specified integral
homological orientation. Thus this is the ordinary fundamental-class
pairing, with no newly chosen generator, rational rescaling or orientation.

Sources: Hatcher, Algebraic Topology, section 3.3, pp.242--245; Atiyah--Singer
III, p.552, u[X] = epsilon(Du), and p.557, formula (2.13). The comparison
uses the actual support colimit and cap augmentation, not an unspecified
integration functional. Empty manifolds, disconnected manifolds, and both
local orientation signs in dimension zero are retained. The definition
uses the established compact-support comparison and integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- Evaluation of an ordinary top-degree class on the same normalized fundamental class. -/
def compactManifoldCohomologyIntegral (O : HomologicalOrientation n M) :
    singularCohomology ℚ M n →ₗ[ℚ] ℚ :=
  (compactSupportCohomologyIntegral O).comp
    (compactSupportCohomologyIso ℚ M n).inv.hom

end AtiyahSinger
