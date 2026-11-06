/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantActionTransport
public import AtiyahSinger.Topology.EquivariantOpenExtension

/-!
# Open extension under equality of equivariant actions

Public module ID: M1792.

The original controlled open extension commutes with transport of both base
actions. This complements proper pullback transport and retains the same
support quotient and the same open map when identifying native cotangent lifts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Topology

variable {G X Y : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- Open extension commutes with transport of the actual source and target actions. -/
theorem kActionTransport_openPushforward (A B : MulAction G X) (C D : MulAction G Y)
    (hA : letI := A; ContinuousSMul G X) (hB : letI := B; ContinuousSMul G X)
    (hC : letI := C; ContinuousSMul G Y) (hD : letI := D; ContinuousSMul G Y)
    (hX : A = B) (hY : C = D) (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heqA : letI := A; letI := C; ∀ (g : G) (x : X), f (g • x) = g • f x)
    (heqB : letI := B; letI := D; ∀ (g : G) (x : X), f (g • x) = g • f x) :
    (kActionTransport C D hC hD hY).comp
      (letI := A; letI := hA; letI := C; letI := hC;
        equivariantSupportTripleKZeroOpenPushforward f hf heqA) =
      (letI := B; letI := hB; letI := D; letI := hD;
        equivariantSupportTripleKZeroOpenPushforward f hf heqB).comp
          (kActionTransport A B hA hB hX) := by
  cases hX
  cases hY
  rfl

end AtiyahSinger.ComplexBundle
