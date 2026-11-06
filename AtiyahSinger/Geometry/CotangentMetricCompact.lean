/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Reuse.Poincare.CompactDisk

/-!
# Compact disks of the prescribed cotangent metric

Public module ID: M1151.

Over a compact Hausdorff base, every closed metric disk is compact in the
original cotangent total space. The specified metric supplies the Riemannian
bundle structure only within the proof; the statement retains the native
cotangent topology and places no positivity restriction on the radius.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Closed disks for the specified smooth cotangent metric are compact over a compact
Hausdorff base. -/
theorem SmoothCotangentMetric.isCompact_sublevel
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) :
    IsCompact {z : CotangentTotalSpace (n := n) (M := M) | g.length z.proj z.snd ≤ R} := by
  let W := CotangentFiber (n := n) (M := M)
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : RiemannianBundle W := ⟨g.toRiemannianMetric⟩
  let : ∀ x : M, NormedAddCommGroup (W x) := fun x ↦ inferInstance
  let : ∀ x : M, InnerProductSpace ℝ (W x) := fun x ↦ inferInstance
  let : IsContinuousRiemannianBundle (CotangentModel n) W :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hcompact := Poincare.VectorBundle.isCompact_disk_over
    (F := CotangentModel n) (E := W) (K := Set.univ) isCompact_univ R
  have hnorm (z : CotangentTotalSpace (n := n) (M := M)) :
      ‖z.snd‖ = g.length z.proj z.snd := norm_eq_sqrt_real_inner z.snd
  simpa only [Set.mem_univ, true_and, hnorm] using hcompact

end AtiyahSinger
