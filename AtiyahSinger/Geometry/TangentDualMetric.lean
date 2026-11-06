/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentMusical
public import Mathlib.Analysis.InnerProductSpace.Dual

import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The inverse musical map for the original tangent metric

Public module ID: M1476.

The sharp map is the inverse Riesz map for the supplied smooth metric on
the original tangent fibers. Installing that metric through RiemannianBundle
retains their existing topology and linear operations. The identities below
relate this exact fiber map to the previously specified flatHomeomorph, so
the differential symbol and compact-support K transport use the same map.

Source: Spin Geometry II.3, p.94, and II.5, p.113. Smoothness is the standard
inverse-Gram-matrix argument in the original tangent and dual charts. The
statements include dimension zero and impose no compactness assumption.
The original inverse identities and smoothness are fully proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothTangentMetric

open Bundle
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (g : SmoothTangentMetric (n := n) (M := M))

/-- The original metric inverse sends a covector to its unique metric-dual tangent vector. -/
def sharp (x : M) : CotangentFiber (n := n) x →ₗ[ℝ]
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
  letI : RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  (InnerProductSpace.toDual ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).symm.toLinearEquiv.toLinearMap

/-- The supplied metric and its exact inverse are inverse in both original fibers. -/
theorem sharp_flat_inverse (x : M)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
    (ξ : CotangentFiber (n := n) x) :
    g.sharp x (g.inner x v) = v ∧ g.inner x (g.sharp x ξ) = ξ := by
  -- The native Riesz map has exactly g.inner as its forward pairing.
  let : RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := InnerProductSpace.toDual ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
  change e.symm (e v) = v ∧ e (e.symm ξ) = ξ
  exact ⟨e.symm_apply_apply v, e.apply_symm_apply ξ⟩

/-- The original global musical homeomorphism has precisely this sharp inverse. -/
theorem flatHomeomorph_symm_apply (x : M) (ξ : CotangentFiber (n := n) x) :
    g.flatHomeomorph.symm ⟨x, ξ⟩ = ⟨x, g.sharp x ξ⟩ := by
  -- Injectivity identifies the inverse of the specified global flat map.
  apply g.flatHomeomorph.injective
  rw [g.flatHomeomorph.apply_symm_apply]
  change (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) =
    ⟨x, g.inner x (g.sharp x ξ)⟩
  rw [(g.sharp_flat_inverse x (g.sharp x ξ) ξ).2]

/-- The same sharp map is smooth on the entire original cotangent bundle. -/
theorem contMDiff_sharp :
    ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).tangent ∞
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦
        (⟨z.proj, g.sharp z.proj z.snd⟩ :
          TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)) := by
  classical
  -- The Riesz maps use the supplied metric and retain each original tangent topology.
  let : RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e (x : M) : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x ≃L[ℝ]
      CotangentFiber (n := n) x :=
    (InnerProductSpace.toDual ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toContinuousLinearEquiv
  -- In the same native frames, the inverse Riesz map is the inverse coordinate operator.
  have hcoordinates (x : M) : ContMDiffAt
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, CotangentModel n →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun y ↦ ContinuousLinearMap.inCoordinates (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)
        x y x y (e y).symm.toContinuousLinearMap) x := by
    let a := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) x
    let b := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    let A (y : M) : EuclideanSpace ℝ (Fin n) →L[ℝ] CotangentModel n :=
      (b.continuousLinearMapAt ℝ y).comp ((e y).toContinuousLinearMap.comp (a.symmL ℝ y))
    let B (y : M) : CotangentModel n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (a.continuousLinearMapAt ℝ y).comp ((e y).symm.toContinuousLinearMap.comp (b.symmL ℝ y))
    have hAB (y : M) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
        (A y).comp (B y) = ContinuousLinearMap.id ℝ (CotangentModel n) ∧
          (B y).comp (A y) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      constructor
      · apply ContinuousLinearMap.ext
        intro v
        change b.continuousLinearMapAt ℝ y (e y (a.symmL ℝ y
          (a.continuousLinearMapAt ℝ y ((e y).symm (b.symmL ℝ y v))))) = v
        rw [a.symmL_continuousLinearMapAt (R := ℝ) ha, (e y).apply_symm_apply,
          b.continuousLinearMapAt_symmL hb]
      · apply ContinuousLinearMap.ext
        intro v
        change a.continuousLinearMapAt ℝ y ((e y).symm (b.symmL ℝ y
          (b.continuousLinearMapAt ℝ y (e y (a.symmL ℝ y v))))) = v
        rw [b.symmL_continuousLinearMapAt (R := ℝ) hb, (e y).symm_apply_apply,
          a.continuousLinearMapAt_symmL ha]
    have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt _ _ x
    have hbx : x ∈ b.baseSet := mem_baseSet_trivializationAt _ _ x
    have hA : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] CotangentModel n) ∞ A x :=
      (contMDiffAt_hom_bundle (fun y ↦ TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] CotangentModel n) y (g.inner y))).mp
        (g.contMDiff x) |>.2
    have hinvertible : (A x).IsInvertible :=
      ContinuousLinearMap.IsInvertible.of_inverse (hAB x hax hbx).1 (hAB x hax hbx).2
    have hinverse := (hinvertible.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp x hA
    change ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, CotangentModel n →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞ B x
    apply hinverse.congr_of_eventuallyEq
    filter_upwards [a.open_baseSet.mem_nhds hax, b.open_baseSet.mem_nhds hbx] with y ha hb
    exact (ContinuousLinearMap.inverse_eq (hAB y ha hb).1 (hAB y ha hb).2).symm
  -- Evaluate the smooth inverse coordinate operators on the original cotangent vector.
  intro z
  have hproj := (contMDiff_proj (F := CotangentModel n)
    (CotangentFiber (n := n) (M := M)) (IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (n := ∞)).contMDiffAt (x := z)
  exact ((hcoordinates z.proj).comp z hproj).clm_apply_of_inCoordinates
    contMDiffAt_id hproj

end AtiyahSinger.SmoothTangentMetric
