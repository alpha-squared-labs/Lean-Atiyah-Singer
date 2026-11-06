/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ComplexificationCohomologyOrientation
public import AtiyahSinger.Topology.CohomologyThomSum
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# The original Thom class under real complexification

Public module ID: M1738.

The real bundle has its given locally positive orientation and its original
metric topology. The complexified bundle has the original ReIm total topology
and any specified continuous Hermitian metric. The original ReIm fiber
comparison determines the whole relative Thom cup by normalized uniqueness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))
  (ho : IsLocallyCompatibleBundleOrientation (2 * m) E o)
  [T2Space X]

set_option maxHeartbeats 600000 in
-- Both geometric orientations retain their original native total-space topologies.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The real double Thom cup equals the signed original complexified Thom class. -/
theorem complexificationCohomologyThomClass
    (hV : letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (hr : ∀ x, Module.finrank ℂ (ℂ ⊗[ℝ] E x) = 2 * m) :
    let F := fun x ↦ ℂ ⊗[ℝ] E x
    letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    letI := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
    letI : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
    letI := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
    letI := hV.realNativeFiberBundle (2 * m) hr
    letI := hV.realNativeVectorBundle (2 * m) hr
    let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
    let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
    ∀ (e : ∀ x, F x ≃L[ℝ] E x × E x)
      (_he : ∀ x, (e x).toLinearEquiv = complexificationReIm (E x))
      (q₁ q₂ : C(TF, TE))
      (_hq₁ : ∀ x v, q₁ ⟨x, v⟩ = ⟨x, (e x v).1⟩)
      (_hq₂ : ∀ x v, q₂ ⟨x, v⟩ = ⟨x, (e x v).2⟩),
    let A : Set TF := q₁ ⁻¹' bundleNonzero (2 * m) E
    let B : Set TF := q₂ ⁻¹' bundleNonzero (2 * m) E
    let N := bundleNonzero (2 * (2 * m)) F
    ∀ (hA : IsOpen A) (hB : IsOpen B)
      (hN : Set.MapsTo (ContinuousMap.id TF) N (A ∪ B)),
      cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ N k))
        (show 2 * m + 2 * m = 2 * (2 * m) by omega))
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id TF) hN (2 * m + 2 * m)
          (relativeSingularCohomologyUnionCup ℚ A B hA hB (2 * m) (2 * m)
            (relativeSingularCohomologyPullback ℚ q₁ (fun _ hv ↦ hv) (2 * m)
              (cohomologyThomClass ℚ (2 * m) E
                (geometricCohomologyOrientation (2 * m) E o ho).rationalization))
            (relativeSingularCohomologyPullback ℚ q₂ (fun _ hv ↦ hv) (2 * m)
              (cohomologyThomClass ℚ (2 * m) E
                (geometricCohomologyOrientation (2 * m) E o ho).rationalization)))) =
      (-1 : ℚ) ^ m • cohomologyThomClass ℚ (2 * (2 * m)) F
        (hV.complexCohomologyOrientation (2 * m) hr).rationalization := by
  let F := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let := hV.realNativeFiberBundle (2 * m) hr
  let := hV.realNativeVectorBundle (2 * m) hr
  dsimp only
  intro e he q₁ q₂ hq₁ hq₂ hA hB hN
  let O := (geometricCohomologyOrientation (2 * m) E o ho).rationalization
  let OC := (hV.complexCohomologyOrientation (2 * m) hr).rationalization
  -- The previously computed fiber sign is the unit used in global Thom uniqueness.
  have hfiber (x : X) := complexificationCohomologyOrientation_fiberClass E o ho hV hr x
    (e x) (he x)
  have h := cohomologyThomClass_prod_of_fiberClass ℚ (2 * m) (2 * m) (2 * (2 * m))
    (by omega) E E F O O OC ((-1 : ℚˣ) ^ m) q₁ q₂ e hq₁ hq₂ (by
      intro x
      dsimp only
      intro hP
      have hx := hfiber x hP
      simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
        ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one] using hx)
    hA hB hN
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

end AtiyahSinger
