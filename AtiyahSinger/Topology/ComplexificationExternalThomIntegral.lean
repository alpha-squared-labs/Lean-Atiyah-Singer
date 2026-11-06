/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportExternalPullback
public import AtiyahSinger.Topology.ComplexificationThomProduct

/-!
# The inverse Thom integral of the supported external product

Public module ID: M1728.

The actual real and imaginary projection pair is assumed proper. Its inverse
image of the product zero sections is exactly the original complex zero section.
The representative pullback comparison therefore connects the genuine compact
external product with the same signed relative Thom product and original inverse.
Neither real nor imaginary projection is assumed proper on its own.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle

attribute [local instance] t2Space_fiberBundleTotal
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
  [T2Space X] [CompactSpace X]

set_option maxHeartbeats 600000 in
-- Both geometric orientations retain their original native total-space topologies.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse complex Thom integral of the original real external Thom product. -/
theorem complexificationCohomologyFiberIntegral_externalThom
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
    letI := hV.realNativeRiemannianBundle (2 * m) hr
    let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
    let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
    ∀ (e : ∀ x, F x ≃L[ℝ] E x × E x)
      (_he : ∀ x, (e x).toLinearEquiv = complexificationReIm (E x))
      (q₁ q₂ : C(TF, TE))
      (_hq₁ : ∀ x v, q₁ ⟨x, v⟩ = ⟨x, (e x v).1⟩)
      (_hq₂ : ∀ x v, q₂ ⟨x, v⟩ = ⟨x, (e x v).2⟩)
      (hp : IsProperMap (q₁.prodMk q₂)),
    ∀ (p q : ℕ) (a : singularCohomology ℚ X p) (b : singularCohomology ℚ X q),
    let τ := cohomologyThomClass ℚ (2 * m) E
      (geometricCohomologyOrientation (2 * m) E o ho).rationalization
    let πE := bundleProjection (2 * m) E
    let K := cohomologyZeroSectionSupport (2 * m) E
    compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
      (hV.complexCohomologyOrientation (2 * m) hr).rationalization (p + q)
      ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ TF ((p + 2 * m) + (q + 2 * m)) ≅
          compactSupportCohomology ℚ TF ((p + q) + 2 * (2 * m))).hom
        (compactSupportCohomologyProperPullback ℚ (q₁.prodMk q₂) hp
          ((p + 2 * m) + (q + 2 * m))
          (compactSupportCohomologyExternalRepresentative ℚ K K (p + 2 * m) (q + 2 * m)
            (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) p (2 * m)
              (singularCohomologyPullback ℚ πE p a) τ)
            (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) q (2 * m)
              (singularCohomologyPullback ℚ πE q b) τ)))) =
      (-1 : ℚ) ^ m • singularCohomologyCup ℚ X p q a b := by
  let F := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let := hV.realNativeFiberBundle (2 * m) hr
  let := hV.realNativeVectorBundle (2 * m) hr
  let := hV.realNativeRiemannianBundle (2 * m) hr
  dsimp only
  intro e he q₁ q₂ hq₁ hq₂ hp p q a b
  let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
  let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
  let K := cohomologyZeroSectionSupport (2 * m) E
  let W := cohomologyZeroSectionSupport (2 * (2 * m)) F
  let Q := q₁.prodMk q₂
  let A : Set TF := q₁ ⁻¹' bundleNonzero (2 * m) E
  let B : Set TF := q₂ ⁻¹' bundleNonzero (2 * m) E
  let N := bundleNonzero (2 * (2 * m)) F
  let τ := cohomologyThomClass ℚ (2 * m) E
    (geometricCohomologyOrientation (2 * m) E o ho).rationalization
  let πE := bundleProjection (2 * m) E
  let α := relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) p (2 * m)
    (singularCohomologyPullback ℚ πE p a) τ
  let β := relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) q (2 * m)
    (singularCohomologyPullback ℚ πE q b) τ
  -- The same ReIm equivalence identifies the compact inverse support, without changing fibers.
  have hW : (W : Set TF) = Q ⁻¹' ((K : Set TE) ×ˢ (K : Set TE)) := by
    ext z
    change z.snd = 0 ↔ (q₁ z).snd = 0 ∧ (q₂ z).snd = 0
    rw [hq₁ z.proj z.snd, hq₂ z.proj z.snd]
    constructor
    · intro hz
      simp only [hz, map_zero, Prod.fst_zero, Prod.snd_zero, and_self]
    · intro hz
      apply (e z.proj).injective
      exact (Prod.ext hz.1 hz.2).trans (map_zero (e z.proj)).symm
  have hA : IsOpen A := K.isCompact.isClosed.isOpen_compl.preimage q₁.continuous
  have hB : IsOpen B := K.isCompact.isClosed.isOpen_compl.preimage q₂.continuous
  have hN : Set.MapsTo (ContinuousMap.id TF) N (A ∪ B) := by
    intro z hz
    change z ∉ (W : Set TF) at hz
    rw [hW] at hz
    exact not_and_or.mp hz
  have hprod := complexificationCohomologyFiberIntegral_thomProduct E o ho hV hr
    e he q₁ q₂ hq₁ hq₂ hA hB hN p q a b
  have hpull := compactSupportCohomologyProperPullback_externalRepresentative ℚ Q hp
    K K W hW (p + 2 * m) (q + 2 * m) α β
  -- Move only the degree transport through the original zero-support colimit leg.
  have hcastLeg (i j : ℕ) (h : i = j) (z : relativeSingularCohomology ℚ N i) :
      (eqToIso (congrArg (compactSupportCohomology ℚ TF) h)).hom
        (compactSupportCohomologyClass ℚ TF W i z) =
      compactSupportCohomologyClass ℚ TF W j
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ N k)) h) z) := by
    subst j
    rfl
  let I := compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
    (hV.complexCohomologyOrientation (2 * m) hr).rationalization (p + q)
  let hd : (p + 2 * m) + (q + 2 * m) = (p + q) + 2 * (2 * m) := by omega
  have h := congrArg (fun z ↦ I ((eqToIso
    (congrArg (compactSupportCohomology ℚ TF) hd)).hom z)) hpull
  exact h.trans ((congrArg I (hcastLeg _ _ hd _)).trans hprod)

end AtiyahSinger
