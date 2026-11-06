/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationThomIntegral
public import AtiyahSinger.Topology.RelativeUnionCupCoefficient

/-!
# Multiplication under the complexification Thom inverse

Public module ID: M1740.

Two classes represented using the original real Thom class are pulled back
along the actual ReIm projections and multiplied in relative cohomology.
The middle-factor sign disappears because the real rank is even. The
specified complex metric and its original compact-base inverse then give
the signed cup product of the two original base coefficients.
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
  [T2Space X] [CompactSpace X]

set_option maxHeartbeats 600000 in
-- Both geometric orientations retain their original native total-space topologies.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Integrating the original two Thom representatives gives the signed base cup product. -/
theorem complexificationCohomologyFiberIntegral_thomProduct
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
      (_hq₂ : ∀ x v, q₂ ⟨x, v⟩ = ⟨x, (e x v).2⟩),
    let A : Set TF := q₁ ⁻¹' bundleNonzero (2 * m) E
    let B : Set TF := q₂ ⁻¹' bundleNonzero (2 * m) E
    let N := bundleNonzero (2 * (2 * m)) F
    ∀ (hA : IsOpen A) (hB : IsOpen B)
      (hN : Set.MapsTo (ContinuousMap.id TF) N (A ∪ B))
      (p q : ℕ) (a : singularCohomology ℚ X p) (b : singularCohomology ℚ X q),
    let τ := cohomologyThomClass ℚ (2 * m) E
      (geometricCohomologyOrientation (2 * m) E o ho).rationalization
    let πE := bundleProjection (2 * m) E
    compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
      (hV.complexCohomologyOrientation (2 * m) hr).rationalization (p + q)
      (compactSupportCohomologyClass ℚ TF (cohomologyZeroSectionSupport (2 * (2 * m)) F)
        ((p + q) + 2 * (2 * m))
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ N k))
          (show (p + 2 * m) + (q + 2 * m) = (p + q) + 2 * (2 * m) by omega))
          (relativeSingularCohomologyPullback ℚ (ContinuousMap.id TF) hN
            ((p + 2 * m) + (q + 2 * m))
            (relativeSingularCohomologyUnionCup ℚ A B hA hB (p + 2 * m) (q + 2 * m)
              (relativeSingularCohomologyPullback ℚ q₁ (fun _ hv ↦ hv) (p + 2 * m)
                (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) p (2 * m)
                  (singularCohomologyPullback ℚ πE p a) τ))
              (relativeSingularCohomologyPullback ℚ q₂ (fun _ hv ↦ hv) (q + 2 * m)
                (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) q (2 * m)
                  (singularCohomologyPullback ℚ πE q b) τ)))))) =
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
  intro e he q₁ q₂ hq₁ hq₂ hA hB hN p q a b
  let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
  let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
  let A : Set TF := q₁ ⁻¹' bundleNonzero (2 * m) E
  let B : Set TF := q₂ ⁻¹' bundleNonzero (2 * m) E
  let N := bundleNonzero (2 * (2 * m)) F
  let πE := bundleProjection (2 * m) E
  let πF := bundleProjection (2 * (2 * m)) F
  let τ := cohomologyThomClass ℚ (2 * m) E
    (geometricCohomologyOrientation (2 * m) E o ho).rationalization
  let u := relativeSingularCohomologyPullback ℚ q₁ (fun _ hv ↦ hv) (2 * m) τ
  let v := relativeSingularCohomologyPullback ℚ q₂ (fun _ hv ↦ hv) (2 * m) τ
  let ac := singularCohomologyPullback ℚ πF p a
  let bc := singularCohomologyPullback ℚ πF q b
  -- Both geometric projections have exactly the same base map as the original complex bundle.
  have hπ₁ : πE.comp q₁ = πF := by
    ext z
    exact congrArg TotalSpace.proj (hq₁ z.proj z.snd)
  have hπ₂ : πE.comp q₂ = πF := by
    ext z
    exact congrArg TotalSpace.proj (hq₂ z.proj z.snd)
  have hcoeff (f : C(TF, TE)) (hf : πE.comp f = πF) (k : ℕ)
      (c : singularCohomology ℚ X k) :
      singularCohomologyPullback ℚ f k (singularCohomologyPullback ℚ πE k c) =
        singularCohomologyPullback ℚ πF k c := by
    rw [← ModuleCat.comp_apply]
    unfold singularCohomologyPullback
    rw [← CategoryTheory.Functor.map_comp, ← op_comp]
    change (singularCohomologyFunctor ℚ k).map (TopCat.ofHom (πE.comp f)).op c = _
    rw [hf]
  have hid (k : ℕ) (c : singularCohomology ℚ TF k) :
      singularCohomologyPullback ℚ (ContinuousMap.id TF) k c = c := by
    change (singularCohomologyFunctor ℚ k).map (𝟙 _) c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  let T (k : ℕ) := ↥(relativeSingularCohomology ℚ N k)
  let U (k : ℕ) := ↥(relativeSingularCohomology ℚ (A ∪ B) k)
  have hcastPull (i j : ℕ) (h : i = j) (z : U i) :
      cast (congrArg T h)
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id TF) hN i z) =
      relativeSingularCohomologyPullback ℚ (ContinuousMap.id TF) hN j
        (cast (congrArg U h) z) := by
    subst j
    rfl
  have hcastAction (i j : ℕ) (h : i = j) (z : T i) :
      cast (congrArg T (congrArg (p + q + ·) h))
        (relativeSingularCohomologyAction ℚ N (p + q) i
          (singularCohomologyPullback ℚ πF (p + q) (singularCohomologyCup ℚ X p q a b)) z) =
      relativeSingularCohomologyAction ℚ N (p + q) j
        (singularCohomologyPullback ℚ πF (p + q) (singularCohomologyCup ℚ X p q a b))
        (cast (congrArg T h) z) := by
    subst j
    rfl
  -- The genuine relative cup keeps its support while the two ordinary coefficients move left.
  have htwo := relativeSingularCohomologyUnionCup_actions ℚ A B hA hB p q
    (2 * m) (2 * m) ac bc u v
  have hsign : (-1 : ℚ) ^ (2 * m * q) = 1 := by
    rw [mul_assoc, pow_mul]
    norm_num
  rw [hsign, one_smul, ← singularCohomologyPullback_cup] at htwo
  have hrestricted := congrArg
    (relativeSingularCohomologyPullback ℚ (ContinuousMap.id TF) hN
      ((p + q) + (2 * m + 2 * m))) htwo
  rw [← hcastPull _ _ (show (p + 2 * m) + (q + 2 * m) =
    (p + q) + (2 * m + 2 * m) by omega),
    relativeSingularCohomologyPullback_action, hid] at hrestricted
  have hdegree : 2 * m + 2 * m = 2 * (2 * m) := by omega
  have hfinal := congrArg (cast (congrArg T (congrArg (p + q + ·) hdegree))) hrestricted
  rw [cast_cast, hcastAction _ _ hdegree] at hfinal
  -- Apply the original inverse only after matching the same real double Thom representative.
  have hintegral := complexificationCohomologyFiberIntegral_thomCup E o ho hV hr
    e he q₁ q₂ hq₁ hq₂ hA hB hN (p + q) (singularCohomologyCup ℚ X p q a b)
  have hleft :
      relativeSingularCohomologyPullback ℚ q₁ (fun _ hv ↦ hv) (p + 2 * m)
        (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) p (2 * m)
          (singularCohomologyPullback ℚ πE p a) τ) =
      relativeSingularCohomologyAction ℚ A p (2 * m) ac u := by
    rw [relativeSingularCohomologyPullback_action, hcoeff q₁ hπ₁]
    rfl
  have hright :
      relativeSingularCohomologyPullback ℚ q₂ (fun _ hv ↦ hv) (q + 2 * m)
        (relativeSingularCohomologyAction ℚ (bundleNonzero (2 * m) E) q (2 * m)
          (singularCohomologyPullback ℚ πE q b) τ) =
      relativeSingularCohomologyAction ℚ B q (2 * m) bc v := by
    rw [relativeSingularCohomologyPullback_action, hcoeff q₂ hπ₂]
    rfl
  rw [← hleft, ← hright] at hfinal
  exact (congrArg (fun z : T ((p + q) + 2 * (2 * m)) ↦
    compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
      (hV.complexCohomologyOrientation (2 * m) hr).rationalization (p + q)
      (compactSupportCohomologyClass ℚ TF (cohomologyZeroSectionSupport (2 * (2 * m)) F)
        ((p + q) + 2 * (2 * m)) z)) hfinal).trans hintegral

end AtiyahSinger
