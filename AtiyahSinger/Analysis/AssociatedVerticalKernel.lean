/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedFiberRestriction
public import AtiyahSinger.Analysis.SmoothAssociatedKernelDescent

/-!
# The vertical kernel in the associated bundle

Apply the supplied sphere operator to the full fiber restrictions of an
upstairs smooth section. Given finite kernel coordinates intertwining the
specified representations, the kernel of this family operator is linearly
equivalent to smooth sections of the associated kernel representation. The
equivalence evaluates through the descended bundle map on every principal
representative.

This identifies the vertical kernel in SG III.13.6 from the supplied finite
kernel data. Horizontal coupling and the index of the graded operator are
handled by separate results.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {W : Type*} [AddCommGroup W] [Module ℂ W]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
/-- The original operator applied to every full fiber restriction of the same section. -/
def associatedSphereVerticalFamilyOperator (T : A.smoothSections →ₗ[ℂ] W) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections →ₗ[ℂ] (P → W) :=
  LinearMap.pi fun p ↦ T.comp (associatedSphereFiberRestriction S A σ hσ p)

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual vertical kernel consists of smooth sections of the same associated kernel bundle. -/
theorem exists_associatedSphereVerticalKernelEquiv
    (T : A.smoothSections →ₗ[ℂ] W) (e : V ≃ₗ[ℂ] T.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : V),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    ∃ a : Hom ((q : Z → B) *ᵖ C) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : V),
        a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ Φ : (associatedOrthogonalRepresentationAtlas S ρ).smoothSections ≃ₗ[ℂ]
          (associatedSphereVerticalFamilyOperator S A σ hσ T).ker,
        ∀ (u : (associatedOrthogonalRepresentationAtlas S ρ).smoothSections) (z : Z),
          (Φ u).val.val z = a.linearMap z (u.val (q z)) := by
  classical
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let AC := associatedOrthogonalRepresentationAtlas S ρ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let R := associatedSphereFiberRestriction S A σ hσ
  let L := associatedSphereVerticalFamilyOperator S A σ hσ T
  obtain ⟨a, ha, hk⟩ := exists_smoothAssociatedKernelDescent S A σ hσ ρ T e he
  let s : V →ₗ[ℂ] A.smoothSections := T.ker.subtype.comp e.toLinearMap
  have hs : Function.Injective s := Subtype.val_injective.comp e.injective
  let F : AC.smoothSections →ₗ[ℂ] AD.smoothSections :=
    { toFun u := ⟨fun z ↦ a.linearMap z (u.val (q z)),
        (isSmoothSection_associatedEvaluation_iff S A σ hσ ρ s hs a ha u.val).mpr
          u.property⟩
      map_add' u v := by
        apply Subtype.ext
        funext z
        exact (a.linearMap z).map_add _ _
      map_smul' c u := by
        apply Subtype.ext
        funext z
        exact (a.linearMap z).map_smul c _ }
  -- The full restriction at p has the same finite kernel coordinates as the coefficient at p.
  have hmem (u : AC.smoothSections) : L (F u) = 0 := by
    funext p
    obtain ⟨v, hv⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
      ρ.representation p rfl).2 (u.val (projection p))
    have hrestriction : R p (F u) = (e v).val := by
      apply Subtype.ext
      funext y
      apply (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y rfl).1
      rw [associatedSphereFiberRestriction_apply]
      change a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
        (u.val (projection p)) = _
      rw [← hv, ha]
    change T (R p (F u)) = 0
    rw [hrestriction]
    exact (e v).property
  have hkernel (w : AD.smoothSections) (hw : L w = 0) :
      ∃! u : AC.smoothSections, ∀ z : Z, a.linearMap z (u.val (q z)) = w.val z := by
    apply (hk w).mp
    intro p
    refine ⟨R p w, congrFun hw p, ?_⟩
    intro y
    exact (associatedSphereFiberRestriction_apply S A σ hσ p w y).symm
  let φ : AC.smoothSections →ₗ[ℂ] L.ker :=
    { toFun u := ⟨F u, hmem u⟩
      map_add' u v := Subtype.ext (F.map_add u v)
      map_smul' c u := Subtype.ext (F.map_smul c u) }
  have hφ : Function.Bijective φ := by
    constructor
    · intro u v huv
      have huniq := hkernel (F u) (hmem u)
      apply huniq.unique (fun _ ↦ rfl)
      intro z
      exact congrArg (fun w : L.ker ↦ w.val.val z) huv.symm
    · intro w
      obtain ⟨u, hu, _⟩ := hkernel w.val w.property
      refine ⟨u, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact hu z
  -- The resulting linear equivalence evaluates through the original associated Hom a.
  exact ⟨a, ha, LinearEquiv.ofBijective φ hφ, fun _ _ ↦ rfl⟩

end AtiyahSinger
