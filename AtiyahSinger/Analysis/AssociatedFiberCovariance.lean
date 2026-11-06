/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedFiberRestriction

/-!
# Covariance of restriction to an associated fiber

Changing the principal point by its right group action changes the restricted
section by the inverse smooth section representation. This uses the original
associated quotient convention and the original equivariant fiber maps.
It supplies the transition law of the full vertical family operator in
SG III.13.6, before any analytic claim about a global horizontal lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedEquivariantFiberAddCommGroup
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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Right translation of the principal point acts by the inverse on the full restricted section. -/
theorem associatedSphereFiberRestriction_smul (g : G) (p : P) :
    letI := lieGroup_orthogonalGroup r
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereSmoothBundleAtlas S A σ hσ).smoothSections,
      associatedSphereFiberRestriction S A σ hσ (MulOpposite.op g • p) w =
        σ.atlasSmoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) A hσ g⁻¹
          (associatedSphereFiberRestriction S A σ hσ p w) := by
  let := lieGroup_orthogonalGroup r
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  intro w
  let s := (associatedSphereFiberRestriction S A σ hσ p w).val
  let s' := (associatedSphereFiberRestriction S A σ hσ (MulOpposite.op g • p) w).val
  let sg := σ.dependentSectionLinearMap g⁻¹ s
  have htotal (k : G) (y : OrthogonalSphere r) :
      (⟨y, σ.dependentSectionLinearMap k s y⟩ : TotalSpace Unit E) =
        k • (⟨k⁻¹ • y, s (k⁻¹ • y)⟩ : TotalSpace Unit E) := by
    let transport : ∀ {x z : OrthogonalSphere r}, x = z → E x →ₗ[ℂ] E z :=
      fun {x z} h ↦ by
        subst z
        exact LinearMap.id
    have htransport {x z : OrthogonalSphere r} (h : x = z) (v : E x) :
        (⟨z, transport h v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
      subst z
      rfl
    exact htransport (smul_inv_smul k y) _
  apply Subtype.ext
  funext y
  change s' y = sg y
  apply (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ
    (MulOpposite.op g • p) y rfl).1
  apply Subtype.ext
  -- Compare total quotient vectors so the base transport does not lose the actual point.
  change associatedBundleMk G P (TotalSpace Unit E) (MulOpposite.op g • p) ⟨y, s' y⟩ =
    associatedBundleMk G P (TotalSpace Unit E) (MulOpposite.op g • p) ⟨y, sg y⟩
  have hleft := congrArg Subtype.val
    (associatedSphereFiberRestriction_apply S A σ hσ (MulOpposite.op g • p) w y)
  have hright := congrArg Subtype.val
    (associatedSphereFiberRestriction_apply S A σ hσ p w (g • y))
  have hbase := congrArg (fun z : Z ↦ (w.val z).val) (associatedBundleMk_smul p g y)
  have hg : (⟨y, sg y⟩ : TotalSpace Unit E) =
      g⁻¹ • (⟨g • y, s (g • y)⟩ : TotalSpace Unit E) := by
    exact (htotal g⁻¹ y).trans (congrArg (fun v : TotalSpace Unit E ↦ g⁻¹ • v)
      (congrArg (fun k : G ↦ (⟨k • y, s (k • y)⟩ : TotalSpace Unit E)) (inv_inv g)))
  calc
    _ = (w.val (associatedBundleMk G P (OrthogonalSphere r)
        (MulOpposite.op g • p) y)).val := hleft
    _ = (w.val (associatedBundleMk G P (OrthogonalSphere r) p (g • y))).val := hbase
    _ = associatedBundleMk G P (TotalSpace Unit E) p ⟨g • y, s (g • y)⟩ := hright.symm
    _ = associatedBundleMk G P (TotalSpace Unit E) (MulOpposite.op g • p)
        (g⁻¹ • (⟨g • y, s (g • y)⟩ : TotalSpace Unit E)) := by
      rw [associatedBundleMk_smul, smul_inv_smul]
    _ = _ := congrArg (associatedBundleMk G P (TotalSpace Unit E)
      (MulOpposite.op g • p)) hg.symm

end AtiyahSinger
