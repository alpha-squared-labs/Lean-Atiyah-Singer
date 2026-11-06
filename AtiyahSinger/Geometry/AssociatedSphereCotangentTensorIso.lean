/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentSplitting
public import AtiyahSinger.Topology.AssociatedSupportProduct
public import AtiyahSinger.Topology.AssociatedTwistedProduct

/-!
# Tensor bundles under the original associated-sphere cotangent realization

Public module ID: M1073.

The inverse of the specified cotangent homeomorphism pulls the original paired
product bundle to the cotangent pullback of the original associated tensor
bundle. The base vector and the sphere vector retain the same principal
representative. The only casts are along the proved identities of the actual
base maps. No compact-support class or symbol identity is assumed.

This is the bundle comparison needed for the full Hermitian representative in
SG III.13. It uses the native full-product cotangent model, and the original
Unit pullback, associated quotient and finite-rank tensor topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology isFiniteRank_associatedEquivariant
  tensorTopology isFiniteRank_tensor isFiniteRank_pullback

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => CotangentTotalSpace (n := n) (M := B)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "f" => cotangentProjection (n := n) (M := B)
local notation "Q" => PrincipalBundlePullback f projection
local notation "W" => AssociatedBundle G Q Y
local notation "CotFiber" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ
local notation "NativeCot" => TotalSpace ((En × Er) →L[ℝ] ℝ) CotFiber

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
-- The original paired map and its inverse pullback retain all dependent fiber topologies.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual inverse cotangent realization preserves the original associated tensor vectors. -/
theorem exists_associatedSphereCotangentTensorIso
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (F : OrthogonalSphere r → Type) [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (σ : EquivariantStructure G F) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let pY := cotangentProjection (n := r) (M := OrthogonalSphere r)
    let σY := σ.pullback pY (fun _ _ ↦ rfl)
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let DY := AssociatedEquivariantFiber S.toIsPrincipalBundle σY
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : AssociatedBundle G P Y) : AddCommGroup (DY z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY z
    letI (z : AssociatedBundle G P Y) : Module ℂ (DY z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σY z
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let qY := associatedBundleMap (P := P) pY (fun _ _ ↦ rfl)
    let e := associatedSphereCotangentHomeomorph S H
    let inverse : C(NativeCot, W) := ⟨e.symm, e.symm.continuous⟩
    let proj : C(NativeCot, Z) := ⟨TotalSpace.proj,
      FiberBundle.continuous_proj ((En × Er) →L[ℝ] ℝ) CotFiber⟩
    let j := associatedBundlePullbackProdMap («G» := G) («Y» := Y) (projection := projection) f
    let c := j.comp inverse
    let A := (ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ (f *ᵖ E)
    let B₀ := (ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ DY
    let Pair := fun z ↦ A z ⊗[ℂ] B₀ z
    let T := fun z : Z ↦ ((base : Z → B) *ᵖ E) z ⊗[ℂ] D z
    letI : TopologicalSpace (TotalSpace Unit Pair) := tensorTopology (E := A) (F := B₀)
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (base : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ Pair)) := pullbackTopology Unit Pair j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ Pair))) :=
      pullbackTopology Unit (j *ᵖ Pair) inverse
    letI : TopologicalSpace (TotalSpace Unit (proj *ᵖ T)) := pullbackTopology Unit T proj
    ∃ (hbase : ∀ z : NativeCot, f (c z).1 = base (proj z))
      (hpoint : ∀ z : NativeCot, qY (c z).2 = proj z),
      ∃ a : Iso (inverse *ᵖ (j *ᵖ Pair)) (proj *ᵖ T),
        ∀ (z : NativeCot) (p : P) (η : Y)
          (hz : associatedBundleMk G P Y p η = (c z).2)
          (u : E (f (c z).1)) (v : F η.proj),
          a.linearEquiv z
              (u ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY p η hz v) =
            cast (congrArg E (hbase z)) u ⊗ₜ[ℂ]
              associatedEquivariantFiberMk S.toIsPrincipalBundle σ p η.proj
                ((congrArg qY hz).trans (hpoint z)) v := by
  classical
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro pY σY D DY
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : AssociatedBundle G P Y) : AddCommGroup (DY z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY z
  let (z : AssociatedBundle G P Y) : Module ℂ (DY z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σY z
  intro base qY e inverse proj j c A B₀ Pair T
  let := tensorTopology (E := A) (F := B₀)
  let := tensorTopology (E := (base : Z → B) *ᵖ E) (F := D)
  let := pullbackTopology Unit Pair j
  let := pullbackTopology Unit (j *ᵖ Pair) inverse
  let := pullbackTopology Unit T proj
  -- Recover both base maps from the original representative and cotangent splitting formulas.
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let split := H.cotangentSplitHomeomorph q hq
  have hsplit (z : NativeCot) : split z = H.cotangentSplitMap q z :=
    (SmoothHorizontalLift.exists_cotangentSplitHomeomorph q hq H).choose_spec.1 z
  have hsplitProj (u) : (split.symm u).proj = u.proj := by
    have hh := congrArg (fun w ↦ w.proj) (split.apply_symm_apply u)
    rw [hsplit] at hh
    exact hh
  have hePoint (w : W) : (e w).proj = qY (j w).2 := by
    induction w using Quotient.inductionOn with
    | h w =>
      change (e (associatedBundleMk G Q Y w.1 w.2)).proj = _
      have he := (exists_associatedSphereCotangentHomeomorph S H).choose_spec w.1 w.2
      change e (associatedBundleMk G Q Y w.1 w.2) = _ at he
      rw [he]
      exact hsplitProj _
  have hpoint (z : NativeCot) : qY (c z).2 = proj z :=
    (hePoint (inverse z)).symm.trans (congrArg TotalSpace.proj (e.apply_symm_apply z))
  have hjBase (w : W) : f (j w).1 = base (qY (j w).2) := by
    induction w using Quotient.inductionOn with
    | h w => exact w.1.property
  have hbase (z : NativeCot) : f (c z).1 = base (proj z) :=
    (hjBase (inverse z)).trans (congrArg base (hpoint z))
  -- Equal continuous base maps induce precisely the cast of each original vector.
  have pullbackEqE (a b : C(NativeCot, B)) (hab : a = b) :
      ∃ t : Iso (a *ᵖ E) (b *ᵖ E), ∀ x v,
        t.linearEquiv x v =
          cast (congrArg E (congrArg (fun g : C(NativeCot, B) ↦ g x) hab)) v := by
    subst b
    exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
  have pullbackEqD (a b : C(NativeCot, Z)) (hab : a = b) :
      ∃ t : Iso (a *ᵖ D) (b *ᵖ D), ∀ x v,
        t.linearEquiv x v =
          cast (congrArg D (congrArg (fun g : C(NativeCot, Z) ↦ g x) hab)) v := by
    subst b
    exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
  let fst : C(X × AssociatedBundle G P Y, X) := ContinuousMap.fst
  let snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y) := ContinuousMap.snd
  choose bE hbE using pullbackEqE ((f).comp (fst.comp c)) (base.comp proj)
    (ContinuousMap.ext hbase)
  choose bD hbD using pullbackEqD (qY.comp (snd.comp c)) proj
    (ContinuousMap.ext hpoint)
  choose d hd using exists_associatedEquivariantFiber_pullback_iso
    S.toIsPrincipalBundle pY (fun _ _ ↦ rfl) F σ
  -- Reassociate the original two factor pullbacks before forming their tensor comparison.
  let := pullbackTopology Unit (f *ᵖ E) fst
  let := pullbackTopology Unit DY snd
  let := pullbackTopology Unit A c
  let := pullbackTopology Unit B₀ c
  let := pullbackTopology Unit (f *ᵖ E) (fst.comp c)
  let := pullbackTopology Unit (qY *ᵖ D) (snd.comp c)
  let := pullbackTopology Unit ((base : Z → B) *ᵖ E) proj
  let := pullbackTopology Unit D proj
  let := tensorTopology (E := c *ᵖ A) (F := c *ᵖ B₀)
  let := tensorTopology (E := proj *ᵖ ((base : Z → B) *ᵖ E)) (F := proj *ᵖ D)
  let := pullbackTopology Unit Pair c
  let u := (pullbackCompIso (E := f *ᵖ E) fst c).trans
    ((pullbackCompIso (E := E) f (fst.comp c)).trans
      (bE.trans (pullbackCompIso (E := E) base proj).symm))
  let v := (pullbackCompIso (E := DY) snd c).trans
    ((d.pullback (snd.comp c)).trans
      ((pullbackCompIso (E := D) qY (snd.comp c)).trans bD))
  let a := (pullbackCompIso (E := Pair) j inverse).trans
    ((pullbackTensorIso (E := A) (F := B₀) c).trans
      ((u.tensor v).trans
        (pullbackTensorIso (E := (base : Z → B) *ᵖ E) (F := D) proj).symm))
  refine ⟨hbase, hpoint, a, ?_⟩
  intro z p η hz w t
  have hu : u.linearEquiv z w = cast (congrArg E (hbase z)) w := by
    apply ((pullbackCompIso (E := E) base proj).linearEquiv z).injective
    change (pullbackCompIso (E := E) base proj).linearEquiv z
      (((pullbackCompIso (E := E) base proj).linearEquiv z).symm
        (bE.linearEquiv z ((pullbackCompIso (E := E) f (fst.comp c)).linearEquiv z
          ((pullbackCompIso (E := f *ᵖ E) fst c).linearEquiv z w)))) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply,
      pullbackCompIso_apply, hbE]
  have hv : v.linearEquiv z
      (associatedEquivariantFiberMk S.toIsPrincipalBundle σY p η hz t) =
      associatedEquivariantFiberMk S.toIsPrincipalBundle σ p η.proj
        ((congrArg qY hz).trans (hpoint z)) t := by
    change bD.linearEquiv z ((pullbackCompIso (E := D) qY (snd.comp c)).linearEquiv z
      (d.linearEquiv (c z).2 ((pullbackCompIso (E := DY) snd c).linearEquiv z
        (associatedEquivariantFiberMk S.toIsPrincipalBundle σY p η hz t)))) = _
    rw [pullbackCompIso_apply, pullbackCompIso_apply, hd, hbD]
    -- Transport changes only the base equality carried by the same quotient representative.
    have htransport (x y : Z) (hxy : x = y)
        (hx : associatedBundleMk G P (OrthogonalSphere r) p η.proj = x) :
        cast (congrArg D hxy)
            (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p η.proj hx t) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p η.proj (hx.trans hxy) t := by
      subst y
      rfl
    exact htransport _ _ (hpoint z) (congrArg qY hz)
  change TensorProduct.congr (u.linearEquiv z) (v.linearEquiv z)
    ((pullbackCompIso (E := Pair) j inverse).linearEquiv z
      (w ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY p η hz t)) = _
  rw [pullbackCompIso_apply, TensorProduct.congr_tmul, hu, hv]

end AtiyahSinger
