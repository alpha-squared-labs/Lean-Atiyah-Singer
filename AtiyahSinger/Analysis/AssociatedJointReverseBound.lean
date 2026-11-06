/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCutoffTensorFiniteInverse
public import AtiyahSinger.Analysis.AssociatedForwardJointReverseBound
public import AtiyahSinger.Analysis.AssociatedSphereCommonBasePartition
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalFamilyRegularization
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalSymbolFactor
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSymbolFactor
public import AtiyahSinger.Analysis.AtlasNativePrincipalConjugate
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.NativeGradedTensorFamily
public import AtiyahSinger.Analysis.NativeTensorMetricEllipticity

import Lean.Meta.Closure
import Lean.Util.FoldConsts

/-!
# The original joint horizontal and vertical graph controls H1

Public module ID: M0097.

For arbitrary original elliptic C and the specified invariant elliptic full symbol
of the original equivariant Q, the joint graph bound uses the supplied native corner models,
metrics and source domain.
The auxiliary cutoff matrix is constructed internally on those same models.
Its quantitative full-symbol ellipticity follows from the original finite
cutoff factors. All localizations and cutoffs used in the graph estimate are
the ones used by this actual auxiliary matrix; no target graph estimate or
ellipticity of a supplied auxiliary operator is assumed.
-/

@[expose] public noncomputable section

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  tensorTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]
  (E E' : SmoothFiniteComplexBundle (n := n) B)
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Enr" => EuclideanSpace ℝ (Fin (n + r))
local notation "Sphere" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Sphere

variable [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 12000000 in
-- The extended limit accommodates the invariant full symbol and both original joint-domain
-- estimates.
/-- The original operators and specified invariant full symbol control their joint domain. -/
theorem associated_joint_reverse_bound_of_invariant_full_symbol
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      EquivariantStructure G F'.Fiber)
    (hσ : σ.IsSmooth (n := r) (r := F.rank) IG)
    (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) IG)
    (ν : Measure Sphere) [IsSmoothPositiveMeasure (n := r) ν]
    (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
    (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (y : Sphere) (u v : F.Fiber y),
        k.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = k.pairing y u v)
    (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (y : Sphere) (u v : F'.Fiber y),
        k'.pairing (g • y) (σ'.linearMap g y u) (σ'.linearMap g y v) = k'.pairing y u v)
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ')
    (qfull : globalSymbolSpace (n := r) (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber 1)
    (hQpr : Q.principalSymbol = globalPrincipalSymbolClass F.Fiber F'.Fiber 1 qfull)
    (hqfixed : ∀ g : G, equivariantGlobalSymbolLinearMap
      (n := r) (r := F.rank) (q := F'.rank) IG σ σ' g qfull.val = qfull.val)
    (hqfull : IsEllipticFullGlobalSymbol (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber 1 qfull.val)
    (C : PrincipalPseudodifferentialLocalization (a := E.rank) (a' := E'.rank)
      S E.Fiber E'.Fiber μ 1)
    (hCell : C.baseOperator.IsElliptic)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (h' : SmoothHermitianMetric (n := n) (r := E'.rank) E'.Fiber) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    have hA := σ.isSmoothAtlas_native IG hσ
    have hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    have hQA := (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
    let πS := associatedBundleProjection (F := Sphere) S.toIsPrincipalBundle
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    let T := fun z : Z ↦ E.Fiber (πS z) ⊗[ℂ] D z
    let U := fun z : Z ↦ E'.Fiber (πS z) ⊗[ℂ] D z
    let T' := fun z : Z ↦ E.Fiber (πS z) ⊗[ℂ] D' z
    let U' := fun z : Z ↦ E'.Fiber (πS z) ⊗[ℂ] D' z
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E.Fiber) (F := D)
    letI : TopologicalSpace (TotalSpace Unit U) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E'.Fiber) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E.Fiber) (F := D')
    letI : TopologicalSpace (TotalSpace Unit U') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E'.Fiber) (F := D')
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := linearModelChartedSpace split.symm Z
    letI := isManifold_linearModelChartedSpace split.symm Z
    let A₀₀ := associatedSphereTensorBundleAtlas (a := E.rank) S E.Fiber A σ hA
    let A₁₀ := associatedSphereTensorBundleAtlas (a := E'.rank) S E'.Fiber A σ hA
    let A₀₁ := associatedSphereTensorBundleAtlas (a := E.rank) S E.Fiber A' σ' hA'
    let A₁₁ := associatedSphereTensorBundleAtlas (a := E'.rank) S E'.Fiber A' σ' hA'
    let c₀ (z : Z) := h.toCore (πS z)
    let c₁ (z : Z) := h'.toCore (πS z)
    let d₀ (z : Z) :=
      associatedEquivariantMetricCore S.toIsPrincipalBundle σ k.toContinuousHermitianMetric z
    let d₁ (z : Z) :=
      associatedEquivariantMetricCore S.toIsPrincipalBundle σ' k'.toContinuousHermitianMetric z
    ∀ (Li : AtlasBundlePresentation A₀₀)
      (l₀₀ : ContinuousHermitianMetric T) (_hl₀₀ : A₀₀.IsSmoothHermitianMetric l₀₀)
      (l₁₀ : ContinuousHermitianMetric U) (_hl₁₀ : A₁₀.IsSmoothHermitianMetric l₁₀)
      (l₀₁ : ContinuousHermitianMetric T') (_hl₀₁ : A₀₁.IsSmoothHermitianMetric l₀₁)
      (N₀₀ N₁₀ N₀₁ N₁₁ : SmoothFiniteComplexBundle (n := n + r) Z)
      (k₀₀ : SmoothHermitianMetric (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
      (k₁₀ : SmoothHermitianMetric (n := n + r) (r := N₁₀.rank) N₁₀.Fiber)
      (k₀₁ : SmoothHermitianMetric (n := n + r) (r := N₀₁.rank) N₀₁.Fiber)
      (k₁₁ : SmoothHermitianMetric (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
      (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    ∀ (e₀₀ : Iso T N₀₀.Fiber)
      (he₀₀ : IsSmoothAtlasBundleMap A₀₀
        (nativeSmoothComplexBundleAtlas N₀₀.Fiber) e₀₀.toHom.linearMap)
      (hi₀₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₀.Fiber)
        A₀₀ e₀₀.symm.toHom.linearMap)
      (e₁₀ : Iso U N₁₀.Fiber)
      (he₁₀ : IsSmoothAtlasBundleMap A₁₀
        (nativeSmoothComplexBundleAtlas N₁₀.Fiber) e₁₀.toHom.linearMap)
      (hi₁₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁₀.Fiber)
        A₁₀ e₁₀.symm.toHom.linearMap)
      (e₀₁ : Iso T' N₀₁.Fiber)
      (he₀₁ : IsSmoothAtlasBundleMap A₀₁
        (nativeSmoothComplexBundleAtlas N₀₁.Fiber) e₀₁.toHom.linearMap)
      (hi₀₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀₁.Fiber)
        A₀₁ e₀₁.symm.toHom.linearMap)
      (e₁₁ : Iso U' N₁₁.Fiber)
      (_he₁₁ : IsSmoothAtlasBundleMap A₁₁
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
        e₁₁.toHom.linearMap)
      (_hi₁₁ : IsSmoothAtlasBundleMap
        (nativeSmoothComplexBundleAtlas (n := n + r) (r := N₁₁.rank) N₁₁.Fiber)
        A₁₁ e₁₁.symm.toHom.linearMap)
      (_hk₀₀ : ∀ z u v, k₀₀.pairing z (e₀₀.linearEquiv z u)
        (e₀₀.linearEquiv z v) = (l₀₀.toCore z).inner u v)
      (_hk₁₀ : ∀ z u v, k₁₀.pairing z (e₁₀.linearEquiv z u)
        (e₁₀.linearEquiv z v) = (l₁₀.toCore z).inner u v)
      (_hk₀₁ : ∀ z u v, k₀₁.pairing z (e₀₁.linearEquiv z u)
        (e₀₁.linearEquiv z v) = (l₀₁.toCore z).inner u v)
      (_hkPure₀₀ : ∀ z u v a b, k₀₀.pairing z (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] a))
        (e₀₀.linearEquiv z (v ⊗ₜ[ℂ] b)) = (c₀ z).inner u v * (d₀ z).inner a b)
      (_hkPure₁₀ : ∀ z u v a b, k₁₀.pairing z (e₁₀.linearEquiv z (u ⊗ₜ[ℂ] a))
        (e₁₀.linearEquiv z (v ⊗ₜ[ℂ] b)) = (c₁ z).inner u v * (d₀ z).inner a b)
      (_hkPure₀₁ : ∀ z u v a b, k₀₁.pairing z (e₀₁.linearEquiv z (u ⊗ₜ[ℂ] a))
        (e₀₁.linearEquiv z (v ⊗ₜ[ℂ] b)) = (c₀ z).inner u v * (d₁ z).inner a b)
      (_hkPure₁₁ : ∀ z u v a b, k₁₁.pairing z (e₁₁.linearEquiv z (u ⊗ₜ[ℂ] a))
        (e₁₁.linearEquiv z (v ⊗ₜ[ℂ] b)) = (c₁ z).inner u v * (d₁ z).inner a b),
      let S₀₀ := (atlasSmoothSectionEquiv A₀₀
        (nativeSmoothComplexBundleAtlas N₀₀.Fiber) e₀₀ he₀₀ hi₀₀).trans
          (nativeSmoothSectionLinearEquiv N₀₀.Fiber)
      let i₀₀ := (k₀₀.smoothToL2 η).comp S₀₀.toLinearMap
      let S₁₀ := (atlasSmoothSectionEquiv A₁₀
        (nativeSmoothComplexBundleAtlas N₁₀.Fiber) e₁₀ he₁₀ hi₁₀).trans
          (nativeSmoothSectionLinearEquiv N₁₀.Fiber)
      let i₁₀ := (k₁₀.smoothToL2 η).comp S₁₀.toLinearMap
      let S₀₁ := (atlasSmoothSectionEquiv A₀₁
        (nativeSmoothComplexBundleAtlas N₀₁.Fiber) e₀₁ he₀₁ hi₀₁).trans
          (nativeSmoothSectionLinearEquiv N₀₁.Fiber)
      let i₀₁ := (k₀₁.smoothToL2 η).comp S₀₁.toLinearMap
      let V := associatedSphereTensorVerticalOperator S E.Fiber A σ hA A' σ' hA' QA hQA
      ∃ B : ℝ, 0 ≤ B ∧ ∀ w : A₀₀.smoothSections,
        ‖Li.smoothToSobolev 1 w‖ ≤ B *
          (‖i₀₀ w‖ + ‖i₁₀ (C.horizontalLift S E.Fiber A σ E'.Fiber hA w)‖ + ‖i₀₁ (V w)‖) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  intro A A' hA hA' QA hQA πS D D'
  -- Use the descended fiber algebraic structures when forming the Hom sums.
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  intro T U T' U'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E.Fiber) (F := D)
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E'.Fiber) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E.Fiber) (F := D')
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E'.Fiber) (F := D')
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro split
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro A₀₀ A₁₀ A₀₁ A₁₁ c₀ c₁ d₀ d₁ Li l₀₀ hl₀₀ l₁₀ hl₁₀ l₀₁ hl₀₁
    N₀₀ N₁₀ N₀₁ N₁₁ k₀₀ k₁₀ k₀₁ k₁₁ η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  intro e₀₀ he₀₀ hi₀₀ e₁₀ he₁₀ hi₁₀ e₀₁ he₀₁ hi₀₁ e₁₁ he₁₁ hi₁₁
    hk₀₀ hk₁₀ hk₀₁ hkPure₀₀ hkPure₁₀ hkPure₀₁ hkPure₁₁ S₀₀ i₀₀ S₁₀ i₁₀ S₀₁ i₀₁ V
  let gB : SmoothCotangentMetric (n := n) (M := B) :=
    Classical.choice (SmoothCotangentMetric.nonempty (n := n) (M := B))
  let g : SmoothCotangentMetric (n := r) (M := Sphere) :=
    Classical.choice (SmoothCotangentMetric.nonempty (n := r) (M := Sphere))
  let gZ : SmoothCotangentMetric (n := n + r) (M := Z) :=
    Classical.choice (SmoothCotangentMetric.nonempty (n := n + r) (M := Z))
  -- A common native sphere partition serves both the Green energy and cutoff constructions.
  have hSphere := exists_common_smoothBundlePresentation_subordinate
      (n := r) (r := F.rank) (q := F'.rank) F.Fiber F'.Fiber
      (fun _ : Unit ↦ (Set.univ : Set Sphere)) (fun _ ↦ isOpen_univ)
      (fun _ ↦ ⟨(), Set.mem_univ _⟩)
  let L₀ := hSphere.choose
  let Lother := hSphere.choose_spec.choose
  let eL := hSphere.choose_spec.choose_spec.choose
  have hLcutoff := hSphere.choose_spec.choose_spec.choose_spec.choose_spec.2.1
  let sphereFrame₁ := fun j ↦ Lother.frame (eL j)
  have hsphereFrame₁ (j : Fin L₀.size) : MemTrivializationAtlas (sphereFrame₁ j) :=
    Lother.frame_mem_atlas (eL j)
  have hsphereSupport₁ (j : Fin L₀.size) :
      tsupport (L₀.cutoff j) ⊆ (sphereFrame₁ j).baseSet := by
    intro y hy
    exact (Lother.support_subset (eL j) (by rwa [hLcutoff])).2
  let L₁ : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber := {
    size := L₀.size
    chart := L₀.chart
    chart_mem_atlas := L₀.chart_mem_atlas
    frame := sphereFrame₁
    frame_mem_atlas := hsphereFrame₁
    cutoff := L₀.cutoff
    smooth_cutoff := L₀.smooth_cutoff
    cutoff_nonneg := L₀.cutoff_nonneg
    compact_support := L₀.compact_support
    support_subset := fun j _ hy ↦ ⟨(L₀.support_subset j hy).1, hsphereSupport₁ j hy⟩
    sum_cutoff := L₀.sum_cutoff }
  -- The actual common base frames are the same named selection used by the cutoff construction.
  have hcommon := exists_associatedSphere_common_base_partition
    (n := n) (r := r) (a := E.rank) (a' := E'.rank) S E.Fiber E'.Fiber
  let Bpres := hcommon.choose
  let frame' := hcommon.choose_spec.choose
  have hframe' := hcommon.choose_spec.choose_spec.choose
  have hsframe' := hcommon.choose_spec.choose_spec.choose_spec.choose
  let b := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hb := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let Bpres' : SmoothBundlePresentation (n := n) (r := E'.rank) E'.Fiber := {
    size := Bpres.size
    chart := Bpres.chart
    chart_mem_atlas := Bpres.chart_mem_atlas
    frame := frame'
    frame_mem_atlas := hframe'
    cutoff := Bpres.cutoff
    smooth_cutoff := Bpres.smooth_cutoff
    cutoff_nonneg := Bpres.cutoff_nonneg
    compact_support := Bpres.compact_support
    support_subset := fun j _ hx ↦ ⟨(Bpres.support_subset j hx).1, hsframe' j hx⟩
    sum_cutoff := Bpres.sum_cutoff }
  have hb' (j : Fin Bpres'.size) :
      tsupport (Bpres'.cutoff j) ⊆ (S.trivialization (b j)).baseSet := hb j
  -- Select the actual component domains once, then retain every original cutoff-row witness.
  let Lo : AtlasBundlePresentation A₁₀ :=
    Classical.choice (nonempty_atlasBundlePresentation A₁₀)
  let Li₁ : AtlasBundlePresentation A₀₁ :=
    Classical.choice (nonempty_atlasBundlePresentation A₀₁)
  let Lo₁ : AtlasBundlePresentation A₁₁ :=
    Classical.choice (nonempty_atlasBundlePresentation A₁₁)
  let JH := L₀.toAtlasBundlePresentation
  let JH' := L₁.toAtlasBundlePresentation
  let JV := Bpres
  let JV' := Bpres'
  have hJV := hb
  have hJV' := hb'
  have hcommonData := hcommon.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
    |>.choose_spec
  let qa := nativeAtlasGlobalSymbol 1 qfull
  let Rq : AtlasQuantizationPresentation A A' :=
    Classical.choice (nonempty_atlasQuantizationPresentation A A')
  -- Quantitative inverse bounds use the same finite C/R(q) factors and all original metrics.
  have hFinite := exists_associatedSphereCutoffTensorSymbol_finite_inverse_bounds
    (n := n) (r := r) (d := F.rank) (e := F'.rank) (ι := Fin JV.size)
    S σ σ' E.Fiber E'.Fiber C hCell gB h h' qfull hqfixed hqfull g k k' hk hk'
    hA hA' JH Rq b JV.chart JV.chart_mem_atlas
    (fun j ↦ (JV.chartCutoff E.Fiber j).cutoff)
    (fun j ↦ (JV.chartCutoff E.Fiber j).compact_support)
    (fun j _ hx ↦ ((JV.chartCutoff E.Fiber j).support_subset hx).1)
    (fun j _ hx ↦ hJV j (JV.chartCutoff_support_subset E.Fiber j hx)) hcommonData.2
  let N := hFinite.choose
  let CC := hFinite.choose_spec.choose
  let KK := hFinite.choose_spec.choose_spec.choose
  have hFiniteData := hFinite.choose_spec.choose_spec.choose_spec
  have hCC := hFiniteData.1
  have hKK := hFiniteData.2.1
  have hKKsource := hFiniteData.2.2.1
  have hcover := hFiniteData.2.2.2.1
  have hlocal := hFiniteData.2.2.2.2
  have hregH₀ := C.exists_horizontalLift_regularization S E.Fiber A σ E'.Fiber hA JH Li Lo
  let Co : ∀ i : Fin C.size, BundleChartCutoff (r :=
    E'.rank) E'.Fiber (C.piece i).chart := hregH₀.choose
  have hCo := hregH₀.choose_spec.choose
  let κ : Fin C.size → Fin JH.size → Er → ℝ := hregH₀.choose_spec.choose_spec.choose
  have hκ := hregH₀.choose_spec.choose_spec.choose_spec.choose
  have hκK := hregH₀.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hκs := hregH₀.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hrest := hregH₀.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hCoF := hrest.1
  have hCoI := hrest.2.1
  have hCoOne := hrest.2.2.1
  have hκOne := hrest.2.2.2.1
  have hio := hrest.2.2.2.2
  let IH₀ : Fin C.size → ∀ j : Fin JH.size, A₀₀.smoothSections →ₗ[ℂ]
      𝓢(Enr, EuclideanSpace ℂ (Fin (E.rank * A.rank (JH.frameIndex j)))) := hio.choose
  let OH₀ : Fin C.size → ∀ j : Fin JH.size,
      𝓢(Enr, EuclideanSpace ℂ (Fin (E'.rank * A.rank (JH.frameIndex j))))
        →ₗ[ℂ] A₁₀.smoothSections := hio.choose_spec.choose
  have hmaps := hio.choose_spec.choose_spec
  have hIH₀ := hmaps.1
  have hOH₀ := hmaps.2.1
  have hrrH₀ := hmaps.2.2.choose_spec
  have hposH₀ := hrrH₀.2.choose_spec.2
  have hregH₁ := C.exists_horizontalLift_regularization S E.Fiber A' σ' E'.Fiber hA' JH' Li₁ Lo₁
  let Co₁ : ∀ i : Fin C.size, BundleChartCutoff (r :=
    E'.rank) E'.Fiber (C.piece i).chart := hregH₁.choose
  have hCo₁ := hregH₁.choose_spec.choose
  let κ₁ : Fin C.size → Fin JH'.size → Er → ℝ := hregH₁.choose_spec.choose_spec.choose
  have hκ₁ := hregH₁.choose_spec.choose_spec.choose_spec.choose
  have hκK₁ := hregH₁.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hκs₁ := hregH₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hrest₁ := hregH₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hCoF₁ := hrest₁.1
  have hCoI₁ := hrest₁.2.1
  have hCoOne₁ := hrest₁.2.2.1
  have hκOne₁ := hrest₁.2.2.2.1
  have hio₁ := hrest₁.2.2.2.2
  let IH₁ : Fin C.size → ∀ j : Fin JH'.size, A₀₁.smoothSections →ₗ[ℂ]
      𝓢(Enr, EuclideanSpace ℂ (Fin (E.rank * A'.rank (JH'.frameIndex j)))) := hio₁.choose
  let OH₁ : Fin C.size → ∀ j : Fin JH'.size,
      𝓢(Enr, EuclideanSpace ℂ (Fin (E'.rank * A'.rank (JH'.frameIndex j))))
        →ₗ[ℂ] A₁₁.smoothSections := hio₁.choose_spec.choose
  have hmaps₁ := hio₁.choose_spec.choose_spec
  have hIH₁ := hmaps₁.1
  have hOH₁ := hmaps₁.2.1
  have hrrH₁ := hmaps₁.2.2.choose_spec
  have hposH₁ := hrrH₁.2.choose_spec.2
  -- These two vertical calls use the same base partition and original Rq pieces.
  let Lq := fun j ↦ (Rq.patch j).toPiece qa
  have hreg0 := exists_associatedSphereTensorVerticalGlobalFamily_regularization
    (a := E.rank) S E.Fiber A σ A' σ' hA hA' QA hQA Rq.size Lq JV b hJV Li Li₁
  let γ0 := hreg0.choose
  have γ0Rest := hreg0.choose_spec
  have hγ0 := γ0Rest.choose
  have hγ0Rest := γ0Rest.choose_spec
  have hcγ0 := hγ0Rest.choose
  have hcγ0Rest := hγ0Rest.choose_spec
  have hsγ0 := hcγ0Rest.choose
  have hsγ0Rest := hcγ0Rest.choose_spec
  have hbγ0 := hsγ0Rest.choose
  have hbγ0Rest := hsγ0Rest.choose_spec
  let κ0 := hbγ0Rest.choose
  have κ0Rest := hbγ0Rest.choose_spec
  have hκ0 := κ0Rest.choose
  have hκ0Rest := κ0Rest.choose_spec
  have hcκ0 := hκ0Rest.choose
  have hcκ0Rest := hκ0Rest.choose_spec
  have hsκ0 := hcκ0Rest.choose
  have hsκ0Rest := hcκ0Rest.choose_spec
  have hγone0 := hsκ0Rest.1
  have hκone0 := hsκ0Rest.2.1
  have hκin0 := hsκ0Rest.2.2.1
  have hIO0 := hsκ0Rest.2.2.2
  let I0 := hIO0.choose
  let O0 := hIO0.choose_spec.choose
  have hIOData0 := hIO0.choose_spec.choose_spec
  have hI0 := hIOData0.1
  have hO0 := hIOData0.2.1
  have hTR0 := hIOData0.2.2
  have hTRData0 := hTR0.choose_spec.choose_spec
  have hW0 := hTRData0.2.2
  have hWData0 := hW0.choose_spec
  have hBound0 := hWData0.2.2.2
  have hpos0 := hBound0.choose_spec.2
  let Co0 (k : Fin JV.size) (j : Fin Rq.size) : BundleChartCutoff E.Fiber (JV.chart k) := {
    JV.chartCutoff E.Fiber k with
      cutoff := γ0 k j
      smooth_cutoff := hγ0 k j
      compact_support := hcγ0 k j
      support_subset := hsγ0 k j }
  have hreg1 := exists_associatedSphereTensorVerticalGlobalFamily_regularization
    (a := E'.rank) S E'.Fiber A σ A' σ' hA hA' QA hQA Rq.size Lq JV' b hJV' Lo Lo₁
  let γ1 := hreg1.choose
  have γ1Rest := hreg1.choose_spec
  have hγ1 := γ1Rest.choose
  have hγ1Rest := γ1Rest.choose_spec
  have hcγ1 := hγ1Rest.choose
  have hcγ1Rest := hγ1Rest.choose_spec
  have hsγ1 := hcγ1Rest.choose
  have hsγ1Rest := hcγ1Rest.choose_spec
  have hbγ1 := hsγ1Rest.choose
  have hbγ1Rest := hsγ1Rest.choose_spec
  let κ1 := hbγ1Rest.choose
  have κ1Rest := hbγ1Rest.choose_spec
  have hκ1 := κ1Rest.choose
  have hκ1Rest := κ1Rest.choose_spec
  have hcκ1 := hκ1Rest.choose
  have hcκ1Rest := hκ1Rest.choose_spec
  have hsκ1 := hcκ1Rest.choose
  have hsκ1Rest := hcκ1Rest.choose_spec
  have hγone1 := hsκ1Rest.1
  have hκone1 := hsκ1Rest.2.1
  have hκin1 := hsκ1Rest.2.2.1
  have hIO1 := hsκ1Rest.2.2.2
  let I1 := hIO1.choose
  let O1 := hIO1.choose_spec.choose
  have hIOData1 := hIO1.choose_spec.choose_spec
  have hI1 := hIOData1.1
  have hO1 := hIOData1.2.1
  have hTR1 := hIOData1.2.2
  have hTRData1 := hTR1.choose_spec.choose_spec
  have hW1 := hTRData1.2.2
  have hWData1 := hW1.choose_spec
  have hBound1 := hWData1.2.2.2
  have hpos1 := hBound1.choose_spec.2
  -- Each positive parameter uses the original local operators and their complete full symbols.
  have hcutH₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := hposH₀ ε hε hε1
  let QH₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₀ ε hε hε1).choose
  let UHloc₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₀ ε hε hε1).choose_spec.choose
  have hDataH₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₀ ε hε hε1).choose_spec.choose_spec.choose_spec
  have hprincipalH₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    C.exists_horizontalCutoff_principalSymbol
      S E.Fiber A σ E'.Fiber hA JH Co hCo κ hκ hκK hκs
      hCoF hCoI IH₀ OH₀ hIH₀ hOH₀ ε hε
      (QH₀Family ε hε hε1) (UHloc₀Family ε hε hε1)
      (hDataH₀ ε hε hε1).1 (hDataH₀ ε hε hε1).2.1
  let gH₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₀ ε hε hε1).choose
  have hgH₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₀ ε hε hε1).choose_spec.1
  let Uat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₀ ε hε hε1).choose_spec.2.choose
  have hUat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₀ ε hε hε1).choose_spec.2.choose_spec.1
  have hsUat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₀ ε hε hε1).choose_spec.2.choose_spec.2
  let sH₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      atlasGlobalSymbolSpace A₀₀ A₁₀ 1 := ∑ i, ∑ j, (gH₀Family ε hε hε1) i j
  have hcutH₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := hposH₁ ε hε hε1
  let QH₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₁ ε hε hε1).choose
  let UHloc₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₁ ε hε hε1).choose_spec.choose
  have hDataH₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutH₁ ε hε hε1).choose_spec.choose_spec.choose_spec
  have hprincipalH₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    C.exists_horizontalCutoff_principalSymbol
      S E.Fiber A' σ' E'.Fiber hA' JH' Co₁ hCo₁ κ₁ hκ₁ hκK₁ hκs₁
      hCoF₁ hCoI₁ IH₁ OH₁ hIH₁ hOH₁ ε hε
      (QH₁Family ε hε hε1) (UHloc₁Family ε hε hε1)
      (hDataH₁ ε hε hε1).1 (hDataH₁ ε hε hε1).2.1
  let gH₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₁ ε hε hε1).choose
  have hgH₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₁ ε hε hε1).choose_spec.1
  let Uat₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₁ ε hε hε1).choose_spec.2.choose
  have hsUat₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalH₁ ε hε hε1).choose_spec.2.choose_spec.2
  let sH₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      atlasGlobalSymbolSpace A₀₁ A₁₁ 1 := ∑ i, ∑ j, (gH₁Family ε hε hε1) i j
  have hcutV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := hpos0 ε hε hε1
  let QV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₀ ε hε hε1).choose
  let UVloc₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₀ ε hε hε1).choose_spec.choose
  have hDataV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₀ ε hε hε1).choose_spec.choose_spec.choose_spec
  have hprincipalV₀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    exists_associatedSphereTensorVerticalGlobal_principalSymbol
      (a := E.rank) S E.Fiber A σ A' σ' hA hA' JV b hJV
      (fun _ ↦ Rq.size) (fun _ ↦ Lq)
      γ0 hγ0 hcγ0 hsγ0 hbγ0 κ0 hκ0 hcκ0 hsκ0 hκin0
      I0 O0 hI0 hO0 ε hε (QV₀Family ε hε hε1) (UVloc₀Family ε hε hε1)
      (hDataV₀ ε hε hε1).1 (hDataV₀ ε hε hε1).2.1
  let gV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₀ ε hε hε1).choose
  have hgV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₀ ε hε hε1).choose_spec.1
  let Vat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₀ ε hε hε1).choose_spec.2.choose
  have hVat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₀ ε hε hε1).choose_spec.2.choose_spec.1
  have hsVat₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₀ ε hε hε1).choose_spec.2.choose_spec.2
  let sV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      atlasGlobalSymbolSpace A₀₀ A₀₁ 1 := ∑ i, ∑ j, (gV₀Family ε hε hε1) i j
  have hcutV₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) := hpos1 ε hε hε1
  let QV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₁ ε hε hε1).choose
  let UVloc₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₁ ε hε hε1).choose_spec.choose
  have hDataV₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hcutV₁ ε hε hε1).choose_spec.choose_spec.choose_spec
  have hprincipalV₁ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    exists_associatedSphereTensorVerticalGlobal_principalSymbol
      (a := E'.rank) S E'.Fiber A σ A' σ' hA hA' JV' b hJV'
      (fun _ ↦ Rq.size) (fun _ ↦ Lq)
      γ1 hγ1 hcγ1 hsγ1 hbγ1 κ1 hκ1 hcκ1 hsκ1 hκin1
      I1 O1 hI1 hO1 ε hε (QV₁Family ε hε hε1) (UVloc₁Family ε hε hε1)
      (hDataV₁ ε hε hε1).1 (hDataV₁ ε hε hε1).2.1
  let gV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₁ ε hε hε1).choose
  have hgV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₁ ε hε hε1).choose_spec.1
  let Vat₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₁ ε hε hε1).choose_spec.2.choose
  have hsVat₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hprincipalV₁ ε hε hε1).choose_spec.2.choose_spec.2
  let sV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      atlasGlobalSymbolSpace A₁₀ A₁₁ 1 := ∑ i, ∑ j, (gV₁Family ε hε hε1) i j
  -- Native conjugation uses the four once-selected Green models and actual smooth maps.
  have hnU₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (Uat₀Family ε hε hε1).exists_native_conjugate_principalSymbol (μ := η)
      (sH₀Family ε hε hε1) (hsUat₀Family ε hε hε1)
      N₀₀ N₁₀ e₀₀ e₁₀ he₀₀ hi₀₀ he₁₀ hi₁₀
  let nativeU₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnU₀Family ε hε hε1).choose_spec.choose
  have hnU₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (Uat₁Family ε hε hε1).exists_native_conjugate_principalSymbol (μ := η)
      (sH₁Family ε hε hε1) (hsUat₁Family ε hε hε1)
      N₀₁ N₁₁ e₀₁ e₁₁ he₀₁ hi₀₁ he₁₁ hi₁₁
  let nativeU₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnU₁Family ε hε hε1).choose_spec.choose
  have hnV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (Vat₀Family ε hε hε1).exists_native_conjugate_principalSymbol (μ := η)
      (sV₀Family ε hε hε1) (hsVat₀Family ε hε hε1)
      N₀₀ N₀₁ e₀₀ e₀₁ he₀₀ hi₀₀ he₀₁ hi₀₁
  let nativeV₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnV₀Family ε hε hε1).choose_spec.choose
  have hnV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (Vat₁Family ε hε hε1).exists_native_conjugate_principalSymbol (μ := η)
      (sV₁Family ε hε hε1) (hsVat₁Family ε hε hε1)
      N₁₀ N₁₁ e₁₀ e₁₁ he₁₀ hi₁₀ he₁₁ hi₁₁
  let nativeV₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnV₁Family ε hε hε1).choose_spec.choose
  let a₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnU₀Family ε hε hε1).choose
  let a₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnU₁Family ε hε hε1).choose
  let b₀Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnV₀Family ε hε hε1).choose
  let b₁Family (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :=
    (hnV₁Family ε hε hε1).choose
  -- Both coefficient rows use the same charts and scalar partition functions.
  let CP (i : Fin C.size) (j : Fin JH.size) :=
    associatedSphereProductChart S (C.center i) (C.piece i).chart (JH.chart j)
  let pfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
    ∑ i, ∑ j,
      let cov := split (covectorInChart (CP i j) z ξ)
      ((JH.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
        productFrequencyCutoff ε ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
          ((C.piece i).globalSymbolFunction (πS z)
            (covectorFromChart (C.piece i).chart (πS z) cov.1)).toLinearMap
  let AD := associatedSphereSmoothBundleAtlas S A σ hA
  let AD' := associatedSphereSmoothBundleAtlas S A' σ' hA'
  let CPv (k : Fin JV.size) (j : Fin Rq.size) :=
    associatedSphereProductChart S (b k) (JV.chart k) (Lq j).chart
  let qfFamily (ε : ℝ) (z : Z) (ξ : CotangentFiber (n := n + r) z) : D z →ₗ[ℂ] D' z :=
    ∑ k : Fin JV.size, ∑ j : Fin Rq.size,
      let y := (associatedSphereTrivialization S (b k) z).2
      let cov := split (covectorInChart (CPv k j) z ξ)
      if hz : z ∈ (CPv k j).source ∩
          (AD.chart (b k, (Lq j).input.frameIndex)).baseSet ∩
          (AD'.chart (b k, (Lq j).output.frameIndex)).baseSet then
        let eIn : D z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A.rank (Lq j).input.frameIndex)) :=
          (AD.frameLinearEquiv (b k, (Lq j).input.frameIndex) z hz.1.2).trans
            (EuclideanSpace.equiv
              (Fin (A.rank (Lq j).input.frameIndex)) ℂ).symm.toLinearEquiv
        let eOut : D' z ≃ₗ[ℂ]
            EuclideanSpace ℂ (Fin (A'.rank (Lq j).output.frameIndex)) :=
          (AD'.frameLinearEquiv (b k, (Lq j).output.frameIndex) z hz.2).trans
            (EuclideanSpace.equiv
              (Fin (A'.rank (Lq j).output.frameIndex)) ℂ).symm.toLinearEquiv
        (((JV.chartCutoff E.Fiber k).cutoff (JV.chart k (πS z)) *
          (Lq j).input.cutoff ((Lq j).chart y) *
          (Lq j).output.cutoff ((Lq j).chart y) *
          productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
          (eOut.symm.toLinearMap.comp
            (((Lq j).symbol ((Lq j).chart y) cov.2).toLinearMap.comp eIn.toLinearMap)
              : D z →ₗ[ℂ] D' z)
      else (0 : D z →ₗ[ℂ] D' z)
  have hsH₀factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) :
      (sH₀Family ε hε hε1).val z ξ = TensorProduct.map (pfFamily ε z ξ)
        (LinearMap.id : Module.End ℂ (D z)) := by
    let ev : atlasGlobalSymbolSpace A₀₀ A₁₀ 1 →ₗ[ℂ] (T z →ₗ[ℂ] U z) :=
      (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
        (atlasGlobalSymbolSpace A₀₀ A₁₀ 1).subtype)
    have heval := (map_sum ev
      (fun i : Fin C.size ↦ ∑ j : Fin JH.size, (gH₀Family ε hε hε1) i j)
        Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
            (fun j : Fin JH.size ↦ (gH₀Family ε hε hε1) i j) Finset.univ))
    refine heval.trans ?_
    have hi (i : Fin C.size) := associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
      S E.Fiber A σ E'.Fiber (C.piece i) hA (C.center i)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inr hx, hxy⟩)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inl hx, hxy⟩)
      JH (Co i) (hCoF i) (hCo i) (hCoOne i) (κ i) (hκ i) (hκK i)
      (hκs i) (hκOne i) ε (fun j ↦ ((gH₀Family ε hε hε1) i j).val)
      ((hgH₀Family ε hε hε1) i) z ξ
    change (∑ i, ∑ j, ((gH₀Family ε hε hε1) i j).val z ξ) = _
    rw [Finset.sum_congr rfl (fun i _ ↦ hi i)]
    change (∑ j : Fin C.size, (LinearMap.rTensorHom (R := ℂ) (D z)) _) =
      (LinearMap.rTensorHom (R := ℂ) (D z)) _
    exact (map_sum (LinearMap.rTensorHom (R := ℂ) (D z)) _ Finset.univ).symm
  have hsH₁factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) :
      (sH₁Family ε hε hε1).val z ξ = TensorProduct.map (pfFamily ε z ξ)
        (LinearMap.id : Module.End ℂ (D' z)) := by
    let ev : atlasGlobalSymbolSpace A₀₁ A₁₁ 1 →ₗ[ℂ] (T' z →ₗ[ℂ] U' z) :=
      (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
        (atlasGlobalSymbolSpace A₀₁ A₁₁ 1).subtype)
    have heval := (map_sum ev
      (fun i : Fin C.size ↦ ∑ j : Fin JH'.size, (gH₁Family ε hε hε1) i j)
        Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
            (fun j : Fin JH'.size ↦ (gH₁Family ε hε hε1) i j) Finset.univ))
    refine heval.trans ?_
    have hi (i : Fin C.size) := associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
      S E.Fiber A' σ' E'.Fiber (C.piece i) hA' (C.center i)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inr hx, hxy⟩)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inl hx, hxy⟩)
      JH' (Co₁ i) (hCoF₁ i) (hCo₁ i) (hCoOne₁ i) (κ₁ i) (hκ₁ i) (hκK₁ i)
      (hκs₁ i) (hκOne₁ i) ε (fun j ↦ ((gH₁Family ε hε hε1) i j).val)
      ((hgH₁Family ε hε hε1) i) z ξ
    change (∑ i, ∑ j, ((gH₁Family ε hε hε1) i j).val z ξ) = _
    rw [Finset.sum_congr rfl (fun i _ ↦ hi i)]
    change (∑ j : Fin C.size, (LinearMap.rTensorHom (R := ℂ) (D' z)) _) =
      (LinearMap.rTensorHom (R := ℂ) (D' z)) _
    exact (map_sum (LinearMap.rTensorHom (R := ℂ) (D' z)) _ Finset.univ).symm
  have hsV₀factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) :
      (sV₀Family ε hε hε1).val z ξ =
        TensorProduct.map (LinearMap.id : Module.End ℂ (E.Fiber (πS z))) (qfFamily ε z ξ) := by
    let ev : atlasGlobalSymbolSpace A₀₀ A₀₁ 1 →ₗ[ℂ] (T z →ₗ[ℂ] T' z) :=
      (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
        (atlasGlobalSymbolSpace A₀₀ A₀₁ 1).subtype)
    have heval := (map_sum ev
      (fun i : Fin JV.size ↦ ∑ j : Fin Rq.size, (gV₀Family ε hε hε1) i j)
        Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
            (fun j : Fin Rq.size ↦ (gV₀Family ε hε hε1) i j) Finset.univ))
    refine heval.trans ?_
    have hj (j : Fin JV.size) := associatedSphereTensorVerticalSymbol_eq_finiteTensorFactor
      (a := E.rank) S E.Fiber A σ A' σ' hA hA' (b j) (JV.chart j)
      (JV.chartCutoff E.Fiber j)
      (fun _ hx ↦ hJV j (JV.chartCutoff_support_subset E.Fiber j hx)) Rq.size Lq
      (γ0 j) (hγ0 j) (hcγ0 j) (hsγ0 j) (hbγ0 j) (hγone0 j)
      (κ0 j) (hκ0 j) (hcκ0 j) (hsκ0 j) (hκone0 j)
      ε (fun k ↦ ((gV₀Family ε hε hε1) j k).val)
      ((hgV₀Family ε hε hε1) j) z ξ
    change (∑ j : Fin JV.size, ∑ k, ((gV₀Family ε hε hε1) j k).val z ξ) = _
    rw [Finset.sum_congr rfl (fun j _ ↦ hj j)]
    change (∑ j : Fin JV.size, (LinearMap.lTensorHom (R := ℂ) (E.Fiber (πS z))) _) =
      (LinearMap.lTensorHom (R := ℂ) (E.Fiber (πS z))) _
    exact (map_sum (LinearMap.lTensorHom (R := ℂ) (E.Fiber (πS z))) _ Finset.univ).symm
  have hsV₁factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) :
      (sV₁Family ε hε hε1).val z ξ =
        TensorProduct.map (LinearMap.id : Module.End ℂ (E'.Fiber (πS z))) (qfFamily ε z ξ) := by
    let ev : atlasGlobalSymbolSpace A₁₀ A₁₁ 1 →ₗ[ℂ] (U z →ₗ[ℂ] U' z) :=
      (LinearMap.proj ξ).comp ((LinearMap.proj z).comp
        (atlasGlobalSymbolSpace A₁₀ A₁₁ 1).subtype)
    have heval := (map_sum ev
      (fun i : Fin JV'.size ↦ ∑ j : Fin Rq.size, (gV₁Family ε hε hε1) i j)
        Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ map_sum ev
            (fun j : Fin Rq.size ↦ (gV₁Family ε hε hε1) i j) Finset.univ))
    refine heval.trans ?_
    have hj (j : Fin JV'.size) := associatedSphereTensorVerticalSymbol_eq_finiteTensorFactor
      (a := E'.rank) S E'.Fiber A σ A' σ' hA hA' (b j) (JV'.chart j)
      (JV'.chartCutoff E'.Fiber j)
      (fun _ hx ↦ hJV' j (JV'.chartCutoff_support_subset E'.Fiber j hx)) Rq.size Lq
      (γ1 j) (hγ1 j) (hcγ1 j) (hsγ1 j) (hbγ1 j) (hγone1 j)
      (κ1 j) (hκ1 j) (hcκ1 j) (hsκ1 j) (hκone1 j)
      ε (fun k ↦ ((gV₁Family ε hε hε1) j k).val)
      ((hgV₁Family ε hε hε1) j) z ξ
    change (∑ j : Fin JV'.size, ∑ k, ((gV₁Family ε hε hε1) j k).val z ξ) = _
    rw [Finset.sum_congr rfl (fun j _ ↦ hj j)]
    change (∑ j : Fin JV'.size, (LinearMap.lTensorHom (R := ℂ) (E'.Fiber (πS z))) _) =
      (LinearMap.lTensorHom (R := ℂ) (E'.Fiber (πS z))) _
    exact (map_sum (LinearMap.lTensorHom (R := ℂ) (E'.Fiber (πS z))) _ Finset.univ).symm
  have ha₀tensor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) (u : E.Fiber (πS z)) (v : D z) :
      (a₀Family ε hε hε1).val z ξ (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        e₁₀.linearEquiv z (pfFamily ε z ξ u ⊗ₜ[ℂ] v) := by
    have h := LinearMap.congr_fun
      ((hnU₀Family ε hε hε1).choose_spec.choose_spec.1 z ξ)
      (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v))
    change (a₀Family ε hε hε1).val z ξ (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
      e₁₀.linearEquiv z ((sH₀Family ε hε hε1).val z ξ
        ((e₀₀.linearEquiv z).symm (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)))) at h
    rw [LinearEquiv.symm_apply_apply, hsH₀factor ε hε hε1 z ξ,
      TensorProduct.map_tmul, LinearMap.id_apply] at h
    exact h
  have ha₁tensor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) (u : E.Fiber (πS z)) (v : D' z) :
      (a₁Family ε hε hε1).val z ξ (e₀₁.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        e₁₁.linearEquiv z (pfFamily ε z ξ u ⊗ₜ[ℂ] v) := by
    have h := LinearMap.congr_fun
      ((hnU₁Family ε hε hε1).choose_spec.choose_spec.1 z ξ)
      (e₀₁.linearEquiv z (u ⊗ₜ[ℂ] v))
    change (a₁Family ε hε hε1).val z ξ (e₀₁.linearEquiv z (u ⊗ₜ[ℂ] v)) =
      e₁₁.linearEquiv z ((sH₁Family ε hε hε1).val z ξ
        ((e₀₁.linearEquiv z).symm (e₀₁.linearEquiv z (u ⊗ₜ[ℂ] v)))) at h
    rw [LinearEquiv.symm_apply_apply, hsH₁factor ε hε hε1 z ξ,
      TensorProduct.map_tmul, LinearMap.id_apply] at h
    exact h
  have hb₀tensor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) (u : E.Fiber (πS z)) (v : D z) :
      (b₀Family ε hε hε1).val z ξ (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        e₀₁.linearEquiv z (u ⊗ₜ[ℂ] qfFamily ε z ξ v) := by
    have h := LinearMap.congr_fun
      ((hnV₀Family ε hε hε1).choose_spec.choose_spec.1 z ξ)
      (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v))
    change (b₀Family ε hε hε1).val z ξ (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
      e₀₁.linearEquiv z ((sV₀Family ε hε hε1).val z ξ
        ((e₀₀.linearEquiv z).symm (e₀₀.linearEquiv z (u ⊗ₜ[ℂ] v)))) at h
    rw [LinearEquiv.symm_apply_apply, hsV₀factor ε hε hε1 z ξ,
      TensorProduct.map_tmul, LinearMap.id_apply] at h
    exact h
  have hb₁tensor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
      (z : Z) (ξ : CotangentFiber (n := n + r) z) (u : E'.Fiber (πS z)) (v : D z) :
      (b₁Family ε hε hε1).val z ξ (e₁₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
        e₁₁.linearEquiv z (u ⊗ₜ[ℂ] qfFamily ε z ξ v) := by
    have h := LinearMap.congr_fun
      ((hnV₁Family ε hε hε1).choose_spec.choose_spec.1 z ξ)
      (e₁₀.linearEquiv z (u ⊗ₜ[ℂ] v))
    change (b₁Family ε hε hε1).val z ξ (e₁₀.linearEquiv z (u ⊗ₜ[ℂ] v)) =
      e₁₁.linearEquiv z ((sV₁Family ε hε hε1).val z ξ
        ((e₁₀.linearEquiv z).symm (e₁₀.linearEquiv z (u ⊗ₜ[ℂ] v)))) at h
    rw [LinearEquiv.symm_apply_apply, hsV₁factor ε hε hε1 z ξ,
      TensorProduct.map_tmul, LinearMap.id_apply] at h
    exact h
  -- The native constructor receives these exact original corner families and fixed Green models.
  let Eps := {ε : ℝ // 0 < ε ∧ ε ≤ 1}
  let : IsFiniteRank D := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ
  let : IsFiniteRank D' := isFiniteRank_associatedEquivariant S.toIsPrincipalBundle σ'
  let (z : Z) : FiniteDimensional ℂ (E.Fiber (πS z)) := finite_fiber (E := E.Fiber) (πS z)
  let (z : Z) : FiniteDimensional ℂ (E'.Fiber (πS z)) := finite_fiber (E := E'.Fiber) (πS z)
  let (z : Z) : FiniteDimensional ℂ (D z) := finite_fiber (E := D) z
  let (z : Z) : FiniteDimensional ℂ (D' z) := finite_fiber (E := D') z
  have hNativeFamily := exists_native_graded_family_of_tensor_symbols
    (n := n + r) (M := Z) (ι := Eps) (μ := η)
    N₀₀ N₁₀ N₀₁ N₁₁ (fun z ↦ E.Fiber (πS z)) (fun z ↦ E'.Fiber (πS z)) D D'
    e₀₀.linearEquiv e₁₀.linearEquiv e₀₁.linearEquiv e₁₁.linearEquiv
    k₀₀ k₁₀ k₀₁ k₁₁ c₀ c₁ d₀ d₁ hkPure₁₀ hkPure₀₁ hkPure₁₁
    (fun ε ↦ nativeU₀Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ nativeU₁Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ nativeV₀Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ nativeV₁Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ a₀Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ a₁Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ b₀Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ b₁Family ε.val ε.property.1 ε.property.2)
    (fun ε ↦ (hnU₀Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.2.1)
    (fun ε ↦ (hnU₁Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.2.1)
    (fun ε ↦ (hnV₀Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.2.1)
    (fun ε ↦ (hnV₁Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.2.1)
    (fun ε ↦ pfFamily ε.val) (fun ε ↦ qfFamily ε.val)
    (fun ε ↦ ha₀tensor ε.val ε.property.1 ε.property.2)
    (fun ε ↦ ha₁tensor ε.val ε.property.1 ε.property.2)
    (fun ε ↦ hb₀tensor ε.val ε.property.1 ε.property.2)
    (fun ε ↦ hb₁tensor ε.val ε.property.1 ε.property.2)
  -- Select only auxiliary sums; the four specified native corners and their metrics stay fixed.
  obtain ⟨NE, hNativeRest⟩ := hNativeFamily
  obtain ⟨NO, hNativeSums⟩ := hNativeRest
  have hSums := hNativeSums.2.2
  let := modelTopology (EuclideanSpace ℂ (Fin NE.rank)) NE.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin NO.rank)) NO.Fiber
  -- The selected sum isomorphisms retain the original component total-space topologies.
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ N₀₀.Fiber z × N₁₁.Fiber z)) :=
    sumTopology (E := N₀₀.Fiber) (F := N₁₁.Fiber)
  let : TopologicalSpace (TotalSpace Unit (fun z : Z ↦ N₁₀.Fiber z × N₀₁.Fiber z)) :=
    sumTopology (E := N₁₀.Fiber) (F := N₀₁.Fiber)
  let es := hSums.choose
  have hSums₁ := hSums.choose_spec
  let fs := hSums₁.choose
  have hSums₂ := hSums₁.choose_spec
  have hes₀ := hSums₂.choose
  have hSums₃ := hSums₂.choose_spec
  have hes₁ := hSums₃.choose
  have hSums₄ := hSums₃.choose_spec
  have hfs₀ := hSums₄.choose
  have hSums₅ := hSums₄.choose_spec
  have hfs₁ := hSums₅.choose
  have hSums₆ := hSums₅.choose_spec
  let kPlus := hSums₆.choose
  have hSums₇ := hSums₆.choose_spec
  let kMinus := hSums₇.choose
  have hkPlus := hSums₇.choose_spec.1
  have hkMinus := hSums₇.choose_spec.2.1
  have hFamily := hSums₇.choose_spec.2.2
  let AA : Fin 2 → SmoothFiniteComplexBundle (n := n + r) Z := ![N₀₀, N₁₁]
  let BB : Fin 2 → SmoothFiniteComplexBundle (n := n + r) Z := ![N₁₀, N₀₁]
  let DD (i : Fin 2) := Classical.choice
    (nonempty_smoothBundlePresentation (n := n + r) (r := (AA i).rank) (AA i).Fiber)
  let HH (i : Fin 2) := Classical.choice
    (nonempty_smoothBundlePresentation (n := n + r) (r := (BB i).rank) (BB i).Fiber)
  let Dplus : SmoothBundlePresentation (n := n + r) (r := NE.rank) NE.Fiber :=
    Classical.choice (nonempty_smoothBundlePresentation NE.Fiber)
  let Dminus : SmoothBundlePresentation (n := n + r) (r := NO.rank) NO.Fiber :=
    Classical.choice (nonempty_smoothBundlePresentation NO.Fiber)
  have hKdata (ε : Eps) := hFamily DD HH Dplus Dminus ε
  let KFamily (ε : Eps) := (hKdata ε).choose
  have hKmatrix (ε : Eps) := (hKdata ε).choose_spec.1
  have hSymbolData (ε : Eps) := (hKdata ε).choose_spec.2.2.2
  let piFamily (ε : Eps) := (hSymbolData ε).choose
  let qiFamily (ε : Eps) := (hSymbolData ε).choose_spec.choose
  have hpiFamily (ε : Eps) := (hSymbolData ε).choose_spec.choose_spec.1
  have hqiFamily (ε : Eps) := (hSymbolData ε).choose_spec.choose_spec.2.1
  have hqKdata (ε : Eps) := (hSymbolData ε).choose_spec.choose_spec.2.2
  let qKFamily (ε : Eps) := (hqKdata ε).choose
  have hqKclass (ε : Eps) := (hqKdata ε).choose_spec.1
  have hqKformula (ε : Eps) := (hqKdata ε).choose_spec.2
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hEllipticity :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
        ∀ ε : Eps, ε.val ≤ ε₀ →
          IsEllipticFullGlobalSymbol (n := n + r) (r := NE.rank) (q := NO.rank)
            NE.Fiber NO.Fiber 1 (qKFamily ε).val := by
    -- Apply the full-symbol ellipticity criterion to the specified tensor corners.
    have hEllObjects := exists_isEllipticFullGlobalSymbol_of_tensor_inverse_bounds
      (n := n + r) (M := Z) (ι := Fin N)
      N₀₀ N₁₀ N₀₁ N₁₁ NE NO
      (fun z ↦ E.Fiber (πS z)) (fun z ↦ E'.Fiber (πS z)) D D'
    have hEllCorners := hEllObjects
      e₀₀.linearEquiv e₁₀.linearEquiv e₀₁.linearEquiv e₁₁.linearEquiv
      k₀₀ k₁₀ k₀₁ k₁₁ c₀ c₁ d₀ d₁
    have hEllPairings := hEllCorners hkPure₀₀ hkPure₁₀ hkPure₀₁ hkPure₁₁
    have hEllSumMaps := hEllPairings es.linearEquiv fs.linearEquiv
    have hEllSumMetrics := hEllSumMaps kPlus kMinus
    have hEllSumPairings := hEllSumMetrics hkPlus hkMinus
    have hEllCover := hEllSumPairings gZ CC hCC KK hKK hKKsource hcover
    have hEllFactors := hEllCover pfFamily qfFamily
    have hEllAdjoints := hEllFactors piFamily qiFamily
    have hEllSymbol := hEllAdjoints (fun ε ↦ (qKFamily ε).val)
    have hEllFormula := hEllSymbol hqKformula
    exact hEllFormula (by
      intro i
      -- Select every local inverse-bound datum from this same finite-cover proof.
      have hi := hlocal i
      let ε₀ := hi.choose
      let R₀ := hi.choose_spec.choose
      let M₀ := hi.choose_spec.choose_spec.choose
      have hs := hi.choose_spec.choose_spec.choose_spec
      have hε₀ := hs.1
      have hε₀one := hs.2.1
      have hR₀ := hs.2.2.1
      have hM₀ := hs.2.2.2.1
      have hbound := hs.2.2.2.2
      refine ⟨ε₀, R₀, M₀, hε₀, hε₀one, hR₀, hM₀, ?_⟩
      intro ε hε z hz ξ hξ
      -- Identify the horizontal linear map before applying the chosen metric norms.
      let pRaw : E.Fiber (πS z) →ₗ[ℂ] E'.Fiber (πS z) :=
        (∑ i : Fin C.size, ∑ j : Fin JH.size,
          let cov := split (covectorInChart (CP i j) z ξ)
          ((JH.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
            productFrequencyCutoff ε.val ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
              (C.piece i).globalSymbolFunction (πS z)
                (covectorFromChart (C.piece i).chart (πS z) cov.1)).toLinearMap
      have hpRaw : pRaw = pfFamily ε.val z ξ := by
        dsimp only [pRaw, pfFamily]
        rw [ContinuousLinearMap.toLinearMap_sum]
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [ContinuousLinearMap.toLinearMap_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact ContinuousLinearMap.toLinearMap_smul _ _
      have hpiRaw : ∀ u v, (c₁ z).inner (pRaw u) v =
          (c₀ z).inner u (piFamily ε z ξ v) := by
        intro u v
        rw [hpRaw]
        exact hpiFamily ε z ξ u v
      -- Preserve the original scalar actions before replacing the fiber norms.
      let : Module ℂ (E.Fiber (πS z)) := inferInstance
      let : Module ℂ (E'.Fiber (πS z)) := inferInstance
      -- Install exactly the four cores appearing in the required pointwise bound.
      let : InnerProductSpace.Core ℂ (E.Fiber (πS z)) := c₀ z
      let : InnerProductSpace.Core ℂ (E'.Fiber (πS z)) := c₁ z
      let : InnerProductSpace.Core ℂ (D z) := d₀ z
      let : InnerProductSpace.Core ℂ (D' z) := d₁ z
      let : NormedAddCommGroup (E.Fiber (πS z)) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      let : NormedAddCommGroup (E'.Fiber (πS z)) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      let : NormedAddCommGroup (D z) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      let : NormedAddCommGroup (D' z) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      let : InnerProductSpace ℂ (E.Fiber (πS z)) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      let : InnerProductSpace ℂ (E'.Fiber (πS z)) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      let : InnerProductSpace ℂ (D z) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      let : InnerProductSpace ℂ (D' z) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      let HasInverseBound (p : E.Fiber (πS z) →ₗ[ℂ] E'.Fiber (πS z)) : Prop :=
        let T := reciprocalTensorSymbol p (piFamily ε z ξ)
          (qfFamily ε.val z ξ) (qiFamily ε z ξ)
        Function.Bijective T ∧ ∀ u,
          ‖u‖ ≤ (M₀ / (1 + ‖covectorInChart (CC i) z ξ‖)) * ‖T u‖
      have hbRaw : HasInverseBound pRaw :=
        hbound ε.val ε.property.1 hε z hz ξ hξ
          (piFamily ε z ξ) (qiFamily ε z ξ) hpiRaw (hqiFamily ε z ξ)
      change HasInverseBound (pfFamily ε.val z ξ)
      exact (congrArg HasInverseBound hpRaw).mp hbRaw)
  let ε₀ := hEllipticity.choose
  have hε₀ := hEllipticity.choose_spec.1
  have hε₀one := hEllipticity.choose_spec.2.1
  have hfull := hEllipticity.choose_spec.2.2
  let ε : Eps := ⟨ε₀, hε₀, hε₀one⟩
  have hKell : (KFamily ε).IsElliptic :=
    ⟨qKFamily ε, hqKclass ε, hfull ε le_rfl⟩
  -- Recover the actual finite O/U/I formulas through the same native section maps.
  have hUn (w : A₀₀.smoothSections) :
      (nativeU₀Family ε.val ε.property.1 ε.property.2).toLinearMap (S₀₀ w) =
        S₁₀ (∑ i, ∑ j, OH₀ i j
          (UHloc₀Family ε.val ε.property.1 ε.property.2 i j (IH₀ i j w))) := by
    -- Identify the horizontal chart operators with their inclusion, local action and extension.
    have hpiece (i : Fin C.size) (j : Fin JH.size) :
        (QH₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap w =
          OH₀ i j (UHloc₀Family ε.val ε.property.1 ε.property.2 i j (IH₀ i j w)) := by
      have hQ : (QH₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap =
          (OH₀ i j).comp
            ((UHloc₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap.comp
              (IH₀ i j)) :=
        (hDataH₀ ε.val ε.property.1 ε.property.2).1 i j
      exact LinearMap.congr_fun hQ w
    have hinner (i : Fin C.size) :
        (∑ j : Fin JH.size, (QH₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap) w =
          ∑ j : Fin JH.size,
            OH₀ i j (UHloc₀Family ε.val ε.property.1 ε.property.2 i j (IH₀ i j w)) :=
      (LinearMap.sum_apply Finset.univ
        (fun j : Fin JH.size ↦ (QH₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap)
        w).trans (Finset.sum_congr rfl (fun j _ ↦ hpiece i j))
    have hsum := (LinearMap.sum_apply Finset.univ
      (fun i : Fin C.size ↦
        ∑ j : Fin JH.size, (QH₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap)
      w).trans (Finset.sum_congr rfl (fun i _ ↦ hinner i))
    calc
      _ = S₁₀ ((Uat₀Family ε.val ε.property.1 ε.property.2).toLinearMap
          (S₀₀.symm (S₀₀ w))) :=
        LinearMap.congr_fun
          (hnU₀Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.1 (S₀₀ w)
      _ = S₁₀ ((Uat₀Family ε.val ε.property.1 ε.property.2).toLinearMap w) :=
        congrArg (fun x ↦ S₁₀ ((Uat₀Family ε.val ε.property.1 ε.property.2).toLinearMap x))
          (S₀₀.symm_apply_apply w)
      _ = _ := congrArg S₁₀
        ((LinearMap.congr_fun (hUat₀Family ε.val ε.property.1 ε.property.2) w).trans hsum)
  have hVn (w : A₀₀.smoothSections) :
      (nativeV₀Family ε.val ε.property.1 ε.property.2).toLinearMap (S₀₀ w) =
        S₀₁ (∑ i, ∑ j, O0 i j
          (UVloc₀Family ε.val ε.property.1 ε.property.2 i j (I0 i j w))) := by
    -- Identify the vertical chart operators with their inclusion, local action and extension.
    have hpiece (i : Fin JV.size) (j : Fin Rq.size) :
        (QV₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap w =
          O0 i j (UVloc₀Family ε.val ε.property.1 ε.property.2 i j (I0 i j w)) := by
      have hQ : (QV₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap =
          (O0 i j).comp
            ((UVloc₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap.comp
              (I0 i j)) :=
        (hDataV₀ ε.val ε.property.1 ε.property.2).1 i j
      exact LinearMap.congr_fun hQ w
    have hinner (i : Fin JV.size) :
        (∑ j : Fin Rq.size, (QV₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap) w =
          ∑ j : Fin Rq.size,
            O0 i j (UVloc₀Family ε.val ε.property.1 ε.property.2 i j (I0 i j w)) :=
      (LinearMap.sum_apply Finset.univ
        (fun j : Fin Rq.size ↦ (QV₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap)
        w).trans (Finset.sum_congr rfl (fun j _ ↦ hpiece i j))
    have hsum := (LinearMap.sum_apply Finset.univ
      (fun i : Fin JV.size ↦
        ∑ j : Fin Rq.size, (QV₀Family ε.val ε.property.1 ε.property.2 i j).toLinearMap)
      w).trans (Finset.sum_congr rfl (fun i _ ↦ hinner i))
    calc
      _ = S₀₁ ((Vat₀Family ε.val ε.property.1 ε.property.2).toLinearMap
          (S₀₀.symm (S₀₀ w))) :=
        LinearMap.congr_fun
          (hnV₀Family ε.val ε.property.1 ε.property.2).choose_spec.choose_spec.2.1 (S₀₀ w)
      _ = S₀₁ ((Vat₀Family ε.val ε.property.1 ε.property.2).toLinearMap w) :=
        congrArg (fun x ↦ S₀₁ ((Vat₀Family ε.val ε.property.1 ε.property.2).toLinearMap x))
          (S₀₀.symm_apply_apply w)
      _ = _ := congrArg S₀₁
        ((LinearMap.congr_fun (hVat₀Family ε.val ε.property.1 ε.property.2) w).trans hsum)
  let Kov0 (i : Fin JV.size) (j : Fin Rq.size) : AtlasChartCutoff A' (Lq j).chart := {
    (Lq j).output with
      cutoff := κ0 i j
      smooth_cutoff := hκ0 i j
      compact_support := hcκ0 i j
      support_subset := hsκ0 i j }
  -- The original forward graph theorem now receives its actual constructed elliptic first column.
  exact associated_forward_joint_reverse_bound
    S E.Fiber F σ hσ F' σ' hσ' E'.Fiber
    ν k k' Q hQ (by exact ⟨qfull, hQpr, hqfull⟩) L₁ C L₀
    Co hCoF hCo hCoOne κ hκ hκK hκs hκOne
    Rq.size JV b hJV Co0 hbγ0 Lq Kov0 IH₀ OH₀ hIH₀ hOH₀ I0 O0 hI0 hO0
    Li Li₁ Lo l₀₀ hl₀₀ l₀₁ hl₀₁ l₁₀ hl₁₀ AA BB k₀₀ k₀₁ k₁₀ η
    e₀₀ he₀₀ hi₀₀ e₀₁ he₀₁ hi₀₁ e₁₀ he₁₀ hi₁₀ hk₀₀ hk₀₁ hk₁₀
    ε.val ε.property.1
    (UHloc₀Family ε.val ε.property.1 ε.property.2)
    (UVloc₀Family ε.val ε.property.1 ε.property.2)
    (hDataH₀ ε.val ε.property.1 ε.property.2).2.1
    (hDataV₀ ε.val ε.property.1 ε.property.2).2.1
    NE NO es.linearEquiv fs.linearEquiv hes₀ hes₁ hfs₀ hfs₁
    (nativeU₀Family ε.val ε.property.1 ε.property.2)
    (nativeV₀Family ε.val ε.property.1 ε.property.2)
    ((nativeV₁Family ε.val ε.property.1 ε.property.2).metricFormalAdjoint k₁₀ k₁₁)
    ((nativeU₁Family ε.val ε.property.1 ε.property.2).metricFormalAdjoint k₀₁ k₁₁)
    DD HH Dplus Dminus (KFamily ε) hKell (hKmatrix ε) hUn hVn

end AtiyahSinger
