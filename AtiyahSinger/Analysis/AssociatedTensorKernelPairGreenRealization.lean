/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorAdjointGreenKernelRealization
public import AtiyahSinger.Analysis.AssociatedTensorGreenKernelRealization

/-!
# Two actual Green kernel comparisons for one coefficient operator

Public module ID: M0177.

The full kernel of the specified sphere metric adjoint gives one associated
coefficient PDO. Its smooth kernel and its metric-adjoint kernel identify the
two prescribed closed joint kernels in the same four upstairs native models.
The two original Green constructions are compared through their complete PDO
actions and their values on every original associated representative. No model,
metric, representation, or joint graph is reselected.

This is the pair used twice in the four-corner associated product assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w w'

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  tensorTopology continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a a' : ℕ} {P : Type u} {B : Type v}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type w) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type w') [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z
local notation "C" => fun b : B ↦ E b ⊗[ℂ] K b
local notation "C'" => fun b : B ↦ E' b ⊗[ℂ] K b

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 32000000 in
-- The extended limit accommodates both joint-kernel comparisons over the same coefficient PDO.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- One actual coefficient PDO gives both prescribed joint-kernel comparisons and bounds. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_kernelPairGreenRealization
    (μ : Measure B) [IsFiniteMeasure μ] [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C₀.baseOperator.IsElliptic)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
    (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (y : Y) (s t : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y s) (σ.linearMap g y t) = k.pairing y s t)
    (hk' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (y : Y) (s t : F'.Fiber y),
      k'.pairing (g • y) (σ'.linearMap g y s) (σ'.linearMap g y t) = k'.pairing y s t)
    (Qn : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1) (hQn : Qn.IsElliptic)
    (hQng : Qn.IsEquivariant IG σ σ' hσ hσ')
    (L₀ : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L₁ : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (Jbase : SmoothBundlePresentation (n := n) (r := a) E)
    (Jbase' : SmoothBundlePresentation (n := n) (r := a') E')
    (b : Fin Jbase.size → B) (b' : Fin Jbase'.size → B)
    (hJbase : ∀ j, tsupport (Jbase.cutoff j) ⊆ (S.trivialization (b j)).baseSet)
    (hJbase' : ∀ j, tsupport (Jbase'.cutoff j) ⊆ (S.trivialization (b' j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let Q := Qn.toAtlasPseudodifferentialOperator
    let hQ := (Qn.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQng
    let Qa := (Qn.metricFormalAdjoint k k').toAtlasPseudodifferentialOperator
    let hQa := ((Qn.metricFormalAdjoint k k').isEquivariant_toAtlas_iff
      IG σ' σ hσ' hσ).mpr
        (Qn.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQng)
    ∀ (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Qa.toLinearMap.ker),
      (∀ (g : G) (y : Y) (v : Fin ρ.dimension → ℂ),
        (e (ρ.representation g v)).val.val (g • y) =
          σ'.linearMap g y ((e v).val.val y)) →
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI : TopologicalSpace (TotalSpace Unit U) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
      letI : TopologicalSpace (TotalSpace Unit U') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
      letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
      letI : TopologicalSpace (TotalSpace Unit C') := tensorTopology (E := E') (F := K)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
      letI : IsSmoothPositiveMeasure (n := n + r) η :=
        isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      let AU := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
      let AU' := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hA'
      let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ)
      let AC' := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρ)
      let H := C₀.horizontalLift S E A' σ' E' hA'
      let _V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
      let _V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA' Q hQ
      let Va := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A σ hA Qa hQa
      let Va' := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hA' A σ hA Qa hQa
      let Pc := C₀.coefficientOperator S E E' ρ
      ∀ (_Γ₀ : AtlasBundlePresentation AT) (_Γ₁ : AtlasBundlePresentation AU)
        (_Γ₂ : AtlasBundlePresentation AT') (_Γ₃ : AtlasBundlePresentation AU')
        (l₀ : ContinuousHermitianMetric T) (l₁ : ContinuousHermitianMetric U)
        (l₂ : ContinuousHermitianMetric T') (l₃ : ContinuousHermitianMetric U')
        (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
        (NC₀ NC₁ : SmoothFiniteComplexBundle (n := n) B)
        (N₀ N₁ N₂ N₃ : SmoothFiniteComplexBundle (n := n + r) Z)
        (kC₀ : SmoothHermitianMetric (n := n) (r := NC₀.rank) NC₀.Fiber)
        (kC₁ : SmoothHermitianMetric (n := n) (r := NC₁.rank) NC₁.Fiber)
        (k₀ : SmoothHermitianMetric (n := n + r) (r := N₀.rank) N₀.Fiber)
        (k₁ : SmoothHermitianMetric (n := n + r) (r := N₁.rank) N₁.Fiber)
        (k₂ : SmoothHermitianMetric (n := n + r) (r := N₂.rank) N₂.Fiber)
        (k₃ : SmoothHermitianMetric (n := n + r) (r := N₃.rank) N₃.Fiber),
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
        ∀ (cIso₀ : Iso C NC₀.Fiber) (cIso₁ : Iso C' NC₁.Fiber)
          (tIso₀ : Iso T N₀.Fiber) (tIso₁ : Iso U N₁.Fiber) (tIso₂ : Iso T' N₂.Fiber)
          (tIso₃ : Iso U' N₃.Fiber)
          (heC₀ : IsSmoothAtlasBundleMap AC (nativeSmoothComplexBundleAtlas NC₀.Fiber)
            cIso₀.toHom.linearMap)
          (hiC₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NC₀.Fiber) AC
            cIso₀.symm.toHom.linearMap)
          (heC₁ : IsSmoothAtlasBundleMap AC' (nativeSmoothComplexBundleAtlas NC₁.Fiber)
            cIso₁.toHom.linearMap)
          (hiC₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NC₁.Fiber) AC'
            cIso₁.symm.toHom.linearMap)
          (heT₀ : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N₀.Fiber)
            tIso₀.toHom.linearMap)
          (hiT₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀.Fiber) AT
            tIso₀.symm.toHom.linearMap)
          (heT₁ : IsSmoothAtlasBundleMap AU (nativeSmoothComplexBundleAtlas N₁.Fiber)
            tIso₁.toHom.linearMap)
          (hiT₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) AU
            tIso₁.symm.toHom.linearMap)
          (heT₂ : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N₂.Fiber)
            tIso₂.toHom.linearMap)
          (hiT₂ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₂.Fiber) AT'
            tIso₂.symm.toHom.linearMap)
          (heT₃ : IsSmoothAtlasBundleMap AU' (nativeSmoothComplexBundleAtlas N₃.Fiber)
            tIso₃.toHom.linearMap)
          (hiT₃ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₃.Fiber) AU'
            tIso₃.symm.toHom.linearMap),
          AT.IsSmoothHermitianMetric l₀ → AU.IsSmoothHermitianMetric l₁ →
          AT'.IsSmoothHermitianMetric l₂ → AU'.IsSmoothHermitianMetric l₃ →
          (∀ (x : B) (u v : C x),
            kC₀.pairing x (cIso₀.linearEquiv x u) (cIso₀.linearEquiv x v) =
              (c₀.toCore x).inner u v) →
          (∀ (x : B) (u v : C' x),
            kC₁.pairing x (cIso₁.linearEquiv x u) (cIso₁.linearEquiv x v) =
              (c₁.toCore x).inner u v) →
          (∀ (x : Z) (u v : T x),
            k₀.pairing x (tIso₀.linearEquiv x u) (tIso₀.linearEquiv x v) =
              (l₀.toCore x).inner u v) →
          (∀ (x : Z) (u v : U x),
            k₁.pairing x (tIso₁.linearEquiv x u) (tIso₁.linearEquiv x v) =
              (l₁.toCore x).inner u v) →
          (∀ (x : Z) (u v : T' x),
            k₂.pairing x (tIso₂.linearEquiv x u) (tIso₂.linearEquiv x v) =
              (l₂.toCore x).inner u v) →
          (∀ (x : Z) (u v : U' x),
            k₃.pairing x (tIso₃.linearEquiv x u) (tIso₃.linearEquiv x v) =
              (l₃.toCore x).inner u v) →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F.Fiber y),
            (l₀.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
              h.pairing (projection p) u v * k.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F.Fiber y),
            (l₁.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
              h'.pairing (projection p) u v * k.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F'.Fiber y),
            (l₂.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E σ' p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E σ' p y (v ⊗ₜ[ℂ] t)) =
              h.pairing (projection p) u v * k'.pairing y s t) →
          (∀ (p : P) (y : Y) (u v : E' (projection p)) (s t : F'.Fiber y),
            (l₃.toCore (associatedBundleMk G P Y p y)).inner
                (associatedSphereTensorFiberEquiv S E' σ' p y (u ⊗ₜ[ℂ] s))
                (associatedSphereTensorFiberEquiv S E' σ' p y (v ⊗ₜ[ℂ] t)) =
              h'.pairing (projection p) u v * k'.pairing y s t) →
          (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₀.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h.pairing (projection p) u v *
                ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
          (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₁.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h'.pairing (projection p) u v *
                ∫ y, k'.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
          ∀ H₁a : AU'.smoothSections →ₗ[ℂ] AT'.smoothSections,
            (∀ u v, (∫ z, (l₃.toCore z).inner ((H u).val z) (v.val z) ∂η) =
              ∫ z, (l₂.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) →
          let S₀ := (atlasSmoothSectionEquiv AC
            (nativeSmoothComplexBundleAtlas NC₀.Fiber) cIso₀ heC₀ hiC₀).trans
              (nativeSmoothSectionLinearEquiv NC₀.Fiber)
          let S₁ := (atlasSmoothSectionEquiv AC'
            (nativeSmoothComplexBundleAtlas NC₁.Fiber) cIso₁ heC₁ hiC₁).trans
              (nativeSmoothSectionLinearEquiv NC₁.Fiber)
          let T₀ := (atlasSmoothSectionEquiv AT
            (nativeSmoothComplexBundleAtlas N₀.Fiber) tIso₀ heT₀ hiT₀).trans
              (nativeSmoothSectionLinearEquiv N₀.Fiber)
          let T₁ := (atlasSmoothSectionEquiv AU
            (nativeSmoothComplexBundleAtlas N₁.Fiber) tIso₁ heT₁ hiT₁).trans
              (nativeSmoothSectionLinearEquiv N₁.Fiber)
          let T₂ := (atlasSmoothSectionEquiv AT'
            (nativeSmoothComplexBundleAtlas N₂.Fiber) tIso₂ heT₂ hiT₂).trans
              (nativeSmoothSectionLinearEquiv N₂.Fiber)
          let T₃ := (atlasSmoothSectionEquiv AU'
            (nativeSmoothComplexBundleAtlas N₃.Fiber) tIso₃ heT₃ hiT₃).trans
              (nativeSmoothSectionLinearEquiv N₃.Fiber)
          let i₀ := (k₀.smoothToL2 η).comp T₀.toLinearMap
          let i₁ := (k₁.smoothToL2 η).comp T₁.toLinearMap
          let i₂ := (k₂.smoothToL2 η).comp T₂.toLinearMap
          let i₃ := (k₃.smoothToL2 η).comp T₃.toLinearMap
          ∀ Rf : k₂.L2SectionSpace η →ₗ.[ℂ] (k₃.L2SectionSpace η × k₀.L2SectionSpace η),
            Rf.graph = (i₂.prod ((i₃.comp H).prod (i₀.comp Va))).range.topologicalClosure →
          ∀ R : k₃.L2SectionSpace η →ₗ.[ℂ] (k₁.L2SectionSpace η × k₂.L2SectionSpace η),
            R.graph = (i₃.prod ((i₁.comp Va').prod (i₂.comp H₁a))).range.topologicalClosure →
            ∃ ev : Hom ((πS : Z → B) *ᵖ K) D',
              (∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
                ev.linearMap (associatedBundleMk G P Y p y)
                    (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
                  associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p y rfl ((e v).val.val y)) ∧
              ∃ (Φ : AC.smoothSections ≃ₗ[ℂ] Va.ker) (Ψ : AC'.smoothSections ≃ₗ[ℂ] Va'.ker),
                (∀ u z, (Φ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                (∀ u z, (Ψ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                ∃ Pn : PseudodifferentialOperator (n := n) (r := NC₀.rank) (q := NC₁.rank)
                    NC₀.Fiber NC₁.Fiber μ 1,
                  Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
                  Pn.IsElliptic ∧
                  ∃ (κf : Pn.toLinearMap.ker ≃ₗ[ℂ] Rf.ker)
                    (κ : (Pn.metricFormalAdjoint kC₀ kC₁).toLinearMap.ker ≃ₗ[ℂ] R.ker),
                    (∀ u, (κf u).val = i₂ (Φ (S₀.symm u.val)).val) ∧
                    (∀ u, (κ u).val = i₃ (Ψ (S₁.symm u.val)).val) ∧
                    ∃ cForward cReverse : ℝ, 0 ≤ cForward ∧ 0 ≤ cReverse ∧
                      (∀ u : Rf.domain, (u : k₂.L2SectionSpace η) ∈ Rf.ker.orthogonal →
                        ‖(u : k₂.L2SectionSpace η)‖ ≤ cForward * ‖Rf u‖) ∧
                      (∀ u : R.domain, (u : k₃.L2SectionSpace η) ∈ R.ker.orthogonal →
                        ‖(u : k₃.L2SectionSpace η)‖ ≤ cReverse * ‖R u‖) ∧
                      IsClosed (Rf.toFun.range : Set
                        (k₃.L2SectionSpace η × k₀.L2SectionSpace η)) ∧
                      IsClosed (R.toFun.range : Set
                        (k₁.L2SectionSpace η × k₂.L2SectionSpace η)) ∧
                      FiniteDimensional ℂ Rf.ker ∧ FiniteDimensional ℂ R.ker := by
  classical
  -- Both constructions retain the given sphere PDO and its literal metric adjoint.
  let Qna := Qn.metricFormalAdjoint k k'
  have hQna : Qna.IsElliptic := (Qn.isElliptic_metricFormalAdjoint_iff k k').mpr hQn
  have hQnag : Qna.IsEquivariant IG σ' σ hσ' hσ :=
    Qn.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQng
  have hforward := C₀.exists_associated_greenKernelRealization
    S E E' F' F σ' σ hσ' hσ ρ μ ν hν hC h h' k' k hk' hk Qna hQna hQnag
      L₁ L₀ Jbase Jbase' b b' hJbase hJbase'
  have hreverse := C₀.exists_associated_adjointGreenKernelRealization
    S E E' F F' σ σ' hσ hσ' ρ μ ν hν hC h h' k k' hk hk' Qn hQn hQng
      L₀ L₁ Jbase Jbase' b b' hJbase hJbase'
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  intro A A' hA hA' Q hQ Qa hQa e he
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let : TopologicalSpace (TotalSpace Unit U) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit U') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D')
  let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
  let : TopologicalSpace (TotalSpace Unit C') := tensorTopology (E := E') (F := K)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro η
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  intro AT AT' AU AU' AC AC' H V V' Va Va' Pc Γ₀ Γ₁ Γ₂ Γ₃ l₀ l₁ l₂ l₃ c₀ c₁
    NC₀ NC₁ N₀ N₁ N₂ N₃ kC₀ kC₁ k₀ k₁ k₂ k₃
  let := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
  intro cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ tIso₃ heC₀ hiC₀ heC₁ hiC₁
    heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂ heT₃ hiT₃ hl₀ hl₁ hl₂ hl₃
    hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hmetricT₃
    hpure₀ hpure₁ hpure₂ hpure₃ hgram₀ hgram₁ H₁a hH₁a
    S₀ S₁ T₀ T₁ T₂ T₃ i₀ i₁ i₂ i₃ Rf hRf R hR
  -- Apply both Green theorems to the original four models and the same coefficient metrics.
  obtain ⟨evf, hevf, Φf, Ψf, hΦf, hΨf, Pf, hPf, hPfEll, hfc⟩ :=
    hforward e he Γ₂ Γ₃ Γ₀ l₂ l₃ l₀ c₀ c₁ NC₀ NC₁ N₂ N₃ N₀
      kC₀ kC₁ k₂ k₃ k₀ cIso₀ cIso₁ tIso₂ tIso₃ tIso₀
      heC₀ hiC₀ heC₁ hiC₁ heT₂ hiT₂ heT₃ hiT₃ heT₀ hiT₀
      hl₂ hl₃ hl₀ hmetricC₀ hmetricC₁ hmetricT₂ hmetricT₃ hmetricT₀
      hpure₂ hpure₃ hgram₀ hgram₁ Rf hRf
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pr, hPr, hPrEll, hrc⟩ :=
    hreverse e he Γ₀ Γ₁ Γ₂ Γ₃ l₀ l₁ l₂ l₃ c₀ c₁ NC₀ NC₁ N₀ N₁ N₂ N₃
      kC₀ kC₁ k₀ k₁ k₂ k₃ cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ tIso₃
      heC₀ hiC₀ heC₁ hiC₁ heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂ heT₃ hiT₃
      hl₀ hl₁ hl₂ hl₃ hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hmetricT₃
      hpure₀ hpure₁ hpure₂ hpure₃ hgram₀ hgram₁ H₁a hH₁a R hR
  -- Equality of their complete operator actions identifies the two coefficient PDOs.
  have hPDOext (P₁ P₂ : PseudodifferentialOperator
      (n := n) (r := NC₀.rank) (q := NC₁.rank) NC₀.Fiber NC₁.Fiber μ 1)
      (heq : P₁.toLinearMap = P₂.toLinearMap) : P₁ = P₂ := by
    cases P₁
    cases P₂
    cases heq
    rfl
  have hPrPf : Pr = Pf := hPDOext Pr Pf (hPr.trans hPf.symm)
  rw [hPrPf] at hrc
  -- The same original full-kernel coordinates determine the entire evaluation map.
  have hevEq : ev = evf := by
    apply Hom.ext
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
        ρ.representation z.1 rfl).2 v
      exact (hev z.1 z.2 w).trans (hevf z.1 z.2 w).symm
  rw [hevEq] at hΦ hΨ
  -- The full section equivalences agree pointwise through that same evaluation.
  have hsections : Φ = Φf ∧ Ψ = Ψf := by
    constructor
    · apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact (hΦ u z).trans (hΦf u z).symm
    · apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact (hΨ u z).trans (hΨf u z).symm
  rw [hsections.2] at hrc
  obtain ⟨κf, hκf, cf, hcf, hfBound, hfRange, hfFinite⟩ := hfc
  obtain ⟨κ, hκ, cr, hcr, hrBound, hrRange, hrFinite⟩ := hrc
  exact ⟨evf, hevf, Φf, Ψf, hΦf, hΨf, Pf, hPf, hPfEll, κf, κ, hκf, hκ,
    cf, cr, hcf, hcr, hfBound, hrBound, hfRange, hrRange, hfFinite, hrFinite⟩

end AtiyahSinger
