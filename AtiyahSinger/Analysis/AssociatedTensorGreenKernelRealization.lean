/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCoefficientEllipticity
public import AtiyahSinger.Analysis.AssociatedKernelL2Embedding
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalKernelRealization
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalVerticalCommutation
public import AtiyahSinger.Analysis.AssociatedTensorVerticalGreenIdentity
public import AtiyahSinger.Analysis.AssociatedTensorVerticalL2Realization
public import AtiyahSinger.Analysis.AtlasNativeEllipticConjugate
public import AtiyahSinger.Analysis.ClosedJointGreenBound
public import AtiyahSinger.Analysis.EquivariantGreenAtlasData
public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev

/-!
# Associated Green maps and coefficient-kernel comparison

Public module ID: M0158.

An elliptic equivariant sphere PDO and elliptic base localization yield
sphere Green data and a kernel projection. In the supplied compatible
models, their vertical L² extensions and coefficient evaluation isometries
compare the joint graph closure with the native coefficient PDO. The
coefficient conjugate remains elliptic, giving an explicit joint-kernel
equivalence, a bound on its orthogonal complement, closed range and a
finite-dimensional kernel.
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
set_option maxHeartbeats 64000000 in
-- The extended limit accommodates the full original Green-kernel and closed-range assembly.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Original elliptic data construct the associated closed-kernel and closed-range comparison. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_greenKernelRealization
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
    ∀ (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker),
      (∀ (g : G) (y : Y) (v : Fin ρ.dimension → ℂ),
        (e (ρ.representation g v)).val.val (g • y) =
          σ.linearMap g y ((e v).val.val y)) →
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
      let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ)
      let AC' := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρ)
      let H := C₀.horizontalLift S E A σ E' hA
      let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
      let V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA' Q hQ
      let Pc := C₀.coefficientOperator S E E' ρ
      ∀ (_Γ₀ : AtlasBundlePresentation AT) (_Γ₁ : AtlasBundlePresentation AU)
        (_Γ₂ : AtlasBundlePresentation AT')
        (l₀ : ContinuousHermitianMetric T) (l₁ : ContinuousHermitianMetric U)
        (l₂ : ContinuousHermitianMetric T')
        (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
        (NC₀ NC₁ : SmoothFiniteComplexBundle (n := n) B)
        (N₀ N₁ N₂ : SmoothFiniteComplexBundle (n := n + r) Z)
        (kC₀ : SmoothHermitianMetric (n := n) (r := NC₀.rank) NC₀.Fiber)
        (kC₁ : SmoothHermitianMetric (n := n) (r := NC₁.rank) NC₁.Fiber)
        (k₀ : SmoothHermitianMetric (n := n + r) (r := N₀.rank) N₀.Fiber)
        (k₁ : SmoothHermitianMetric (n := n + r) (r := N₁.rank) N₁.Fiber)
        (k₂ : SmoothHermitianMetric (n := n + r) (r := N₂.rank) N₂.Fiber),
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
        ∀ (cIso₀ : Iso C NC₀.Fiber) (cIso₁ : Iso C' NC₁.Fiber)
          (tIso₀ : Iso T N₀.Fiber) (tIso₁ : Iso U N₁.Fiber) (tIso₂ : Iso T' N₂.Fiber)
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
            tIso₂.symm.toHom.linearMap),
          AT.IsSmoothHermitianMetric l₀ → AU.IsSmoothHermitianMetric l₁ →
          AT'.IsSmoothHermitianMetric l₂ →
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
          (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₀.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h.pairing (projection p) u v *
                ∫ y, k.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
          (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρ.dimension → ℂ),
            (c₁.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
              h'.pairing (projection p) u v *
                ∫ y, k.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν) →
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
          let i₀ := (k₀.smoothToL2 η).comp T₀.toLinearMap
          let i₁ := (k₁.smoothToL2 η).comp T₁.toLinearMap
          let i₂ := (k₂.smoothToL2 η).comp T₂.toLinearMap
          ∀ R : k₀.L2SectionSpace η →ₗ.[ℂ] (k₁.L2SectionSpace η × k₂.L2SectionSpace η),
            R.graph = (i₀.prod ((i₁.comp H).prod (i₂.comp V))).range.topologicalClosure →
            ∃ ev : Hom ((πS : Z → B) *ᵖ K) D,
              (∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
                ev.linearMap (associatedBundleMk G P Y p y)
                    (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
                  associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
              ∃ (Φ : AC.smoothSections ≃ₗ[ℂ] V.ker) (Ψ : AC'.smoothSections ≃ₗ[ℂ] V'.ker),
                (∀ u z, (Φ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                (∀ u z, (Ψ u).val.val z =
                  TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
                ∃ Pn : PseudodifferentialOperator (n := n) (r := NC₀.rank) (q := NC₁.rank)
                    NC₀.Fiber NC₁.Fiber μ 1,
                  Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
                  Pn.IsElliptic ∧
                  ∃ κ : Pn.toLinearMap.ker ≃ₗ[ℂ] R.ker,
                    (∀ u, (κ u).val = i₀ (Φ (S₀.symm u.val)).val) ∧
                    ∃ cBound : ℝ, 0 ≤ cBound ∧
                      (∀ u : R.domain, (u : k₀.L2SectionSpace η) ∈ R.ker.orthogonal →
                        ‖(u : k₀.L2SectionSpace η)‖ ≤ cBound * ‖R u‖) ∧
                      IsClosed (R.toFun.range : Set (k₁.L2SectionSpace η × k₂.L2SectionSpace η)) ∧
                      FiniteDimensional ℂ R.ker := by
  classical
  -- Obtain the equivariant sphere Green map and kernel projection.
  have hGreenData := Qn.exists_equivariantGreenAtlasData IG F F' σ σ' hσ hσ' k k'
    hk hk' ν hν hQng L₀ L₁ hQn
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  intro A A' hA hA' Q hQ e he
  obtain ⟨Green, J, hGreen, hJ, _, hQJ, hGQ, Rzero, hRzero, Jzero, hJzero⟩ := hGreenData
  have hkernelData := C₀.exists_horizontalLift_coefficientKernelRealization
    S E E' A σ hA A' σ' hA' ρ Q hQ e he
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
  intro AT AT' AU AC AC' H V V' Pc Γ₀ Γ₁ Γ₂ l₀ l₁ l₂ c₀ c₁ NC₀ NC₁ N₀ N₁ N₂
    kC₀ kC₁ k₀ k₁ k₂
  let := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
  intro cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ heC₀ hiC₀ heC₁ hiC₁ heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂
    hl₀ hl₁ hl₂ hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hpure₀ hpure₁ hgram₀ hgram₁
    S₀ S₁ T₀ T₁ T₂ i₀ i₁ i₂ R hR
  -- Retain the full-kernel evaluation equivalences and their horizontal intertwining.
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, hH⟩ := hkernelData
  let J₀ := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A σ hA J hJ
  let J₁ := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A σ hA J hJ
  let G₀ := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A σ hA Green hGreen
  -- All three bounded lifts are constructed in the originally supplied upstairs models.
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : k₀.L2SectionSpace η →L[ℂ] k₀.L2SectionSpace η,
      ∀ u : AT.smoothSections, P₀ (i₀ u) = i₀ (J₀ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a) (m := 0)
      S E F F σ σ hσ hσ k k ν L₀ L₀ Jbase b hJbase J hJ Jzero hJzero
        Γ₀ Γ₀ l₀ hl₀ l₀ hl₀ N₀ N₀ k₀ k₀ η tIso₀ heT₀ hiT₀ tIso₀ heT₀ hiT₀
          hmetricT₀ hmetricT₀
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : k₁.L2SectionSpace η →L[ℂ] k₁.L2SectionSpace η,
      ∀ u : AU.smoothSections, P₁ (i₁ u) = i₁ (J₁ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a') (m := 0)
      S E' F F σ σ hσ hσ k k ν L₀ L₀ Jbase' b' hJbase' J hJ Jzero hJzero
        Γ₁ Γ₁ l₁ hl₁ l₁ hl₁ N₁ N₁ k₁ k₁ η tIso₁ heT₁ hiT₁ tIso₁ heT₁ hiT₁
          hmetricT₁ hmetricT₁
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : k₂.L2SectionSpace η →L[ℂ] k₀.L2SectionSpace η,
      ∀ u : AT'.smoothSections, G₁ (i₂ u) = i₀ (G₀ u) := by
    exact exists_associatedSphereTensorVertical_global_l2_realization
      (n := n) (r := r) (a := a) (m := -1)
      S E F' F σ' σ hσ' hσ k' k ν L₁ L₀ Jbase b hJbase Green hGreen Rzero hRzero
        Γ₂ Γ₀ l₂ hl₂ l₀ hl₀ N₂ N₀ k₂ k₀ η tIso₂ heT₂ hiT₂ tIso₀ heT₀ hiT₀
          hmetricT₂ hmetricT₀
  -- Extend the very same Phi/Psi evaluation using the original tensor and Gram pairings.
  let f := Q.toLinearMap.ker.subtype.comp e.toLinearMap
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : kC₀.L2SectionSpace μ →ₗᵢ[ℂ] k₀.L2SectionSpace η,
      ∀ u : AC.smoothSections, e₀ (kC₀.smoothToL2 μ (S₀ u)) = i₀ (Φ u).val := by
    exact exists_associatedTensorKernelEvaluation_l2_isometry (n := n) (r := r) (a := a)
      S E A σ hA ρ h k.toContinuousHermitianMetric k.isSmoothHermitianMetric_nativeAtlas
        μ ν hν f ev hev l₀ c₀ hl₀ hpure₀ hgram₀ (V.ker.subtype.comp Φ.toLinearMap) hΦ
          NC₀ N₀ kC₀ k₀ cIso₀ tIso₀ heC₀ hiC₀ heT₀ hiT₀ hmetricC₀ hmetricT₀
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : kC₁.L2SectionSpace μ →ₗᵢ[ℂ] k₁.L2SectionSpace η,
      ∀ u : AC'.smoothSections, e₁ (kC₁.smoothToL2 μ (S₁ u)) = i₁ (Ψ u).val := by
    exact exists_associatedTensorKernelEvaluation_l2_isometry (n := n) (r := r) (a := a')
      S E' A σ hA ρ h' k.toContinuousHermitianMetric k.isSmoothHermitianMetric_nativeAtlas
        μ ν hν f ev hev l₁ c₁ hl₁ hpure₁ hgram₁ (V'.ker.subtype.comp Ψ.toLinearMap) hΨ
          NC₁ N₁ kC₁ k₁ cIso₁ tIso₁ heC₁ hiC₁ heT₁ hiT₁ hmetricC₁ hmetricT₁
  -- The coefficient PDO has its actual elliptic conjugate under these prescribed native maps.
  have hPc := C₀.coefficientOperator_isElliptic S E E' ρ hC
  obtain ⟨Pn, hPn, hEll⟩ : ∃ Pn : PseudodifferentialOperator
      (n := n) (r := NC₀.rank) (q := NC₁.rank) NC₀.Fiber NC₁.Fiber μ 1,
      Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
      Pn.IsElliptic := by
    exact Pc.exists_elliptic_native_conjugate (μ := μ) hPc NC₀ NC₁
      cIso₀ cIso₁ heC₀ hiC₀ heC₁ hiC₁
  have hi₀ : Function.Injective i₀ := (k₀.smoothToL2_injective η).comp T₀.injective
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  -- The actual lifted kernel projection takes values in the full vertical kernel.
  have hJker (s : AT.smoothSections) : J₀ s ∈ V.ker := by
    let restr := associatedSphereTensorFiberRestriction (a := a) S E A σ hA
    have hrestrict (p : P) : restr p (J₀ s) =
        tensorSectionOperator (E (projection p)) A.smoothSections A.smoothSections
          J.toLinearMap (restr p s) := by
      apply Subtype.ext
      funext y
      apply (associatedSphereTensorFiberEquiv S E σ p y).injective
      rw [associatedSphereTensorFiberRestriction_apply,
        associatedSphereTensorVerticalOperator_apply]
      rfl
    have htensor (p : P) : tensorSectionOperator (E (projection p))
        A.smoothSections A'.smoothSections Q.toLinearMap (restr p (J₀ s)) = 0 := by
      rw [hrestrict]
      obtain ⟨z, hz⟩ := (tensorSectionEquiv (E (projection p)) A.smoothSections).surjective
        (restr p s)
      rw [← hz]
      simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rw [← LinearMap.lTensor_comp_apply, hQJ, LinearMap.lTensor_zero]
      simp only [LinearMap.zero_apply, map_zero]
    change V (J₀ s) = 0
    apply Subtype.ext
    funext z
    induction z using Quotient.inductionOn with
    | h z =>
      change (V (J₀ s)).val (associatedBundleMk G P (OrthogonalSphere r) z.1 z.2) = 0
      calc
        _ = associatedSphereTensorFiberEquiv S E σ' z.1 z.2
            ((tensorSectionOperator (E (projection z.1)) A.smoothSections A'.smoothSections
              Q.toLinearMap (restr z.1 (J₀ s))).val z.2) :=
          associatedSphereTensorVerticalOperator_apply (a := a)
            S E A σ hA A' σ' hA' Q hQ (J₀ s) z.1 z.2
        _ = associatedSphereTensorFiberEquiv S E σ' z.1 z.2 0 :=
          congrArg (fun w ↦ associatedSphereTensorFiberEquiv S E σ' z.1 z.2 (w.val z.2))
            (htensor z.1)
        _ = 0 := map_zero _
  have hcommute (s : AT.smoothSections) : J₁ (H s) = H (J₀ s) :=
    LinearMap.congr_fun (C₀.horizontalLift_vertical_commute S E A σ hA A σ hA E' J hJ) s
  have hgreen (s : AT.smoothSections) : G₀ (V s) = s - J₀ s :=
    LinearMap.congr_fun
      (associatedSphereTensorVerticalOperator_comp_eq_id_sub
        S E A σ hA A' σ' hA' Q Green J hQ hGreen hJ hGQ) s
  let L := Pn.metricL2ClosedRealization kC₀ kC₁
  have hL := Pn.metricL2ClosedRealization_realization kC₀ kC₁
  have hcoefficient (u : AC.smoothSections) : Pn.toLinearMap (S₀ u) =
      S₁ (Pc.toLinearMap u) := by
    rw [hPn]
    change S₁ (Pc.toLinearMap (S₀.symm (S₀ u))) = _
    rw [S₀.symm_apply_apply]
  have hsmoothGraph (u : smoothSections (n := n) (r := NC₀.rank) NC₀.Fiber) :
      (kC₀.smoothToL2 μ u, kC₁.smoothToL2 μ (Pn.toLinearMap u)) ∈ L.graph := by
    rw [hL.1]
    apply (Pn.metricL2SmoothCore kC₀ kC₁).graph.le_topologicalClosure
    let f := LinearEquiv.ofInjective (kC₀.smoothToL2 μ) (kC₀.smoothToL2_injective μ)
    exact (Pn.metricL2SmoothCore kC₀ kC₁).mem_graph_iff.mpr
      ⟨f u, rfl, congrArg (fun w ↦ kC₁.smoothToL2 μ (Pn.toLinearMap w))
        (f.symm_apply_apply u)⟩
  -- Projection and horizontal commutation give the graph of this same coefficient operator.
  have hproject (s : AT.smoothSections) : (P₀ (i₀ s), P₁ (i₁ (H s))) ∈
      L.graph.map (e₀.toLinearMap.prodMap e₁.toLinearMap) := by
    let c := Φ.symm ⟨J₀ s, hJker s⟩
    have hvalue : (Φ c).val = J₀ s := congrArg Subtype.val (Φ.apply_symm_apply _)
    refine ⟨(kC₀.smoothToL2 μ (S₀ c), kC₁.smoothToL2 μ (Pn.toLinearMap (S₀ c))),
      hsmoothGraph (S₀ c), ?_⟩
    apply Prod.ext
    · change e₀ (kC₀.smoothToL2 μ (S₀ c)) = P₀ (i₀ s)
      rw [he₀, hvalue, hP₀]
    · change e₁ (kC₁.smoothToL2 μ (Pn.toLinearMap (S₀ c))) = P₁ (i₁ (H s))
      rw [hcoefficient, he₁, ← hH, hvalue, hP₁, hcommute]
  have hsplit (s : AT.smoothSections) : P₀ (i₀ s) = i₀ s - G₁ (i₂ (V s)) := by
    rw [hP₀, hG₁, hgreen, map_sub]
    abel
  have hreduce : R.ker ≤ L.ker.map e₀.toLinearMap :=
    ker_le_map_of_closedJointGreenSplitting i₀ (i₁.comp H) (i₂.comp V) R hR L hL.2.1
      e₀ e₁ P₀ P₁ G₁ hsplit hproject
  -- Native elliptic regularity identifies the original closed coefficient zeros with smooth zeros.
  obtain ⟨ec, _, hec, _⟩ := Pn.exists_metricL2ClosedRealization_kernel_cokernel_equiv kC₀ kC₁ hEll
  let f₀ : Pn.toLinearMap.ker →ₗ[ℂ] (k₀.L2SectionSpace η) :=
    i₀.comp (V.ker.subtype.comp (Φ.toLinearMap.comp
      (S₀.symm.toLinearMap.comp Pn.toLinearMap.ker.subtype)))
  have hf₀ (u : Pn.toLinearMap.ker) : f₀ u ∈ R.ker := by
    have hz : Pc.toLinearMap (S₀.symm u.val) = 0 := by
      apply S₁.injective
      rw [S₁.map_zero]
      have hvalue := congrArg (fun f ↦ f u.val) hPn
      exact hvalue.symm.trans u.property
    have hHz : H (Φ (S₀.symm u.val)).val = 0 :=
      (hH (S₀.symm u.val)).trans
        ((congrArg (fun w ↦ (Ψ w).val) hz).trans (congrArg Subtype.val Ψ.map_zero))
    have hVz : V (Φ (S₀.symm u.val)).val = 0 := (Φ (S₀.symm u.val)).property
    have hgraph : (f₀ u, (0, 0)) ∈ R.graph := by
      rw [hR]
      apply Submodule.le_topologicalClosure
      refine ⟨(Φ (S₀.symm u.val)).val, ?_⟩
      exact Prod.ext rfl (Prod.ext ((congrArg i₁ hHz).trans i₁.map_zero)
        ((congrArg i₂ hVz).trans i₂.map_zero))
    obtain ⟨v, hv, hzero⟩ := R.mem_graph_iff.mp hgraph
    exact R.mem_ker_iff.mpr ⟨v, hv.symm, hzero⟩
  let fk := f₀.codRestrict R.ker hf₀
  have hbij : Function.Bijective fk := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply S₀.symm.injective
      apply Φ.injective
      apply Subtype.ext
      exact hi₀ (congrArg Subtype.val huv)
    · intro x
      obtain ⟨c, hc, hcx⟩ := hreduce x.property
      obtain ⟨u, hu⟩ := ec.surjective ⟨c, hc⟩
      have huc : kC₀.smoothToL2 μ u.val = c :=
        (hec u).symm.trans (congrArg Subtype.val hu)
      have hsame : e₀ (kC₀.smoothToL2 μ u.val) = i₀ (Φ (S₀.symm u.val)).val :=
        (congrArg (fun w ↦ e₀ (kC₀.smoothToL2 μ w))
          (S₀.apply_symm_apply u.val).symm).trans (he₀ (S₀.symm u.val))
      refine ⟨u, Subtype.ext ?_⟩
      exact hsame.symm.trans ((congrArg e₀ huc).trans hcx)
  let κ := LinearEquiv.ofBijective fk hbij
  have hκ (u : Pn.toLinearMap.ker) : (κ u).val = i₀ (Φ (S₀.symm u.val)).val := rfl
  refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hEll, κ, hκ, ?_⟩
  -- The reverse kernel inclusion uses the same native smooth/closed map and the same kappa.
  have hkernel : L.ker.map e₀.toLinearMap ≤ R.ker := by
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨u, hu⟩ := ec.surjective ⟨c, hc⟩
    have huc : kC₀.smoothToL2 μ u.val = c :=
      (hec u).symm.trans (congrArg Subtype.val hu)
    have hsame : e₀ (kC₀.smoothToL2 μ u.val) = i₀ (Φ (S₀.symm u.val)).val :=
      (congrArg (fun w ↦ e₀ (kC₀.smoothToL2 μ w))
        (S₀.apply_symm_apply u.val).symm).trans (he₀ (S₀.symm u.val))
    have heq : e₀ c = (κ u).val :=
      (congrArg e₀ huc.symm).trans (hsame.trans (hκ u).symm)
    change e₀ c ∈ R.ker
    rw [heq]
    exact (κ u).property
  have hFred := Pn.closed_range_finite_metricL2ClosedRealization kC₀ kC₁ hEll
  let : FiniteDimensional ℂ L.ker := hFred.2.1
  exact exists_closedJointGreenBound i₀ (i₁.comp H) (i₂.comp V) R hR L hL.2.1 hL.2.2
    hFred.1 e₀ e₁ P₀ P₁ G₁ hsplit hproject hkernel

end AtiyahSinger
