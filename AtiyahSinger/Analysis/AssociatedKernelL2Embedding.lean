/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedKernelEvaluationMetric
public import AtiyahSinger.Geometry.AssociatedProductDensity
public import AtiyahSinger.Geometry.AtlasSectionEquiv
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The original associated kernel evaluation on metric L² completions

Public module ID: M0100.

Whole-fiber integration identifies the original coefficient Gram pairing
with the upstairs tensor pairing. The specified native isomorphisms retain
that identity on smooth sections. Its completion is a linear isometric
embedding between the same metric L² spaces, with the original evaluation
formula on every smooth input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "C" => fun b : B ↦ E b ⊗[ℂ] K b

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1200000 in
-- Normalize the same associated evaluation and its specified metric completions.
/-- The original associated evaluation extends isometrically to the specified metric completions. -/
theorem exists_associatedTensorKernelEvaluation_l2_isometry
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : ContinuousHermitianMetric F) (hk : A.IsSmoothHermitianMetric k)
    (μ : Measure B) [IsFiniteMeasure μ] [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : Y ↦ g • y) ν = ν)
    (f : (Fin ρ.dimension → ℂ) →ₗ[ℂ] A.smoothSections)
    (ev : Hom ((πS : Z → B) *ᵖ K) D)
    (hev : ∀ (p : P) (y : Y) (v : Fin ρ.dimension → ℂ),
      ev.linearMap (associatedBundleMk G P Y p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((f v).val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    ∀ (l : ContinuousHermitianMetric T) (c : ContinuousHermitianMetric C),
      AT.IsSmoothHermitianMetric l →
      (∀ (p : P) (y : Y) (u v : E (projection p)) (s t : F y),
        (l.toCore (associatedBundleMk G P Y p y)).inner
            (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
            (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
          h.pairing (projection p) u v * (k.toCore y).inner s t) →
      (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
        (c.toCore (projection p)).inner
            (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
            (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
          h.pairing (projection p) u v *
            ∫ y, (k.toCore y).inner ((f s).val y) ((f t).val y) ∂ν) →
      ∀ (Φ : AC.smoothSections →ₗ[ℂ] AT.smoothSections),
        (∀ (u : AC.smoothSections) z,
          (Φ u).val z = TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) →
        ∀ (NC : SmoothFiniteComplexBundle (n := n) B)
          (NT : SmoothFiniteComplexBundle (n := n + r) Z)
          (kC : SmoothHermitianMetric (n := n) (r := NC.rank) NC.Fiber)
          (kT : SmoothHermitianMetric (n := n + r) (r := NT.rank) NT.Fiber),
          letI := modelTopology (EuclideanSpace ℂ (Fin NC.rank)) NC.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin NT.rank)) NT.Fiber
          ∀ (eC : Iso C NC.Fiber) (eT : Iso T NT.Fiber)
            (heC : IsSmoothAtlasBundleMap AC (nativeSmoothComplexBundleAtlas NC.Fiber)
              eC.toHom.linearMap)
            (hiC : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NC.Fiber) AC
              eC.symm.toHom.linearMap)
            (heT : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas NT.Fiber)
              eT.toHom.linearMap)
            (hiT : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas NT.Fiber) AT
              eT.symm.toHom.linearMap),
            (∀ (b : B) (u v : C b),
              kC.pairing b (eC.linearEquiv b u) (eC.linearEquiv b v) = (c.toCore b).inner u v) →
            (∀ (z : Z) (u v : T z),
              kT.pairing z (eT.linearEquiv z u) (eT.linearEquiv z v) = (l.toCore z).inner u v) →
            let SC := (atlasSmoothSectionEquiv AC (nativeSmoothComplexBundleAtlas NC.Fiber)
              eC heC hiC).trans (nativeSmoothSectionLinearEquiv NC.Fiber)
            let ST := (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas NT.Fiber)
              eT heT hiT).trans (nativeSmoothSectionLinearEquiv NT.Fiber)
            let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
            letI : IsSmoothPositiveMeasure (n := n + r) η :=
              isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
            ∃ j : kC.L2SectionSpace μ →ₗᵢ[ℂ] kT.L2SectionSpace η,
              ∀ u : AC.smoothSections,
                j (kC.smoothToL2 μ (SC u)) = kT.smoothToL2 η (ST (Φ u)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro AT AC l c hl hpair hgram Φ hΦ NC NT kC kT
  let := modelTopology (EuclideanSpace ℂ (Fin NC.rank)) NC.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin NT.rank)) NT.Fiber
  intro eC eT heC hiC heT hiT hkC hkT SC ST η
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  -- Native transport retains the same two pointwise pairings before integration.
  have hC (u v : AC.smoothSections) :
      kC.sectionPairing μ (SC u) (SC v) = ∫ b, (c.toCore b).inner (u.val b) (v.val b) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun b ↦ hkC b (u.val b) (v.val b)
  have hT (u v : AT.smoothSections) :
      kT.sectionPairing η (ST u) (ST v) = ∫ z, (l.toCore z).inner (u.val z) (v.val z) ∂η := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ hkT z (u.val z) (v.val z)
  have hPhiPair (u v : AC.smoothSections) :
      kT.sectionPairing η (ST (Φ u)) (ST (Φ v)) = kC.sectionPairing μ (SC u) (SC v) := by
    rw [hT, hC]
    exact associatedTensorKernelEvaluation_integral S E A σ hσ ρ h k hk μ ν hν f ev hev
      l c hl hpair hgram u v (Φ u) (Φ v) (hΦ u) (hΦ v)
  -- The original evaluation is an isometry for these tagged smooth integral norms.
  let L : kC.SmoothL2Section μ →ₗ[ℂ] kT.SmoothL2Section η :=
    ST.toLinearMap.comp (Φ.comp SC.symm.toLinearMap)
  have hinner (u v : kC.SmoothL2Section μ) : inner ℂ (L u) (L v) = inner ℂ u v := by
    change kT.sectionPairing η (ST (Φ (SC.symm u))) (ST (Φ (SC.symm v))) =
      kC.sectionPairing μ u v
    have hp := hPhiPair (SC.symm u) (SC.symm v)
    exact hp.trans (congrArg₂ (kC.sectionPairing μ)
      (SC.apply_symm_apply u) (SC.apply_symm_apply v))
  let e : kC.SmoothL2Section μ →ₗᵢ[ℂ] kT.SmoothL2Section η := L.isometryOfInner hinner
  refine ⟨e.completion, ?_⟩
  intro u
  have heval : e (SC u) = ST (Φ u) := by
    change ST (Φ (SC.symm (SC u))) = ST (Φ u)
    rw [SC.symm_apply_apply]
  have he := e.completion_apply_coe (show kC.SmoothL2Section μ from SC u)
  exact he.trans (congrArg (kT.smoothToL2 η) heval)

end AtiyahSinger
