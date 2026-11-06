/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedKernelEvaluationMetric
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalVerticalCommutation
public import AtiyahSinger.Analysis.AtlasBundleIsoPseudodifferential
public import AtiyahSinger.Analysis.KernelMetricAdjoint
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Geometry.AssociatedProductDensity

/-!
# The same associated coefficient PDO and its odd metric adjoint

Public module ID: M0102.

The specified full kernel evaluation, its integral Gram metrics and the
specified native coefficient models identify the reverse horizontal action
with the metric formal adjoint of the original coefficient PDO. Native
transport keeps the actual smooth bundle isomorphisms; the whole-fiber
pairing comparison keeps the original associated product measure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w w' u' v'

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

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
  {F : OrthogonalSphere r → Type u'} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type v'} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')
  (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
  {μ : MeasureTheory.Measure B} [IsSmoothPositiveMeasure (n := n) μ]
  [MeasureTheory.IsFiniteMeasure μ]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "U" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "U'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D' z

variable
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "C" => fun b : B ↦ E b ⊗[ℂ] K b
local notation "C'" => fun b : B ↦ E' b ⊗[ℂ] K b

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the native metric-adjoint and joint Green-kernel comparisons.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The metric-adjoint kernel of the specified native coefficient PDO identifies with
the joint kernel of the reverse horizontal and vertical actions. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_coefficientMetricAdjoint
    {m d : ℝ} (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    [IsSmoothPositiveMeasure (n := r) ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
    (k : ContinuousHermitianMetric F) (hk : A.IsSmoothHermitianMetric k)
    (Q : AtlasPseudodifferentialOperator A' A d)
    (hQ : Q.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ' σ hσ' hσ)
    (J : AtlasPseudodifferentialOperator A A' d)
    (hJ : J.IsEquivariant 𝓘(ℝ, OrthogonalGroupModel r) σ σ' hσ hσ')
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] J.toLinearMap.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
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
    let A₀₀ := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let _A₁₀ := associatedSphereTensorBundleAtlas (a := a') S E' A' σ' hσ'
    let A₀₁ := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let A₁₁ := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let AC₀ := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    let AC₁ := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
      (associatedOrthogonalRepresentationAtlas S ρ)
    let _H₀ := C₀.horizontalLift S E A' σ' E' hσ'
    let H₁ := C₀.horizontalLift S E A σ E' hσ
    let V₀ := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hσ' A σ hσ Q hQ
    let V₁ := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hσ' A σ hσ Q hQ
    let V₀a := associatedSphereTensorVerticalOperator (a := a) S E A σ hσ A' σ' hσ' J hJ
    let V₁a := associatedSphereTensorVerticalOperator (a := a') S E' A σ hσ A' σ' hσ' J hJ
    let Pc := C₀.coefficientOperator S E E' ρ
    ∀ (l₀₀ : ContinuousHermitianMetric T') (l₁₀ : ContinuousHermitianMetric U')
      (l₀₁ : ContinuousHermitianMetric T) (l₁₁ : ContinuousHermitianMetric U)
      (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
      (N₀₀ : SmoothFiniteComplexBundle (n := n + r) Z)
      (N₀ N₁ : SmoothFiniteComplexBundle (n := n) B)
      (k₀₀ : SmoothHermitianMetric (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
      (k₀ : SmoothHermitianMetric (n := n) (r := N₀.rank) N₀.Fiber)
      (k₁ : SmoothHermitianMetric (n := n) (r := N₁.rank) N₁.Fiber),
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
      let BN₀₀ := nativeSmoothComplexBundleAtlas (n := n + r) (r := N₀₀.rank) N₀₀.Fiber
      let BN₀ := nativeSmoothComplexBundleAtlas (n := n) (r := N₀.rank) N₀.Fiber
      let BN₁ := nativeSmoothComplexBundleAtlas (n := n) (r := N₁.rank) N₁.Fiber
      ∀ (e₀₀ : Iso T' N₀₀.Fiber) (e₀ : Iso C N₀.Fiber) (e₁ : Iso C' N₁.Fiber)
        (_he₀₀ : IsSmoothAtlasBundleMap A₀₀
          BN₀₀
          e₀₀.toHom.linearMap)
        (_hi₀₀ : IsSmoothAtlasBundleMap
          BN₀₀
          A₀₀ e₀₀.symm.toHom.linearMap)
        (he₀ : IsSmoothAtlasBundleMap AC₀
          BN₀ e₀.toHom.linearMap)
        (hi₀ : IsSmoothAtlasBundleMap
          BN₀
          AC₀ e₀.symm.toHom.linearMap)
        (he₁ : IsSmoothAtlasBundleMap AC₁
          BN₁ e₁.toHom.linearMap)
        (hi₁ : IsSmoothAtlasBundleMap
          BN₁
          AC₁ e₁.symm.toHom.linearMap),
        A₀₁.IsSmoothHermitianMetric l₀₁ → A₁₁.IsSmoothHermitianMetric l₁₁ →
        (∀ z v w, k₀₀.pairing z (e₀₀.linearEquiv z v) (e₀₀.linearEquiv z w) =
          (l₀₀.toCore z).inner v w) →
        (∀ b v w, k₀.pairing b (e₀.linearEquiv b v) (e₀.linearEquiv b w) =
          (c₀.toCore b).inner v w) →
        (∀ b v w, k₁.pairing b (e₁.linearEquiv b v) (e₁.linearEquiv b w) =
          (c₁.toCore b).inner v w) →
        (∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
          (l₀₁.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
              (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
            h.pairing (projection p) u v * (k.toCore y).inner s t) →
        (∀ (p : P) (y : OrthogonalSphere r) (u v : E' (projection p)) (s t : F y),
          (l₁₁.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
              (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
            h'.pairing (projection p) u v * (k.toCore y).inner s t) →
        (∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
          (c₀.toCore (projection p)).inner
              (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
              (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
            h.pairing (projection p) u v *
              ∫ y, (k.toCore y).inner ((e s).val.val y) ((e t).val.val y) ∂ν) →
        (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρ.dimension → ℂ),
          (c₁.toCore (projection p)).inner
              (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
              (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
            h'.pairing (projection p) u v *
              ∫ y, (k.toCore y).inner ((e s).val.val y) ((e t).val.val y) ∂ν) →
        ∀ H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections,
          (∀ u v, (∫ z, (l₁₁.toCore z).inner ((H₁ u).val z) (v.val z) ∂η) =
            ∫ z, (l₀₁.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) →
          (∀ u v, (∫ z, (l₀₁.toCore z).inner ((V₀ u).val z) (v.val z) ∂η) =
            ∫ z, (l₀₀.toCore z).inner (u.val z) ((V₀a v).val z) ∂η) →
          (∀ u v, (∫ z, (l₁₁.toCore z).inner ((V₁ u).val z) (v.val z) ∂η) =
            ∫ z, (l₁₀.toCore z).inner (u.val z) ((V₁a v).val z) ∂η) →
          let S₀ := (atlasSmoothSectionEquiv AC₀
            BN₀
            e₀ he₀ hi₀).trans (nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber)
          let S₁ := (atlasSmoothSectionEquiv AC₁
            BN₁
            e₁ he₁ hi₁).trans (nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber)
          ∃ ev : Hom ((πS : Z → B) *ᵖ K) D,
            (∀ (p : P) (y : OrthogonalSphere r) (v : Fin ρ.dimension → ℂ),
              ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
                  (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
                associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
            ∃ (Φ : AC₀.smoothSections ≃ₗ[ℂ] V₀a.ker)
              (Ψ : AC₁.smoothSections ≃ₗ[ℂ] V₁a.ker),
              (∀ u z, (Φ u).val.val z =
                TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
              (∀ u z, (Ψ u).val.val z =
                TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) ∧
              ∃ Pn : PseudodifferentialOperator
                  (n := n) (r := N₀.rank) (q := N₁.rank) N₀.Fiber N₁.Fiber μ m,
                Pn.toLinearMap = S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) ∧
                (∀ v, H₁a (Ψ (S₁.symm v)).val =
                  (Φ (S₀.symm ((Pn.metricFormalAdjoint k₀ k₁).toLinearMap v))).val) ∧
                ∃ κ : (Pn.metricFormalAdjoint k₀ k₁).toLinearMap.ker ≃ₗ[ℂ]
                    ↥(H₁a.ker ⊓ V₁a.ker),
                  ∀ v, (κ v).val = (Ψ (S₁.symm v.val)).val := by
  classical
  -- Obtain the coefficient realization from the specified horizontal lift and full kernel.
  have hrealization :=
    C₀.exists_horizontalLift_coefficientKernelRealization S E E' A σ hσ A' σ' hσ'
      ρ J hJ e he
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
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace lm Z
  let := isManifold_linearModelChartedSpace lm Z
  intro η A₀₀ A₁₀ A₀₁ A₁₁ AC₀ AC₁ H₀ H₁ V₀ V₁ V₀a V₁a Pc
  let : IsSmoothPositiveMeasure (n := n + r) η :=
    isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
  -- One full-kernel realization supplies the evaluation and both coefficient coordinates.
  obtain ⟨ev, hev, Φ, Ψ, hΦ, hΨ, hP⟩ := hrealization
  intro l₀₀ l₁₀ l₀₁ l₁₁ c₀ c₁ N₀₀ N₀ N₁ k₀₀ k₀ k₁
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro BN₀₀ BN₀ BN₁ e₀₀ e₀ e₁ he₀₀ hi₀₀ he₀ hi₀ he₁ hi₁ hl₀₁ hl₁₁ hk₀₀ hk₀ hk₁
    hpure₀ hpure₁ hgram₀ hgram₁ H₁a hH₁ hV₀ hV₁ S₀ S₁
  -- Multiplication by the specified bundle maps transports this same full coefficient PDO.
  have hU₀exists := exists_atlasPseudodifferentialOperator_bundleMap
    (n := n) (M := B) (E := N₀.Fiber) (F := C) BN₀ AC₀
    e₀.symm.toHom.linearMap hi₀
  obtain ⟨hu, U₀, hU₀, _⟩ := hU₀exists
  have hU₁exists := exists_atlasPseudodifferentialOperator_bundleMap
    (n := n) (M := B) (E := C') (F := N₁.Fiber) AC₁ BN₁ e₁.toHom.linearMap he₁
  obtain ⟨hv, U₁, hU₁, _⟩ := hU₁exists
  let Pa : AtlasPseudodifferentialOperator
      BN₀
      BN₁ m :=
    ⟨(U₁.comp (Pc.comp U₀)).toLinearMap, by
      simpa only [zero_add, add_zero] using (U₁.comp (Pc.comp U₀)).isPseudodifferentialOperator⟩
  let i₀ := nativeSmoothSectionLinearEquiv (n := n) (r := N₀.rank) N₀.Fiber
  let i₁ := nativeSmoothSectionLinearEquiv (n := n) (r := N₁.rank) N₁.Fiber
  let Pmap := i₁.toLinearMap.comp (Pa.toLinearMap.comp i₀.symm.toLinearMap)
  have hPa : IsPseudodifferentialOperator N₀.Fiber N₁.Fiber μ m Pmap := by
    apply (isAtlasPseudodifferentialOperator_native_iff μ m Pmap).mp
    have heq : i₁.symm.toLinearMap.comp (Pmap.comp i₀.toLinearMap) = Pa.toLinearMap := by
      ext u
      simp only [Pmap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        i₀.symm_apply_apply, i₁.symm_apply_apply]
    rw [heq]
    exact Pa.isPseudodifferentialOperator
  let Pn : PseudodifferentialOperator
      (n := n) (r := N₀.rank) (q := N₁.rank) N₀.Fiber N₁.Fiber μ m := ⟨Pmap, hPa⟩
  have hPn : Pn.toLinearMap =
      S₁.toLinearMap.comp (Pc.toLinearMap.comp S₀.symm.toLinearMap) := by
    change i₁.toLinearMap.comp
      ((U₁.toLinearMap.comp (Pc.toLinearMap.comp U₀.toLinearMap)).comp
        i₀.symm.toLinearMap) = _
    rw [hU₀, hU₁]
    rfl
  -- Each coefficient integral is the same whole-fiber evaluation pairing.
  let f := J.toLinearMap.ker.subtype.comp e.toLinearMap
  have hpair₀ (u v : AC₀.smoothSections) :
      (∫ z, (l₀₁.toCore z).inner ((Φ u).val.val z) ((Φ v).val.val z) ∂η) =
        k₀.sectionPairing μ (S₀ u) (S₀ v) := by
    have heval := associatedTensorKernelEvaluation_integral
      S E A σ hσ ρ h k hk μ ν hν f ev hev l₀₁ c₀ hl₀₁ hpure₀ hgram₀
        u v (Φ u).val (Φ v).val (hΦ u) (hΦ v)
    refine heval.trans ?_
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun b ↦ (hk₀ b (u.val b) (v.val b)).symm
  have hpair₁ (u v : AC₁.smoothSections) :
      (∫ z, (l₁₁.toCore z).inner ((Ψ u).val.val z) ((Ψ v).val.val z) ∂η) =
        k₁.sectionPairing μ (S₁ u) (S₁ v) := by
    have heval := associatedTensorKernelEvaluation_integral
      S E' A σ hσ ρ h' k hk μ ν hν f ev hev l₁₁ c₁ hl₁₁ hpure₁ hgram₁
        u v (Ψ u).val (Ψ v).val (hΨ u) (hΨ v)
    refine heval.trans ?_
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun b ↦ (hk₁ b (u.val b) (v.val b)).symm
  -- Nondegeneracy uses the supplied lower-left model, without replacing its metric.
  let S₀₀ := (atlasSmoothSectionEquiv A₀₀
    BN₀₀
    e₀₀ he₀₀ hi₀₀).trans (nativeSmoothSectionLinearEquiv (n := n + r) (r := N₀₀.rank) N₀₀.Fiber)
  have hnondeg (v : A₀₀.smoothSections)
      (hv : ∀ u : A₀₀.smoothSections,
        (∫ z, (l₀₀.toCore z).inner (u.val z) (v.val z) ∂η) = 0) : v = 0 := by
    apply S₀₀.injective
    rw [S₀₀.map_zero]
    apply (k₀₀.sectionPairing_self_eq_zero_iff η (S₀₀ v)).mp
    calc
      k₀₀.sectionPairing η (S₀₀ v) (S₀₀ v) =
          ∫ z, (l₀₀.toCore z).inner (v.val z) (v.val z) ∂η := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ hk₀₀ z (v.val z) (v.val z)
      _ = 0 := hv v
  have hzero (u : A₁₀.smoothSections) :
      (∫ z, (l₁₀.toCore z).inner (u.val z) ((0 : A₁₀.smoothSections).val z) ∂η) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with z
    let := l₁₀.toCore z
    exact InnerProductSpace.Core.inner_zero_right (u.val z)
  have hcomm (u : A₀₀.smoothSections) : H₁ (V₀ u) = V₁ (H₀ u) := by
    exact (DFunLike.congr_fun (C₀.horizontalLift_vertical_commute
      S E A' σ' hσ' A σ hσ E' Q hQ) u).symm
  let Φn := S₀.symm.trans Φ
  let Ψn := S₁.symm.trans Ψ
  have hPnative (u : smoothSections (n := n) (r := N₀.rank) N₀.Fiber) :
      H₁ (Φn u).val = (Ψn (Pn.toLinearMap u)).val := by
    change H₁ (Φ (S₀.symm u)).val = (Ψ (S₁.symm (Pn.toLinearMap u))).val
    rw [hP, hPn]
    simp only [Pc, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, S₁.symm_apply_apply]
  -- Uniqueness now identifies the reverse restriction with this exact native PDO's adjoint.
  have hresult := Pn.exists_adjoint_jointKernelEquiv k₀ k₁ H₀ H₁ H₁a V₀ V₀a V₁ V₁a
    (fun u v ↦ ∫ z, (l₀₀.toCore z).inner (u.val z) (v.val z) ∂η)
    (fun u v ↦ ∫ z, (l₁₀.toCore z).inner (u.val z) (v.val z) ∂η)
    (fun u v ↦ ∫ z, (l₀₁.toCore z).inner (u.val z) (v.val z) ∂η)
    (fun u v ↦ ∫ z, (l₁₁.toCore z).inner (u.val z) (v.val z) ∂η)
    hnondeg hzero hH₁ hV₀ hV₁ hcomm Φn Ψn hPnative
    (fun u v ↦ by
      simpa only [Φn, LinearEquiv.trans_apply, S₀.apply_symm_apply] using
        hpair₀ (S₀.symm u) (S₀.symm v))
    (fun u v ↦ by
      simpa only [Ψn, LinearEquiv.trans_apply, S₁.apply_symm_apply] using
        hpair₁ (S₁.symm u) (S₁.symm v))
  obtain ⟨_, hreverse, κ, hκ⟩ := hresult
  exact ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hreverse, κ, hκ⟩

end AtiyahSinger

