/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalSymbolFactor
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalPrincipalSymbol
public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalDualApproximation
public import AtiyahSinger.Geometry.CommonAtlasBundlePresentation

/-!
# Common horizontal cutoff corners (M2322)

A common sphere partition regularizes the same base localization on two
supplied associated tensor pairs. Their full symbol representatives share
one finite base factor. At each common positive parameter, the operators
approximate both horizontal lifts in the supplied H¹-to-H⁰ and H⁰-to-H⁻¹
Sobolev norms.
-/

@[expose] public noncomputable section

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)
local notation "V₁" => EuclideanSpace ℂ (Fin a')

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z


variable
  {F₁ : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F₁ y)] [∀ y, Module ℂ (F₁ y)]
  [TopologicalSpace (TotalSpace Unit F₁)] [IsFiniteRank F₁]
  (A₁ : SmoothComplexBundleAtlas (n := r) F₁)
  (σ₁ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F₁)

local notation "D₁" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ₁
local notation "T₁" => fun z : Z ↦ E (πS z) ⊗[ℂ] D₁ z
local notation "T₁'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D₁ z

variable [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
-- The extended limit accommodates the common dependent context of both horizontal cutoff corners.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the common dependent context of both horizontal cutoff corners.
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- Both actual horizontal corners share one chosen finite factor and parameter. -/
theorem associated_cutoff_actual_horizontal_pair_call
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ₁ : σ₁.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A₁) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI : TopologicalSpace (TotalSpace Unit T₁) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D₁)
    letI : TopologicalSpace (TotalSpace Unit T₁') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D₁)
    letI := associatedSphereChartedSpace S
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := linearModelChartedSpace split.symm Z
    letI := isManifold_linearModelChartedSpace split.symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let BT := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let AT₁ := associatedSphereTensorBundleAtlas (a := a) S E A₁ σ₁ hσ₁
    let BT₁ := associatedSphereTensorBundleAtlas (a := a') S E' A₁ σ₁ hσ₁
    ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation BT)
      (Li₁ : AtlasBundlePresentation AT₁) (Lo₁ : AtlasBundlePresentation BT₁),
      ∃ (J : AtlasBundlePresentation A) (frame₁ : Fin J.size → A₁.Index)
        (_hframe₁ : ∀ j, tsupport (J.cutoff j) ⊆ (A₁.chart (frame₁ j)).baseSet),
        ∃ (R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)
          (R₁ : Li₁.SobolevSpace 1 →L[ℂ] Lo₁.SobolevSpace 0) (B₀ B₁ Bneg₀ Bneg₁ : ℝ),
          (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
            Lo.smoothToSobolev 0 (C.horizontalLift S E A σ E' hσ w)) ∧
          (∀ w : AT₁.smoothSections, R₁ (Li₁.smoothToSobolev 1 w) =
            Lo₁.smoothToSobolev 0 (C.horizontalLift S E A₁ σ₁ E' hσ₁ w)) ∧
          0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ Bneg₀ ∧ 0 ≤ Bneg₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            let CP (i : Fin C.size) (j : Fin J.size) :=
              associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
            let p (z : Z) (ξ : CotangentFiber (n := n + r) z) :=
              ∑ i, ∑ j,
                let cov := split (covectorInChart (CP i j) z ξ)
                ((J.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
                  productFrequencyCutoff ε ‖cov.1‖ ‖cov.2‖ : ℝ) : ℂ) •
                    ((C.piece i).globalSymbolFunction (πS z)
                      (covectorFromChart (C.piece i).chart (πS z) cov.1)).toLinearMap
            ∃ (U : AtlasPseudodifferentialOperator AT BT 1)
              (U₁ : AtlasPseudodifferentialOperator AT₁ BT₁ 1)
              (s : atlasGlobalSymbolSpace AT BT 1) (s₁ : atlasGlobalSymbolSpace AT₁ BT₁ 1)
              (Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0)
              (Rε₁ : Li₁.SobolevSpace 1 →L[ℂ] Lo₁.SobolevSpace 0),
              U.principalSymbol = atlasGlobalPrincipalSymbolClass AT BT 1 s ∧
              U₁.principalSymbol = atlasGlobalPrincipalSymbolClass AT₁ BT₁ 1 s₁ ∧
              (∀ z ξ, s.val z ξ = TensorProduct.map (p z ξ)
                (LinearMap.id : Module.End ℂ (D z))) ∧
              (∀ z ξ, s₁.val z ξ = TensorProduct.map (p z ξ)
                (LinearMap.id : Module.End ℂ (D₁ z))) ∧
              (∀ w : AT.smoothSections, Rε (Li.smoothToSobolev 1 w) =
                Lo.smoothToSobolev 0 (U.toLinearMap w)) ∧
              (∀ w : AT₁.smoothSections, Rε₁ (Li₁.smoothToSobolev 1 w) =
                Lo₁.smoothToSobolev 0 (U₁.toLinearMap w)) ∧
              ‖Rε - R‖ ≤ B₀ * ε ∧ ‖Rε₁ - R₁‖ ≤ B₁ * ε ∧
              (∀ w : AT.smoothSections,
                ‖Lo.smoothToSobolev (-1)
                  (C.horizontalLift S E A σ E' hσ w - U.toLinearMap w)‖ ≤
                    Bneg₀ * ε * ‖Li.smoothToSobolev 0 w‖) ∧
              (∀ w : AT₁.smoothSections,
                ‖Lo₁.smoothToSobolev (-1)
                  (C.horizontalLift S E A₁ σ₁ E' hσ₁ w - U₁.toLinearMap w)‖ ≤
                    Bneg₁ * ε * ‖Li₁.smoothToSobolev 0 w‖) := by
  classical
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let : TopologicalSpace (TotalSpace Unit T₁) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D₁)
  let : TopologicalSpace (TotalSpace Unit T₁') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D₁)
  let := associatedSphereChartedSpace S
  intro split
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro AT BT AT₁ BT₁ Li Lo Li₁ Lo₁
  -- Choose the sphere partition once, before either regularization and before epsilon.
  have hcommon := exists_atlasBundlePresentation_common_frames A A₁
  let J : AtlasBundlePresentation A := hcommon.choose
  let frame₁ : Fin J.size → A₁.Index := hcommon.choose_spec.choose
  have hframe₁ := hcommon.choose_spec.choose_spec
  let J₁ : AtlasBundlePresentation A₁ := {
    size := J.size
    chart := J.chart
    chart_mem_atlas := J.chart_mem_atlas
    frameIndex := frame₁
    cutoff := J.cutoff
    smooth_cutoff := J.smooth_cutoff
    cutoff_nonneg := J.cutoff_nonneg
    compact_support := J.compact_support
    support_subset := fun j _ hy ↦ ⟨(J.support_subset j hy).1, hframe₁ j hy⟩
    sum_cutoff := J.sum_cutoff }
  have hreg := C.exists_horizontalLift_regularization S E A σ E' hσ J Li Lo
  let Co : ∀ i : Fin C.size, BundleChartCutoff (r := a') E' (C.piece i).chart := hreg.choose
  have hCo := hreg.choose_spec.choose
  let κ : Fin C.size → Fin J.size → Y → ℝ := hreg.choose_spec.choose_spec.choose
  have hκ := hreg.choose_spec.choose_spec.choose_spec.choose
  have hκK := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hκs := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hrest := hreg.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hCoF := hrest.1
  have hCoI := hrest.2.1
  have hCoOne := hrest.2.2.1
  have hκOne := hrest.2.2.2.1
  have hio := hrest.2.2.2.2
  let I : Fin C.size → ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
      𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) := hio.choose
  let O : Fin C.size → ∀ j : Fin J.size,
      𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
        →ₗ[ℂ] BT.smoothSections := hio.choose_spec.choose
  have hmaps := hio.choose_spec.choose_spec
  have hI := hmaps.1
  have hO := hmaps.2.1
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hmaps.2.2.choose
  have hrr := hmaps.2.2.choose_spec
  have hR : ∀ w : AT.smoothSections,
      R (Li.smoothToSobolev 1 w) =
        Lo.smoothToSobolev 0 (C.horizontalLift S E A σ E' hσ w) := hrr.1
  let B₀ : ℝ := hrr.2.choose
  have hB₀ := hrr.2.choose_spec.1
  have hpos := hrr.2.choose_spec.2
  have hreg₁ := C.exists_horizontalLift_regularization S E A₁ σ₁ E' hσ₁ J₁ Li₁ Lo₁
  let Co₁ : ∀ i : Fin C.size, BundleChartCutoff (r := a') E' (C.piece i).chart := hreg₁.choose
  have hCo₁ := hreg₁.choose_spec.choose
  let κ₁ : Fin C.size → Fin J₁.size → Y → ℝ := hreg₁.choose_spec.choose_spec.choose
  have hκ₁ := hreg₁.choose_spec.choose_spec.choose_spec.choose
  have hκK₁ := hreg₁.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hκs₁ := hreg₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hrest₁ := hreg₁.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hCoF₁ := hrest₁.1
  have hCoI₁ := hrest₁.2.1
  have hCoOne₁ := hrest₁.2.2.1
  have hκOne₁ := hrest₁.2.2.2.1
  have hio₁ := hrest₁.2.2.2.2
  let I₁ : Fin C.size → ∀ j : Fin J₁.size, AT₁.smoothSections →ₗ[ℂ]
      𝓢(XY, EuclideanSpace ℂ (Fin (a * A₁.rank (J₁.frameIndex j)))) := hio₁.choose
  let O₁ : Fin C.size → ∀ j : Fin J₁.size,
      𝓢(XY, EuclideanSpace ℂ (Fin (a' * A₁.rank (J₁.frameIndex j))))
        →ₗ[ℂ] BT₁.smoothSections := hio₁.choose_spec.choose
  have hmaps₁ := hio₁.choose_spec.choose_spec
  have hI₁ := hmaps₁.1
  have hO₁ := hmaps₁.2.1
  let R₁ : Li₁.SobolevSpace 1 →L[ℂ] Lo₁.SobolevSpace 0 := hmaps₁.2.2.choose
  have hrr₁ := hmaps₁.2.2.choose_spec
  have hR₁ : ∀ w : AT₁.smoothSections,
      R₁ (Li₁.smoothToSobolev 1 w) =
        Lo₁.smoothToSobolev 0 (C.horizontalLift S E A₁ σ₁ E' hσ₁ w) := hrr₁.1
  let B₁ : ℝ := hrr₁.2.choose
  have hB₁ := hrr₁.2.choose_spec.1
  have hpos₁ := hrr₁.2.choose_spec.2
  -- The fixed chart maps also give H⁰-to-H⁻¹ bounds for the forward errors.
  have hneg := C.horizontalLift_error_sobolev_neg_one_bound S E A σ E' hσ J
    Co hCoF hCo hCoOne κ hκ hκK hκs hκOne I O hI hO Li Lo
  let Bneg₀ : ℝ := hneg.choose
  have hD₀ := hneg.choose_spec.1
  have hneg₁ := C.horizontalLift_error_sobolev_neg_one_bound S E A₁ σ₁ E' hσ₁ J₁
    Co₁ hCoF₁ hCo₁ hCoOne₁ κ₁ hκ₁ hκK₁ hκs₁ hκOne₁ I₁ O₁ hI₁ hO₁ Li₁ Lo₁
  let Bneg₁ : ℝ := hneg₁.choose
  have hD₁ := hneg₁.choose_spec.1
  refine ⟨J, frame₁, hframe₁, ?_⟩
  refine ⟨R, R₁, B₀, B₁, Bneg₀, Bneg₁, ?_⟩
  refine ⟨hR, hR₁, hB₀, hB₁, hD₀, hD₁, ?_⟩
  intro ε hε hε1
  -- Use the cutoff PDO families at the shared positive parameter.
  have hcut := hpos ε hε hε1
  let Q : Fin C.size → Fin J.size → AtlasPseudodifferentialOperator AT BT 1 := hcut.choose
  let Uloc : Fin C.size → ∀ j : Fin J.size,
      𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))) := hcut.choose_spec.choose
  let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hcut.choose_spec.choose_spec.choose
  have hQ := hcut.choose_spec.choose_spec.choose_spec.1
  have hV := hcut.choose_spec.choose_spec.choose_spec.2.1
  have hRε : ∀ w : AT.smoothSections,
      Rε (Li.smoothToSobolev 1 w) =
        Lo.smoothToSobolev 0 (∑ i, ∑ j, (Q i j).toLinearMap w) :=
    hcut.choose_spec.choose_spec.choose_spec.2.2.1
  have hbound := hcut.choose_spec.choose_spec.choose_spec.2.2.2
  have hcut₁ := hpos₁ ε hε hε1
  let Q₁ : Fin C.size → Fin J₁.size → AtlasPseudodifferentialOperator AT₁ BT₁ 1 := hcut₁.choose
  let Uloc₁ : Fin C.size → ∀ j : Fin J₁.size,
      𝓢(XY, EuclideanSpace ℂ (Fin (a * A₁.rank (J₁.frameIndex j)))) →L[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A₁.rank (J₁.frameIndex j)))) := hcut₁.choose_spec.choose
  let Rε₁ : Li₁.SobolevSpace 1 →L[ℂ] Lo₁.SobolevSpace 0 := hcut₁.choose_spec.choose_spec.choose
  have hQ₁ := hcut₁.choose_spec.choose_spec.choose_spec.1
  have hV₁ := hcut₁.choose_spec.choose_spec.choose_spec.2.1
  have hRε₁ : ∀ w : AT₁.smoothSections,
      Rε₁ (Li₁.smoothToSobolev 1 w) =
        Lo₁.smoothToSobolev 0 (∑ i, ∑ j, (Q₁ i j).toLinearMap w) :=
    hcut₁.choose_spec.choose_spec.choose_spec.2.2.1
  have hbound₁ := hcut₁.choose_spec.choose_spec.choose_spec.2.2.2
  have hprincipal := C.exists_horizontalCutoff_principalSymbol
    S E A σ E' hσ J Co hCo κ hκ hκK hκs hCoF hCoI I O hI hO ε hε Q Uloc hQ hV
  let g : Fin C.size → Fin J.size → atlasGlobalSymbolSpace AT BT 1 := hprincipal.choose
  have hg := hprincipal.choose_spec.1
  let U : AtlasPseudodifferentialOperator AT BT 1 := hprincipal.choose_spec.2.choose
  have hU : U.toLinearMap = ∑ i, ∑ j, (Q i j).toLinearMap :=
    hprincipal.choose_spec.2.choose_spec.1
  have hs : U.principalSymbol =
      atlasGlobalPrincipalSymbolClass AT BT 1 (∑ i, ∑ j, g i j) :=
    hprincipal.choose_spec.2.choose_spec.2
  have hprincipal₁ := C.exists_horizontalCutoff_principalSymbol
    S E A₁ σ₁ E' hσ₁ J₁ Co₁ hCo₁ κ₁ hκ₁ hκK₁ hκs₁ hCoF₁ hCoI₁
      I₁ O₁ hI₁ hO₁ ε hε Q₁ Uloc₁ hQ₁ hV₁
  let g₁ : Fin C.size → Fin J₁.size → atlasGlobalSymbolSpace AT₁ BT₁ 1 := hprincipal₁.choose
  have hg₁ := hprincipal₁.choose_spec.1
  let U₁ : AtlasPseudodifferentialOperator AT₁ BT₁ 1 := hprincipal₁.choose_spec.2.choose
  have hU₁ : U₁.toLinearMap = ∑ i, ∑ j, (Q₁ i j).toLinearMap :=
    hprincipal₁.choose_spec.2.choose_spec.1
  have hs₁ : U₁.principalSymbol =
      atlasGlobalPrincipalSymbolClass AT₁ BT₁ 1 (∑ i, ∑ j, g₁ i j) :=
    hprincipal₁.choose_spec.2.choose_spec.2
  refine ⟨U, U₁, ∑ i, ∑ j, g i j, ∑ i, ∑ j, g₁ i j, Rε, Rε₁, ?_⟩
  refine ⟨hs, hs₁, ?_, ?_, ?_, ?_, hbound, hbound₁, ?_, ?_⟩
  · intro z ξ
    simp only [Submodule.coe_sum, Finset.sum_apply]
    have hi (i : Fin C.size) := associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
      S E A σ E' (C.piece i) hσ (C.center i)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inr hx, hxy⟩)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inl hx, hxy⟩)
      J (Co i) (hCoF i) (hCo i) (hCoOne i) (κ i) (hκ i) (hκK i)
      (hκs i) (hκOne i) ε (fun j ↦ (g i j).val) (hg i) z ξ
    change (∑ i, ∑ j, (g i j).val z ξ) = _
    rw [Finset.sum_congr rfl (fun i _ ↦ hi i)]
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.sum_tmul, split]
  · intro z ξ
    simp only [Submodule.coe_sum, Finset.sum_apply]
    have hi (i : Fin C.size) := associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
      S E A₁ σ₁ E' (C.piece i) hσ₁ (C.center i)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inr hx, hxy⟩)
      (fun _ ⟨x, hx, hxy⟩ ↦ C.piece_support i ⟨x, Or.inl hx, hxy⟩)
      J₁ (Co₁ i) (hCoF₁ i) (hCo₁ i) (hCoOne₁ i) (κ₁ i) (hκ₁ i) (hκK₁ i)
      (hκs₁ i) (hκOne₁ i) ε (fun j ↦ (g₁ i j).val) (hg₁ i) z ξ
    change (∑ i, ∑ j, (g₁ i j).val z ξ) = _
    rw [Finset.sum_congr rfl (fun i _ ↦ hi i)]
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.sum_tmul, split, J₁]
  · -- Apply the retained equality of operators on this same smooth input.
    intro w
    have hUw : U.toLinearMap w = ∑ i, ∑ j, (Q i j).toLinearMap w := by
      simpa only [LinearMap.sum_apply] using congrArg
        (fun f : AT.smoothSections →ₗ[ℂ] BT.smoothSections ↦ f w) hU
    exact (hRε w).trans (congrArg (Lo.smoothToSobolev 0) hUw.symm)
  · intro w
    have hUw : U₁.toLinearMap w = ∑ i, ∑ j, (Q₁ i j).toLinearMap w := by
      simpa only [LinearMap.sum_apply] using congrArg
        (fun f : AT₁.smoothSections →ₗ[ℂ] BT₁.smoothSections ↦ f w) hU₁
    exact (hRε₁ w).trans (congrArg (Lo₁.smoothToSobolev 0) hUw.symm)
  · -- The very same coordinate sum controls the negative-order error.
    intro w
    have h := hneg.choose_spec.2 ε hε hε1 Uloc hV w
    have hUw : U.toLinearMap w = ∑ i, ∑ j, (Q i j).toLinearMap w := by
      simpa only [LinearMap.sum_apply] using congrArg
        (fun f : AT.smoothSections →ₗ[ℂ] BT.smoothSections ↦ f w) hU
    have hQw : (∑ i, ∑ j, (Q i j).toLinearMap w) =
        ∑ i, ∑ j, O i j (Uloc i j (I i j w)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun f : AT.smoothSections →ₗ[ℂ] BT.smoothSections ↦ f w) (hQ i j)
    have heq := congrArg
      (fun v : BT.smoothSections ↦
        ‖Lo.smoothToSobolev (-1) (C.horizontalLift S E A σ E' hσ w - v)‖)
      (hUw.trans hQw)
    exact heq.trans_le h
  · intro w
    have h := hneg₁.choose_spec.2 ε hε hε1 Uloc₁ hV₁ w
    have hUw : U₁.toLinearMap w = ∑ i, ∑ j, (Q₁ i j).toLinearMap w := by
      simpa only [LinearMap.sum_apply] using congrArg
        (fun f : AT₁.smoothSections →ₗ[ℂ] BT₁.smoothSections ↦ f w) hU₁
    have hQw : (∑ i, ∑ j, (Q₁ i j).toLinearMap w) =
        ∑ i, ∑ j, O₁ i j (Uloc₁ i j (I₁ i j w)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg
        (fun f : AT₁.smoothSections →ₗ[ℂ] BT₁.smoothSections ↦ f w) (hQ₁ i j)
    have heq := congrArg
      (fun v : BT₁.smoothSections ↦
        ‖Lo₁.smoothToSobolev (-1) (C.horizontalLift S E A₁ σ₁ E' hσ₁ w - v)‖)
      (hUw.trans hQw)
    exact heq.trans_le h

end AtiyahSinger
