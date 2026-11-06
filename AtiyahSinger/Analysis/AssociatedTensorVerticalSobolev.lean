/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalCoordinates
public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Analysis.MetricSobolevParametrix

/-!
# Vertical Sobolev reconstruction for the actual associated operator (M2320)

The full elliptic sphere PDO supplies two fixed bounded reconstruction maps
from its specified metric L² graph into its original sphere H¹ space. The
exact associated vertical coordinate formula identifies that graph with the
original input and vertical-output coordinates in every principal/base frame.
The same maps act on L² families over the base, with a uniform norm estimate.

No finite separated expansion or global tensor decomposition of an upstairs
section is assumed. Input and output membership in these coordinate L²
families remains an explicit hypothesis; comparison with the global associated
metric and the complete associated H¹ norm is a further localization step.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
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
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

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
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
  [MeasurableSpace B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the full fiber-coordinate reconstruction from the vertical graph.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual vertical graph reconstructs all original fiber coordinates in sphere H¹. -/
theorem exists_associatedSphereTensorVertical_sobolev_reconstruction
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic)
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    ∃ hQA : QA.IsEquivariant IG σ σ' hA hA',
      ∃ R : k'.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
      ∃ R₀ : k.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
        letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
        letI : TopologicalSpace (TotalSpace Unit T) :=
          tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
        letI : TopologicalSpace (TotalSpace Unit T') :=
          tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
        letI := associatedSphereChartedSpace S
        letI := linearModelChartedSpace
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
        let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
        ∀ (b : B) (e : Trivialization (EuclideanSpace ℂ (Fin a))
            (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
          (i : Fin a) (ρ : B → ℂ)
          (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hA).smoothSections),
          let u := fun x ↦ nativeSmoothSectionLinearEquiv F.Fiber
            (ρ x • associatedSphereTensorLocalFiberCoordinates S E A b e he i
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w) x)
          let v := fun x ↦ nativeSmoothSectionLinearEquiv F'.Fiber
            (ρ x • associatedSphereTensorLocalFiberCoordinates S E A' b e he i
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a)
                S E A' σ' hA' p (V w)) x)
          (∀ x, L.smoothToSobolev 1 (u x) =
            R (k'.smoothToL2 ν (v x)) + R₀ (k.smoothToL2 ν (u x))) ∧
          ∀ (μ : Measure B)
            (hu : MemLp (fun x ↦ k.smoothToL2 ν (u x)) 2 μ)
            (hv : MemLp (fun x ↦ k'.smoothToL2 ν (v x)) 2 μ),
            let fu := hu.toLp (fun x ↦ k.smoothToL2 ν (u x))
            let fv := hv.toLp (fun x ↦ k'.smoothToL2 ν (v x))
            let g := R.compLpL 2 μ fv + R₀.compLpL 2 μ fu
            g =ᵐ[μ] (fun x ↦ L.smoothToSobolev 1 (u x)) ∧
              ‖g‖ ≤ (‖R‖ + ‖R₀‖) * (‖fu‖ + ‖fv‖) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let QA := Q.toAtlasPseudodifferentialOperator
  have hQA : QA.IsEquivariant IG σ σ' hA hA' :=
    (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
  -- Choose the actual elliptic graph reconstruction before every base chart and section.
  have hparam :
      ∃ R : k'.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
      ∃ R₀ : k.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
        ∀ z : smoothSections (n := r) (r := F.rank) F.Fiber,
          L.smoothToSobolev 1 z =
            R (k'.smoothToL2 ν (Q.toLinearMap z)) + R₀ (k.smoothToL2 ν z) :=
    PseudodifferentialOperator.exists_metricSobolev_left_parametrix
      (n := r) (r := F.rank) (q := F'.rank) (M := Y)
      (E := F.Fiber) (F := F'.Fiber) (μ := ν) k k' Q hQell L L'
  obtain ⟨R, R₀, hsplit⟩ := hparam
  refine ⟨hQA, R, R₀, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
  dsimp only
  intro b e he i ρ w
  let u := fun x ↦ nativeSmoothSectionLinearEquiv F.Fiber
    (ρ x • associatedSphereTensorLocalFiberCoordinates S E A b e he i
      (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w) x)
  let v := fun x ↦ nativeSmoothSectionLinearEquiv F'.Fiber
    (ρ x • associatedSphereTensorLocalFiberCoordinates S E A' b e he i
      (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A' σ' hA' p (V w)) x)
  -- The complete original vertical map is exactly Q on these same normalized coordinates.
  have hvu (x : B) : v x = Q.toLinearMap (u x) :=
    congrArg (nativeSmoothSectionLinearEquiv F'.Fiber)
      (associatedSphereTensorVerticalOperator_localFiberCoordinates (a := a)
        S E A σ hA A' σ' hA' QA hQA b e he i ρ w x)
  have hpoint (x : B) : L.smoothToSobolev 1 (u x) =
      R (k'.smoothToL2 ν (v x)) + R₀ (k.smoothToL2 ν (u x)) := by
    rw [hvu]
    exact hsplit (u x)
  -- Prove the L² amplification with arbitrary Hilbert-valued families before substitution.
  have hLp (f₀ : B → k.L2SectionSpace ν) (f₁ : B → k'.L2SectionSpace ν)
      (f : B → L.SobolevSpace 1) (hf : ∀ x, f x = R (f₁ x) + R₀ (f₀ x))
      (μ : Measure B) (hf₀ : MemLp f₀ 2 μ) (hf₁ : MemLp f₁ 2 μ) :
      let fu := hf₀.toLp f₀
      let fv := hf₁.toLp f₁
      let g := R.compLpL 2 μ fv + R₀.compLpL 2 μ fu
      g =ᵐ[μ] f ∧ ‖g‖ ≤ (‖R‖ + ‖R₀‖) * (‖fu‖ + ‖fv‖) := by
    let fu := hf₀.toLp f₀
    let fv := hf₁.toLp f₁
    let g := R.compLpL 2 μ fv + R₀.compLpL 2 μ fu
    constructor
    · filter_upwards [R.coeFn_compLpL fv, R₀.coeFn_compLpL fu,
        Lp.coeFn_add (R.compLpL 2 μ fv) (R₀.compLpL 2 μ fu),
        hf₀.coeFn_toLp, hf₁.coeFn_toLp] with x hxR hxR₀ hxadd hxu hxv
      exact hxadd.trans ((congrArg₂ (· + ·) hxR hxR₀).trans
        ((congrArg₂ (· + ·) (congrArg R hxv) (congrArg R₀ hxu)).trans (hf x).symm))
    · have hR : ‖R.compLpL 2 μ fv‖ ≤ ‖R‖ * ‖fv‖ := R.norm_compLp_le fv
      have hR₀ : ‖R₀.compLpL 2 μ fu‖ ≤ ‖R₀‖ * ‖fu‖ := R₀.norm_compLp_le fu
      calc
        ‖g‖ ≤ ‖R.compLpL 2 μ fv‖ + ‖R₀.compLpL 2 μ fu‖ := norm_add_le _ _
        _ ≤ ‖R‖ * ‖fv‖ + ‖R₀‖ * ‖fu‖ := add_le_add hR hR₀
        _ ≤ (‖R‖ + ‖R₀‖) * (‖fu‖ + ‖fv‖) := by
          nlinarith [mul_nonneg (norm_nonneg R) (norm_nonneg fu),
            mul_nonneg (norm_nonneg R₀) (norm_nonneg fv)]
  exact ⟨hpoint, hLp _ _ _ hpoint⟩

end AtiyahSinger
