/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorKernelPairGreenRealization

/-!
# The four prescribed associated joint kernels

Public module ID: M0144.

The sphere operator and its metric formal adjoint act in one supplied
associated four-corner square. Two Green constructions yield four closed-kernel
equivalences for the same two native coefficient PDOs. Output permutations
transport the opposite joint graphs while preserving their domains, kernels,
closed range and max-norm bounds. All upstairs and coefficient models remain
the supplied ones.
-/

@[expose] public noncomputable section

set_option Elab.async false


/- The auxiliary proof is closed after expanding its free local let values. -/
open Lean Elab Tactic Meta in
local elab "as_aux_lemma_zeta" " => " s:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic s)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished proof"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Cannot abstract a proof containing a recovery placeholder"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

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
  (ρ ρp : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

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
local notation "Kp" => AssociatedVectorFiber S.toIsPrincipalBundle ρp.representation
local notation "Cp" => fun b : B ↦ E b ⊗[ℂ] Kp b
local notation "Cp'" => fun b : B ↦ E' b ⊗[ℂ] Kp b

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 96000000 in
-- The extended limit accommodates the four specified joint Green-kernel constructions.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same two actual coefficient PDOs identify all four prescribed closed joint kernels. -/
theorem PrincipalPseudodifferentialLocalization.exists_associated_fourJointGreenRealization
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
    ∀ (ep : (Fin ρp.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker),
      (∀ (g : G) (y : Y) (v : Fin ρp.dimension → ℂ),
        (ep (ρp.representation g v)).val.val (g • y) =
          σ.linearMap g y ((ep v).val.val y)) →
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
      letI : TopologicalSpace (TotalSpace Unit Cp) := tensorTopology (E := E) (F := Kp)
      letI : TopologicalSpace (TotalSpace Unit Cp') := tensorTopology (E := E') (F := Kp)
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
      let AK₀ := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρp)
      let AK₁ := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a') E')
        (associatedOrthogonalRepresentationAtlas S ρp)
      let H := C₀.horizontalLift S E A' σ' E' hA'
      let H₀ := C₀.horizontalLift S E A σ E' hA
      let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' Q hQ
      let V' := associatedSphereTensorVerticalOperator (a := a') S E' A σ hA A' σ' hA' Q hQ
      let Va := associatedSphereTensorVerticalOperator (a := a) S E A' σ' hA' A σ hA Qa hQa
      let Va' := associatedSphereTensorVerticalOperator (a := a') S E' A' σ' hA' A σ hA Qa hQa
      let Pc := C₀.coefficientOperator S E E' ρ
      let Pcp := C₀.coefficientOperator S E E' ρp
      ∀ (_Γ₀ : AtlasBundlePresentation AT) (_Γ₁ : AtlasBundlePresentation AU)
        (_Γ₂ : AtlasBundlePresentation AT') (_Γ₃ : AtlasBundlePresentation AU')
        (l₀ : ContinuousHermitianMetric T) (l₁ : ContinuousHermitianMetric U)
        (l₂ : ContinuousHermitianMetric T') (l₃ : ContinuousHermitianMetric U')
        (d₀ : ContinuousHermitianMetric Cp) (d₁ : ContinuousHermitianMetric Cp')
        (ND₀ ND₁ : SmoothFiniteComplexBundle (n := n) B)
        (kD₀ : SmoothHermitianMetric (n := n) (r := ND₀.rank) ND₀.Fiber)
        (kD₁ : SmoothHermitianMetric (n := n) (r := ND₁.rank) ND₁.Fiber)
        (c₀ : ContinuousHermitianMetric C) (c₁ : ContinuousHermitianMetric C')
        (NC₀ NC₁ : SmoothFiniteComplexBundle (n := n) B)
        (N₀ N₁ N₂ N₃ : SmoothFiniteComplexBundle (n := n + r) Z)
        (kC₀ : SmoothHermitianMetric (n := n) (r := NC₀.rank) NC₀.Fiber)
        (kC₁ : SmoothHermitianMetric (n := n) (r := NC₁.rank) NC₁.Fiber)
        (k₀ : SmoothHermitianMetric (n := n + r) (r := N₀.rank) N₀.Fiber)
        (k₁ : SmoothHermitianMetric (n := n + r) (r := N₁.rank) N₁.Fiber)
        (k₂ : SmoothHermitianMetric (n := n + r) (r := N₂.rank) N₂.Fiber)
        (k₃ : SmoothHermitianMetric (n := n + r) (r := N₃.rank) N₃.Fiber),
        letI := modelTopology (EuclideanSpace ℂ (Fin ND₀.rank)) ND₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin ND₁.rank)) ND₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
        ∀ (dIso₀ : Iso Cp ND₀.Fiber) (dIso₁ : Iso Cp' ND₁.Fiber)
          (heD₀ : IsSmoothAtlasBundleMap AK₀ (nativeSmoothComplexBundleAtlas ND₀.Fiber)
            dIso₀.toHom.linearMap)
          (hiD₀ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas ND₀.Fiber) AK₀
            dIso₀.symm.toHom.linearMap)
          (heD₁ : IsSmoothAtlasBundleMap AK₁ (nativeSmoothComplexBundleAtlas ND₁.Fiber)
            dIso₁.toHom.linearMap)
          (hiD₁ : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas ND₁.Fiber) AK₁
            dIso₁.symm.toHom.linearMap)
          (cIso₀ : Iso C NC₀.Fiber) (cIso₁ : Iso C' NC₁.Fiber)
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
          (∀ (x : B) (u v : Cp x),
            kD₀.pairing x (dIso₀.linearEquiv x u) (dIso₀.linearEquiv x v) =
              (d₀.toCore x).inner u v) →
          (∀ (x : B) (u v : Cp' x),
            kD₁.pairing x (dIso₁.linearEquiv x u) (dIso₁.linearEquiv x v) =
              (d₁.toCore x).inner u v) →
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
          (∀ (p : P) (u v : E (projection p)) (s t : Fin ρp.dimension → ℂ),
            (d₀.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl t) =
              h.pairing (projection p) u v *
                ∫ y, k.pairing y ((ep s).val.val y) ((ep t).val.val y) ∂ν) →
          (∀ (p : P) (u v : E' (projection p)) (s t : Fin ρp.dimension → ℂ),
            (d₁.toCore (projection p)).inner
                (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl s)
                (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρp.representation p rfl t) =
              h'.pairing (projection p) u v *
                ∫ y, k.pairing y ((ep s).val.val y) ((ep t).val.val y) ∂ν) →
          ∀ (H₀a : AU.smoothSections →ₗ[ℂ] AT.smoothSections),
            (∀ u v, (∫ z, (l₁.toCore z).inner ((H₀ u).val z) (v.val z) ∂η) =
              ∫ z, (l₀.toCore z).inner (u.val z) ((H₀a v).val z) ∂η) →
          ∀ H₁a : AU'.smoothSections →ₗ[ℂ] AT'.smoothSections,
            (∀ u v, (∫ z, (l₃.toCore z).inner ((H u).val z) (v.val z) ∂η) =
              ∫ z, (l₂.toCore z).inner (u.val z) ((H₁a v).val z) ∂η) →
          let SD₀ := (atlasSmoothSectionEquiv AK₀
            (nativeSmoothComplexBundleAtlas ND₀.Fiber) dIso₀ heD₀ hiD₀).trans
              (nativeSmoothSectionLinearEquiv ND₀.Fiber)
          let SD₁ := (atlasSmoothSectionEquiv AK₁
            (nativeSmoothComplexBundleAtlas ND₁.Fiber) dIso₁ heD₁ hiD₁).trans
              (nativeSmoothSectionLinearEquiv ND₁.Fiber)
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
          ∀ (R₀₀ : k₀.L2SectionSpace η →ₗ.[ℂ] (k₁.L2SectionSpace η × k₂.L2SectionSpace η))
            (R₁₁ : k₃.L2SectionSpace η →ₗ.[ℂ] (k₁.L2SectionSpace η × k₂.L2SectionSpace η))
            (R₁₀ : k₁.L2SectionSpace η →ₗ.[ℂ] (k₀.L2SectionSpace η × k₃.L2SectionSpace η))
            (R₀₁ : k₂.L2SectionSpace η →ₗ.[ℂ] (k₀.L2SectionSpace η × k₃.L2SectionSpace η)),
            R₀₀.graph = (i₀.prod ((i₁.comp H₀).prod (i₂.comp V))).range.topologicalClosure →
            R₁₁.graph = (i₃.prod ((i₁.comp Va').prod (i₂.comp H₁a))).range.topologicalClosure →
            R₁₀.graph = (i₁.prod ((i₀.comp H₀a).prod (i₃.comp V'))).range.topologicalClosure →
            R₀₁.graph = (i₂.prod ((i₀.comp Va).prod (i₃.comp H))).range.topologicalClosure →
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
                  ∃ evp : Hom ((πS : Z → B) *ᵖ Kp) D,
                    (∀ (p : P) (y : Y) (v : Fin ρp.dimension → ℂ),
                      evp.linearMap (associatedBundleMk G P Y p y)
                          (associatedVectorFiberMk S.toIsPrincipalBundle
                            ρp.representation p rfl v) =
                        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl
                          ((ep v).val.val y)) ∧
                    ∃ (Φp : AK₀.smoothSections ≃ₗ[ℂ] V.ker)
                      (Ψp : AK₁.smoothSections ≃ₗ[ℂ] V'.ker),
                      (∀ u z, (Φp u).val.val z =
                        TensorProduct.map LinearMap.id (evp.linearMap z) (u.val (πS z))) ∧
                      (∀ u z, (Ψp u).val.val z =
                        TensorProduct.map LinearMap.id (evp.linearMap z) (u.val (πS z))) ∧
                      ∃ Pp : PseudodifferentialOperator
                          (n := n) (r := ND₀.rank) (q := ND₁.rank) ND₀.Fiber ND₁.Fiber μ 1,
                        Pp.toLinearMap =
                          SD₁.toLinearMap.comp (Pcp.toLinearMap.comp SD₀.symm.toLinearMap) ∧
                        Pp.IsElliptic ∧
                        ∃ (κ₀₀ : Pp.toLinearMap.ker ≃ₗ[ℂ] R₀₀.ker)
                          (κ₁₀ : (Pp.metricFormalAdjoint kD₀ kD₁).toLinearMap.ker ≃ₗ[ℂ] R₁₀.ker)
                          (κ₀₁ : Pn.toLinearMap.ker ≃ₗ[ℂ] R₀₁.ker)
                          (κ₁₁ : (Pn.metricFormalAdjoint kC₀ kC₁).toLinearMap.ker ≃ₗ[ℂ] R₁₁.ker),
                          (∀ u, (κ₀₀ u).val = i₀ (Φp (SD₀.symm u.val)).val) ∧
                          (∀ u, (κ₁₀ u).val = i₁ (Ψp (SD₁.symm u.val)).val) ∧
                          (∀ u, (κ₀₁ u).val = i₂ (Φ (S₀.symm u.val)).val) ∧
                          (∀ u, (κ₁₁ u).val = i₃ (Ψ (S₁.symm u.val)).val) ∧
                          ∃ c₀₀ c₁₀ c₀₁ c₁₁ : ℝ,
                            0 ≤ c₀₀ ∧ 0 ≤ c₁₀ ∧ 0 ≤ c₀₁ ∧ 0 ≤ c₁₁ ∧
                            (∀ u : R₀₀.domain,
                              (u : k₀.L2SectionSpace η) ∈ R₀₀.ker.orthogonal →
                              ‖(u : k₀.L2SectionSpace η)‖ ≤ c₀₀ * ‖R₀₀ u‖) ∧
                            (∀ u : R₁₀.domain,
                              (u : k₁.L2SectionSpace η) ∈ R₁₀.ker.orthogonal →
                              ‖(u : k₁.L2SectionSpace η)‖ ≤ c₁₀ * ‖R₁₀ u‖) ∧
                            (∀ u : R₀₁.domain,
                              (u : k₂.L2SectionSpace η) ∈ R₀₁.ker.orthogonal →
                              ‖(u : k₂.L2SectionSpace η)‖ ≤ c₀₁ * ‖R₀₁ u‖) ∧
                            (∀ u : R₁₁.domain,
                              (u : k₃.L2SectionSpace η) ∈ R₁₁.ker.orthogonal →
                              ‖(u : k₃.L2SectionSpace η)‖ ≤ c₁₁ * ‖R₁₁ u‖) ∧
                            IsClosed (R₀₀.toFun.range : Set
                              (k₁.L2SectionSpace η × k₂.L2SectionSpace η)) ∧
                            IsClosed (R₁₀.toFun.range : Set
                              (k₀.L2SectionSpace η × k₃.L2SectionSpace η)) ∧
                            IsClosed (R₀₁.toFun.range : Set
                              (k₀.L2SectionSpace η × k₃.L2SectionSpace η)) ∧
                            IsClosed (R₁₁.toFun.range : Set
                              (k₁.L2SectionSpace η × k₂.L2SectionSpace η)) ∧
                            FiniteDimensional ℂ R₀₀.ker ∧ FiniteDimensional ℂ R₁₀.ker ∧
                            FiniteDimensional ℂ R₀₁.ker ∧ FiniteDimensional ℂ R₁₁.ker := by
  as_aux_lemma_zeta =>
    classical
    -- Output permutation transports the graph, preserving the kernel, norm and closed range.
    have hswap {𝓧 𝓨 𝓩 : Type u}
        [NormedAddCommGroup 𝓧] [NormedSpace ℂ 𝓧]
        [NormedAddCommGroup 𝓨] [NormedSpace ℂ 𝓨]
        [NormedAddCommGroup 𝓩] [NormedSpace ℂ 𝓩]
        (M : Submodule ℂ (𝓧 × (𝓨 × 𝓩)))
        (R : 𝓧 →ₗ.[ℂ] (𝓨 × 𝓩))
        (hR : R.graph = M.topologicalClosure) :
        let swap := ContinuousLinearEquiv.prodComm ℂ 𝓨 𝓩
        let Rs := swap.toLinearMap.compPMap R
        let swapGraph := (ContinuousLinearEquiv.refl ℂ 𝓧).prodCongr swap
        Rs.graph = (M.map swapGraph.toLinearMap).topologicalClosure ∧ Rs.ker = R.ker ∧
          (∀ u : R.domain, ‖Rs u‖ = ‖R u‖) ∧
          (IsClosed (Rs.toFun.range : Set (𝓩 × 𝓨)) → IsClosed (R.toFun.range : Set (𝓨 × 𝓩))) := by
      intro swap Rs swapGraph
      have hRsmap : Rs.graph = R.graph.map swapGraph.toLinearMap := by
        ext z
        constructor
        · intro hz
          obtain ⟨u, hu, hRu⟩ := Rs.mem_graph_iff.mp hz
          exact ⟨(u.val, R u), R.mem_graph u, Prod.ext hu hRu⟩
        · rintro ⟨z, hz, rfl⟩
          obtain ⟨u, hu, hRu⟩ := R.mem_graph_iff.mp hz
          exact Rs.mem_graph_iff.mpr ⟨u, hu, congrArg swap hRu⟩
      have hRs : Rs.graph = (M.map swapGraph.toLinearMap).topologicalClosure := by
        rw [hRsmap, hR]
        ext z
        exact Set.ext_iff.mp
          (swapGraph.toHomeomorph.image_closure (M : Set (𝓧 × (𝓨 × 𝓩)))) z
      have hker : Rs.ker = R.ker := by
        ext x
        constructor
        · intro hx
          obtain ⟨u, hu, hRu⟩ := Rs.mem_ker_iff.mp hx
          exact R.mem_ker_iff.mpr ⟨u, hu, swap.injective (hRu.trans swap.map_zero.symm)⟩
        · intro hx
          obtain ⟨u, hu, hRu⟩ := R.mem_ker_iff.mp hx
          exact Rs.mem_ker_iff.mpr ⟨u, hu, (congrArg swap hRu).trans swap.map_zero⟩
      refine ⟨hRs, hker, ?_, ?_⟩
      · intro u
        change max ‖(R u).2‖ ‖(R u).1‖ = max ‖(R u).1‖ ‖(R u).2‖
        exact max_comm _ _
      · intro hclosed
        have hrange : Rs.toFun.range = R.toFun.range.map swap.toLinearMap :=
          LinearMap.range_comp _ _
        have himage := swap.symm.toHomeomorph.isClosedMap _ hclosed
        have heq : swap.symm '' (Rs.toFun.range : Set (𝓩 × 𝓨)) = R.toFun.range := by
          rw [hrange]
          ext y
          constructor
          · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
            change swap.symm (swap w) ∈ (R.toFun.range : Set (𝓨 × 𝓩))
            exact (swap.symm_apply_apply w).symm ▸ hw
          · intro hy
            exact ⟨swap y, ⟨y, hy, rfl⟩, swap.symm_apply_apply y⟩
        exact heq ▸ himage
    -- Apply the Green construction to both sphere orientations.
    let Qna := Qn.metricFormalAdjoint k k'
    have hQna : Qna.IsElliptic := (Qn.isElliptic_metricFormalAdjoint_iff k k').mpr hQn
    have hQnag : Qna.IsEquivariant IG σ' σ hσ' hσ :=
      Qn.isEquivariant_metricFormalAdjoint IG σ σ' hσ hσ' k k' hk hk' hν hQng
    have hminus := C₀.exists_associated_kernelPairGreenRealization
      S E E' F F' σ σ' hσ hσ' ρ μ ν hν hC h h' k k' hk hk' Qn hQn hQng
        L₀ L₁ Jbase Jbase' b b' hJbase hJbase'
    have hdouble : Qna.metricFormalAdjoint k' k = Qn :=
      Qn.metricFormalAdjoint_metricFormalAdjoint k k'
    have hplus := C₀.exists_associated_kernelPairGreenRealization
      S E E' F' F σ' σ hσ' hσ ρp μ ν hν hC h h' k' k hk' hk Qna hQna hQnag
        L₁ L₀ Jbase Jbase' b b' hJbase hJbase'
    -- Identify the second metric adjoint with the original sphere operator.
    dsimp only [Qna] at hplus
    generalize_proofs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hQaa at hplus
    revert hQaa
    rw [hdouble]
    intro hQaa hplus
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA' Q hQ Qa hQa ep hep e he
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
    let : TopologicalSpace (TotalSpace Unit Cp) := tensorTopology (E := E) (F := Kp)
    let : TopologicalSpace (TotalSpace Unit Cp') := tensorTopology (E := E') (F := Kp)
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    intro η
    let : IsSmoothPositiveMeasure (n := n + r) η :=
      isSmoothPositiveMeasure_associatedProductMeasure S μ ν hν
    intro AT AT' AU AU' AC AC' AK₀ AK₁ H H₀ V V' Va Va' Pc Pcp
      Γ₀ Γ₁ Γ₂ Γ₃ l₀ l₁ l₂ l₃ d₀ d₁ ND₀ ND₁ kD₀ kD₁ c₀ c₁
      NC₀ NC₁ N₀ N₁ N₂ N₃ kC₀ kC₁ k₀ k₁ k₂ k₃
    let := modelTopology (EuclideanSpace ℂ (Fin ND₀.rank)) ND₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin ND₁.rank)) ND₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin NC₀.rank)) NC₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin NC₁.rank)) NC₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₂.rank)) N₂.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin N₃.rank)) N₃.Fiber
    intro dIso₀ dIso₁ heD₀ hiD₀ heD₁ hiD₁ cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ tIso₃
      heC₀ hiC₀ heC₁ hiC₁ heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂ heT₃ hiT₃ hl₀ hl₁ hl₂ hl₃
      hmetricD₀ hmetricD₁ hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hmetricT₃
      hpure₀ hpure₁ hpure₂ hpure₃ hgram₀ hgram₁ hgramD₀ hgramD₁ H₀a hH₀a H₁a hH₁a
      SD₀ SD₁ S₀ S₁ T₀ T₁ T₂ T₃ i₀ i₁ i₂ i₃ R₀₀ R₁₁ R₁₀ R₀₁ hR₀₀ hR₁₁ hR₁₀ hR₀₁
    -- Only the opposite output order changes; both actual source domains remain fixed.
    let swap := ContinuousLinearEquiv.prodComm ℂ (k₀.L2SectionSpace η) (k₃.L2SectionSpace η)
    let R₀₁s := swap.toLinearMap.compPMap R₀₁
    let R₁₀s := swap.toLinearMap.compPMap R₁₀
    have hswap₀₁ :=
      hswap (𝓧 := k₂.L2SectionSpace η) (𝓨 := k₀.L2SectionSpace η)
        (𝓩 := k₃.L2SectionSpace η)
        (i₂.prod ((i₀.comp Va).prod (i₃.comp H))).range R₀₁ hR₀₁
    have hR₀₁map := hswap₀₁.1
    have hK₀₁s := hswap₀₁.2.1
    have hN₀₁s := hswap₀₁.2.2.1
    have hC₀₁s := hswap₀₁.2.2.2
    have hswap₁₀ :=
      hswap (𝓧 := k₁.L2SectionSpace η) (𝓨 := k₀.L2SectionSpace η)
        (𝓩 := k₃.L2SectionSpace η)
        (i₁.prod ((i₀.comp H₀a).prod (i₃.comp V'))).range R₁₀ hR₁₀
    have hR₁₀map := hswap₁₀.1
    have hK₁₀s := hswap₁₀.2.1
    have hN₁₀s := hswap₁₀.2.2.1
    have hC₁₀s := hswap₁₀.2.2.2
    have hR₀₁s : R₀₁s.graph =
        (i₂.prod ((i₃.comp H).prod (i₀.comp Va))).range.topologicalClosure := by
      let swapGraph := (ContinuousLinearEquiv.refl ℂ (k₂.L2SectionSpace η)).prodCongr swap
      let gSmooth := i₂.prod ((i₀.comp Va).prod (i₃.comp H))
      let gSwapped := i₂.prod ((i₃.comp H).prod (i₀.comp Va))
      have hcomp : swapGraph.toLinearMap.comp gSmooth = gSwapped := by
        apply LinearMap.ext
        intro u
        rfl
      exact hR₀₁map.trans (congrArg Submodule.topologicalClosure
        ((LinearMap.range_comp gSmooth swapGraph.toLinearMap).symm.trans
          (congrArg LinearMap.range hcomp)))
    have hR₁₀s : R₁₀s.graph =
        (i₁.prod ((i₃.comp V').prod (i₀.comp H₀a))).range.topologicalClosure := by
      let swapGraph := (ContinuousLinearEquiv.refl ℂ (k₁.L2SectionSpace η)).prodCongr swap
      let gSmooth := i₁.prod ((i₀.comp H₀a).prod (i₃.comp V'))
      let gSwapped := i₁.prod ((i₃.comp V').prod (i₀.comp H₀a))
      have hcomp : swapGraph.toLinearMap.comp gSmooth = gSwapped := by
        apply LinearMap.ext
        intro u
        rfl
      exact hR₁₀map.trans (congrArg Submodule.topologicalClosure
        ((LinearMap.range_comp gSmooth swapGraph.toLinearMap).symm.trans
          (congrArg LinearMap.range hcomp)))
    -- The sphere-adjoint kernel representation gives one coefficient model at corners 01 and 11.
    choose ev hev Φ Ψ hΦ hΨ Pn hPn hPnEll κ₀₁s κ₁₁ hκ₀₁s hκ₁₁
      c₀₁ c₁₁ hc₀₁ hc₁₁ hb₀₁s hb₁₁ hr₀₁s hr₁₁ hf₀₁s hf₁₁ using
      hminus e he Γ₀ Γ₁ Γ₂ Γ₃ l₀ l₁ l₂ l₃ c₀ c₁ NC₀ NC₁ N₀ N₁ N₂ N₃
        kC₀ kC₁ k₀ k₁ k₂ k₃ cIso₀ cIso₁ tIso₀ tIso₁ tIso₂ tIso₃
        heC₀ hiC₀ heC₁ hiC₁ heT₀ hiT₀ heT₁ hiT₁ heT₂ hiT₂ heT₃ hiT₃
        hl₀ hl₁ hl₂ hl₃ hmetricC₀ hmetricC₁ hmetricT₀ hmetricT₁ hmetricT₂ hmetricT₃
        hpure₀ hpure₁ hpure₂ hpure₃ hgram₀ hgram₁ H₁a hH₁a R₀₁s hR₀₁s R₁₁ hR₁₁
    -- The plus pair reverses the original sphere roles and reuses all four original models.
    choose evp hevp Φp Ψp hΦp hΨp Pp hPp hPpEll κ₀₀ κ₁₀s hκ₀₀ hκ₁₀s
      c₀₀ c₁₀ hc₀₀ hc₁₀ hb₀₀ hb₁₀s hr₀₀ hr₁₀s hf₀₀ hf₁₀s using
      hplus ep hep Γ₂ Γ₃ Γ₀ Γ₁ l₂ l₃ l₀ l₁ d₀ d₁ ND₀ ND₁ N₂ N₃ N₀ N₁
        kD₀ kD₁ k₂ k₃ k₀ k₁ dIso₀ dIso₁ tIso₂ tIso₃ tIso₀ tIso₁
        heD₀ hiD₀ heD₁ hiD₁ heT₂ hiT₂ heT₃ hiT₃ heT₀ hiT₀ heT₁ hiT₁
        hl₂ hl₃ hl₀ hl₁ hmetricD₀ hmetricD₁ hmetricT₂ hmetricT₃ hmetricT₀ hmetricT₁
        hpure₂ hpure₃ hpure₀ hpure₁ hgramD₀ hgramD₁ H₀a hH₀a R₀₀ hR₀₀ R₁₀s hR₁₀s
    let κ₀₁ := κ₀₁s.trans (LinearEquiv.ofEq _ _ hK₀₁s)
    let κ₁₀ := κ₁₀s.trans (LinearEquiv.ofEq _ _ hK₁₀s)
    refine ⟨ev, hev, Φ, Ψ, hΦ, hΨ, Pn, hPn, hPnEll, evp, hevp, Φp, Ψp, hΦp, hΨp,
      Pp, hPp, hPpEll, κ₀₀, κ₁₀, κ₀₁, κ₁₁, hκ₀₀, hκ₁₀s, hκ₀₁s, hκ₁₁,
      c₀₀, c₁₀, c₀₁, c₁₁, hc₀₀, hc₁₀, hc₀₁, hc₁₁, hb₀₀, ?_, ?_, hb₁₁,
      hr₀₀, hC₁₀s hr₁₀s, hC₀₁s hr₀₁s, hr₁₁, hf₀₀, ?_, ?_, hf₁₁⟩
    · intro u hu
      have hn := hb₁₀s u (hK₁₀s.symm ▸ hu)
      exact hn.trans_eq (congrArg (fun t : ℝ ↦ c₁₀ * t) (hN₁₀s u))
    · intro u hu
      have hn := hb₀₁s u (hK₀₁s.symm ▸ hu)
      exact hn.trans_eq (congrArg (fun t : ℝ ↦ c₀₁ * t) (hN₀₁s u))
    · exact hK₁₀s ▸ hf₁₀s
    · exact hK₀₁s ▸ hf₀₁s

end AtiyahSinger
