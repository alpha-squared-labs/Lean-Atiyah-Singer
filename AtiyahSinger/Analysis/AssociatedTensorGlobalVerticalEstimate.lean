/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalL2Bound
public import AtiyahSinger.Analysis.AssociatedTensorLocalizedVerticalEstimate

/-!
# Global control of the localized vertical H¹ family

Public module ID: M0152.

The full sphere parametrix bounds the H¹ norm of the localized whole-fiber
family by its input and vertical-output L² norms. Global metric comparisons
bound those terms using the supplied native metrics and smooth isomorphisms.
Pointwise coordinate identities identify the independently obtained families,
so all three estimates apply to the same section and vertical image. This
supplies the vertical part of the joint graph estimate.
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
  [T2Space B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

include k k' in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3200000 in
-- The extended limit accommodates the global-to-local vertical graph and Sobolev estimates.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual global input and vertical output control the localized whole-fiber H¹ norm. -/
theorem exists_associatedSphereTensorLocalizedVertical_global_sobolev_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic)
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1) :
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
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI := associatedSphereChartedSpace S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
      ∀ (_G₀ : AtlasBundlePresentation AT) (_G₀' : AtlasBundlePresentation AT')
        (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
        (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
        (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
        (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
        (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
        (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
        letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
        ∀ (e : Iso T N.Fiber)
          (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
            e.toHom.linearMap)
          (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
            e.symm.toHom.linearMap)
          (e' : Iso T' N'.Fiber)
          (he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
            e'.toHom.linearMap)
          (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
            e'.symm.toHom.linearMap),
          (∀ (z : Z) (v w : T z),
            kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
              (l.toCore z).inner v w) →
          (∀ (z : Z) (v w : T' z),
            kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
              (l'.toCore z).inner v w) →
          let sectionEquiv :=
            (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
              (nativeSmoothSectionLinearEquiv N.Fiber)
          let sectionEquiv' :=
            (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
              e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
          let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
          let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
          ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
            ∃ u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber,
              (∀ (z : Xp) (i : Fin a), u z i = nativeSmoothSectionLinearEquiv F.Fiber
                ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
                  associatedSphereTensorLocalFiberCoordinates S E A b input.frame
                    input.frame_mem_atlas i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                    (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
              ∃ h₁ : ∀ i : Fin a,
                  MemLp (fun z ↦ L.smoothToSobolev 1 (u z i)) 2 (volume : Measure Xp),
                ∀ i : Fin a, ‖(h₁ i).toLp (fun z ↦ L.smoothToSobolev 1 (u z i))‖ ≤
                  C * (‖inclusion w‖ + ‖inclusion' (V w)‖) := by
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
  -- Fix the full-Q parametrix constant and retain its exact equivariance witness.
  have hverticalData := exists_associatedSphereTensorLocalizedVertical_sobolev_bound (a := a)
    S E F F' σ σ' hσ hσ' k k' ν Q hQ hQell L L' b input hc hinput
    χ hχ hχsupport hχone
  have hQA : QA.IsEquivariant IG σ σ' hA hA' := hverticalData.choose
  have hverticalSpec := hverticalData.choose_spec
  let C : ℝ := hverticalSpec.choose
  have hC := hverticalSpec.choose_spec.1
  have hvertical := hverticalSpec.choose_spec.2
  refine ⟨hQA, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
  dsimp only
  intro G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
  intro e he hi e' he' hi' hpair hpair'
  let sectionEquiv :=
    (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
      (nativeSmoothSectionLinearEquiv N.Fiber)
  let sectionEquiv' :=
    (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber) e' he' hi').trans
      (nativeSmoothSectionLinearEquiv N'.Fiber)
  let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
  let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
  -- Both global L² comparisons use the given native realization and its original metric.
  have hinputData := exists_associatedSphereTensorLocalizedFiber_global_l2_bound (a := a)
    S E F σ hσ b input hc hinput χ hχ hχsupport hχone L k ν
    G₀ l hl N kGlobal η e he hi hpair
  let C₀ : ℝ := hinputData.choose
  have hC₀ := hinputData.choose_spec.1
  have hinputBound := hinputData.choose_spec.2
  have houtputData := exists_associatedSphereTensorLocalizedFiber_global_l2_bound (a := a)
    S E F' σ' hσ' b input hc hinput χ hχ hχsupport hχone L' k' ν
    G₀' l' hl' N' kGlobal' η e' he' hi' hpair'
  let C₁ : ℝ := houtputData.choose
  have hC₁ := houtputData.choose_spec.1
  have houtputBound := houtputData.choose_spec.2
  refine ⟨C * (C₀ + C₁), mul_nonneg hC (add_nonneg hC₀ hC₁), ?_⟩
  intro w
  let u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
    (hvertical w).choose
  let v : Xp → Fin a → smoothSections (n := r) (r := F'.rank) F'.Fiber :=
    (hvertical w).choose_spec.choose
  have huvalue := (hvertical w).choose_spec.choose_spec.1
  have hvvalue := (hvertical w).choose_spec.choose_spec.2.1
  have hmembers := (hvertical w).choose_spec.choose_spec.2.2
  have hu := hmembers.choose
  have hv := hmembers.choose_spec.choose
  have h₁ := hmembers.choose_spec.choose_spec.choose
  have hgraph := hmembers.choose_spec.choose_spec.choose_spec
  let u₀ : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
    (hinputBound w).choose
  have hu₀value := (hinputBound w).choose_spec.1
  have hu₀ := (hinputBound w).choose_spec.2.2.choose
  have hu₀bound := (hinputBound w).choose_spec.2.2.choose_spec
  let v₀ : Xp → Fin a → smoothSections (n := r) (r := F'.rank) F'.Fiber :=
    (houtputBound (V w)).choose
  have hv₀value := (houtputBound (V w)).choose_spec.1
  have hv₀ := (houtputBound (V w)).choose_spec.2.2.choose
  have hv₀bound := (houtputBound (V w)).choose_spec.2.2.choose_spec
  -- The pointwise coordinate formulas identify families, not merely their separate norms.
  have huEq : u₀ = u := by
    funext z i
    exact (hu₀value z i).trans (huvalue z i).symm
  have hvEq : v₀ = v := by
    funext z i
    exact (hv₀value z i).trans (hvvalue z i).symm
  have hinputNorm (i : Fin a) :
      ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ ≤ C₀ * ‖inclusion w‖ := by
    have heq : (hu₀ i).toLp (fun z ↦ k.smoothToL2 ν (u₀ z i)) =
        (hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i)) := by
      apply Lp.ext
      filter_upwards [(hu₀ i).coeFn_toLp, (hu i).coeFn_toLp] with z hz₀ hz
      exact hz₀.trans ((congrArg (k.smoothToL2 ν)
        (congrFun (congrFun huEq z) i)).trans hz.symm)
    exact (congrArg norm heq).symm.trans_le (hu₀bound i)
  have houtputNorm (i : Fin a) :
      ‖(hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i))‖ ≤ C₁ * ‖inclusion' (V w)‖ := by
    have heq : (hv₀ i).toLp (fun z ↦ k'.smoothToL2 ν (v₀ z i)) =
        (hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i)) := by
      apply Lp.ext
      filter_upwards [(hv₀ i).coeFn_toLp, (hv i).coeFn_toLp] with z hz₀ hz
      exact hz₀.trans ((congrArg (k'.smoothToL2 ν)
        (congrFun (congrFun hvEq z) i)).trans hz.symm)
    exact (congrArg norm heq).symm.trans_le (hv₀bound i)
  refine ⟨u, huvalue, h₁, ?_⟩
  intro i
  apply (hgraph i).trans
  calc
    C * (‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ +
        ‖(hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i))‖) ≤
        C * (C₀ * ‖inclusion w‖ + C₁ * ‖inclusion' (V w)‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (hinputNorm i) (houtputNorm i)) hC
    _ ≤ C * ((C₀ + C₁) * (‖inclusion w‖ + ‖inclusion' (V w)‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith only [mul_nonneg hC₀ (norm_nonneg (inclusion' (V w))),
        mul_nonneg hC₁ (norm_nonneg (inclusion w))]
    _ = C * (C₀ + C₁) * (‖inclusion w‖ + ‖inclusion' (V w)‖) :=
      (mul_assoc _ _ _).symm

end AtiyahSinger
