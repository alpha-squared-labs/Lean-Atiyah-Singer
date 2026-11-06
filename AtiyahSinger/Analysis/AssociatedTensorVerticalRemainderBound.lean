/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalL2Bound
public import AtiyahSinger.Analysis.AssociatedTensorGlobalReturnBound
public import AtiyahSinger.Analysis.AssociatedTensorVerticalRemainder

/-!
# Global L² bounds for supported fiber operators

Public module ID: M0212.

A supplied smooth upstairs map with normalized return and support certificates
is bounded in the specified global native L² models. A base plateau determines
its input and output whole-fiber families. Contracting the tensor return
commutes with the supplied sphere map and bounded base multiplier; a supplied
Sobolev-zero realization gives the fiber bound in the prescribed metrics.

The sphere map need not be equivariant or smoothing. This interface also
applies to smoothing residuals and Green maps with a supplied fiber H⁰ bound,
while retaining the same upstairs map. It asserts no tensor compactness.
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
set_option maxHeartbeats 3600000 in
-- Normalize the supported fiber return and the supplied H⁰ operator bound.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A supported fiber return with a supplied H⁰ bound has a global native L² bound. -/
theorem exists_associatedSphereTensorFiberOperator_global_l2_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1)
    (θ : B → ℝ) (Cθ : ℝ) (hCθ : 0 ≤ Cθ) (hθ : ∀ x, ‖θ x‖ ≤ Cθ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (R : A.smoothSections →ₗ[ℂ] A'.smoothSections)
      (R₀ : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0),
      (∀ u : A.smoothSections, R₀ (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        L'.toAtlasBundlePresentation.smoothToSobolev 0 (R u)) →
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
      letI (x : B) : FiniteDimensional ℂ (E x) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      ∀ W : AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
        (∀ w z, (W w).val z ≠ 0 → πS z ∈ c.symm '' {x | input.cutoff x = 1}) →
        (∀ w x, x ∈ c.source → x ∈ (S.trivialization b).baseSet →
          x ∈ input.frame.baseSet → ∀ y : Y,
            let q := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
            (W w).val (associatedBundleMk G P Y q y) =
              (θ x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections R
                  (associatedSphereTensorFiberRestriction (a := a) S E A σ hA q w)).val y)) →
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
              ‖inclusion' (W w)‖ ≤ C * ‖inclusion w‖ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
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
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
  dsimp only
  intro R R₀ hR₀value W hW hreturn G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
  intro e he hi e' he' hi' hpair hpair'
  let sectionEquiv :=
    (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
      (nativeSmoothSectionLinearEquiv N.Fiber)
  let sectionEquiv' :=
    (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
      e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
  let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
  let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
  let en := nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber
  let en' := nativeSmoothSectionLinearEquiv (n := r) (r := F'.rank) F'.Fiber
  let a₀ := L.nativeAtlasSobolevEquiv 0
  let b₀ := L'.nativeAtlasSobolevEquiv 0
  let em := k.sobolevZeroEquivL2 (μ := ν) L
  let em' := k'.sobolevZeroEquivL2 (μ := ν) L'
  -- Transport the supplied Sobolev-zero realization to the two sphere metric models.
  let Rmetric : k.L2SectionSpace ν →L[ℂ] k'.L2SectionSpace ν :=
    em'.toContinuousLinearMap.comp (b₀.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R₀.comp (a₀.toContinuousLinearEquiv.toContinuousLinearMap.comp
        em.symm.toContinuousLinearMap)))
  have hRmetric (v : smoothSections (n := r) (r := F.rank) F.Fiber) :
      Rmetric (k.smoothToL2 ν v) = k'.smoothToL2 ν (en' (R (en.symm v))) := by
    have hinputValue : a₀ (em.symm (k.smoothToL2 ν v)) =
        L.toAtlasBundlePresentation.smoothToSobolev 0 (en.symm v) := by
      have hem : em.symm (k.smoothToL2 ν v) = L.smoothToSobolev 0 v :=
        (congrArg em.symm (k.sobolevZeroEquivL2_smooth (μ := ν) L v).symm).trans
          (em.symm_apply_apply _)
      exact (congrArg a₀ hem).trans (L.nativeAtlasSobolevEquiv_smoothToSobolev 0 v)
    have houtputValue (v' : A'.smoothSections) :
        em' (b₀.symm (L'.toAtlasBundlePresentation.smoothToSobolev 0 v')) =
          k'.smoothToL2 ν (en' v') := by
      have hn : b₀ (L'.smoothToSobolev 0 (en' v')) =
          L'.toAtlasBundlePresentation.smoothToSobolev 0 v' :=
        (L'.nativeAtlasSobolevEquiv_smoothToSobolev 0 (en' v')).trans
          (congrArg (L'.toAtlasBundlePresentation.smoothToSobolev 0)
            (en'.symm_apply_apply v'))
      have hb : b₀.symm (L'.toAtlasBundlePresentation.smoothToSobolev 0 v') =
          L'.smoothToSobolev 0 (en' v') :=
        (congrArg b₀.symm hn.symm).trans (b₀.symm_apply_apply _)
      exact (congrArg em' hb).trans (k'.sobolevZeroEquivL2_smooth (μ := ν) L' (en' v'))
    exact (congrArg (fun t ↦ em' (b₀.symm (R₀ t))) hinputValue).trans
      ((congrArg (fun t ↦ em' (b₀.symm t)) (hR₀value (en.symm v))).trans (houtputValue _))
  have hinputData := exists_associatedSphereTensorLocalizedFiber_global_l2_bound (a := a)
    S E F σ hσ b input hc hinput χ hχ hχsupport hχone L k ν
    G₀ l hl N kGlobal η e he hi hpair
  let Cinput : ℝ := hinputData.choose
  have hCinput := hinputData.choose_spec.1
  have hinputBound := hinputData.choose_spec.2
  have houtputData := exists_associatedSphereTensorLocalizedFiber_global_return_bound (a := a)
    S E F' σ' hσ' b input hc hinput χ hχ hχsupport hχone L' k' ν
    G₀' l' hl' N' kGlobal' η e' he' hi' hpair'
  let Coutput : ℝ := houtputData.choose
  have hCoutput := houtputData.choose_spec.1
  have houtputBound := houtputData.choose_spec.2
  let Cfiber : ℝ := Cθ * ‖Rmetric‖
  have hCfiber : 0 ≤ Cfiber := mul_nonneg hCθ (norm_nonneg Rmetric)
  refine ⟨Coutput * (a * (Cfiber * Cinput)),
    mul_nonneg hCoutput (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCfiber hCinput)), ?_⟩
  intro w
  let u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
    (hinputBound w).choose
  have huvalue := (hinputBound w).choose_spec.1
  have hu := (hinputBound w).choose_spec.2.2.choose
  have hubound := (hinputBound w).choose_spec.2.2.choose_spec
  let v : Xp → Fin a → smoothSections (n := r) (r := F'.rank) F'.Fiber :=
    (houtputBound (W w) (hW w)).choose
  have hvvalue := (houtputBound (W w) (hW w)).choose_spec.1
  have hv := (houtputBound (W w) (hW w)).choose_spec.2.2.choose
  have hvbound := (houtputBound (W w) (hW w)).choose_spec.2.2.choose_spec
  -- The normalized representative identifies the whole-fiber output family before estimation.
  have hvR (z : Xp) (i : Fin a) : v z i =
      (θ (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)) : ℂ) •
        en' (R (en.symm (u z i))) := by
    let x₀ := (EuclideanSpace.equiv (Fin n) ℝ).symm z
    let x := c.symm x₀
    by_cases hz : input.cutoff x₀ = 0
    · have hu0 : u z i = 0 := by
        apply (huvalue z i).trans
        change en ((input.cutoff x₀ : ℂ) • _) = 0
        rw [hz, Complex.ofReal_zero, zero_smul, map_zero]
      have hv0 : v z i = 0 := by
        apply (hvvalue z i).trans
        change en' ((input.cutoff x₀ : ℂ) • _) = 0
        rw [hz, Complex.ofReal_zero, zero_smul, map_zero]
      simp only [hu0, hv0, map_zero, smul_zero]
    · have hs := subset_tsupport input.cutoff hz
      have hxc : x ∈ c.source := c.map_target (input.support_subset hs).1
      have hxp : x ∈ (S.trivialization b).baseSet := hinput ⟨x₀, hs, rfl⟩
      have hxf : x ∈ input.frame.baseSet := (input.support_subset hs).2
      let q := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      let U := associatedSphereTensorFiberRestriction (a := a) S E A σ hA
      let U' := associatedSphereTensorFiberRestriction (a := a) S E A' σ' hA'
      have hrestriction : U' q (W w) = (θ x : ℂ) •
          tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
            R (U q w) := by
        apply Subtype.ext
        funext y
        apply (associatedSphereTensorFiberEquiv S E σ' q y).injective
        rw [associatedSphereTensorFiberRestriction_apply, hreturn w x hxc hxp hxf y]
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
        rfl
      let ci := associatedSphereTensorLocalFiberCoordinates S E A b input.frame
        input.frame_mem_atlas i (fun p ↦ U p w) x
      let co := associatedSphereTensorLocalFiberCoordinates S E A' b input.frame
        input.frame_mem_atlas i (fun p ↦ U' p (W w)) x
      have hcoordinate : co = (θ x : ℂ) • R ci := by
        let := input.frame_mem_atlas
        let φ : E (projection q) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
          ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
            ((input.frame.linearEquivAt ℂ x hxf).toLinearMap.comp
              (LinearEquiv.cast (R := ℂ) (M := E)
                ((S.trivialization b).proj_symm_apply' hxp)).toLinearMap))
        have hcontract := tensorSectionOperator_contract (E (projection q)) A.smoothSections
          A'.smoothSections R (U q w) φ
        apply Subtype.ext
        simp only [co, ci, associatedSphereTensorLocalFiberCoordinates,
          dite_eq_left (show x ∈ (S.trivialization b).baseSet ∩ input.frame.baseSet
            from ⟨hxp, hxf⟩)]
        change (fun y ↦ TensorProduct.lid ℂ (F'.Fiber y)
          (TensorProduct.map φ LinearMap.id ((U' q (W w)).val y))) = _
        rw [hrestriction]
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
        exact congrArg (fun f : ∀ y, F'.Fiber y ↦ (θ x : ℂ) • f) hcontract
      have hinputValue : en.symm (u z i) = (input.cutoff x₀ : ℂ) • ci := by
        have h := congrArg en.symm (huvalue z i)
        exact h.trans (en.symm_apply_apply _)
      change v z i = (θ x : ℂ) • en' (R (en.symm (u z i)))
      rw [hinputValue]
      have houtputValue : v z i = en' ((input.cutoff x₀ : ℂ) • co) := hvvalue z i
      rw [houtputValue, hcoordinate]
      calc
        en' ((input.cutoff x₀ : ℂ) • ((θ x : ℂ) • R ci)) =
            (input.cutoff x₀ : ℂ) • ((θ x : ℂ) • en' (R ci)) :=
          (en'.map_smul _ _).trans
            (congrArg ((input.cutoff x₀ : ℂ) • ·) (en'.map_smul _ _))
        _ = (θ x : ℂ) • ((input.cutoff x₀ : ℂ) • en' (R ci)) := smul_comm _ _ _
        _ = (θ x : ℂ) • en' (R ((input.cutoff x₀ : ℂ) • ci)) :=
          congrArg ((θ x : ℂ) • ·) ((en'.map_smul _ _).symm.trans
            (congrArg en' (R.map_smul _ _).symm))
  have hrow (i : Fin a) :
      ‖(hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i))‖ ≤
        Cfiber * ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ := by
    have hpoint (z : Xp) : ‖k'.smoothToL2 ν (v z i)‖ ≤
        Cfiber * ‖k.smoothToL2 ν (u z i)‖ := by
      let x := c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)
      have hvalue : k'.smoothToL2 ν (v z i) =
          (θ x : ℂ) • Rmetric (k.smoothToL2 ν (u z i)) :=
        (congrArg (k'.smoothToL2 ν) (hvR z i)).trans
          (((k'.smoothToL2 ν).map_smul (θ x : ℂ) _).trans
            (congrArg ((θ x : ℂ) • ·) (hRmetric (u z i)).symm))
      have hnorm : ‖k'.smoothToL2 ν (v z i)‖ =
          ‖θ x‖ * ‖Rmetric (k.smoothToL2 ν (u z i))‖ := by
        rw [hvalue, norm_smul, Complex.norm_real]
      exact hnorm.trans_le
        ((mul_le_mul (hθ x) (Rmetric.le_opNorm _) (norm_nonneg _) hCθ).trans_eq
          (mul_assoc _ _ _).symm)
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hv i).coeFn_toLp, (hu i).coeFn_toLp] with z hvz huz
    exact (congrArg norm hvz).trans_le ((hpoint z).trans_eq
      (congrArg (fun t ↦ Cfiber * ‖t‖) huz.symm))
  -- A finite real inequality combines the row bounds.
  have hfinite (m : ℕ) (f g : Fin m → ℝ) (c₁ c₂ c₃ t : ℝ)
      (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
      (hf : ∀ i : Fin m, f i ≤ c₂ * g i) (hg : ∀ i : Fin m, g i ≤ c₃ * t) :
      c₁ * (∑ i : Fin m, f i) ≤ c₁ * (m * (c₂ * c₃)) * t := by
    have hsum : (∑ i : Fin m, f i) ≤ ∑ _i : Fin m, c₂ * c₃ * t := by
      apply Finset.sum_le_sum
      intro i _
      exact (hf i).trans ((mul_le_mul_of_nonneg_left (hg i) hc₂).trans_eq
        (mul_assoc _ _ _).symm)
    have hbound := mul_le_mul_of_nonneg_left hsum hc₁
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using hbound
  -- Sum the same finite rows, then return to the exact original global output section.
  exact hvbound.trans (hfinite a
    (fun i ↦ ‖(hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i))‖)
    (fun i ↦ ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖)
    Coutput Cfiber Cinput ‖inclusion w‖ hCoutput hCfiber hrow hubound)

end AtiyahSinger
