/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalResidualL2Bound
public import AtiyahSinger.Analysis.PairedSmoothingApproximation

/-!
# Paired smoothing of the associated vertical residual

Public module ID: M0190.

Supplied L²-bounded sphere residuals and their supported associated lifts give
a bounded extension in the fixed native metric L² spaces. A single smoothing
operator simultaneously approximates this extension and its Hilbert adjoint
after the prescribed order-one Sobolev inclusions. Both errors use the same
residual extension and the same smoothing operator.
-/

@[expose] public noncomputable section

/- This is the standard auxiliary-theorem construction with explicit expansion of
free local let values. The resulting closed declaration is checked by Lean's kernel. -/
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
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the paired whole-space smoothing and residual estimates.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The same actual vertical residual admits a simultaneous whole-space smoothing approximation. -/
theorem exists_associatedSphereTensorVerticalResidual_paired_smoothing
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (Q : AtlasPseudodifferentialOperator A A' 1)
      (Npiece : Fin J.size → ℕ)
      (Ppiece : ∀ j : Fin J.size, Fin (Npiece j) → AtlasPseudodifferentialPiece A A' 1)
      (R₀ : ∀ _j : Fin J.size, L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0),
      (∀ j u, R₀ j (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        L'.toAtlasBundlePresentation.smoothToSobolev 0
          ((Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap) u)) →
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
      ∀ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
        (∀ j (w : AT.smoothSections) z,
          πS z ∉ tsupport (J.cutoff j) → (W j w).val z = 0) →
        (∀ j (w : AT.smoothSections) x, x ∈ (J.chart j).source →
          x ∈ (S.trivialization (b j)).baseSet → x ∈ (J.frame j).baseSet → ∀ y : Y,
            let q := (S.trivialization (b j)).toOpenPartialHomeomorph.symm (x, 1)
            (W j w).val (associatedBundleMk G P Y q y) =
              (J.cutoff j x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
                  (Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap)
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
            ∃ R : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η,
              (∀ w : AT.smoothSections, R (inclusion w) = inclusion' (∑ j, W j w)) ∧
              ∀ (Li : SmoothBundlePresentation (n := n + r) (r := N.rank) N.Fiber)
                (Lo : SmoothBundlePresentation (n := n + r) (r := N'.rank) N'.Fiber)
                (ε : ℝ), 0 < ε →
                let Ii := (kGlobal.sobolevZeroEquivL2 (μ := η) Li).toContinuousLinearMap.comp
                  (Li.sobolevInclusion 1 0 (by norm_num))
                let Io := (kGlobal'.sobolevZeroEquivL2 (μ := η) Lo).toContinuousLinearMap.comp
                  (Lo.sobolevInclusion 1 0 (by norm_num))
                ∃ Ls : smoothSections (n := n + r) (r := N.rank) N.Fiber →ₗ[ℂ]
                    smoothSections (n := n + r) (r := N'.rank) N'.Fiber,
                  IsSmoothingOperator η Ls ∧
                    ∃ Rs : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η,
                      (∀ u, Rs (kGlobal.smoothToL2 η u) = kGlobal'.smoothToL2 η (Ls u)) ∧
                      ‖R.comp Ii - Rs.comp Ii‖ < ε ∧
                      ‖R.adjoint.comp Io - Rs.adjoint.comp Io‖ < ε := by
  as_aux_lemma_zeta =>
    classical
    have hbound := exists_associatedSphereTensorVerticalResidual_global_l2_bound (a := a)
      S E F F' σ σ' hσ hσ' k k' ν L L' J b hJ
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
    intro Q Npiece Ppiece R₀ hR₀ W hWzero hreturn G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
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
    have hactual := hbound Q Npiece Ppiece R₀ hR₀ W hWzero hreturn
      G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
    let C := hactual.choose
    have hCbound : ∀ w : AT.smoothSections,
        ‖inclusion' (∑ j, W j w)‖ ≤ (∑ j, C j) * ‖inclusion w‖ :=
      hactual.choose_spec.2.2
    -- Extend the literal finite residual sum along the same native smooth inclusion.
    have hdense : DenseRange inclusion := by
      have hrange : Set.range inclusion = Set.range (kGlobal.smoothToL2 η) := by
        ext v
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨sectionEquiv u, rfl⟩
        · rintro ⟨u, rfl⟩
          refine ⟨sectionEquiv.symm u, ?_⟩
          change kGlobal.smoothToL2 η (sectionEquiv (sectionEquiv.symm u)) = _
          rw [LinearEquiv.apply_symm_apply]
      change Dense (Set.range inclusion)
      rw [hrange]
      exact kGlobal.denseRange_smoothToL2 η
    let f := inclusion'.comp (∑ j, W j)
    let R : kGlobal.L2SectionSpace η →L[ℂ] kGlobal'.L2SectionSpace η :=
      f.extendOfNorm inclusion
    have hfbound (w : AT.smoothSections) : ‖f w‖ ≤ (∑ j, C j) * ‖inclusion w‖ := by
      change ‖inclusion' ((∑ j, W j) w)‖ ≤ _
      rw [LinearMap.sum_apply]
      exact hCbound w
    have hR (w : AT.smoothSections) : R (inclusion w) = inclusion' (∑ j, W j w) :=
      (f.extendOfNorm_eq hdense ⟨∑ j, C j, hfbound⟩ w).trans
        (congrArg inclusion' (LinearMap.sum_apply Finset.univ W w))
    refine ⟨R, hR, ?_⟩
    intro Li Lo ε hε
    -- All smooth sections are the prescribed dense core, with the original residual as output.
    let smoothCore : Submodule ℂ (kGlobal.SmoothL2Section η) := ⊤
    have hD : DenseRange (fun u : smoothCore ↦ kGlobal.smoothToL2 η u.val) := by
      have hrange : Set.range (fun u : smoothCore ↦ kGlobal.smoothToL2 η u.val) =
          Set.range (kGlobal.smoothToL2 η) := by
        ext v
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u.val, rfl⟩
        · rintro ⟨u, rfl⟩
          exact ⟨⟨u, Submodule.mem_top⟩, rfl⟩
      change Dense (Set.range _)
      rw [hrange]
      exact kGlobal.denseRange_smoothToL2 η
    have hcore (u : smoothCore) : ∃ v : smoothSections (n := n + r) (r := N'.rank) N'.Fiber,
        R (kGlobal.smoothToL2 η u.val) = kGlobal'.smoothToL2 η v := by
      refine ⟨sectionEquiv' (∑ j, W j (sectionEquiv.symm u.val)), ?_⟩
      have h := hR (sectionEquiv.symm u.val)
      change R (kGlobal.smoothToL2 η (sectionEquiv (sectionEquiv.symm u.val))) = _ at h
      have heq := congrArg
        (fun v : smoothSections (n := n + r) (r := N.rank) N.Fiber ↦
          R (kGlobal.smoothToL2 η v)) (sectionEquiv.apply_symm_apply u.val)
      exact heq.symm.trans h
    -- One kernel controls both original inclusions and the literal adjoint of this same R.
    exact exists_paired_smoothing_approximation_of_smooth_core
      kGlobal kGlobal' Li Lo smoothCore hD R hcore ε hε

end AtiyahSinger
