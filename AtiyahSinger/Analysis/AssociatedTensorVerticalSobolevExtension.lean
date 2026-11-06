/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalRemainderBound
public import AtiyahSinger.Analysis.AssociatedTensorGlobalResidualL2Bound
public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalFamilyRegularization
public import AtiyahSinger.Analysis.AtlasMetricL2Equivalence
public import AtiyahSinger.Analysis.AtlasQuantizationAsymptotics
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.NativePresentationChartCutoff

/-!
# The full vertical operator on specified Sobolev spaces

Public module ID: M0214.

Equality of the supplied principal class with its prescribed quantization
gives an order-zero sphere residual. The quantized finite family has an
H¹-to-H⁰ extension, and that exact residual has a global L² extension in the
same associated bundle and metric models. Adding the residual after the H¹
inclusion recovers the complete vertical operator on smooth inputs.
-/

@[expose] public noncomputable section

set_option Elab.async false

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
-- The extended limit accommodates the original vertical operator on both atlas Sobolev domains.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the original vertical operator on both atlas Sobolev domains.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The whole original vertical operator extends on the two specified atlas Sobolev domains. -/
theorem exists_associatedSphereTensorVertical_sobolevExtension
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
      (hQ : Q.IsEquivariant IG σ σ' hA hA')
      (q : atlasGlobalSymbolSpace A A' 1)
      (_hq : Q.principalSymbol = atlasGlobalPrincipalSymbolClass A A' 1 q)
      (_Rq : AtlasQuantizationPresentation A A'),
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
      let V := associatedSphereTensorVerticalOperator (a := a)
        S E A σ hA A' σ' hA' Q hQ
        ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
          (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
          (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
          (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
          (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
          (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
          letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
          ∀ (e : Iso T N.Fiber)
            (_he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
              e.toHom.linearMap)
            (_hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
              e.symm.toHom.linearMap)
            (e' : Iso T' N'.Fiber)
            (_he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
              e'.toHom.linearMap)
            (_hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
              e'.symm.toHom.linearMap),
            (∀ (z : Z) (v w : T z),
              kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
                (l.toCore z).inner v w) →
            (∀ (z : Z) (v w : T' z),
              kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
                (l'.toCore z).inner v w) →
            ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
              ∀ u : AT.smoothSections,
                R (Li.smoothToSobolev 1 u) = Lo.smoothToSobolev 0 (V u) := by
  as_aux_lemma_zeta =>
    classical
    have hboundBase := exists_associatedSphereTensorVerticalResidual_global_l2_bound (a := a)
      S E F F' σ σ' hσ hσ' k k' ν L L' J b hJ
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA' Q hQ q hq Rq
    -- The original principal equality gives a genuine order-zero fiber residual.
    have horder : IsAtlasPseudodifferentialOperator A A' 0
        (Q.toLinearMap - (Rq.quantize q).toLinearMap) := by
      have hp : Q.principalSymbol = (Rq.quantize q).principalSymbol :=
        hq.trans (Rq.principalSymbol_quantize q).symm
      simpa only [sub_self] using
        (AtlasPseudodifferentialOperator.principalSymbol_eq_iff A A' Q (Rq.quantize q)).mp hp
    let Qres : AtlasPseudodifferentialOperator A A' 0 :=
      ⟨Q.toLinearMap - (Rq.quantize q).toLinearMap, horder⟩
    let pieces := fun j ↦ (Rq.patch j).toPiece q
    have hRres : ∃ Rres : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0,
        ∀ u, Rres (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
          L'.toAtlasBundlePresentation.smoothToSobolev 0
            ((Q.toLinearMap - ∑ j, (pieces j).toLinearMap) u) := by
      have hR : ∃ R : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
          L'.toAtlasBundlePresentation.SobolevSpace (0 - 0),
          ∀ u : A.smoothSections,
            R (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
              L'.toAtlasBundlePresentation.smoothToSobolev (0 - 0)
                ((Q.toLinearMap - ∑ j, (pieces j).toLinearMap) u) :=
        (Qres.existsUnique_sobolevExtension L.toAtlasBundlePresentation
          L'.toAtlasBundlePresentation 0).exists
      exact Eq.mp (congrArg (fun t : ℝ ↦
        ∃ R : L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
          L'.toAtlasBundlePresentation.SobolevSpace t,
          ∀ u : A.smoothSections,
            R (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
              L'.toAtlasBundlePresentation.smoothToSobolev t
                ((Q.toLinearMap - ∑ j, (pieces j).toLinearMap) u)) (sub_self (0 : ℝ))) hR
    obtain ⟨Rres, hRres⟩ := hRres
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
    intro AT AT' V Li Lo
    let : NormedAddCommGroup (Li.SobolevSpace 1) := inferInstance
    let : NormedSpace ℂ (Li.SobolevSpace 1) := inferInstance
    let : NormedAddCommGroup (Lo.SobolevSpace 0) := inferInstance
    let : NormedSpace ℂ (Lo.SobolevSpace 0) := inferInstance
    let : AddCommGroup (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0) := inferInstance
    have hreg := exists_associatedSphereTensorVerticalGlobalFamily_regularization
      (a := a) S E A σ A' σ' hA hA' Q hQ Rq.size pieces J b hJ Li Lo
    obtain ⟨_γ, _hγ, _hcγ, _hsγ, _hbγ, _κ, _hκ, _hcκ, _hsκ,
      _hγone, _hκone, _hκin, _I, _O, _hI, _hO, Tj, Rb, _hTj, hRb,
      W, hWV, hWzero, hWreturn, _hrest⟩ := hreg
    intro l hl l' hl' N N' kGlobal kGlobal' η hη
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
    have hactual := hboundBase Q
        (fun _ ↦ Rq.size) (fun _ j ↦ pieces j) (fun _ ↦ Rres) (fun _ ↦ hRres)
        W hWzero hWreturn Li Lo l hl l' hl' N N' kGlobal kGlobal' η
        e he hi e' he' hi' hpair hpair'
    let C := hactual.choose
    have hbound : ∀ w : AT.smoothSections,
        ‖inclusion' (∑ j, W j w)‖ ≤ (∑ j, C j) * ‖inclusion w‖ :=
      hactual.choose_spec.2.2
    -- Complete the same original metric inclusions, then add the residual on H1.
    have hΦiData := AT.exists_sobolevZero_equiv_nativeL2 Li l hl N kGlobal η e he hi hpair
    let Φi := hΦiData.choose
    have hJi := hΦiData.choose_spec.2.2
    have hΦoData := AT'.exists_sobolevZero_equiv_nativeL2
      Lo l' hl' N' kGlobal' η e' he' hi' hpair'
    let Φo := hΦoData.choose
    have hΦo := hΦoData.choose_spec.1
    have hdense : DenseRange inclusion := by
      apply (kGlobal.denseRange_smoothToL2 η).mono
      rintro _ ⟨u, rfl⟩
      exact ⟨sectionEquiv.symm u,
        congrArg (kGlobal.smoothToL2 η) (sectionEquiv.apply_symm_apply u)⟩
    let f := inclusion'.comp (∑ j, W j)
    let WR := f.extendOfNorm inclusion
    have hWR (u : AT.smoothSections) : WR (inclusion u) = inclusion' (∑ j, W j u) := by
      have hb : ∃ c, ∀ u, ‖f u‖ ≤ c * ‖inclusion u‖ := by
        refine ⟨∑ j, C j, ?_⟩
        intro v
        simpa only [f, LinearMap.comp_apply, LinearMap.sum_apply] using hbound v
      simpa only [f, LinearMap.comp_apply, LinearMap.sum_apply] using
        f.extendOfNorm_eq hdense hb u
    let Ji := Φi.toContinuousLinearMap.comp (Li.sobolevInclusion 1 0 (by norm_num))
    let residual : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 :=
      Φo.symm.toContinuousLinearMap.comp (WR.comp Ji)
    let RbTyped : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := Rb
    let addMaps : Add (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0) := inferInstance
    let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 :=
      @Add.add (Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0) addMaps RbTyped residual
    refine ⟨R, ?_⟩
    intro u
    apply Φo.injective
    let x := Li.smoothToSobolev 1 u
    let t := ∑ k, ∑ j, Tj k j u
    let w := ∑ j, W j u
    have hpart : Φo (Rb x) = inclusion' t :=
      (congrArg Φo (hRb u)).trans (hΦo t)
    have hres : Φo (residual x) = inclusion' w :=
      (Φo.apply_symm_apply (WR (Ji x))).trans
        ((congrArg WR (hJi u)).trans (hWR u))
    have hv : t + w = V u := by
      have hvalue := LinearMap.congr_fun hWV u
      have heq : V u = t + w := by
        simpa only [LinearMap.add_apply, LinearMap.sum_apply] using hvalue
      exact heq.symm
    calc
      Φo (R x) = Φo (Rb x) + Φo (residual x) := map_add Φo (Rb x) (residual x)
      _ = inclusion' t + inclusion' w := congrArg₂ (· + ·) hpart hres
      _ = inclusion' (t + w) := (map_add inclusion' t w).symm
      _ = inclusion' (V u) := congrArg inclusion' hv
      _ = Φo (Lo.smoothToSobolev 0 (V u)) := (hΦo (V u)).symm

end AtiyahSinger
