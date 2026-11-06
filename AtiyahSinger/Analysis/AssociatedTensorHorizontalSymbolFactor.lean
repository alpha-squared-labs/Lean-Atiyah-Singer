/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AtlasTensorCoefficientSymbol
public import AtiyahSinger.Analysis.FiniteAtlasProductCutoff
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff

/-!
# The actual horizontal cutoff symbol as a finite tensor factor

Public module ID: M0174.

The full finite symbol in the original associated product charts is the
identity amplification of one explicit base-fiber map. The original output
and sphere plateaus disappear only where the actual symbol and partition
supports require them to equal one. Every chart covector and frequency
cutoff remains in the finite factor, including at general cotangent vectors.

With common original charts and partition weights this factor is independent
of the sphere coefficient bundle. No equality of separately selected factors,
homogeneous replacement or discarded lower-order term is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] tensorTopology associatedEquivariantFiberAddCommGroup
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


set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The actual finite horizontal cutoff symbol has one explicit coefficient-independent factor. -/
theorem associatedSphereTensorHorizontalSymbol_eq_finiteTensorFactor
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (J : AtlasBundlePresentation A)
    (Co : BundleChartCutoff (r := a') E' L.chart) (hCoFrame : Co.frame = L.output.frame)
    (hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (hCoOne : ∀ x ∈ tsupport L.output.cutoff, Co.cutoff x = 1)
    (κ : Fin J.size → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
    (hκK : ∀ j, HasCompactSupport (κ j))
    (hκsupport : ∀ j, tsupport (κ j) ⊆ (J.chart j).target ∩
      (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet)
    (hκone : ∀ j y, y ∈ tsupport (J.chartCutoff j).cutoff → κ j y = 1)
    (ε : ℝ) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
      ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
    let CP (j : Fin J.size) := associatedSphereProductChart S b L.chart (J.chart j)
    let Din (j : Fin J.size) := associatedSphereTensorChartCutoff S E A σ hσ b
      L.chart L.input hinput (J.chart j) (J.chartCutoff j)
    let Dout (j : Fin J.size) := associatedSphereTensorChartCutoff S E' A σ hσ b
      L.chart Co hCo (J.chart j) (Kout j)
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    ∀ (g : Fin J.size → AtlasSymbolFunction (n := n + r) T T'),
      (∀ j z ξ, g j z ξ =
        if hz : z ∈ (CP j).source ∩ (AT.chart (Din j).frameIndex).baseSet ∩
            (AT'.chart (Dout j).frameIndex).baseSet then
          (((Dout j).cutoff (CP j z) * (Din j).cutoff (CP j z) : ℝ) : ℂ) •
            ((AT'.frameLinearEquiv (Dout j).frameIndex z hz.2).symm.toLinearMap.comp
              (EuclideanSpace.equiv (Fin (a' * A.rank (J.frameIndex j))) ℂ).toLinearMap).comp
              ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                (productCutoffSymbol α (κ j) ε (CP j z)
                  (covectorInChart (CP j) z ξ))).toLinearMap.comp
                (((EuclideanSpace.equiv
                  (Fin (a * A.rank (J.frameIndex j))) ℂ).symm.toLinearMap).comp
                    (AT.frameLinearEquiv (Din j).frameIndex z hz.1.2).toLinearMap))
        else 0) →
      ∀ (z : Z) (ξ : TangentSpace (𝓡 (n + r)) z →L[ℝ] ℝ),
        let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
        let cov (j : Fin J.size) := split (covectorInChart (CP j) z ξ)
        let weight (j : Fin J.size) :=
          J.cutoff j (associatedSphereTrivialization S b z).2 *
            productFrequencyCutoff ε ‖(cov j).1‖ ‖(cov j).2‖
        (∑ j, g j z ξ) = TensorProduct.map
          (∑ j, (weight j : ℂ) •
            (L.globalSymbolFunction (πS z)
              (covectorFromChart L.chart (πS z) (cov j).1)).toLinearMap)
          (LinearMap.id : Module.End ℂ (D z)) := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
    ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
  let CP (j : Fin J.size) := associatedSphereProductChart S b L.chart (J.chart j)
  let Din (j : Fin J.size) := associatedSphereTensorChartCutoff S E A σ hσ b
    L.chart L.input hinput (J.chart j) (J.chartCutoff j)
  let Dout (j : Fin J.size) := associatedSphereTensorChartCutoff S E' A σ hσ b
    L.chart Co hCo (J.chart j) (Kout j)
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  have hFrame
      (A : SmoothComplexBundleAtlas (n := n + r) ((πS : Z → B) *ᵖ E))
      (B' : SmoothComplexBundleAtlas (n := n + r) ((πS : Z → B) *ᵖ E'))
      (K : SmoothComplexBundleAtlas (n := n + r) D)
      (i : A.Index) (j : B'.Index) (k : K.Index) (x : Z)
      (hxA : x ∈ (A.chart i).baseSet) (hxB : x ∈ (B'.chart j).baseSet)
      (hxK : x ∈ (K.chart k).baseSet)
      (a : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (B'.rank j))) :
      let AT := tensorSmoothAtlas A K
      let BT := tensorSmoothAtlas B' K
      ∀ (hxAT : x ∈ (AT.chart (i, k)).baseSet) (hxBT : x ∈ (BT.chart (j, k)).baseSet),
      let eA := (A.frameLinearEquiv i x hxA).trans
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
      let eB := (B'.frameLinearEquiv j x hxB).trans
        (EuclideanSpace.equiv (Fin (B'.rank j)) ℂ).symm.toLinearEquiv
      let eAT := (AT.frameLinearEquiv (i, k) x hxAT).trans
        (EuclideanSpace.equiv (Fin (A.rank i * K.rank k)) ℂ).symm.toLinearEquiv
      let eBT := (BT.frameLinearEquiv (j, k) x hxBT).trans
        (EuclideanSpace.equiv (Fin (B'.rank j * K.rank k)) ℂ).symm.toLinearEquiv
      eBT.symm.toLinearMap.comp
        ((tensorIdentitySymbolMap _ _ (K.rank k) a).toLinearMap.comp eAT.toLinearMap) =
        TensorProduct.map
          (eB.symm.toLinearMap.comp (a.toLinearMap.comp eA.toLinearMap))
          (LinearMap.id : Module.End ℂ (D x)) := by
    classical
    let AT := tensorSmoothAtlas A K
    let BT := tensorSmoothAtlas B' K
    dsimp only
    intro hxAT hxBT
    let eA := (A.frameLinearEquiv i x hxA).trans
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
    let eB := (B'.frameLinearEquiv j x hxB).trans
      (EuclideanSpace.equiv (Fin (B'.rank j)) ℂ).symm.toLinearEquiv
    let eK := (K.frameLinearEquiv k x hxK).trans
      (EuclideanSpace.equiv (Fin (K.rank k)) ℂ).symm.toLinearEquiv
    let eAT := (AT.frameLinearEquiv (i, k) x hxAT).trans
      (EuclideanSpace.equiv (Fin (A.rank i * K.rank k)) ℂ).symm.toLinearEquiv
    let eBT := (BT.frameLinearEquiv (j, k) x hxBT).trans
      (EuclideanSpace.equiv (Fin (B'.rank j * K.rank k)) ℂ).symm.toLinearEquiv
    have hA (v : E (πS x)) (w : D x) (s : Fin (A.rank i)) (t : Fin (K.rank k)) :
        eAT (v ⊗ₜ[ℂ] w) (finProdFinEquiv (s, t)) = eA v s * eK w t := by
      change (tensorBundleChart A K i k ⟨x, v ⊗ₜ[ℂ] w⟩).2 (finProdFinEquiv (s, t)) =
        (A.chart i ⟨x, v⟩).2 s * (K.chart k ⟨x, w⟩).2 t
      exact (ComplexBundle.exists_tensor_trivialization (A.chart i) (K.chart k)
        (A.linear i) (K.linear k)).choose_spec.2.2 x ⟨hxA, hxK⟩ v w s t
    have hB (v : E' (πS x)) (w : D x) (s : Fin (B'.rank j)) (t : Fin (K.rank k)) :
        eBT (v ⊗ₜ[ℂ] w) (finProdFinEquiv (s, t)) = eB v s * eK w t := by
      change (tensorBundleChart B' K j k ⟨x, v ⊗ₜ[ℂ] w⟩).2 (finProdFinEquiv (s, t)) =
        (B'.chart j ⟨x, v⟩).2 s * (K.chart k ⟨x, w⟩).2 t
      exact (ComplexBundle.exists_tensor_trivialization (B'.chart j) (K.chart k)
        (B'.linear j) (K.linear k)).choose_spec.2.2 x ⟨hxB, hxK⟩ v w s t
    apply TensorProduct.ext'
    intro v w
    change eBT.symm (tensorIdentitySymbolMap _ _ (K.rank k) a (eAT (v ⊗ₜ[ℂ] w))) =
      eB.symm (a (eA v)) ⊗ₜ[ℂ] w
    apply eBT.injective
    rw [eBT.apply_symm_apply]
    apply PiLp.ext
    intro t
    obtain ⟨⟨s, b⟩, rfl⟩ := finProdFinEquiv.surjective t
    rw [tensorIdentitySymbolMap_apply _ (eA v) (eK w) _ (hA v w), hB,
      eB.apply_symm_apply]
  dsimp only
  intro g hg z ξ
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let dm := linearModelDiffeomorph split.symm Z
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ πS :=
    (smoothAssociatedSphereProjection S).contMDiff.comp dm.symm.contMDiff
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AE' := nativeSmoothComplexBundleAtlas (n := n) (r := a') E'
  let AC := AE.pullback πS hq
  let AC' := AE'.pullback πS hq
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let t := associatedSphereTrivialization S b
  let y := (t z).2
  let cov (j : Fin J.size) := split (covectorInChart (CP j) z ξ)
  let frequency (j : Fin J.size) : ℝ :=
    productFrequencyCutoff ε ‖(cov j).1‖ ‖(cov j).2‖
  let baseCov (j : Fin J.size) := covectorFromChart L.chart (πS z) (cov j).1
  let baseMap (j : Fin J.size) := (L.globalSymbolFunction (πS z) (baseCov j)).toLinearMap
  let tensorMap (j : Fin J.size) :=
    TensorProduct.map (baseMap j) (LinearMap.id : Module.End ℂ (D z))
  have hpoint (j : Fin J.size) :
      g j z ξ =
        ((J.cutoff j y * frequency j : ℝ) : ℂ) • tensorMap j := by
    let d := J.chart j
    let ix : AC.Index := ⟨L.input.frame, L.input.frame_mem_atlas⟩
    let ox : AC'.Index := ⟨Co.frame, Co.frame_mem_atlas⟩
    let fx : AD.Index := (b, J.frameIndex j)
    have hAD : (AD.chart fx).baseSet =
        t.source ∩ t ⁻¹' (univ ×ˢ (A.chart (J.frameIndex j)).baseSet) :=
      (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
        (S.trivialization b) (S.equivariant b) (A.chart (J.frameIndex j))
        (A.linear (J.frameIndex j))).choose_spec.1
    have hAI : (AC.chart ix).baseSet = πS ⁻¹' L.input.frame.baseSet :=
      (AE.exists_pullbackChart πS ⟨L.input.frame, L.input.frame_mem_atlas⟩).choose_spec.1
    have hAO : (AC'.chart ox).baseSet = πS ⁻¹' Co.frame.baseSet :=
      (AE'.exists_pullbackChart πS ⟨Co.frame, Co.frame_mem_atlas⟩).choose_spec.1
    have hTI : (AT.chart (Din j).frameIndex).baseSet =
        (AC.chart ix).baseSet ∩ (AD.chart fx).baseSet :=
      (exists_tensor_trivialization (AC.chart ix) (AD.chart fx)
        (AC.linear ix) (AD.linear fx)).choose_spec.1
    have hTO : (AT'.chart (Dout j).frameIndex).baseSet =
        (AC'.chart ox).baseSet ∩ (AD.chart fx).baseSet :=
      (exists_tensor_trivialization (AC'.chart ox) (AD.chart fx)
        (AC'.linear ox) (AD.linear fx)).choose_spec.1
    have hcoord (hz : z ∈ (CP j).source) :
        split (CP j z) = (L.chart (πS z), d y) := by
      have ht : z ∈ t.source := hz.1.1
      change split (split.symm ((L.chart.prod d) (t z))) = _
      rw [split.apply_symm_apply]
      change (L.chart (t z).1, d (t z).2) = _
      rw [t.coe_fst ht]
    rw [hg]
    by_cases hz : z ∈ (CP j).source ∩ (AT.chart (Din j).frameIndex).baseSet ∩
        (AT'.chart (Dout j).frameIndex).baseSet
    · rw [dite_eq_left hz]
      have hi : z ∈ (AC.chart ix).baseSet := (hTI ▸ hz.1.2).1
      have ho : z ∈ (AC'.chart ox).baseSet := (hTO ▸ hz.2).1
      have hf : z ∈ (AD.chart fx).baseSet := (hTI ▸ hz.1.2).2
      have hxs : πS z ∈ L.chart.source := by
        have h : (t z).1 ∈ L.chart.source := hz.1.1.1.2.1
        rwa [t.coe_fst hz.1.1.1.1] at h
      have hxI : πS z ∈ L.input.frame.baseSet := by
        change z ∈ πS ⁻¹' L.input.frame.baseSet
        exact hAI ▸ hi
      have hxO : πS z ∈ L.output.frame.baseSet := by
        have h : πS z ∈ Co.frame.baseSet := by
          change z ∈ πS ⁻¹' Co.frame.baseSet
          exact hAO ▸ ho
        rwa [hCoFrame] at h
      have hys : y ∈ d.source := hz.1.1.1.2.2
      have hcut : (J.chartCutoff j).cutoff (d y) = J.cutoff j y := by
        have h := J.chartCutoff_pullback j y
        change (if y ∈ d.source then (J.chartCutoff j).cutoff (d y) else 0) = _ at h
        rwa [ite_eq_left hys] at h
      have hbaseCov : covectorInChart L.chart (πS z) (baseCov j) = (cov j).1 :=
        covectorInChart_covectorFromChart L.chart L.chart_mem_atlas (πS z) hxs (cov j).1
      have hprod : productCutoffSymbol α (κ j) ε (CP j z)
          (covectorInChart (CP j) z ξ) =
          (frequency j : ℂ) • ((κ j (d y) : ℂ) •
            ((L.output.cutoff (L.chart (πS z)) : ℂ) •
              L.symbol (L.chart (πS z)) (cov j).1)) := by
        change (frequency j : ℂ) •
          ((κ j (split (CP j z)).2 : ℂ) • α (split (CP j z)).1 (cov j).1) = _
        rw [hcoord hz.1.1]
        simp only [α, zeroExtendedSymbol, mem_univ, ite_true]
      rw [hprod]
      let eIn : E (πS z) ≃ₗ[ℂ] V₀ := (AC.frameLinearEquiv ix z hi).trans
        (EuclideanSpace.equiv (Fin a) ℂ).symm.toLinearEquiv
      let eOut : E' (πS z) ≃ₗ[ℂ] V₁ := (AC'.frameLinearEquiv ox z ho).trans
        (EuclideanSpace.equiv (Fin a') ℂ).symm.toLinearEquiv
      let eTin : T z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j))) :=
        (AT.frameLinearEquiv (Din j).frameIndex z hz.1.2).trans
          (EuclideanSpace.equiv (Fin (a * A.rank (J.frameIndex j))) ℂ).symm.toLinearEquiv
      let eTout : T' z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))) :=
        (AT'.frameLinearEquiv (Dout j).frameIndex z hz.2).trans
          (EuclideanSpace.equiv (Fin (a' * A.rank (J.frameIndex j))) ℂ).symm.toLinearEquiv
      let aScaled : V₀ →L[ℂ] V₁ := (frequency j : ℂ) • ((κ j (d y) : ℂ) •
        ((L.output.cutoff (L.chart (πS z)) : ℂ) •
          L.symbol (L.chart (πS z)) (cov j).1))
      have hei : eIn =
          (L.input.frame.continuousLinearEquivAt ℂ (πS z) hxI).toLinearEquiv := by
        apply LinearEquiv.ext
        intro v
        have hpull : (AC.chart ix ⟨z, v⟩).2 =
            (EuclideanSpace.equiv (Fin a) ℂ) (L.input.frame ⟨πS z, v⟩).2 :=
          (AE.exists_pullbackChart πS ⟨L.input.frame, L.input.frame_mem_atlas⟩).choose_spec.2
            (⟨z, v⟩ : TotalSpace Unit ((πS : Z → B) *ᵖ E))
        apply PiLp.ext
        intro s
        exact congrArg (fun c : Fin a → ℂ ↦ c s) hpull
      have heo : eOut =
          (L.output.frame.continuousLinearEquivAt ℂ (πS z) hxO).toLinearEquiv := by
        apply LinearEquiv.ext
        intro v
        have hpull : (AC'.chart ox ⟨z, v⟩).2 =
            (EuclideanSpace.equiv (Fin a') ℂ) (Co.frame ⟨πS z, v⟩).2 :=
          (AE'.exists_pullbackChart πS ⟨Co.frame, Co.frame_mem_atlas⟩).choose_spec.2
            (⟨z, v⟩ : TotalSpace Unit ((πS : Z → B) *ᵖ E'))
        apply PiLp.ext
        intro s
        have h := congrArg (fun c : Fin a' → ℂ ↦ c s) hpull
        rw [hCoFrame] at h
        exact h
      have htf : eTout.symm.toLinearMap.comp
          ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j)) aScaled).toLinearMap.comp
            eTin.toLinearMap) =
          TensorProduct.map
            (eOut.symm.toLinearMap.comp (aScaled.toLinearMap.comp eIn.toLinearMap))
            (LinearMap.id : Module.End ℂ (D z)) :=
        hFrame AC AC' AD ix ox fx z hi ho hf aScaled hz.1.2 hz.2
      rw [hei, heo] at htf
      have hcutI : (Din j).cutoff (CP j z) =
          L.input.cutoff (L.chart (πS z)) * J.cutoff j y := by
        change L.input.cutoff (split (CP j z)).1 *
          (J.chartCutoff j).cutoff (split (CP j z)).2 = _
        rw [hcoord hz.1.1, hcut]
      have hcutO : (Dout j).cutoff (CP j z) =
          Co.cutoff (L.chart (πS z)) * κ j (d y) := by
        change Co.cutoff (split (CP j z)).1 * κ j (split (CP j z)).2 = _
        rw [hcoord hz.1.1]
      have hscalar : (Co.cutoff (L.chart (πS z)) * κ j (d y) *
          (L.input.cutoff (L.chart (πS z)) * J.cutoff j y)) *
          (frequency j * κ j (d y) * L.output.cutoff (L.chart (πS z))) =
          (J.cutoff j y * frequency j) *
            (L.output.cutoff (L.chart (πS z)) * L.input.cutoff (L.chart (πS z))) := by
        by_cases ho0 : L.output.cutoff (L.chart (πS z)) = 0
        · simp only [ho0, mul_zero, zero_mul]
        by_cases hj0 : J.cutoff j y = 0
        · simp only [hj0, mul_zero, zero_mul]
        have hCo1 : Co.cutoff (L.chart (πS z)) = 1 :=
          hCoOne _ (subset_tsupport _ ho0)
        have hκ1 : κ j (d y) = 1 := hκone j _ (subset_tsupport _ (by
          change (J.chartCutoff j).cutoff (d y) ≠ 0
          rw [hcut]
          exact hj0))
        rw [hCo1, hκ1]
        ring
      change ((((Dout j).cutoff (CP j z) * (Din j).cutoff (CP j z) : ℝ) : ℂ)) •
        (eTout.symm.toLinearMap.comp
          ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j)) aScaled).toLinearMap.comp
            eTin.toLinearMap)) = _
      rw [hcutI, hcutO, htf]
      apply TensorProduct.ext'
      intro v w
      have hx : πS z ∈ L.chart.source ∩ L.input.frame.baseSet ∩
          L.output.frame.baseSet := ⟨⟨hxs, hxI⟩, hxO⟩
      simp only [tensorMap, baseMap, aScaled, PseudodifferentialPiece.globalSymbolFunction,
        ite_eq_left hx, hbaseCov, LinearMap.smul_apply, TensorProduct.map_tmul,
        LinearMap.comp_apply,
        LinearMap.id_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        smul_apply, LinearEquiv.coe_coe, map_smul,
        TensorProduct.smul_tmul', smul_smul]
      have hout_apply (q : V₁) :
          (L.output.frame.continuousLinearEquivAt ℂ (πS z) hxO).toLinearEquiv.symm q =
            L.output.frame.symmL ℂ (πS z) q := by
        change (L.output.frame.continuousLinearEquivAt ℂ (πS z) hxO).symm q = _
        exact congrFun (L.output.frame.symm_continuousLinearEquivAt_eq hxO) q
      have hin_apply :
          (L.input.frame.continuousLinearEquivAt ℂ (πS z) hxI).toLinearEquiv v =
            L.input.frame.continuousLinearMapAt ℂ (πS z) v := by
        change (L.input.frame.continuousLinearEquivAt ℂ (πS z) hxI) v = _
        exact congrFun (L.input.frame.coe_continuousLinearEquivAt_eq hxI) v
      rw [hout_apply, hin_apply]
      simp only [← Complex.ofReal_mul]
      rw [hscalar]
    · rw [dite_eq_right hz]
      by_cases hj0 : J.cutoff j y = 0
      · simp only [hj0, zero_mul, Complex.ofReal_zero, zero_smul]
      have hG : L.globalSymbolFunction (πS z) (baseCov j) = 0 := by
        apply L.globalSymbolFunction_eq_zero
        rintro ⟨x, hx, hxe⟩
        have hxt := (L.output.support_subset hx.1).1
        have hxs : πS z ∈ L.chart.source := hxe ▸ L.chart.map_target hxt
        have hxI : πS z ∈ L.input.frame.baseSet :=
          hxe ▸ (L.input.support_subset hx.2).2
        have hxO : πS z ∈ L.output.frame.baseSet :=
          hxe ▸ (L.output.support_subset hx.1).2
        have hxC : πS z ∈ Co.frame.baseSet := hCoFrame.symm ▸ hxO
        have hxb : πS z ∈ (S.trivialization b).baseSet :=
          houtput ⟨x, hx.1, hxe⟩
        have htbase : t.baseSet = (S.trivialization b).baseSet :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            (S.trivialization b) (S.equivariant b)).choose_spec.1
        have ht : z ∈ t.source := t.mem_source.mpr (htbase.symm ▸ hxb)
        have hys := J.support_subset j (subset_tsupport _ hj0)
        have hcp : z ∈ (CP j).source := by
          change z ∈ ((t.toOpenPartialHomeomorph.trans (L.chart.prod d)).trans
            split.symm.toHomeomorph.toOpenPartialHomeomorph).source
          refine ⟨⟨ht, ?_⟩, Set.mem_univ _⟩
          change (t z).1 ∈ L.chart.source ∧ (t z).2 ∈ d.source
          rw [t.coe_fst ht]
          exact ⟨hxs, hys.1⟩
        have hf : z ∈ (AD.chart fx).baseSet :=
          hAD.symm ▸ ⟨ht, ⟨Set.mem_univ _, hys.2⟩⟩
        apply hz
        exact ⟨⟨hcp, hTI.symm ▸ ⟨hAI.symm ▸ hxI, hf⟩⟩,
          hTO.symm ▸ ⟨hAO.symm ▸ hxC, hf⟩⟩
      simp only [tensorMap, baseMap, hG, ContinuousLinearMap.toLinearMap_zero,
        TensorProduct.map_zero_left, smul_zero]
  change (∑ j, g j z ξ) = TensorProduct.map
    (∑ j, ((J.cutoff j y * frequency j : ℝ) : ℂ) • baseMap j)
    (LinearMap.id : Module.End ℂ (D z))
  rw [Finset.sum_congr rfl (fun j _ ↦ hpoint j)]
  apply TensorProduct.ext'
  intro v w
  simp only [tensorMap, LinearMap.sum_apply, LinearMap.smul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul']

end AtiyahSinger
