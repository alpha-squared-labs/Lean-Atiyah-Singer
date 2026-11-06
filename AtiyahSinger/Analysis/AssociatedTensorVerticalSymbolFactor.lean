/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Analysis.RightTensorCoefficient

/-!
# The actual vertical cutoff symbol as a finite tensor factor

Public module ID: M0215.

The original finite family of sphere pieces determines one associated-fiber
factor at every actual cotangent vector. The common base frame cancels from
identity amplification, while the supplied spatial plateaus disappear on
the original supports. Both coordinate swaps and every frequency cutoff are
retained. With common charts, scalar partition and original sphere pieces,
this factor is independent of the base coefficient bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set
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


variable
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)] [∀ y, Module ℂ (F' y)]
  [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)


set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The actual finite vertical cutoff symbol has one explicit coefficient-independent factor. -/
theorem associatedSphereTensorVerticalSymbol_eq_finiteTensorFactor
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1)
    (γ : Fin N → X → ℝ) (hγ : ∀ j, ContDiff ℝ ∞ (γ j))
    (hcγ : ∀ j, HasCompactSupport (γ j))
    (hsγ : ∀ j, tsupport (γ j) ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet)
    (hbγ : ∀ j, c.symm '' tsupport (γ j) ⊆ (S.trivialization b).baseSet)
    (hγone : ∀ j x, x ∈ tsupport C.cutoff → γ j x = 1)
    (κ : Fin N → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
    (hcκ : ∀ j, HasCompactSupport (κ j))
    (hsκ : ∀ j, tsupport (κ j) ⊆ (L j).chart.target ∩ (L j).chart.symm ⁻¹'
      (A'.chart (L j).output.frameIndex).baseSet)
    (hκone : ∀ j y, y ∈ tsupport (L j).output.cutoff → κ j y = 1)
    (ε : ℝ) :
    letI := modelTopology V₀ E
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let AD := associatedSphereSmoothBundleAtlas S A σ hσ
    let AD' := associatedSphereSmoothBundleAtlas S A' σ' hσ'
    let Co (j : Fin N) : BundleChartCutoff E c :=
      { C with
        cutoff := γ j
        smooth_cutoff := hγ j
        compact_support := hcγ j
        support_subset := hsγ j }
    let Ko (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
      { (L j).output with
        cutoff := κ j
        smooth_cutoff := hκ j
        compact_support := hcκ j
        support_subset := hsκ j }
    let CP (j : Fin N) := associatedSphereProductChart S b c (L j).chart
    let Din (j : Fin N) := associatedSphereTensorChartCutoff S E A σ hσ
      b c C hC (L j).chart (L j).input
    let Dout (j : Fin N) := associatedSphereTensorChartCutoff S E A' σ' hσ'
      b c (Co j) (hbγ j) (L j).chart (Ko j)
    let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
    let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
        (A'.rank (L j).output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
        (A'.rank (L j).output.frameIndex) a (α j y η)
    ∀ (g : Fin N → AtlasSymbolFunction (n := n + r) T T'),
      (∀ j z ξ, g j z ξ =
        if hz : z ∈ (CP j).source ∩ (AT.chart (Din j).frameIndex).baseSet ∩
            (AT'.chart (Dout j).frameIndex).baseSet then
          (((Dout j).cutoff (CP j z) * (Din j).cutoff (CP j z) : ℝ) : ℂ) •
            ((AT'.frameLinearEquiv (Dout j).frameIndex z hz.2).symm.toLinearMap.comp
              (EuclideanSpace.equiv
                (Fin (a * A'.rank (L j).output.frameIndex)) ℂ).toLinearMap).comp
              ((rightProductCutoffSymbol (β j) (γ j) ε (CP j z)
                (covectorInChart (CP j) z ξ)).toLinearMap.comp
                (((EuclideanSpace.equiv
                  (Fin (a * A.rank (L j).input.frameIndex)) ℂ).symm.toLinearMap).comp
                    (AT.frameLinearEquiv (Din j).frameIndex z hz.1.2).toLinearMap))
        else 0) →
      ∀ (z : Z) (ξ : TangentSpace (𝓡 (n + r)) z →L[ℝ] ℝ),
        let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
        let y := (associatedSphereTrivialization S b z).2
        let cov (j : Fin N) := split (covectorInChart (CP j) z ξ)
        let factor (j : Fin N) : D z →ₗ[ℂ] D' z :=
          if hz : z ∈ (CP j).source ∩ (AD.chart (b, (L j).input.frameIndex)).baseSet ∩
              (AD'.chart (b, (L j).output.frameIndex)).baseSet then
            let eIn : D z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (A.rank (L j).input.frameIndex)) :=
              (AD.frameLinearEquiv (b, (L j).input.frameIndex) z hz.1.2).trans
                (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut : D' z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (A'.rank (L j).output.frameIndex)) :=
              (AD'.frameLinearEquiv (b, (L j).output.frameIndex) z hz.2).trans
                (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((C.cutoff (c (πS z)) * (L j).input.cutoff ((L j).chart y) *
              (L j).output.cutoff ((L j).chart y) *
              productFrequencyCutoff ε ‖(cov j).2‖ ‖(cov j).1‖ : ℝ) : ℂ) •
              (eOut.symm.toLinearMap.comp
                (((L j).symbol ((L j).chart y) (cov j).2).toLinearMap.comp eIn.toLinearMap)
                  : D z →ₗ[ℂ] D' z)
          else 0
        (∑ j, g j z ξ) =
          TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z))) (∑ j, factor j) := by
  classical
  let := C.frame_mem_atlas
  let := modelTopology V₀ E
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let AD' := associatedSphereSmoothBundleAtlas S A' σ' hσ'
  let Co (j : Fin N) : BundleChartCutoff E c :=
    { C with
      cutoff := γ j
      smooth_cutoff := hγ j
      compact_support := hcγ j
      support_subset := hsγ j }
  let Ko (j : Fin N) : AtlasChartCutoff A' (L j).chart :=
    { (L j).output with
      cutoff := κ j
      smooth_cutoff := hκ j
      compact_support := hcκ j
      support_subset := hsκ j }
  let CP (j : Fin N) := associatedSphereProductChart S b c (L j).chart
  let Din (j : Fin N) := associatedSphereTensorChartCutoff S E A σ hσ
    b c C hC (L j).chart (L j).input
  let Dout (j : Fin N) := associatedSphereTensorChartCutoff S E A' σ' hσ'
    b c (Co j) (hbγ j) (L j).chart (Ko j)
  let α (j : Fin N) := zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol
  let β (j : Fin N) : SymbolFunction r (A.rank (L j).input.frameIndex * a)
      (A'.rank (L j).output.frameIndex * a) :=
    fun y η ↦ tensorIdentitySymbolMap (A.rank (L j).input.frameIndex)
      (A'.rank (L j).output.frameIndex) a (α j y η)
  -- In a common coefficient frame the right matrix action is id tensored with the sphere map.
  have hFrame
      (K : SmoothComplexBundleAtlas (n := n + r) ((πS : Z → B) *ᵖ E))
      (A : SmoothComplexBundleAtlas (n := n + r) D)
      (B' : SmoothComplexBundleAtlas (n := n + r) D')
      (k : K.Index) (i : A.Index) (j : B'.Index) (x : Z)
      (hxK : x ∈ (K.chart k).baseSet) (hxA : x ∈ (A.chart i).baseSet)
      (hxB : x ∈ (B'.chart j).baseSet)
      (a : EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (B'.rank j))) :
      let AT := tensorSmoothAtlas K A
      let BT := tensorSmoothAtlas K B'
      ∀ (hxAT : x ∈ (AT.chart (k, i)).baseSet) (hxBT : x ∈ (BT.chart (k, j)).baseSet),
      let eA := (A.frameLinearEquiv i x hxA).trans
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
      let eB := (B'.frameLinearEquiv j x hxB).trans
        (EuclideanSpace.equiv (Fin (B'.rank j)) ℂ).symm.toLinearEquiv
      let eAT := (AT.frameLinearEquiv (k, i) x hxAT).trans
        (EuclideanSpace.equiv (Fin (K.rank k * A.rank i)) ℂ).symm.toLinearEquiv
      let eBT := (BT.frameLinearEquiv (k, j) x hxBT).trans
        (EuclideanSpace.equiv (Fin (K.rank k * B'.rank j)) ℂ).symm.toLinearEquiv
      eBT.symm.toLinearMap.comp
        ((identityTensorSymbolMap (K.rank k) _ _ a).toLinearMap.comp eAT.toLinearMap) =
        TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS x)))
          (eB.symm.toLinearMap.comp (a.toLinearMap.comp eA.toLinearMap)) := by
    classical
    let AT := tensorSmoothAtlas K A
    let BT := tensorSmoothAtlas K B'
    dsimp only
    intro hxAT hxBT
    let eK := (K.frameLinearEquiv k x hxK).trans
      (EuclideanSpace.equiv (Fin (K.rank k)) ℂ).symm.toLinearEquiv
    let eA := (A.frameLinearEquiv i x hxA).trans
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
    let eB := (B'.frameLinearEquiv j x hxB).trans
      (EuclideanSpace.equiv (Fin (B'.rank j)) ℂ).symm.toLinearEquiv
    let eAT := (AT.frameLinearEquiv (k, i) x hxAT).trans
      (EuclideanSpace.equiv (Fin (K.rank k * A.rank i)) ℂ).symm.toLinearEquiv
    let eBT := (BT.frameLinearEquiv (k, j) x hxBT).trans
      (EuclideanSpace.equiv (Fin (K.rank k * B'.rank j)) ℂ).symm.toLinearEquiv
    have hA (v : E (πS x)) (w : D x) (s : Fin (K.rank k)) (t : Fin (A.rank i)) :
        eAT (v ⊗ₜ[ℂ] w) (finProdFinEquiv (s, t)) = eK v s * eA w t := by
      change (tensorBundleChart K A k i ⟨x, v ⊗ₜ[ℂ] w⟩).2 (finProdFinEquiv (s, t)) =
        (K.chart k ⟨x, v⟩).2 s * (A.chart i ⟨x, w⟩).2 t
      exact (ComplexBundle.exists_tensor_trivialization (K.chart k) (A.chart i)
        (K.linear k) (A.linear i)).choose_spec.2.2 x ⟨hxK, hxA⟩ v w s t
    have hB (v : E (πS x)) (w : D' x) (s : Fin (K.rank k)) (t : Fin (B'.rank j)) :
        eBT (v ⊗ₜ[ℂ] w) (finProdFinEquiv (s, t)) = eK v s * eB w t := by
      change (tensorBundleChart K B' k j ⟨x, v ⊗ₜ[ℂ] w⟩).2 (finProdFinEquiv (s, t)) =
        (K.chart k ⟨x, v⟩).2 s * (B'.chart j ⟨x, w⟩).2 t
      exact (ComplexBundle.exists_tensor_trivialization (K.chart k) (B'.chart j)
        (K.linear k) (B'.linear j)).choose_spec.2.2 x ⟨hxK, hxB⟩ v w s t
    apply TensorProduct.ext'
    intro v w
    change eBT.symm (identityTensorSymbolMap (K.rank k) _ _ a (eAT (v ⊗ₜ[ℂ] w))) =
      v ⊗ₜ[ℂ] eB.symm (a (eA w))
    apply eBT.injective
    rw [eBT.apply_symm_apply]
    apply PiLp.ext
    intro t
    obtain ⟨⟨s, b⟩, rfl⟩ := finProdFinEquiv.surjective t
    rw [identityTensorSymbolMap_apply _ (eK v) (eA w) _ (hA v w), hB,
      eB.apply_symm_apply]
  dsimp only
  intro g hg z ξ
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let dm := linearModelDiffeomorph split.symm Z
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ πS :=
    (smoothAssociatedSphereProjection S).contMDiff.comp dm.symm.contMDiff
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AC := AE.pullback πS hq
  let t := associatedSphereTrivialization S b
  let y := (t z).2
  let cov (j : Fin N) := split (covectorInChart (CP j) z ξ)
  let frequency (j : Fin N) := productFrequencyCutoff ε ‖(cov j).2‖ ‖(cov j).1‖
  let factor (j : Fin N) : D z →ₗ[ℂ] D' z :=
    if hz : z ∈ (CP j).source ∩ (AD.chart (b, (L j).input.frameIndex)).baseSet ∩
        (AD'.chart (b, (L j).output.frameIndex)).baseSet then
      let eIn : D z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (A.rank (L j).input.frameIndex)) :=
        (AD.frameLinearEquiv (b, (L j).input.frameIndex) z hz.1.2).trans
          (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
      let eOut : D' z ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (A'.rank (L j).output.frameIndex)) :=
        (AD'.frameLinearEquiv (b, (L j).output.frameIndex) z hz.2).trans
          (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
      ((C.cutoff (c (πS z)) * (L j).input.cutoff ((L j).chart y) *
        (L j).output.cutoff ((L j).chart y) * frequency j : ℝ) : ℂ) •
        (eOut.symm.toLinearMap.comp
          (((L j).symbol ((L j).chart y) (cov j).2).toLinearMap.comp eIn.toLinearMap)
            : D z →ₗ[ℂ] D' z)
    else 0
  -- The actual supports remove only the auxiliary plateaus, including in zero branches.
  have hpoint (j : Fin N) : g j z ξ =
      TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z))) (factor j) := by
    let d := (L j).chart
    let ix : AC.Index := ⟨C.frame, C.frame_mem_atlas⟩
    let fi : AD.Index := (b, (L j).input.frameIndex)
    let fo : AD'.Index := (b, (L j).output.frameIndex)
    have hAC : (AC.chart ix).baseSet = πS ⁻¹' C.frame.baseSet :=
      (AE.exists_pullbackChart πS ⟨C.frame, C.frame_mem_atlas⟩).choose_spec.1
    have hTI : (AT.chart (Din j).frameIndex).baseSet =
        (AC.chart ix).baseSet ∩ (AD.chart fi).baseSet :=
      (exists_tensor_trivialization (AC.chart ix) (AD.chart fi)
        (AC.linear ix) (AD.linear fi)).choose_spec.1
    have hTO : (AT'.chart (Dout j).frameIndex).baseSet =
        (AC.chart ix).baseSet ∩ (AD'.chart fo).baseSet :=
      (exists_tensor_trivialization (AC.chart ix) (AD'.chart fo)
        (AC.linear ix) (AD'.linear fo)).choose_spec.1
    have hcoord (hz : z ∈ (CP j).source) : split (CP j z) = (c (πS z), d y) := by
      have ht : z ∈ t.source := hz.1.1
      change split (split.symm ((c.prod d) (t z))) = _
      rw [split.apply_symm_apply]
      change (c (t z).1, d (t z).2) = _
      rw [t.coe_fst ht]
    rw [hg]
    by_cases hz : z ∈ (CP j).source ∩ (AT.chart (Din j).frameIndex).baseSet ∩
        (AT'.chart (Dout j).frameIndex).baseSet
    · rw [dite_eq_left hz]
      have hx : z ∈ (AC.chart ix).baseSet := (hTI ▸ hz.1.2).1
      have hi : z ∈ (AD.chart fi).baseSet := (hTI ▸ hz.1.2).2
      have ho : z ∈ (AD'.chart fo).baseSet := (hTO ▸ hz.2).2
      have hred : z ∈ (CP j).source ∩ (AD.chart fi).baseSet ∩
          (AD'.chart fo).baseSet := ⟨⟨hz.1.1, hi⟩, ho⟩
      dsimp only [factor]
      rw [dite_eq_left hred]
      let aScaled := (frequency j : ℂ) • ((γ j (c (πS z)) : ℂ) •
        (((L j).output.cutoff (d y) : ℂ) • (L j).symbol (d y) (cov j).2))
      have hprod : rightProductCutoffSymbol (β j) (γ j) ε (CP j z)
          (covectorInChart (CP j) z ξ) =
          identityTensorSymbolMap a (A.rank (L j).input.frameIndex)
            (A'.rank (L j).output.frameIndex) aScaled := by
        have hp : CP j z = split.symm (c (πS z), d y) := by
          rw [← hcoord hz.1.1, split.symm_apply_apply]
        have hv : covectorInChart (CP j) z ξ = split.symm ((cov j).1, (cov j).2) := by
          exact (split.symm_apply_apply _).symm
        rw [hp, hv]
        rw [rightProductCutoffSymbol_eq]
        simp only [aScaled, α, frequency, zeroExtendedSymbol, mem_univ, ite_true, map_smul]
      let eIn := (AD.frameLinearEquiv fi z hi).trans
        (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
      let eOut := (AD'.frameLinearEquiv fo z ho).trans
        (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
      let eTin := (AT.frameLinearEquiv (Din j).frameIndex z hz.1.2).trans
        (EuclideanSpace.equiv (Fin (a * A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
      let eTout := (AT'.frameLinearEquiv (Dout j).frameIndex z hz.2).trans
        (EuclideanSpace.equiv (Fin (a * A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
      have htf : eTout.symm.toLinearMap.comp
          ((identityTensorSymbolMap a (A.rank (L j).input.frameIndex)
            (A'.rank (L j).output.frameIndex) aScaled).toLinearMap.comp eTin.toLinearMap) =
          TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z)))
            (eOut.symm.toLinearMap.comp (aScaled.toLinearMap.comp eIn.toLinearMap)) :=
        hFrame AC AD AD' ix fi fo z hx hi ho aScaled hz.1.2 hz.2
      rw [hprod]
      change (((Dout j).cutoff (CP j z) * (Din j).cutoff (CP j z) : ℝ) : ℂ) •
        (eTout.symm.toLinearMap.comp
          ((identityTensorSymbolMap a _ _ aScaled).toLinearMap.comp eTin.toLinearMap)) = _
      rw [htf]
      have hcutI : (Din j).cutoff (CP j z) =
          C.cutoff (c (πS z)) * (L j).input.cutoff (d y) := by
        change C.cutoff (split (CP j z)).1 * (L j).input.cutoff (split (CP j z)).2 = _
        rw [hcoord hz.1.1]
      have hcutO : (Dout j).cutoff (CP j z) = γ j (c (πS z)) * κ j (d y) := by
        change γ j (split (CP j z)).1 * κ j (split (CP j z)).2 = _
        rw [hcoord hz.1.1]
      have hscalar : (γ j (c (πS z)) * κ j (d y) *
          (C.cutoff (c (πS z)) * (L j).input.cutoff (d y))) *
          (frequency j * γ j (c (πS z)) * (L j).output.cutoff (d y)) =
          C.cutoff (c (πS z)) * (L j).input.cutoff (d y) *
            (L j).output.cutoff (d y) * frequency j := by
        by_cases hC0 : C.cutoff (c (πS z)) = 0
        · simp only [hC0, zero_mul, mul_zero]
        by_cases ho0 : (L j).output.cutoff (d y) = 0
        · simp only [ho0, zero_mul, mul_zero]
        rw [hγone j _ (subset_tsupport _ hC0), hκone j _ (subset_tsupport _ ho0)]
        ring
      rw [hcutI, hcutO]
      apply TensorProduct.ext'
      intro v w
      simp only [aScaled, TensorProduct.map_tmul, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe,
        smul_apply, LinearEquiv.coe_coe, map_smul, TensorProduct.tmul_smul, smul_smul]
      simp only [← Complex.ofReal_mul]
      rw [hscalar]
    · rw [dite_eq_right hz]
      dsimp only [factor]
      split_ifs with hred
      · have hC0 : C.cutoff (c (πS z)) = 0 := by
          by_contra hC0
          have hxs : πS z ∈ c.source := by
            have h : (t z).1 ∈ c.source := hred.1.1.1.2.1
            rwa [t.coe_fst hred.1.1.1.1] at h
          have hxC : πS z ∈ C.frame.baseSet := by
            have h := (C.support_subset (subset_tsupport _ hC0)).2
            change c.symm (c (πS z)) ∈ C.frame.baseSet at h
            rwa [c.left_inv hxs] at h
          have hx : z ∈ (AC.chart ix).baseSet := hAC.symm ▸ hxC
          exact hz ⟨⟨hred.1.1, hTI.symm ▸ ⟨hx, hred.1.2⟩⟩,
            hTO.symm ▸ ⟨hx, hred.2⟩⟩
        simp only [hC0, zero_mul, Complex.ofReal_zero, zero_smul, TensorProduct.map_zero_right]
      · exact (TensorProduct.map_zero_right _).symm
  -- The unchanged finite family assembles by linearity in the sphere factor.
  change (∑ j, g j z ξ) =
    TensorProduct.map (LinearMap.id : Module.End ℂ (E (πS z))) (∑ j, factor j)
  rw [Finset.sum_congr rfl (fun j _ ↦ hpoint j)]
  apply TensorProduct.ext'
  intro v w
  simp only [LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.tmul_sum]

end AtiyahSinger
