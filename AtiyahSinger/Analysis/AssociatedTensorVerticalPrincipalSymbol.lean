/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalRegularization
public import AtiyahSinger.Analysis.CompatibleChartGlobalSymbol
public import AtiyahSinger.Analysis.CompatibleChartPrincipalSymbol

/-!
# Principal class of a vertical cutoff for a positive parameter

Public module ID: M0209.

The supplied operator and its full right-product Fourier action retain the
coordinate swaps, frames, and spatial cutoffs. Its intrinsic symbol uses the
same two cutoff weights and computes the atlas principal class from this
compatible-chart representation. The regularization parameter is positive;
the cutoff hypotheses require smoothness, compact support, and frame overlap.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the full vertical cutoff principal-symbol comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The supplied vertical cutoff PDO has the intrinsic class of its complete cutoff symbol. -/
theorem associatedSphereTensorVerticalPiece_principalSymbol
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (L : AtlasPseudodifferentialPiece A A' 1)
    (γ : X → ℝ) (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ)
    (hsγ : tsupport γ ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet)
    (hbγ : c.symm '' tsupport γ ⊆ (S.trivialization b).baseSet)
    (κ : Y → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ L.chart.target ∩ L.chart.symm ⁻¹'
      (A'.chart L.output.frameIndex).baseSet)
    (hκInput : tsupport κ ⊆ L.chart.symm ⁻¹' (A.chart L.input.frameIndex).baseSet) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    let Co : BundleChartCutoff E c :=
      { C with cutoff := γ, smooth_cutoff := hγ, compact_support := hcγ, support_subset := hsγ }
    let Ko : AtlasChartCutoff A' L.chart :=
      { L.output with
        cutoff := κ, smooth_cutoff := hκ, compact_support := hcκ, support_subset := hsκ }
    let CP := associatedSphereProductChart S b c L.chart
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
    let Dout := associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    let β : SymbolFunction r (A.rank L.input.frameIndex * a)
        (A'.rank L.output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
        (A'.rank L.output.frameIndex) a (α y η)
    ∀ (I : AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))))
      (O : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex)))
        →ₗ[ℂ] AT'.smoothSections),
      (∀ w z, I w z = Din.localizedFunction w z) →
      (∀ v z, (O v).val z = Dout.extendedFunction v z) →
      ∀ ε : ℝ, 0 < ε →
        ∀ (Q : AtlasPseudodifferentialOperator AT AT' 1)
          (U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))) →L[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex)))),
          Q.toLinearMap = O.comp (U.toLinearMap.comp I) →
          (∀ v z, U v z = quantize (rightProductCutoffSymbol β γ ε) v z) →
          ∃ g : atlasGlobalSymbolSpace AT AT' 1,
            (∀ z ξ, g.val z ξ =
              if hz : z ∈ CP.source ∩ (AT.chart Din.frameIndex).baseSet ∩
                  (AT'.chart Dout.frameIndex).baseSet then
                ((Dout.cutoff (CP z) * Din.cutoff (CP z) : ℝ) : ℂ) •
                  ((AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm.toLinearMap.comp
                    (EuclideanSpace.equiv
                      (Fin (a * A'.rank L.output.frameIndex)) ℂ).toLinearMap).comp
                    ((rightProductCutoffSymbol β γ ε (CP z)
                      (covectorInChart CP z ξ)).toLinearMap.comp
                      (((EuclideanSpace.equiv
                        (Fin (a * A.rank L.input.frameIndex)) ℂ).symm.toLinearMap).comp
                          (AT.frameLinearEquiv Din.frameIndex z hz.1.2).toLinearMap))
              else 0) ∧
            Q.principalSymbol = atlasGlobalPrincipalSymbolClass AT AT' 1 g := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let Co : BundleChartCutoff E c :=
    { C with cutoff := γ, smooth_cutoff := hγ, compact_support := hcγ, support_subset := hsγ }
  let Ko : AtlasChartCutoff A' L.chart :=
    { L.output with
      cutoff := κ, smooth_cutoff := hκ, compact_support := hcκ, support_subset := hsκ }
  let CP := associatedSphereProductChart S b c L.chart
  let Din : AtlasChartCutoff AT CP :=
    associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
  let Dout : AtlasChartCutoff AT' CP :=
    associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
  dsimp only
  intro I O hI hO ε hε Q U hQ hU
  have hCP : CP ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc L.chart L.chart_mem_atlas
  -- The cutoff overlap proofs keep the original two sphere frames.
  let Ki' : AtlasChartCutoff A' L.chart :=
    { frameIndex := L.output.frameIndex
      cutoff := L.input.cutoff
      smooth_cutoff := L.input.smooth_cutoff
      compact_support := L.input.compact_support
      support_subset := fun y hy ↦
        ⟨(L.input.support_subset hy).1, L.input_support_in_output_frame hy⟩ }
  let Ko' : AtlasChartCutoff A L.chart :=
    { frameIndex := L.input.frameIndex
      cutoff := κ
      smooth_cutoff := hκ
      compact_support := hcκ
      support_subset := fun y hy ↦ ⟨(hsκ hy).1, hκInput hy⟩ }
  have hio : tsupport Din.cutoff ⊆ CP.symm ⁻¹'
      (AT'.chart Dout.frameIndex).baseSet := by
    let oppositeCutoff :=
      associatedSphereTensorChartCutoff S E A' σ' hσ' b c C hC L.chart Ki'
    exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
  have hoi : tsupport Dout.cutoff ⊆ CP.symm ⁻¹'
      (AT.chart Din.frameIndex).baseSet := by
    let oppositeCutoff :=
      associatedSphereTensorChartCutoff S E A σ hσ b c Co hbγ L.chart Ko'
    exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
  let α : SymbolFunction r (A.rank L.input.frameIndex) (A'.rank L.output.frameIndex) :=
    zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  have hα : IsSymbol Set.univ 1 α := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1
    L.output.cutoff L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _)
    L.symbol L.isSymbol
  let β : SymbolFunction r (A.rank L.input.frameIndex * a)
      (A'.rank L.output.frameIndex * a) :=
    fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
      (A'.rank L.output.frameIndex) a (α y η)
  have hβ : IsSymbol Set.univ 1 β := isSymbol_continuousLinearMap 1 α hα
    ((tensorIdentitySymbolMap (A.rank L.input.frameIndex)
      (A'.rank L.output.frameIndex) a).restrictScalars ℝ)
  let p : SymbolFunction (n + r) (a * A.rank L.input.frameIndex)
      (a * A'.rank L.output.frameIndex) := rightProductCutoffSymbol β γ ε
  have hp : IsSymbol Set.univ 1 p := isSymbol_rightProductCutoffSymbol β hβ γ hγ ε hε
  -- The same swapped full symbol defines the intrinsic two-cutoff representative.
  let gRaw : AtlasSymbolFunction (n := n + r) T T' := fun z ξ ↦
    if hz : z ∈ CP.source ∩ (AT.chart Din.frameIndex).baseSet ∩
        (AT'.chart Dout.frameIndex).baseSet then
      ((Dout.cutoff (CP z) * Din.cutoff (CP z) : ℝ) : ℂ) •
        ((AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ).toLinearMap).comp
          ((p (CP z) (covectorInChart CP z ξ)).toLinearMap.comp
            (((EuclideanSpace.equiv (Fin (a * A.rank L.input.frameIndex)) ℂ).symm.toLinearMap).comp
              (AT.frameLinearEquiv Din.frameIndex z hz.1.2).toLinearMap))
    else 0
  have hgRaw : IsAtlasGlobalSymbol AT AT' 1 gRaw :=
    isAtlasGlobalSymbol_of_mem_maximalAtlas AT AT' CP hCP Din Dout hoi p hp
  let g : atlasGlobalSymbolSpace AT AT' 1 := ⟨gRaw, hgRaw⟩
  refine ⟨g, fun _ _ ↦ rfl, ?_⟩
  have hrepresentation : IsAtlasSmoothingOperator AT AT'
      (Q.toLinearMap - ∑ _j : Fin 1, O.comp (U.toLinearMap.comp I)) := by
    rw [Fin.sum_univ_one, hQ, sub_self]
    intro Li Lo s t
    refine ⟨0, ?_⟩
    intro w
    change (0 : Lo.SobolevSpace t) = Lo.smoothToSobolev t (0 : AT'.smoothSections)
    exact (map_zero (Lo.smoothToSobolev t)).symm
  have hclass := Q.principalSymbol_eq_of_compatible_representation AT AT' 1
    (fun _ ↦ CP) (fun _ ↦ hCP) (fun _ ↦ Din) (fun _ ↦ Dout)
    (fun _ ↦ hio) (fun _ ↦ hoi) (fun _ ↦ U) (fun _ ↦ p) (fun _ ↦ hp)
    (fun _ ↦ hU) (fun _ ↦ I) (fun _ ↦ O) (fun _ ↦ hI) (fun _ ↦ hO)
    (fun _ ↦ g) (fun _ _ _ ↦ rfl) hrepresentation
  simpa only [Fin.sum_univ_one] using hclass

end AtiyahSinger
