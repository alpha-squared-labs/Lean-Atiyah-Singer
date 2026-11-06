/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalApproximation
public import AtiyahSinger.Analysis.AssociatedTensorProductCutoffOperator

import all AtiyahSinger.Analysis.CompactLocalSymbolCalculus

/-!
# Regularization of the local horizontal lift

Public module ID: M0173.

Choose compact output plateaus in the base and sphere frames, followed by
localization and extension maps. These fixed maps give order-one
pseudodifferential operators for positive regularization parameters and a
controlled Sobolev approximation of the horizontal lift. The conclusion
retains all witnesses and the complete amplified product-cutoff symbols.
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

variable [T2Space B]

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

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Fixed cutoffs give order-one PDOs approximating the local horizontal lift as ε tends to zero. -/
theorem exists_associatedSphereTensorLocalHorizontal_regularization
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (J : AtlasBundlePresentation A) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    ∀ (Li : AtlasBundlePresentation (n := n + r) (M := Z) (E := T) AT)
      (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
      ∃ (Co : BundleChartCutoff (r := a') E' L.chart)
        (hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
        (κ : Fin J.size → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
        (hκK : ∀ j, HasCompactSupport (κ j))
        (hκsupport : ∀ j, tsupport (κ j) ⊆ (J.chart j).target ∩
          (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet),
        let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
          ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
        let Din (j : Fin J.size) := associatedSphereTensorChartCutoff S E A σ hσ b
          L.chart L.input hinput (J.chart j) (J.chartCutoff j)
        let Dout (j : Fin J.size) := associatedSphereTensorChartCutoff S E' A σ hσ b
          L.chart Co hCo (J.chart j) (Kout j)
        let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
        Co.frame = L.output.frame ∧
        (tsupport Co.cutoff ⊆ L.chart.symm ⁻¹' L.input.frame.baseSet) ∧
        (∀ x ∈ tsupport L.output.cutoff, Co.cutoff x = 1) ∧
        (∀ j y, y ∈ tsupport (J.chartCutoff j).cutoff → κ j y = 1) ∧
        ∃ (I : ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))))
          (O : ∀ j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
              →ₗ[ℂ] AT'.smoothSections),
          (∀ j w z, I j w z = (Din j).localizedFunction w z) ∧
          (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) ∧
          ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
            (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
              Lo.smoothToSobolev 0 (associatedSphereTensorLocalHorizontalLift (a := a)
                S E A σ E' L hσ b χ hχ hχsupport houtput w)) ∧
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
              ∃ (Q : Fin J.size → AtlasPseudodifferentialOperator AT AT' 1)
                (U : ∀ j : Fin J.size,
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
                    𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))))
                (Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0),
                (∀ j, (Q j).toLinearMap = (O j).comp ((U j).toLinearMap.comp (I j))) ∧
                (∀ j v z, U j v z = quantize
                  (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                    (productCutoffSymbol α (κ j) ε x ξ)) v z) ∧
                (∀ w, Rε (Li.smoothToSobolev 1 w) =
                  Lo.smoothToSobolev 0 (∑ j, (Q j).toLinearMap w)) ∧
                  ‖Rε - R‖ ≤ C * ε := by
  classical
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  dsimp only
  intro Li Lo
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  -- The base plateau stays inside the same principal chart and both original frames.
  let V := L.chart.target ∩ L.chart.symm ⁻¹'
    ((S.trivialization b).baseSet ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hV : IsOpen V := L.chart.isOpen_inter_preimage_symm
    (((S.trivialization b).open_baseSet.inter L.input.frame.open_baseSet).inter
      L.output.frame.open_baseSet)
  have hKV : tsupport L.output.cutoff ⊆ V := by
    intro x hx
    exact ⟨(L.output.support_subset hx).1,
      ⟨houtput ⟨x, hx, rfl⟩, L.output_support_in_input_frame hx⟩,
      (L.output.support_subset hx).2⟩
  have hbasePlateau : ∃ δ : X → ℝ,
      ContDiff ℝ ∞ δ ∧ HasCompactSupport δ ∧ tsupport δ ⊆ V ∧
        tsupport L.output.cutoff ⊆ interior {x | δ x = 1} :=
    exists_compact_cutoff_one_near
      (tsupport L.output.cutoff) V L.output.compact_support hV hKV
  let δ : X → ℝ := hbasePlateau.choose
  have hδ : ContDiff ℝ ∞ δ := hbasePlateau.choose_spec.1
  have hδK : HasCompactSupport δ := hbasePlateau.choose_spec.2.1
  have hδV : tsupport δ ⊆ V := hbasePlateau.choose_spec.2.2.1
  have hδone : tsupport L.output.cutoff ⊆ interior {x | δ x = 1} :=
    hbasePlateau.choose_spec.2.2.2
  let Co : BundleChartCutoff (r := a') E' L.chart :=
    { frame := L.output.frame
      frame_mem_atlas := L.output.frame_mem_atlas
      cutoff := δ
      smooth_cutoff := hδ
      compact_support := hδK
      support_subset := fun x hx ↦ ⟨(hδV hx).1, (hδV hx).2.2⟩ }
  have hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hδV hx).2.1.1
  have hCoOne (x : X) (hx : x ∈ tsupport L.output.cutoff) : Co.cutoff x = 1 :=
    interior_subset (s := {x : X | δ x = 1}) (hδone hx)
  -- Choose one sphere plateau for each weight of the specified original partition.
  have hplateau (j : Fin J.size) : ∃ κ : Y → ℝ,
      ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
        tsupport κ ⊆ (J.chart j).target ∩
          (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet ∧
        ∀ y ∈ tsupport (J.chartCutoff j).cutoff, κ y = 1 := by
    obtain ⟨κ, hκ, hκK, hκsupport, hκone⟩ := exists_compact_cutoff_one_near
      (tsupport (J.chartCutoff j).cutoff)
      ((J.chart j).target ∩ (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet)
      (J.chartCutoff j).compact_support
      ((J.chart j).isOpen_inter_preimage_symm (A.chart (J.frameIndex j)).open_baseSet)
      (J.chartCutoff j).support_subset
    exact ⟨κ, hκ, hκK, hκsupport,
      fun y hy ↦ interior_subset (s := {y : Y | κ y = 1}) (hκone hy)⟩
  choose κ hκ hκK hκsupport hκone using hplateau
  let CP (j : Fin J.size) : OpenPartialHomeomorph Z XY :=
    associatedSphereProductChart S b L.chart (J.chart j)
  have hCP (j : Fin J.size) : CP j ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b L.chart L.chart_mem_atlas
      (J.chart j) (J.chart_mem_atlas j)
  let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
    ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
  let Din (j : Fin J.size) : AtlasChartCutoff AT (CP j) :=
    associatedSphereTensorChartCutoff S E A σ hσ b L.chart L.input hinput
      (J.chart j) (J.chartCutoff j)
  let Dout (j : Fin J.size) : AtlasChartCutoff AT' (CP j) :=
    associatedSphereTensorChartCutoff S E' A σ hσ b L.chart Co hCo (J.chart j) (Kout j)
  refine ⟨Co, hCo, κ, hκ, hκK, hκsupport, rfl,
    (fun x hx ↦ (hδV hx).2.1.2), hCoOne, hκone, ?_⟩
  -- The two original finite-atlas norms select literal input and output maps before epsilon.
  have hI (j : Fin J.size) :
      ∃ I : AT.smoothSections →ₗ[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))),
        ∀ w z, I w z = (Din j).localizedFunction w z := by
    let I : AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) :=
      ((Din j).exists_localize_sobolev_of_mem_maximalAtlas (hCP j) Li 1).choose
    exact ⟨I, ((Din j).exists_localize_sobolev_of_mem_maximalAtlas (hCP j) Li 1).choose_spec.1⟩
  have hO (j : Fin J.size) :
      ∃ O : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
          →ₗ[ℂ] AT'.smoothSections,
        ∀ v z, (O v).val z = (Dout j).extendedFunction v z := by
    let O : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
        →ₗ[ℂ] AT'.smoothSections :=
      ((Dout j).exists_extend_sobolev_of_mem_maximalAtlas (hCP j) Lo 0).choose
    exact ⟨O, ((Dout j).exists_extend_sobolev_of_mem_maximalAtlas (hCP j) Lo 0).choose_spec.1⟩
  choose I hI using hI
  choose O hO using hO
  have hlimit := exists_associatedSphereTensorLocalHorizontal_sobolev_approximation
    (a := a) S E A σ E' L hσ b hinput houtput χ hχ hχsupport hχone J
    Co rfl hCo hCoOne κ hκ hκK hκsupport hκone I O hI hO Li Lo
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hlimit.choose
  have hR (w : AT.smoothSections) : R (Li.smoothToSobolev 1 w) =
      Lo.smoothToSobolev 0 (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E'
        L hσ b χ hχ hχsupport houtput w) := hlimit.choose_spec.1 w
  let C : ℝ := hlimit.choose_spec.2.choose
  have hC : 0 ≤ C := hlimit.choose_spec.2.choose_spec.1
  have hbound := hlimit.choose_spec.2.choose_spec.2
  refine ⟨I, O, hI, hO, R, hR, C, hC, ?_⟩
  intro ε hε hε1
  -- The opposite-frame cutoff objects certify the exact cross-support requirements.
  let Ci' : BundleChartCutoff (r := a') E' L.chart :=
    { frame := L.output.frame
      frame_mem_atlas := L.output.frame_mem_atlas
      cutoff := L.input.cutoff
      smooth_cutoff := L.input.smooth_cutoff
      compact_support := L.input.compact_support
      support_subset := fun x hx ↦
        ⟨(L.input.support_subset hx).1, L.input_support_in_output_frame hx⟩ }
  let Co' : BundleChartCutoff (r := a) E L.chart :=
    { frame := L.input.frame
      frame_mem_atlas := L.input.frame_mem_atlas
      cutoff := δ
      smooth_cutoff := hδ
      compact_support := hδK
      support_subset := fun x hx ↦ ⟨(hδV hx).1, (hδV hx).2.1.2⟩ }
  have hi' : L.chart.symm '' tsupport Ci'.cutoff ⊆ (S.trivialization b).baseSet := hinput
  have ho' : L.chart.symm '' tsupport Co'.cutoff ⊆ (S.trivialization b).baseSet := hCo
  have hcrossIn (j : Fin J.size) :
      tsupport (Din j).cutoff ⊆ (CP j).symm ⁻¹' (AT'.chart (Dout j).frameIndex).baseSet := by
    let D' := associatedSphereTensorChartCutoff S E' A σ hσ b L.chart Ci' hi'
      (J.chart j) (J.chartCutoff j)
    exact fun z hz ↦ (D'.support_subset hz).2
  have hcrossOut (j : Fin J.size) :
      tsupport (Dout j).cutoff ⊆ (CP j).symm ⁻¹' (AT.chart (Din j).frameIndex).baseSet := by
    let D' := associatedSphereTensorChartCutoff S E A σ hσ b L.chart Co' ho'
      (J.chart j) (Kout j)
    exact fun z hz ↦ (D'.support_subset hz).2
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  have hα : IsSymbol Set.univ 1 α := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1
    L.output.cutoff L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _)
    L.symbol L.isSymbol
  have hαK : HasCompactSupport α := by
    apply L.output.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport L.output.cutoff)
    intro x hx
    by_contra hout
    apply hx
    funext ξ
    simp [α, zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hout]
  have hpositive (j : Fin J.size) :
      ∃ (Q : AtlasPseudodifferentialOperator AT AT' 1)
        (U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))),
        Q.toLinearMap = (O j).comp (U.toLinearMap.comp (I j)) ∧
        ∀ v z, U v z = quantize
          (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
            (productCutoffSymbol α (κ j) ε x ξ)) v z := by
    obtain ⟨Q, U, hQ, hU, _⟩ := exists_associatedSphereTensorProductCutoffOperator
      (a := a) S E A σ E' hσ b L.chart L.chart_mem_atlas L.input Co hinput hCo
      (J.chart j) (J.chart_mem_atlas j) (J.chartCutoff j)
      (κ j) (hκ j) (hκK j) (hκsupport j) α hα hαK (κ j) (hκ j) (hκK j)
      (hcrossIn j) (hcrossOut j) (I j) (O j) (hI j) (hO j) ε hε
    exact ⟨Q, U, hQ, hU⟩
  choose Q U hQ hU using hpositive
  have hregularized := hbound ε hε hε1 U hU
  let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hregularized.choose
  have hRε (w : AT.smoothSections) : Rε (Li.smoothToSobolev 1 w) =
      Lo.smoothToSobolev 0 (∑ j, O j (U j (I j w))) := hregularized.choose_spec.1 w
  have herror : ‖Rε - R‖ ≤ C * ε := hregularized.choose_spec.2
  refine ⟨Q, U, Rε, hQ, hU, ?_, herror⟩
  intro w
  have hsum : (∑ j, O j (U j (I j w))) = ∑ j, (Q j).toLinearMap w := by
    apply Finset.sum_congr rfl
    intro j _
    exact (congrArg (fun f : AT.smoothSections →ₗ[ℂ] AT'.smoothSections ↦ f w) (hQ j)).symm
  exact (hRε w).trans (congrArg (Lo.smoothToSobolev 0) hsum)

end AtiyahSinger
