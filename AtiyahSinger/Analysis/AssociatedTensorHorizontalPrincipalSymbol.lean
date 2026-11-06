/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.CompatibleChartGlobalSymbol
public import AtiyahSinger.Analysis.CompatibleChartPrincipalSymbol

/-!
# Principal class of the horizontal regularization for positive parameters

Public module ID: M0172.

The supplied regularized operators, fixed chart maps, and complete amplified
product-cutoff symbols use a positive regularization parameter. The two cutoff
weights and frame maps give intrinsic global-symbol representatives. Their
finite sum computes the principal class of the exact finite operator sum.
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

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
-- The extended limit accommodates the two-cutoff horizontal principal-symbol comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The given regularized horizontal PDOs have the two-cutoff symbol class on their exact sum. -/
theorem exists_horizontalCutoff_principalSymbol
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
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
    ∀ (Co : ∀ k : Fin L.size, BundleChartCutoff (r := a') E' (L.piece k).chart)
      (hCo : ∀ k, (L.piece k).chart.symm '' tsupport (Co k).cutoff ⊆
        (S.trivialization (L.center k)).baseSet)
      (κ : Fin L.size → Fin J.size → Y → ℝ)
      (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j))
      (hκK : ∀ k j, HasCompactSupport (κ k j))
      (hκsupport : ∀ k j, tsupport (κ k j) ⊆ (J.chart j).target ∩
        (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet),
      let Kout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
        ⟨J.frameIndex j, κ k j, hκ k j, hκK k j, hκsupport k j⟩
      let CP (k : Fin L.size) (j : Fin J.size) :=
        associatedSphereProductChart S (L.center k) (L.piece k).chart (J.chart j)
      let Din (k : Fin L.size) (j : Fin J.size) :=
        associatedSphereTensorChartCutoff S E A σ hσ (L.center k) (L.piece k).chart
          (L.piece k).input (fun _ ⟨x, hx, hxy⟩ ↦
            L.piece_support k ⟨x, Or.inr hx, hxy⟩) (J.chart j) (J.chartCutoff j)
      let Dout (k : Fin L.size) (j : Fin J.size) :=
        associatedSphereTensorChartCutoff S E' A σ hσ (L.center k) (L.piece k).chart
          (Co k) (hCo k) (J.chart j) (Kout k j)
      let α (k : Fin L.size) :=
        zeroExtendedSymbol Set.univ (L.piece k).output.cutoff (L.piece k).symbol
      (∀ k, (Co k).frame = (L.piece k).output.frame) →
      (∀ k, tsupport (Co k).cutoff ⊆
        (L.piece k).chart.symm ⁻¹' (L.piece k).input.frame.baseSet) →
      ∀ (I : Fin L.size → ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))))
        (O : Fin L.size → ∀ j : Fin J.size,
          𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))
            →ₗ[ℂ] AT'.smoothSections),
        (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
        (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
        ∀ ε : ℝ, 0 < ε →
          ∀ (Q : Fin L.size → Fin J.size → AtlasPseudodifferentialOperator AT AT' 1)
            (U : Fin L.size → ∀ j : Fin J.size,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
                𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j))))),
            (∀ k j, (Q k j).toLinearMap =
              (O k j).comp ((U k j).toLinearMap.comp (I k j))) →
            (∀ k j v z, U k j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                (productCutoffSymbol (α k) (κ k j) ε x ξ)) v z) →
            ∃ g : Fin L.size → Fin J.size → atlasGlobalSymbolSpace AT AT' 1,
              (∀ k j z ξ, (g k j).val z ξ =
                if hz : z ∈ (CP k j).source ∩ (AT.chart (Din k j).frameIndex).baseSet ∩
                    (AT'.chart (Dout k j).frameIndex).baseSet then
                  (((Dout k j).cutoff (CP k j z) *
                    (Din k j).cutoff (CP k j z) : ℝ) : ℂ) •
                    ((AT'.frameLinearEquiv (Dout k j).frameIndex z hz.2).symm.toLinearMap.comp
                      (EuclideanSpace.equiv
                        (Fin (a' * A.rank (J.frameIndex j))) ℂ).toLinearMap).comp
                      ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                        (productCutoffSymbol (α k) (κ k j) ε (CP k j z)
                          (covectorInChart (CP k j) z ξ))).toLinearMap.comp
                        (((EuclideanSpace.equiv
                          (Fin (a * A.rank (J.frameIndex j))) ℂ).symm.toLinearMap).comp
                            (AT.frameLinearEquiv (Din k j).frameIndex z hz.1.2).toLinearMap))
                else 0) ∧
              ∃ Pε : AtlasPseudodifferentialOperator AT AT' 1,
                Pε.toLinearMap = ∑ k, ∑ j, (Q k j).toLinearMap ∧
                Pε.principalSymbol =
                  atlasGlobalPrincipalSymbolClass AT AT' 1 (∑ k, ∑ j, g k j) := by
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
  intro Co hCo κ hκ hκK hκsupport
  let Kout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
    ⟨J.frameIndex j, κ k j, hκ k j, hκK k j, hκsupport k j⟩
  let CP (k : Fin L.size) (j : Fin J.size) : OpenPartialHomeomorph Z XY :=
    associatedSphereProductChart S (L.center k) (L.piece k).chart (J.chart j)
  have hinput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).input.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inr hx, hxy⟩
  let Din (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff AT (CP k j) :=
    associatedSphereTensorChartCutoff S E A σ hσ (L.center k) (L.piece k).chart
      (L.piece k).input (hinput k) (J.chart j) (J.chartCutoff j)
  let Dout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff AT' (CP k j) :=
    associatedSphereTensorChartCutoff S E' A σ hσ (L.center k) (L.piece k).chart
      (Co k) (hCo k) (J.chart j) (Kout k j)
  intro hCoFrame hCoInput I O hI hO ε hε Q U hQ hU
  have hCP (k : Fin L.size) (j : Fin J.size) :
      CP k j ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S (L.center k) (L.piece k).chart
      (L.piece k).chart_mem_atlas (J.chart j) (J.chart_mem_atlas j)
  -- The original two cross-support conditions are realized in opposite original frames.
  let Ci' (k : Fin L.size) : BundleChartCutoff (r := a') E' (L.piece k).chart :=
    { frame := (Co k).frame
      frame_mem_atlas := (Co k).frame_mem_atlas
      cutoff := (L.piece k).input.cutoff
      smooth_cutoff := (L.piece k).input.smooth_cutoff
      compact_support := (L.piece k).input.compact_support
      support_subset := by
        intro x hx
        refine ⟨((L.piece k).input.support_subset hx).1, ?_⟩
        rw [hCoFrame k]
        exact (L.piece k).input_support_in_output_frame hx }
  let Co' (k : Fin L.size) : BundleChartCutoff (r := a) E (L.piece k).chart :=
    { frame := (L.piece k).input.frame
      frame_mem_atlas := (L.piece k).input.frame_mem_atlas
      cutoff := (Co k).cutoff
      smooth_cutoff := (Co k).smooth_cutoff
      compact_support := (Co k).compact_support
      support_subset := fun x hx ↦ ⟨((Co k).support_subset hx).1, hCoInput k hx⟩ }
  have hio (k : Fin L.size) (j : Fin J.size) :
      tsupport (Din k j).cutoff ⊆ (CP k j).symm ⁻¹'
        (AT'.chart (Dout k j).frameIndex).baseSet := by
    let oppositeCutoff := associatedSphereTensorChartCutoff S E' A σ hσ (L.center k)
      (L.piece k).chart (Ci' k) (hinput k) (J.chart j) (J.chartCutoff j)
    exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
  have hoi (k : Fin L.size) (j : Fin J.size) :
      tsupport (Dout k j).cutoff ⊆ (CP k j).symm ⁻¹'
        (AT.chart (Din k j).frameIndex).baseSet := by
    let oppositeCutoff := associatedSphereTensorChartCutoff S E A σ hσ (L.center k)
      (L.piece k).chart (Co' k) (hCo k) (J.chart j) (Kout k j)
    exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
  let α (k : Fin L.size) : SymbolFunction n a a' :=
    zeroExtendedSymbol Set.univ (L.piece k).output.cutoff (L.piece k).symbol
  have hα (k : Fin L.size) : IsSymbol Set.univ 1 (α k) :=
    isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 (L.piece k).output.cutoff
      (L.piece k).output.smooth_cutoff (L.piece k).output.compact_support
      (Set.subset_univ _) (L.piece k).symbol (L.piece k).isSymbol
  let p (k : Fin L.size) (j : Fin J.size) :
      SymbolFunction (n + r) (a * A.rank (J.frameIndex j)) (a' * A.rank (J.frameIndex j)) :=
    fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
      (productCutoffSymbol (α k) (κ k j) ε x ξ)
  have hp (k : Fin L.size) (j : Fin J.size) : IsSymbol Set.univ 1 (p k j) :=
    isSymbol_continuousLinearMap 1 _
      (isSymbol_productCutoffSymbol (α k) (hα k) (κ k j) (hκ k j) ε hε)
      ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))).restrictScalars ℝ)
  -- Intrinsic full representatives retain the same two cutoff weights and frame maps.
  let gRaw (k : Fin L.size) (j : Fin J.size) : AtlasSymbolFunction (n := n + r) T T' :=
    fun z ξ ↦
      if hz : z ∈ (CP k j).source ∩ (AT.chart (Din k j).frameIndex).baseSet ∩
          (AT'.chart (Dout k j).frameIndex).baseSet then
        (((Dout k j).cutoff (CP k j z) * (Din k j).cutoff (CP k j z) : ℝ) : ℂ) •
          ((AT'.frameLinearEquiv (Dout k j).frameIndex z hz.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (a' * A.rank (J.frameIndex j))) ℂ).toLinearMap).comp
            ((p k j (CP k j z) (covectorInChart (CP k j) z ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (a * A.rank (J.frameIndex j))) ℂ).symm.toLinearMap).comp
                (AT.frameLinearEquiv (Din k j).frameIndex z hz.1.2).toLinearMap))
      else 0
  have hgRaw (k : Fin L.size) (j : Fin J.size) : IsAtlasGlobalSymbol AT AT' 1 (gRaw k j) :=
    isAtlasGlobalSymbol_of_mem_maximalAtlas AT AT' (CP k j) (hCP k j)
      (Din k j) (Dout k j) (hoi k j) (p k j) (hp k j)
  let g (k : Fin L.size) (j : Fin J.size) : atlasGlobalSymbolSpace AT AT' 1 :=
    ⟨gRaw k j, hgRaw k j⟩
  let Pε : AtlasPseudodifferentialOperator AT AT' 1 :=
    ⟨∑ k, ∑ j, (Q k j).toLinearMap,
      (atlasPseudodifferentialSpace AT AT' 1).sum_mem (fun k _ ↦
        (atlasPseudodifferentialSpace AT AT' 1).sum_mem
          (fun j _ ↦ (Q k j).isPseudodifferentialOperator))⟩
  refine ⟨g, fun _ _ _ _ ↦ rfl, Pε, rfl, ?_⟩
  -- Reindex only the finite family; all local objects remain the specified k/j witnesses.
  let ij : Fin (L.size * J.size) ≃ Fin L.size × Fin J.size := finProdFinEquiv.symm
  have hsumMaps :
      (∑ t, (O (ij t).1 (ij t).2).comp
        ((U (ij t).1 (ij t).2).toLinearMap.comp (I (ij t).1 (ij t).2))) =
      ∑ k, ∑ j, (O k j).comp ((U k j).toLinearMap.comp (I k j)) := by
    simpa only [Fintype.sum_prod_type] using
      (Fintype.sum_equiv ij
        (fun t ↦ (O (ij t).1 (ij t).2).comp
          ((U (ij t).1 (ij t).2).toLinearMap.comp (I (ij t).1 (ij t).2)))
        (fun kj ↦ (O kj.1 kj.2).comp ((U kj.1 kj.2).toLinearMap.comp (I kj.1 kj.2)))
        (fun _ ↦ rfl))
  have hrepresentation : IsAtlasSmoothingOperator AT AT'
      (Pε.toLinearMap - ∑ t, (O (ij t).1 (ij t).2).comp
        ((U (ij t).1 (ij t).2).toLinearMap.comp (I (ij t).1 (ij t).2))) := by
    have hmaps : Pε.toLinearMap = ∑ t, (O (ij t).1 (ij t).2).comp
        ((U (ij t).1 (ij t).2).toLinearMap.comp (I (ij t).1 (ij t).2)) := by
      exact (Finset.sum_congr rfl
        (fun k _ ↦ Finset.sum_congr rfl (fun j _ ↦ hQ k j))).trans hsumMaps.symm
    rw [hmaps, sub_self]
    intro Li Lo s t
    exact ⟨0, fun w ↦ by simp⟩
  have hprincipal := Pε.principalSymbol_eq_of_compatible_representation AT AT'
    (L.size * J.size) (fun t ↦ CP (ij t).1 (ij t).2) (fun t ↦ hCP (ij t).1 (ij t).2)
    (fun t ↦ Din (ij t).1 (ij t).2) (fun t ↦ Dout (ij t).1 (ij t).2)
    (fun t ↦ hio (ij t).1 (ij t).2) (fun t ↦ hoi (ij t).1 (ij t).2)
    (fun t ↦ U (ij t).1 (ij t).2) (fun t ↦ p (ij t).1 (ij t).2)
    (fun t ↦ hp (ij t).1 (ij t).2) (fun t ↦ hU (ij t).1 (ij t).2)
    (fun t ↦ I (ij t).1 (ij t).2) (fun t ↦ O (ij t).1 (ij t).2)
    (fun t ↦ hI (ij t).1 (ij t).2) (fun t ↦ hO (ij t).1 (ij t).2)
    (fun t ↦ g (ij t).1 (ij t).2) (fun _ _ _ ↦ rfl) hrepresentation
  have hsumSymbols : (∑ t, g (ij t).1 (ij t).2) = ∑ k, ∑ j, g k j := by
    simpa only [Fintype.sum_prod_type] using
      (Fintype.sum_equiv ij (fun t ↦ g (ij t).1 (ij t).2)
        (fun kj ↦ g kj.1 kj.2) (fun _ ↦ rfl))
  exact hprincipal.trans (congrArg (atlasGlobalPrincipalSymbolClass AT AT' 1) hsumSymbols)

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
