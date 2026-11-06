/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalExtension
public import AtiyahSinger.Analysis.AssociatedTensorVerticalCutoffOperator
public import AtiyahSinger.Analysis.AtlasIsometricProductApproximation
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus

/-!
# Controlled regularization of a complete vertical piece

Public module ID: M0210.

Choose a base plateau and a sphere output plateau in the prescribed frames
before the regularization parameter. Fixed localization and extension maps
realize the full unregularized action, its product support, and its normalized
principal-chart return. For positive parameters they give order-one PDO
cutoffs with a controlled approximation in the supplied geometric H¹-to-H⁰
operator norm.

Source: SG III.13.5--13.6. A representation of a full sphere operator also
retains its smoothing remainder.
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
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Fixed cutoffs give order-one PDOs and a controlled full vertical-piece limit. -/
theorem exists_associatedSphereTensorVerticalPiece_regularization
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (L : AtlasPseudodifferentialPiece A A' 1) :
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
    letI (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
    ∀ (Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT'),
      ∃ (γ : X → ℝ) (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ)
        (hsγ : tsupport γ ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet)
        (hbγ : c.symm '' tsupport γ ⊆ (S.trivialization b).baseSet)
        (κ : Y → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
        (hsκ : tsupport κ ⊆ L.chart.target ∩ L.chart.symm ⁻¹'
          (A'.chart L.output.frameIndex).baseSet),
        let Co : BundleChartCutoff E c :=
          { C with
            cutoff := γ
            smooth_cutoff := hγ
            compact_support := hcγ
            support_subset := hsγ }
        let Ko : AtlasChartCutoff A' L.chart :=
          { L.output with
            cutoff := κ
            smooth_cutoff := hκ
            compact_support := hcκ
            support_subset := hsκ }
        let Din := associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
        let Dout := associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
        let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
        let β : SymbolFunction r (A.rank L.input.frameIndex * a)
            (A'.rank L.output.frameIndex * a) :=
          fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
            (A'.rank L.output.frameIndex) a (α y η)
        let p := isometricSymbolTransport (productCoordinateSwap n r)
          (tensorCoordinateSwap a (A.rank L.input.frameIndex))
          (tensorCoordinateSwap a (A'.rank L.output.frameIndex)).symm (liftedProductSymbol β γ)
        (∀ x ∈ tsupport C.cutoff, γ x = 1) ∧
        (∀ y ∈ tsupport L.output.cutoff, κ y = 1) ∧
        (tsupport κ ⊆ L.chart.symm ⁻¹' (A.chart L.input.frameIndex).baseSet) ∧
        ∃ (I : AT.smoothSections →ₗ[ℂ]
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))))
          (O : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex)))
            →ₗ[ℂ] AT'.smoothSections),
          (∀ w z, I w z = Din.localizedFunction w z) ∧
          (∀ v z, (O v).val z = Dout.extendedFunction v z) ∧
          ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
            (∀ w : AT.smoothSections,
              ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))),
                (∀ z, quantize p (I w) z = v z) ∧
                (tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
                  (tsupport C.cutoff ×ˢ tsupport L.output.cutoff)) ∧
                R (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (O v) ∧
                ∀ x : B, x ∈ c.source → x ∈ (S.trivialization b).baseSet →
                  x ∈ C.frame.baseSet → ∀ y : OrthogonalSphere r,
                    let q := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
                    (O v).val (associatedBundleMk G P (OrthogonalSphere r) q y) =
                      (C.cutoff (c x) : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                        ((tensorSectionOperator (E (projection q)) A.smoothSections
                          A'.smoothSections L.toLinearMap
                          (associatedSphereTensorFiberRestriction (a := a)
                            S E A σ hσ q w)).val y)) ∧
            ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
              ∃ (Q : AtlasPseudodifferentialOperator AT AT' 1)
                (U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))) →L[ℂ]
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))))
                (Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0),
                Q.toLinearMap = O.comp (U.toLinearMap.comp I) ∧
                (∀ v z, U v z = quantize (rightProductCutoffSymbol β γ ε) v z) ∧
                (∀ w, Rε (Li.smoothToSobolev 1 w) =
                  Lo.smoothToSobolev 0 (Q.toLinearMap w)) ∧ ‖Rε - R‖ ≤ K * ε := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace ef.symm Z
  let := isManifold_linearModelChartedSpace ef.symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  dsimp only
  intro Li Lo
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  -- Both plateaus are chosen inside the original principal and tensor-frame overlaps.
  let V := c.target ∩ c.symm ⁻¹' (C.frame.baseSet ∩ (S.trivialization b).baseSet)
  have hV : IsOpen V := c.isOpen_inter_preimage_symm
    (C.frame.open_baseSet.inter (S.trivialization b).open_baseSet)
  have hCV : tsupport C.cutoff ⊆ V := fun x hx ↦
    ⟨(C.support_subset hx).1, (C.support_subset hx).2, hC ⟨x, hx, rfl⟩⟩
  have hbasePlateau : ∃ γ : X → ℝ, ContDiff ℝ ∞ γ ∧ HasCompactSupport γ ∧
      tsupport γ ⊆ V ∧ tsupport C.cutoff ⊆ interior {x | γ x = 1} :=
    exists_compact_cutoff_one_near (tsupport C.cutoff) V C.compact_support hV hCV
  let γ : X → ℝ := hbasePlateau.choose
  have hγ : ContDiff ℝ ∞ γ := hbasePlateau.choose_spec.1
  have hcγ : HasCompactSupport γ := hbasePlateau.choose_spec.2.1
  have hγV : tsupport γ ⊆ V := hbasePlateau.choose_spec.2.2.1
  have hγone : tsupport C.cutoff ⊆ interior {x | γ x = 1} :=
    hbasePlateau.choose_spec.2.2.2
  have hsγ : tsupport γ ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet :=
    fun x hx ↦ ⟨(hγV hx).1, (hγV hx).2.1⟩
  have hbγ : c.symm '' tsupport γ ⊆ (S.trivialization b).baseSet := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hγV hx).2.2
  have hγone' (x : X) (hx : x ∈ tsupport C.cutoff) : γ x = 1 :=
    interior_subset (s := {x : X | γ x = 1}) (hγone hx)
  let W := L.chart.target ∩ L.chart.symm ⁻¹'
    ((A'.chart L.output.frameIndex).baseSet ∩ (A.chart L.input.frameIndex).baseSet)
  have hW : IsOpen W := L.chart.isOpen_inter_preimage_symm
    ((A'.chart L.output.frameIndex).open_baseSet.inter
      (A.chart L.input.frameIndex).open_baseSet)
  have hLW : tsupport L.output.cutoff ⊆ W := fun y hy ↦
    ⟨(L.output.support_subset hy).1, (L.output.support_subset hy).2,
      L.output_support_in_input_frame hy⟩
  have hspherePlateau : ∃ κ : Y → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ W ∧ tsupport L.output.cutoff ⊆ interior {y | κ y = 1} :=
    exists_compact_cutoff_one_near (tsupport L.output.cutoff) W L.output.compact_support hW hLW
  let κ : Y → ℝ := hspherePlateau.choose
  have hκ : ContDiff ℝ ∞ κ := hspherePlateau.choose_spec.1
  have hcκ : HasCompactSupport κ := hspherePlateau.choose_spec.2.1
  have hκW : tsupport κ ⊆ W := hspherePlateau.choose_spec.2.2.1
  have hκone : tsupport L.output.cutoff ⊆ interior {y | κ y = 1} :=
    hspherePlateau.choose_spec.2.2.2
  have hsκ : tsupport κ ⊆ L.chart.target ∩ L.chart.symm ⁻¹'
      (A'.chart L.output.frameIndex).baseSet := fun y hy ↦ ⟨(hκW hy).1, (hκW hy).2.1⟩
  have hκInput : tsupport κ ⊆ L.chart.symm ⁻¹' (A.chart L.input.frameIndex).baseSet :=
    fun y hy ↦ (hκW hy).2.2
  have hκone' (y : Y) (hy : y ∈ tsupport L.output.cutoff) : κ y = 1 :=
    interior_subset (s := {y : Y | κ y = 1}) (hκone hy)
  let Co : BundleChartCutoff E c :=
    { C with
      cutoff := γ
      smooth_cutoff := hγ
      compact_support := hcγ
      support_subset := hsγ }
  let Ko : AtlasChartCutoff A' L.chart :=
    { L.output with
      cutoff := κ
      smooth_cutoff := hκ
      compact_support := hcκ
      support_subset := hsκ }
  let CP : OpenPartialHomeomorph Z XY := associatedSphereProductChart S b c L.chart
  have hCP : CP ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc L.chart L.chart_mem_atlas
  let Din : AtlasChartCutoff AT CP :=
    associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
  let Dout : AtlasChartCutoff AT' CP :=
    associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
  refine ⟨γ, hγ, hcγ, hsγ, hbγ, κ, hκ, hcκ, hsκ, hγone', hκone', hκInput, ?_⟩
  -- Actual chart maps are fixed before the regularization parameter and the input section.
  let I : AT.smoothSections →ₗ[ℂ]
      𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))) :=
    (Din.exists_localize_sobolev_of_mem_maximalAtlas hCP Li 1).choose
  have hI : ∀ w z, I w z = Din.localizedFunction w z :=
    (Din.exists_localize_sobolev_of_mem_maximalAtlas hCP Li 1).choose_spec.1
  let O : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex)))
      →ₗ[ℂ] AT'.smoothSections :=
    (Dout.exists_extend_sobolev_of_mem_maximalAtlas hCP Lo 0).choose
  have hO : ∀ v z, (O v).val z = Dout.extendedFunction v z :=
    (Dout.exists_extend_sobolev_of_mem_maximalAtlas hCP Lo 0).choose_spec.1
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
  have hαK : HasCompactSupport α := by
    apply L.output.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport L.output.cutoff)
    intro y hy
    by_contra hout
    apply hy
    funext η
    simp only [α, zeroExtendedSymbol, Set.mem_univ, ite_true,
      image_eq_zero_of_notMem_tsupport hout, Complex.ofReal_zero, zero_smul, Pi.zero_apply]
  have hβK : HasCompactSupport β := by
    apply hαK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport α)
    intro y hy
    by_contra hout
    apply hy
    funext η
    change tensorIdentitySymbolMap _ _ _ (α y η) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap _ _ _).map_zero
  let hApprox :=
    exists_atlas_isometricProductCutoff_sobolev_approximation AT AT' CP hCP Din Dout I O hI hO
      (productCoordinateSwap n r) (tensorCoordinateSwap a (A.rank L.input.frameIndex))
      (tensorCoordinateSwap a (A'.rank L.output.frameIndex)).symm β hβ hβK γ hγ hcγ Li Lo
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := hApprox.choose
  have hR := hApprox.choose_spec.1
  let K : ℝ := hApprox.choose_spec.2.choose
  have hK : 0 ≤ K := hApprox.choose_spec.2.choose_spec.1
  have hbound := hApprox.choose_spec.2.choose_spec.2
  refine ⟨I, O, hI, hO, R, ?_, K, hK, ?_⟩
  · intro w
    change AT.smoothSections at w
    let hext :=
      exists_associatedSphereTensorVerticalCutoff_extension (a := a)
        S E A σ A' σ' hσ hσ' b c C hC L
        γ hγ hcγ hsγ hbγ hγone' κ hκ hcκ hsκ hκone' γ hγ hcγ hγone' I hI w
    let v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))) := hext.choose
    have hv := hext.choose_spec.1
    have hvsupport := hext.choose_spec.2.1
    have hreturn := hext.choose_spec.2.2
    have hlimit : ∃ g : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))),
        (∀ z, quantize (isometricSymbolTransport (productCoordinateSwap n r)
          (tensorCoordinateSwap a (A.rank L.input.frameIndex))
          (tensorCoordinateSwap a (A'.rank L.output.frameIndex)).symm
          (liftedProductSymbol β γ)) (I w) z = g z) ∧
        R (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (O g) := hR w
    let g : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))) := hlimit.choose
    have hg := hlimit.choose_spec.1
    have hRg := hlimit.choose_spec.2
    have heq : g = v := by
      apply SchwartzMap.ext
      intro z
      exact (hg z).symm.trans (hv z)
    have hRv : R (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (O v) :=
      hRg.trans (congrArg (fun f ↦ Lo.smoothToSobolev 0 (O f)) heq)
    refine ⟨v, hv, hvsupport, hRv, ?_⟩
    intro x hx hxb hxe y
    exact (hO v _).trans (hreturn x hx hxb hxe y)
  · intro ε hε hε1
    -- Opposite-frame cutoffs prove the real cross-support conditions of the same PDO.
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
    have hcrossIn : tsupport Din.cutoff ⊆ CP.symm ⁻¹'
        (AT'.chart Dout.frameIndex).baseSet := by
      let oppositeCutoff :=
        associatedSphereTensorChartCutoff S E A' σ' hσ' b c C hC L.chart Ki'
      exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
    have hcrossOut : tsupport Dout.cutoff ⊆ CP.symm ⁻¹'
        (AT.chart Din.frameIndex).baseSet := by
      let oppositeCutoff :=
        associatedSphereTensorChartCutoff S E A σ hσ b c Co hbγ L.chart Ko'
      exact fun z hz ↦ (oppositeCutoff.support_subset hz).2
    let hpositive := exists_associatedSphereTensorVerticalCutoffOperator (a := a)
      S E A σ A' σ' hσ hσ' b c hc C Co hC hbγ L.chart L.chart_mem_atlas L.input Ko
      α hα hαK γ hγ hcγ hcrossIn hcrossOut I O hI hO ε hε
    let Q : AtlasPseudodifferentialOperator AT AT' 1 := hpositive.choose
    let U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))) →L[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))) :=
      hpositive.choose_spec.choose
    have hQ := hpositive.choose_spec.choose_spec.1
    have hU := hpositive.choose_spec.choose_spec.2
    let herrorBound := hbound ε hε hε1 U (fun v z ↦ (hU v z).symm)
    let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := herrorBound.choose
    have hRε := herrorBound.choose_spec.1
    have herror := herrorBound.choose_spec.2
    refine ⟨Q, U, Rε, hQ, hU, ?_, herror⟩
    intro w
    have hvalue : Q.toLinearMap w = O (U (I w)) := congrArg (fun f ↦ f w) hQ
    exact (hRε w).trans (congrArg (Lo.smoothToSobolev 0) hvalue.symm)

end AtiyahSinger
