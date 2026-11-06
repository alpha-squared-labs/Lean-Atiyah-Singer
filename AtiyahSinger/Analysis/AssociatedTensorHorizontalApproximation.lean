/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module


public import AtiyahSinger.Analysis.AssociatedTensorHorizontalExtension
public import AtiyahSinger.Analysis.AtlasProductCutoffApproximation
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff

/-!
# Controlled approximation of a local horizontal lift

Public module ID: M0159.

A fixed sphere presentation and fixed input/output maps are used for every
positive product-frequency cutoff. The unregularized outputs reconstruct
the local horizontal lift through the finite sphere partition. Their finite
sum converges in the supplied H¹-to-H⁰ norm with a common linear error bound.
The Schwartz regularization maps are explicit inputs, and the conclusion
extends their sum through the same fixed localization.
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

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One original sphere partition gives controlled approximation of the actual horizontal lift. -/
theorem exists_associatedSphereTensorLocalHorizontal_sobolev_approximation
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (J : AtlasBundlePresentation A)
    (Co : BundleChartCutoff (r := a') E' L.chart) (hCoFrame : Co.frame = L.output.frame)
    (hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (hCoOne : ∀ x ∈ tsupport L.output.cutoff, Co.cutoff x = 1)
    (κ : Fin J.size → Y → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
    (hκK : ∀ j, HasCompactSupport (κ j))
    (hκsupport : ∀ j, tsupport (κ j) ⊆ (J.chart j).target ∩
      (J.chart j).symm ⁻¹' (A.chart (J.frameIndex j)).baseSet)
    (hκone : ∀ j y, y ∈ tsupport (J.chartCutoff j).cutoff → κ j y = 1) :
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
    let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
      ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
    let Din (j : Fin J.size) := associatedSphereTensorChartCutoff S E A σ hσ b
      L.chart L.input hinput (J.chart j) (J.chartCutoff j)
    let Dout (j : Fin J.size) := associatedSphereTensorChartCutoff S E' A σ hσ b
      L.chart Co hCo (J.chart j) (Kout j)
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    ∀ (I : ∀ j : Fin J.size, AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))))
      (O : ∀ j : Fin J.size,
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))) →ₗ[ℂ] AT'.smoothSections),
      (∀ j w z, I j w z = (Din j).localizedFunction w z) →
      (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) →
      ∀ (Li : AtlasBundlePresentation (n := n + r) (M := Z) (E := T) AT)
        (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
        ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
          (∀ w : AT.smoothSections, R (Li.smoothToSobolev 1 w) =
            Lo.smoothToSobolev 0 (associatedSphereTensorLocalHorizontalLift (a := a)
              S E A σ E' L hσ b χ hχ hχsupport houtput w)) ∧
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∀ U : ∀ j : Fin J.size,
              𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
                𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
              (∀ j v z, U j v z = quantize
                (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                  (productCutoffSymbol α (κ j) ε x ξ)) v z) →
              ∃ Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
                (∀ w, Rε (Li.smoothToSobolev 1 w) =
                  Lo.smoothToSobolev 0 (∑ j, O j (U j (I j w)))) ∧
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
  let CP (j : Fin J.size) : OpenPartialHomeomorph Z XY :=
    associatedSphereProductChart S b L.chart (J.chart j)
  let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
    ⟨J.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
  let Din (j : Fin J.size) : AtlasChartCutoff AT (CP j) :=
    associatedSphereTensorChartCutoff S E A σ hσ b L.chart L.input hinput
      (J.chart j) (J.chartCutoff j)
  let Dout (j : Fin J.size) : AtlasChartCutoff AT' (CP j) :=
    associatedSphereTensorChartCutoff S E' A σ hσ b L.chart Co hCo (J.chart j) (Kout j)
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  let hα := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 L.output.cutoff
    L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _) L.symbol L.isSymbol
  let β (j : Fin J.size) : SymbolFunction n (a * A.rank (J.frameIndex j))
      (a' * A.rank (J.frameIndex j)) :=
    fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j)) (α x ξ)
  have hβ (j : Fin J.size) : IsSymbol Set.univ 1 (β j) :=
    isSymbol_continuousLinearMap 1 α hα
      ((tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))).restrictScalars ℝ)
  have hβK (j : Fin J.size) : HasCompactSupport (β j) := by
    apply L.output.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport L.output.cutoff)
    intro x hx
    by_contra hout
    apply hx
    funext ξ
    change tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
      (zeroExtendedSymbol Set.univ L.output.cutoff L.symbol x ξ) = 0
    simp [zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hout]
  dsimp only
  intro I O hI hO Li Lo
  change AtlasBundlePresentation AT at Li
  change AtlasBundlePresentation AT' at Lo
  change ∀ j w z, I j w z = (Din j).localizedFunction w z at hI
  change ∀ j v z, (O j v).val z = (Dout j).extendedFunction v z at hO
  have hCP (j : Fin J.size) : CP j ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b L.chart L.chart_mem_atlas
      (J.chart j) (J.chart_mem_atlas j)
  -- All local limits and constants are chosen before the section or positive parameter.
  have hlocal (j : Fin J.size) :
      ∃ R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
        (∀ w : AT.smoothSections,
          ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ z, quantize (liftedProductSymbol (β j) (κ j)) (I j w) z = v z) ∧
              R (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (O j v)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ w z, quantize (productCutoffSymbol (β j) (κ j) ε) w z = U w z) →
            ∃ Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0,
              (∀ w, Rε (Li.smoothToSobolev 1 w) =
                Lo.smoothToSobolev 0 (O j (U (I j w)))) ∧ ‖Rε - R‖ ≤ C * ε :=
    exists_atlas_productCutoff_sobolev_approximation
    (n := n) (m := r) (M := Z) (E := T) (F := T') AT AT' (CP j) (hCP j)
    (Din j) (Dout j) (I j) (O j) (hI j) (hO j) (β j) (hβ j) (hβK j)
    (κ j) (hκ j) (hκK j) Li Lo
  choose Rj hRj Cj hCj hbound using hlocal
  let R : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ j, Rj j
  refine ⟨R, ?_, ∑ j, Cj j, Finset.sum_nonneg (fun j _ ↦ hCj j), ?_⟩
  · intro w
    change AT.smoothSections at w
    have houtputLocal (j : Fin J.size) :
        ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
          (∀ z, quantize (liftedProductSymbol (β j) (κ j)) (I j w) z = v z) ∧
          ∀ z : Z, (Dout j).extendedFunction v z =
            ((if (associatedSphereTrivialization S b z).2 ∈ (J.chart j).source then
              (J.chartCutoff j).cutoff ((J.chart j) (associatedSphereTrivialization S b z).2)
              else 0 : ℝ) : ℂ) •
              (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
                hχ hχsupport houtput w).val z :=
      exists_associatedSphereTensorHorizontalCutoff_extension
      (a := a) S E A σ E' L hσ b hinput houtput χ hχ hχsupport hχone
      (J.chart j) (J.chart_mem_atlas j) (J.chartCutoff j) Co hCoFrame hCo hCoOne
      (κ j) (hκ j) (hκK j) (hκsupport j) (hκone j)
      (κ j) (hκ j) (hκK j) (hκone j) (I j) (hI j) w
    let v : ∀ j : Fin J.size,
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))) :=
      fun j ↦ (houtputLocal j).choose
    have hv (j : Fin J.size) :
        ∀ z, quantize (liftedProductSymbol (β j) (κ j)) (I j w) z = v j z :=
      (houtputLocal j).choose_spec.1
    have hvExtension (j : Fin J.size) : ∀ z : Z, (Dout j).extendedFunction (v j) z =
        ((if (associatedSphereTrivialization S b z).2 ∈ (J.chart j).source then
          (J.chartCutoff j).cutoff ((J.chart j) (associatedSphereTrivialization S b z).2)
          else 0 : ℝ) : ℂ) •
          (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
            hχ hχsupport houtput w).val z := (houtputLocal j).choose_spec.2
    have hlimit (j : Fin J.size) : Rj j (Li.smoothToSobolev 1 w) =
        Lo.smoothToSobolev 0 (O j (v j)) := by
      have hvalue :
          ∃ g : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ z, quantize (liftedProductSymbol (β j) (κ j)) (I j w) z = g z) ∧
              Rj j (Li.smoothToSobolev 1 w) = Lo.smoothToSobolev 0 (O j g) := hRj j w
      obtain ⟨g, hg, hRg⟩ := hvalue
      have heq : g = v j := by
        apply SchwartzMap.ext
        intro z
        exact (hg z).symm.trans (hv j z)
      rwa [heq] at hRg
    have hsum : (∑ j, O j (v j)) =
        associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
          hχ hχsupport houtput w := by
      apply Subtype.ext
      funext z
      let H : AT'.smoothSections := associatedSphereTensorLocalHorizontalLift (a := a)
        S E A σ E' L hσ b χ hχ hχsupport houtput w
      let weight (j : Fin J.size) : ℝ :=
        if (associatedSphereTrivialization S b z).2 ∈ (J.chart j).source then
          (J.chartCutoff j).cutoff ((J.chart j) (associatedSphereTrivialization S b z).2)
        else 0
      have hweights : ∑ j, weight j = 1 := by
        calc
          ∑ j, weight j = ∑ j, J.cutoff j (associatedSphereTrivialization S b z).2 :=
            Finset.sum_congr rfl (fun j _ ↦ J.chartCutoff_pullback j _)
          _ = 1 := J.sum_cutoff _
      simp only [Submodule.coe_sum, Finset.sum_apply]
      change ∑ j, (O j (v j)).val z = H.val z
      calc
        ∑ j, (O j (v j)).val z = ∑ j, (weight j : ℂ) • H.val z :=
          Finset.sum_congr rfl (fun j _ ↦ (hO j (v j) z).trans (hvExtension j z))
        _ = (∑ j, (weight j : ℂ)) • H.val z := (Finset.sum_smul ..).symm
        _ = H.val z := by
          rw [← Complex.ofReal_sum, hweights, Complex.ofReal_one, one_smul]
    change (∑ j, Rj j) (Li.smoothToSobolev 1 w) = _
    calc
      (∑ j, Rj j) (Li.smoothToSobolev 1 w) =
          ∑ j, Rj j (Li.smoothToSobolev 1 w) :=
        sum_apply Finset.univ Rj (Li.smoothToSobolev 1 w)
      _ =
          ∑ j, Lo.smoothToSobolev 0 (O j (v j)) :=
        Finset.sum_congr rfl (fun j _ ↦ hlimit j)
      _ = Lo.smoothToSobolev 0 (∑ j, O j (v j)) :=
        (map_sum (Lo.smoothToSobolev 0) (fun j ↦ O j (v j)) Finset.univ).symm
      _ = _ := congrArg (Lo.smoothToSobolev 0) hsum
  · intro ε hε hε1 U hU
    have hsymbol (j : Fin J.size) : productCutoffSymbol (β j) (κ j) ε =
        (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
          (productCutoffSymbol α (κ j) ε x ξ)) := by
      funext x ξ
      simp only [productCutoffSymbol, liftedProductSymbol, β, map_smul]
    have hpositive (j : Fin J.size) := hbound j ε hε hε1 (U j) (by
      intro v z
      rw [hsymbol]
      exact (hU j v z).symm)
    choose Rεj hRεj herror using hpositive
    let Rε : Li.SobolevSpace 1 →L[ℂ] Lo.SobolevSpace 0 := ∑ j, Rεj j
    refine ⟨Rε, ?_, ?_⟩
    · intro w
      change (∑ j, Rεj j) (Li.smoothToSobolev 1 w) = _
      calc
        (∑ j, Rεj j) (Li.smoothToSobolev 1 w) =
            ∑ j, Rεj j (Li.smoothToSobolev 1 w) :=
          sum_apply Finset.univ Rεj (Li.smoothToSobolev 1 w)
        _ =
            ∑ j, Lo.smoothToSobolev 0 (O j (U j (I j w))) :=
          Finset.sum_congr rfl (fun j _ ↦ hRεj j w)
        _ = Lo.smoothToSobolev 0 (∑ j, O j (U j (I j w))) :=
          (map_sum (Lo.smoothToSobolev 0) (fun j ↦ O j (U j (I j w))) Finset.univ).symm
    · -- The common epsilon is retained in the finite sum of the actual operator errors.
      change ‖(∑ j, Rεj j) - ∑ j, Rj j‖ ≤ (∑ j, Cj j) * ε
      calc
        ‖(∑ j, Rεj j) - ∑ j, Rj j‖ = ‖∑ j, (Rεj j - Rj j)‖ :=
          congrArg norm (Finset.sum_sub_distrib (s := Finset.univ) Rεj Rj).symm
        _ ≤ ∑ j, ‖Rεj j - Rj j‖ := norm_sum_le Finset.univ (fun j ↦ Rεj j - Rj j)
        _ ≤ ∑ j, Cj j * ε :=
          Finset.sum_le_sum (fun j _ ↦ herror j)
        _ = (∑ j, Cj j) * ε := (Finset.sum_mul Finset.univ Cj ε).symm

end AtiyahSinger

