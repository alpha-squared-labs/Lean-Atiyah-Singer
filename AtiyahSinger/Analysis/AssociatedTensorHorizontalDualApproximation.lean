/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalExtension
public import AtiyahSinger.Analysis.AtlasProductCutoffDualBound
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff

/-!
# Negative-norm approximation of the original local horizontal lift

Public module ID: M0163.

The given local horizontal lift and the supplied positive cutoffs use the
same input/output maps and the same whole sphere partition. Their literal
error has H⁰-to-H⁻¹ norm bounded by one constant times epsilon. This direction
is required for the actual formal-adjoint approximation; it is proved directly
from the negative-order Fourier estimate, with all original maps retained.
-/

@[expose] public noncomputable section

set_option Elab.async false


/- The auxiliary proof is closed after expanding its free local let values. -/
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
-- The finite original chart outputs reconstruct the same lift before the negative-norm estimate.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original local horizontal cutoff error has a uniform negative Sobolev bound. -/
theorem associatedSphereTensorLocalHorizontal_error_sobolev_neg_one_bound
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
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ U : ∀ j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ j v z, U j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                (productCutoffSymbol α (κ j) ε x ξ)) v z) →
            ∀ w : AT.smoothSections,
              ‖Lo.smoothToSobolev (-1)
                (associatedSphereTensorLocalHorizontalLift (a := a)
                  S E A σ E' L hσ b χ hχ hχsupport houtput w - ∑ j, O j (U j (I j w)))‖ ≤
                C * ε * ‖Li.smoothToSobolev 0 w‖ := by
  as_aux_lemma_zeta =>
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
    -- Every local bound is fixed before epsilon and before choosing the input section.
    have hlocal (j : Fin J.size) := norm_productCutoff_error_sobolev_neg_one_le
      (n := n) (m := r) (M := Z) (E := T) (F := T') AT AT' (CP j) (hCP j)
      (Din j) (Dout j) (I j) (O j) (hI j) (hO j) (β j) (hβ j) (hβK j)
      (κ j) (hκ j) (hκK j) Li Lo
    choose Cj hCj hbound using hlocal
    refine ⟨∑ j, Cj j, Finset.sum_nonneg (fun j _ ↦ hCj j), ?_⟩
    intro ε hε hεone U hU w
    -- The original whole-fiber extension supplies the actual unregularized output at each slot.
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
    have hsymbol (j : Fin J.size) : productCutoffSymbol (β j) (κ j) ε =
        (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
          (productCutoffSymbol α (κ j) ε x ξ)) := by
      funext x ξ
      simp only [productCutoffSymbol, liftedProductSymbol, β, map_smul]
    have herror (j : Fin J.size) :
        ‖Lo.smoothToSobolev (-1) (O j (v j - U j (I j w)))‖ ≤
          Cj j * ε * ‖Li.smoothToSobolev 0 w‖ := by
      have hcut (z : XY) :
          quantize (productCutoffSymbol (β j) (κ j) ε) (I j w) z = U j (I j w) z := by
        rw [hsymbol j]
        exact (hU j (I j w) z).symm
      exact hbound j ε hε hεone w (v j) (U j (I j w)) (hv j) hcut
    -- Sum the section errors using the fixed lift, partition and Sobolev presentations.
    have hsumError : associatedSphereTensorLocalHorizontalLift (a := a)
        S E A σ E' L hσ b χ hχ hχsupport houtput w - ∑ j, O j (U j (I j w)) =
          ∑ j, O j (v j - U j (I j w)) := by
      rw [← hsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ ↦ (O j).map_sub _ _ |>.symm)
    have hcoordinate : Lo.smoothToSobolev (-1)
        (associatedSphereTensorLocalHorizontalLift (a := a)
          S E A σ E' L hσ b χ hχ hχsupport houtput w - ∑ j, O j (U j (I j w))) =
        ∑ j, Lo.smoothToSobolev (-1) (O j (v j - U j (I j w))) :=
      (congrArg (Lo.smoothToSobolev (-1)) hsumError).trans
        (map_sum (Lo.smoothToSobolev (-1)) (fun j ↦ O j (v j - U j (I j w))) Finset.univ)
    have hboundSum : ‖∑ j, Lo.smoothToSobolev (-1) (O j (v j - U j (I j w)))‖ ≤
        (∑ j, Cj j) * ε * ‖Li.smoothToSobolev 0 w‖ := by
      have hn := norm_sum_le Finset.univ
        (fun j ↦ Lo.smoothToSobolev (-1) (O j (v j - U j (I j w))))
      have hp := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ herror j)
      have heq : (∑ j, Cj j * ε * ‖Li.smoothToSobolev 0 w‖) =
          (∑ j, Cj j) * ε * ‖Li.smoothToSobolev 0 w‖ :=
        (Finset.sum_mul Finset.univ (fun j ↦ Cj j * ε) ‖Li.smoothToSobolev 0 w‖).symm.trans
          (congrArg (· * ‖Li.smoothToSobolev 0 w‖) (Finset.sum_mul Finset.univ Cj ε).symm)
      exact hn.trans (hp.trans_eq heq)
    exact (congrArg norm hcoordinate).trans_le hboundSum

end AtiyahSinger
