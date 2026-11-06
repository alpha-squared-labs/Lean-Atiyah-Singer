/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasCutoffVerticalCoordinateEnergy
public import AtiyahSinger.Analysis.RightProductVerticalBound
public import AtiyahSinger.Analysis.AssociatedChartExtensionSupport
public import AtiyahSinger.Analysis.AssociatedTensorVerticalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorSupportedReturnBound
public import AtiyahSinger.Analysis.AssociatedTensorVerticalCoordinateEnergy

/-!
# The actual vertical regularization is bounded by its original native fiber family

Public module ID: M1050.

The given I/O/U maps retain their original product coordinates. Spatial estimates
control the actual right cutoff, arbitrary original sphere cutoffs are bounded in
the fixed native fiber norm, and the actual output chart is returned at order zero.
No unregularized vertical map is declared to be a joint pseudodifferential operator.
-/

@[expose] public noncomputable section

set_option Elab.async false


open Lean Elab Tactic Meta in
local elab "as_aux_native_zeta" " => " seq:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic seq)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished native bound"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Native bound contains an error-recovery admission"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

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
  (F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [T2Space B]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D" => AssociatedEquivariantFiber (E := F.Fiber) S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable (F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D'" => AssociatedEquivariantFiber (E := F'.Fiber) S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Yc" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

omit [T2Space B] in
set_option maxSynthPendingDepth 40 in
set_option cleanup.letToHave false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
-- Keep the same original cutoff coordinates, native family, and extension witnesses.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- At a fixed positive cutoff parameter, vertical regularization is bounded by its native rows. -/
theorem vertical_regularization_native_source_bound
    (b : B) (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C Co : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (hCo : c.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (N : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      AtlasPseudodifferentialPiece
        (nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber)
        (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber) 1)
    (Ko : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      AtlasChartCutoff (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber)
        L.chart) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A : SmoothComplexBundleAtlas (n := r) F.Fiber :=
      nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' : SmoothComplexBundleAtlas (n := r) F'.Fiber :=
      nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native 𝓘(ℝ, OrthogonalGroupModel r) hσ
    let hA' := σ'.isSmoothAtlas_native 𝓘(ℝ, OrthogonalGroupModel r) hσ'
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
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
      associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
    let Din := associatedSphereTensorChartCutoff S E A σ hA b c C hC L.chart L.input
    let Dout := associatedSphereTensorChartCutoff S E A' σ' hA' b c Co hCo L.chart Ko
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    let β : SymbolFunction r (F.rank * a) (F'.rank * a) :=
      fun y η ↦ tensorIdentitySymbolMap F.rank F'.rank a (α y η)
    ∀ (I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
      (O : 𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))) →ₗ[ℂ] AT'.smoothSections),
      (∀ w z, I w z = Din.localizedFunction w z) →
      (∀ v z, (O v).val z = Dout.extendedFunction v z) →
      ∀ (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT')
        (ε : ℝ), 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
          ∀ U : 𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))),
            (∀ v z, U v z = quantize (rightProductCutoffSymbol (n := n) (m := r) (r := a)
              (s := F.rank) (t := F'.rank) β Co.cutoff ε) v z) →
            ∀ (w : AT.smoothSections)
              (u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber),
              (∀ x i, u x i = nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber
                ((C.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
                  associatedSphereTensorLocalFiberCoordinates (n := n) (r := r) (a := a)
                    S E A b C.frame
                    C.frame_mem_atlas i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                    (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x)))) →
              ∀ hu : ∀ i : Fin a,
                  MemLp (fun x ↦ N.smoothToSobolev 1 (u x i)) 2 (volume : Measure Xp),
                ‖Lo.smoothToSobolev 0 (O (U (I w)))‖ ^ 2 ≤
                  K * ∑ i : Fin a,
                    ‖(hu i).toLp (fun x ↦ N.smoothToSobolev 1 (u x i))‖ ^ 2 := by
  as_aux_native_zeta =>
    classical

    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA'
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    let := associatedSphereChartedSpace S
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let := linearModelChartedSpace e.symm Z
    let := isManifold_linearModelChartedSpace e.symm Z
    intro AT AT' Din Dout α β I O hI hO Lo ε hε
    let CP := associatedSphereProductChart S b c L.chart
    have hNd := SmoothBundlePresentation.exists_atlasCutoff_vertical_energy_le_family_sobolev
      (n := r) (r := F.rank) (M := Y) (E := F.Fiber) (m := n) (a := a)
      N L.chart L.chart_mem_atlas L.input
    let cN : ℝ := hNd.choose
    have hcN : 0 ≤ cN := hNd.choose_spec.1
    have hN := hNd.choose_spec.2
    have hα : IsSymbol Set.univ 1 α := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1
      L.output.cutoff L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _)
      L.symbol L.isSymbol
    have hβ : IsSymbol Set.univ 1 β := isSymbol_continuousLinearMap 1 α hα
      ((tensorIdentitySymbolMap F.rank F'.rank a).restrictScalars ℝ)
    have hαK : HasCompactSupport α := hasCompactSupport_zeroExtendedSymbol
      Set.univ L.output.cutoff L.symbol L.output.compact_support
    have hβK : HasCompactSupport β := by
      let g : (Yc → (EuclideanSpace ℂ (Fin F.rank) →L[ℂ]
          EuclideanSpace ℂ (Fin F'.rank))) →
          (Yc → (EuclideanSpace ℂ (Fin (F.rank * a)) →L[ℂ]
            EuclideanSpace ℂ (Fin (F'.rank * a)))) :=
        fun f η ↦ tensorIdentitySymbolMap F.rank F'.rank a (f η)
      have hg : g 0 = 0 := by
        funext η
        exact (tensorIdentitySymbolMap F.rank F'.rank a).map_zero
      exact hαK.comp_left hg
    change AtlasBundlePresentation AT' at Lo
    change ∀ w z, I w z = Din.localizedFunction w z at hI
    change ∀ v z, (O v).val z = Dout.extendedFunction v z at hO
    have hCP : CP ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
      associatedSphereProductChart_mem_maximalAtlas S b c hc L.chart L.chart_mem_atlas
    -- The supplied return map is the bounded extension of the same original output chart.
    have hreturn : ∃ cO : ℝ, 0 ≤ cO ∧
        ∀ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))),
          ‖Lo.smoothToSobolev 0 (O v)‖ ≤ cO * ‖v.toLp 2‖ := by
      have hd : ∃ O₀ :
          𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))) →ₗ[ℂ] AT'.smoothSections,
          (∀ v x, (O₀ v).val x = Dout.extendedFunction v x) ∧
            ∃ cO : ℝ, 0 ≤ cO ∧ ∀ v,
              ‖Lo.smoothToSobolev 0 (O₀ v)‖ ≤ cO * ‖schwartzSobolevCoordinate 0 v‖ :=
        AtlasChartCutoff.exists_extend_sobolev_of_mem_maximalAtlas
          (n := n + r) (M := Z) (E := T') (A := AT') (c := CP) Dout hCP Lo 0
      obtain ⟨O₀, hO₀, cO, hcO, hb⟩ := hd
      have heq : O = O₀ := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        funext x
        exact (hO v x).trans (hO₀ v x).symm
      refine ⟨cO, hcO, ?_⟩
      intro v
      rw [heq]
      simpa only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
        SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply] using hb v
    let cO : ℝ := hreturn.choose
    have hreturnBound := hreturn.choose_spec.2
    have hverticalData := exists_rightProductCutoff_vertical_estimate
      (n := n) (m := r) (r := a) (s := F.rank) (t := F'.rank)
      β hβ hβK Co.cutoff Co.smooth_cutoff Co.compact_support ε hε
    let cV : ℝ := hverticalData.choose
    have hcV : 0 ≤ cV := hverticalData.choose_spec.1
    have hvertical := hverticalData.choose_spec.2
    refine ⟨cO ^ 2 * (cV * cN), mul_nonneg (sq_nonneg _) (mul_nonneg hcV hcN), ?_⟩
    intro U hU w u hvalue hu
    -- The actual I row equals the given native family through the fixed section equivalence.
    have hcoords (i : Fin a) (x : Xp) (y : Yc) (l : Fin F.rank) :
        L.input.localize L.chart_mem_atlas
            ((nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber).symm (u x i)) y l =
          I w (e.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x, y))
            (finProdFinEquiv (i, l)) := by
      rw [hvalue,
        (nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber).symm_apply_apply, hI]
      exact (associatedSphereTensorChartCutoff_localizedFunction (a := a)
        S E A σ hA b c C hC L.chart L.chart_mem_atlas L.input
        w ((EuclideanSpace.equiv (Fin n) ℝ).symm x) y i l).symm
    have henergy := hN u hu (I w) hcoords
    have hv := hvertical (I w) (U (I w)) (hU (I w))
    have ho := (pow_le_pow_left₀ (norm_nonneg (Lo.smoothToSobolev 0 (O (U (I w)))))
      (hreturnBound (U (I w))) 2).trans_eq (mul_pow _ _ 2)
    have hmiddle := hv.trans (mul_le_mul_of_nonneg_left henergy hcV)
    have hscaled := mul_le_mul_of_nonneg_left hmiddle (sq_nonneg cO)
    let en : ℝ := ∑ i : Fin a,
      ‖(hu i).toLp (fun x ↦ N.smoothToSobolev 1 (u x i))‖ ^ 2
    have heq : cO ^ 2 * (cV * (cN * en)) = (cO ^ 2 * (cV * cN)) * en :=
      (congrArg (fun z : ℝ ↦ cO ^ 2 * z) (mul_assoc cV cN en).symm).trans
        (mul_assoc (cO ^ 2) (cV * cN) en).symm
    exact (ho.trans hscaled).trans_eq heq

end AtiyahSinger
