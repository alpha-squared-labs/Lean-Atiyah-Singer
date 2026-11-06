/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalHorizontalRegularization
public import AtiyahSinger.Analysis.CompatibleChartGlobalSymbol
public import AtiyahSinger.Analysis.CompatibleChartCommonSymbolMaps

/-!
# Complete horizontal symbols in a specified product chart

A supplied order-one regularized horizontal family is localized in any
compatible target chart, using one pair of cutoff maps for the whole finite
family. The full symbol represents the finite operator sum exactly, and its
difference from the sum of the supplied intrinsic representatives has order
zero. The strengthened theorem retains common plateau cutoffs.
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
set_option maxHeartbeats 4800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The same complete horizontal local symbol retains its actual common plateau cutoffs. -/
theorem exists_horizontalCutoff_localSymbol_with_plateaus
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
          (L.piece k).input (fun _ h ↦ h.elim (fun x hx ↦
            L.piece_support k ⟨x, Or.inr hx.1, hx.2⟩)) (J.chart j) (J.chartCutoff j)
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
            ∀ g : Fin L.size → Fin J.size → atlasGlobalSymbolSpace AT AT' 1,
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
                else 0) →
              ∀ (c : OpenPartialHomeomorph Z XY)
                (_hc : c ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z)
                (e₀ : AT.Index) (f₀ : AT'.Index) (z : XY),
                z ∈ atlasSymbolChartDomain AT AT' c e₀ f₀ →
                ∃ (D₀ : AtlasChartCutoff AT c) (K₀ : AtlasChartCutoff AT' c),
                  ∃ (I₀ : AT'.smoothSections →ₗ[ℂ]
                      𝓢(XY, EuclideanSpace ℂ (Fin (AT'.rank K₀.frameIndex))))
                    (O₀ : 𝓢(XY, EuclideanSpace ℂ (Fin (AT.rank D₀.frameIndex)))
                      →ₗ[ℂ] AT.smoothSections),
                    (∀ v y, I₀ v y = K₀.localizedFunction v y) ∧
                    (∀ u x, (O₀ u).val x = D₀.extendedFunction u x) ∧
                    D₀.frameIndex = e₀ ∧ K₀.frameIndex = f₀ ∧
                    D₀.cutoff = K₀.cutoff ∧
                    ∃ (V : Set XY)
                      (p : SymbolFunction (n + r) (AT.rank D₀.frameIndex)
                        (AT'.rank K₀.frameIndex)),
                      IsOpen V ∧ z ∈ V ∧
                      V ⊆ atlasSymbolChartDomain AT AT' c D₀.frameIndex K₀.frameIndex ∧
                      (∀ y ∈ V, D₀.cutoff y = 1) ∧ IsSymbol Set.univ 1 p ∧
                      IsSymbol V 0 (p - atlasGlobalSymbolInChart AT AT'
                        (∑ k, ∑ j, g k j).val c D₀.frameIndex K₀.frameIndex) ∧
                      ∀ (u : 𝓢(XY, EuclideanSpace ℂ (Fin (AT.rank D₀.frameIndex)))) y,
                        quantize p u y =
                          I₀ ((∑ k, ∑ j, (Q k j).toLinearMap) (O₀ u)) y := by
  classical
  have hquant_sum {d ri ro : ℕ} {ι : Type} [Fintype ι]
      (b : ι → SymbolFunction d ri ro) (hb : ∀ j, IsSymbol Set.univ 1 (b j))
      (u : 𝓢(EuclideanSpace ℝ (Fin d), EuclideanSpace ℂ (Fin ri)))
      (y : EuclideanSpace ℝ (Fin d)) :
      quantize (∑ j, b j) u y = ∑ j, quantize (b j) u y := by
    have hInt (q : SymbolFunction d ri ro) (hq : IsSymbol Set.univ 1 q) :
        Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ y ξ : ℂ)) •
          q y ξ (fourierSG u ξ)) := by
      have hgrowth : (q y).HasTemperateGrowth := by
        refine ⟨?_, ?_⟩
        · have hs : ContDiff ℝ ∞ (Function.uncurry q) := by
            simpa only [Set.univ_prod_univ, contDiffOn_univ] using hq.1
          exact hs.comp (contDiff_const.prodMk contDiff_id)
        · intro j
          obtain ⟨C, hC, hbound⟩ := hq.2 {y} (Set.subset_univ _) isCompact_singleton 0 j
          refine ⟨⌈1 - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
          have hbound' := hbound y (Set.mem_singleton y) ξ
          simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hbound'
          apply hbound'.trans
          apply mul_le_mul_of_nonneg_left _ hC
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
      have hphase : (fun ξ : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (Complex.I * (inner ℝ y ξ : ℂ))).HasTemperateGrowth := by
        simpa [Function.comp_def, mul_comm] using
          Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ y).hasTemperateGrowth
      have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
        inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      let d : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
        (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d))
          ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
      let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (FourierTransform.fourier u)
      exact (SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.id ℂ
          (EuclideanSpace ℂ (Fin ri) →L[ℂ]
            EuclideanSpace ℂ (Fin ro))).flip
        (hphase.smul hgrowth) w).integrable
    simp only [quantize, Finset.sum_apply, sum_apply, Finset.smul_sum]
    rw [integral_finsetSum _ (fun j _ ↦ hInt (b j) (hb j)), Finset.smul_sum]
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
    fun _ h ↦ h.elim (fun x hx ↦ L.piece_support k ⟨x, Or.inr hx.1, hx.2⟩)
  let Din (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff AT (CP k j) :=
    associatedSphereTensorChartCutoff S E A σ hσ (L.center k) (L.piece k).chart
      (L.piece k).input (hinput k) (J.chart j) (J.chartCutoff j)
  let Dout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff AT' (CP k j) :=
    associatedSphereTensorChartCutoff S E' A σ hσ (L.center k) (L.piece k).chart
      (Co k) (hCo k) (J.chart j) (Kout k j)
  intro hCoFrame hCoInput I O hI hO ε hε Q U hQ hU g hg c hc e₀ f₀ z hz
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
  -- One target cutoff pair retains all original source maps and complete symbols.
  obtain ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, hDK, V, q, hV, hzV, hVU,
      hOne, hq, hqlower, hqaction⟩ :=
    exists_common_local_symbols_with_plateaus_of_compatible_charts AT AT'
      (fun kj : Fin L.size × Fin J.size ↦ CP kj.1 kj.2)
      (fun kj ↦ hCP kj.1 kj.2) (fun kj ↦ Din kj.1 kj.2) (fun kj ↦ Dout kj.1 kj.2)
      (fun kj ↦ hio kj.1 kj.2) (fun kj ↦ hoi kj.1 kj.2)
      (fun kj ↦ U kj.1 kj.2) (fun kj ↦ p kj.1 kj.2) (fun kj ↦ hp kj.1 kj.2)
      (fun kj ↦ hU kj.1 kj.2) (fun kj ↦ I kj.1 kj.2) (fun kj ↦ O kj.1 kj.2)
      (fun kj ↦ hI kj.1 kj.2) (fun kj ↦ hO kj.1 kj.2)
      (fun kj ↦ (g kj.1 kj.2).val) (fun kj ↦ hg kj.1 kj.2) c hc e₀ f₀ z hz
  let qsum := ∑ kj : Fin L.size × Fin J.size, q kj
  have hqsum : IsSymbol Set.univ 1 qsum :=
    (symbolSpace Set.univ isOpen_univ 1 _ _).sum_mem (fun kj _ ↦ hq kj)
  have hrem : IsSymbol V 0 (qsum - atlasGlobalSymbolInChart AT AT'
      (∑ k, ∑ j, g k j).val c D₀.frameIndex K₀.frameIndex) := by
    have hsum := (symbolSpace V hV (1 - 1) _ _).sum_mem (t := Finset.univ)
      (fun kj _ ↦ hqlower kj)
    change IsSymbol V (1 - 1) (∑ kj : Fin L.size × Fin J.size,
      (q kj - atlasGlobalSymbolInChart AT AT' (g kj.1 kj.2).val
        c D₀.frameIndex K₀.frameIndex)) at hsum
    norm_num only [sub_self] at hsum
    convert hsum using 1
    funext y η
    apply ContinuousLinearMap.ext
    intro v
    by_cases hframes : c.symm y ∈ (AT.chart D₀.frameIndex).baseSet ∧
        c.symm y ∈ (AT'.chart K₀.frameIndex).baseSet
    all_goals
      simp only [qsum, atlasGlobalSymbolInChart, hframes, and_self, dite_true, dite_false,
        Submodule.coe_sum, Finset.sum_apply, sub_apply,
        Pi.sub_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        LinearEquiv.toLinearMap_eq_ofClass, map_sum, LinearMap.sum_apply, sum_apply,
        Finset.sum_sub_distrib, Fintype.sum_prod_type, zero_apply, Finset.sum_const_zero]
  refine ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, hDK, V, qsum, hV, hzV, hVU,
    hOne, hqsum, hrem, ?_⟩
  intro u y
  -- Integrable full Fourier actions commute with this finite sum, including its remainder.
  have hquant := hquant_sum (d := n + r) (ri := AT.rank D₀.frameIndex)
    (ro := AT'.rank K₀.frameIndex) q hq u y
  rw [hquant]
  simp_rw [hqaction, ← hQ]
  simp only [Fintype.sum_prod_type, LinearMap.sum_apply, map_sum, sum_apply]
  rfl

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The original horizontal sum has a complete symbol in the specified compatible chart. -/
theorem exists_horizontalCutoff_localSymbol
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
            ∀ g : Fin L.size → Fin J.size → atlasGlobalSymbolSpace AT AT' 1,
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
                else 0) →
              ∀ (c : OpenPartialHomeomorph Z XY)
                (_hc : c ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z)
                (e₀ : AT.Index) (f₀ : AT'.Index) (z : XY),
                z ∈ atlasSymbolChartDomain AT AT' c e₀ f₀ →
                ∃ (D₀ : AtlasChartCutoff AT c) (K₀ : AtlasChartCutoff AT' c),
                  ∃ (I₀ : AT'.smoothSections →ₗ[ℂ]
                      𝓢(XY, EuclideanSpace ℂ (Fin (AT'.rank K₀.frameIndex))))
                    (O₀ : 𝓢(XY, EuclideanSpace ℂ (Fin (AT.rank D₀.frameIndex)))
                      →ₗ[ℂ] AT.smoothSections),
                    (∀ v y, I₀ v y = K₀.localizedFunction v y) ∧
                    (∀ u x, (O₀ u).val x = D₀.extendedFunction u x) ∧
                    D₀.frameIndex = e₀ ∧ K₀.frameIndex = f₀ ∧
                    ∃ (V : Set XY)
                      (p : SymbolFunction (n + r) (AT.rank D₀.frameIndex)
                        (AT'.rank K₀.frameIndex)),
                      IsOpen V ∧ z ∈ V ∧
                      V ⊆ atlasSymbolChartDomain AT AT' c D₀.frameIndex K₀.frameIndex ∧
                      IsSymbol Set.univ 1 p ∧
                      IsSymbol V 0 (p - atlasGlobalSymbolInChart AT AT'
                        (∑ k, ∑ j, g k j).val c D₀.frameIndex K₀.frameIndex) ∧
                      ∀ (u : 𝓢(XY, EuclideanSpace ℂ (Fin (AT.rank D₀.frameIndex)))) y,
                        quantize p u y =
                          I₀ ((∑ k, ∑ j, (Q k j).toLinearMap) (O₀ u)) y := by
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
  intro Co hCo κ hκ hκK hκsupport hCoFrame hCoInput I O hI hO ε hε Q U hQ hU g hg
    c hc e₀ f₀ z hz
  obtain ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, _, V, p, hV, hzV, hVU, _,
      hp, hrem, haction⟩ :=
    exists_horizontalCutoff_localSymbol_with_plateaus S E A σ E' L hσ J
      Co hCo κ hκ hκK hκsupport hCoFrame hCoInput I O hI hO ε hε Q U hQ hU g hg
      c hc e₀ f₀ z hz
  exact ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, V, p, hV, hzV, hVU, hp, hrem, haction⟩

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
