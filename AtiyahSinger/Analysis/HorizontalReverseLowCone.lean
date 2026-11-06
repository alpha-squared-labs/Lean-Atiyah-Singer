/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalExtension
public import AtiyahSinger.Analysis.AtlasProductCutoffApproximation
public import AtiyahSinger.Analysis.LowConeVerticalEstimate
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff

import Mathlib.Algebra.Order.Chebyshev

/-!
# Actual fixed-parameter horizontal error in its original source charts

Public module ID: M0754.

The local horizontal lift minus its given positive regularization is bounded
by the right-coordinate energy. The proof keeps the specified input, output
and quantization maps, both cutoffs and the finite sphere partition. The
high-cone comparison and full reverse estimate are treated separately.
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
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
-- The same product charts and dependent tensor coordinate maps occur on both sides.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual fixed positive cutoff error is controlled by original source vertical energy. -/
theorem horizontal_reverse_low_cone_source_bound
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
      ∀ (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
          ∀ U : ∀ j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank (J.frameIndex j)))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
            (∀ j v z, U j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank (J.frameIndex j))
                (productCutoffSymbol α (κ j) ε x ξ)) v z) →
            ∀ w : AT.smoothSections,
              ‖Lo.smoothToSobolev 0
                (associatedSphereTensorLocalHorizontalLift (a := a)
                  S E A σ E' L hσ b χ hχ hχsupport houtput w -
                    ∑ j, O j (U j (I j w)))‖ ^ 2 ≤
                C * ∑ j : Fin J.size, (‖(I j w).toLp 2‖ ^ 2 +
                  ∑ l : Fin r, ‖(LineDeriv.lineDerivOp
                    (EuclideanSpace.single (Fin.natAdd n l) (1 : ℝ)) (I j w)).toLp 2‖ ^ 2) := by
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
  intro I O hI hO Lo ε hε
  change AtlasBundlePresentation AT' at Lo
  change ∀ j w z, I j w z = (Din j).localizedFunction w z at hI
  change ∀ j v z, (O j v).val z = (Dout j).extendedFunction v z at hO
  have hCP (j : Fin J.size) : CP j ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b L.chart L.chart_mem_atlas
      (J.chart j) (J.chart_mem_atlas j)
  -- Bound each source-chart extension uniformly over its Schwartz input.
  have hreturn (j : Fin J.size) : ∃ c : ℝ, 0 ≤ c ∧
      ∀ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))),
        ‖Lo.smoothToSobolev 0 (O j v)‖ ≤ c * ‖v.toLp 2‖ := by
    have hd : ∃ O₀ :
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank (J.frameIndex j)))) →ₗ[ℂ] AT'.smoothSections,
        (∀ v x, (O₀ v).val x = (Dout j).extendedFunction v x) ∧
          ∃ c : ℝ, 0 ≤ c ∧ ∀ v,
            ‖Lo.smoothToSobolev 0 (O₀ v)‖ ≤ c * ‖schwartzSobolevCoordinate 0 v‖ :=
      AtlasChartCutoff.exists_extend_sobolev_of_mem_maximalAtlas
        (n := n + r) (M := Z) (E := T') (A := AT') (c := CP j) (Dout j) (hCP j) Lo 0
    obtain ⟨O₀, hO₀, c, hc, hb⟩ := hd
    have heq : O j = O₀ := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext x
      exact (hO j v x).trans (hO₀ v x).symm
    subst O₀
    refine ⟨c, hc, ?_⟩
    intro v
    simpa only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply] using hb v
  choose cO hcO hOestimate using hreturn
  have hlow (j : Fin J.size) :=
    exists_productCutoffError_vertical_estimate (β j) (hβ j) (hβK j)
      (κ j) (hκ j) (hκK j) ε hε
  choose cE hcE hEestimate using hlow
  let coefficient (j : Fin J.size) : ℝ := cO j ^ 2 * cE j
  have hcoef (j : Fin J.size) : 0 ≤ coefficient j := mul_nonneg (sq_nonneg _) (hcE j)
  let total : ℝ := ∑ j, coefficient j
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun j _ ↦ hcoef j)
  refine ⟨J.size * total, mul_nonneg (Nat.cast_nonneg _) htotal, ?_⟩
  intro U hU w
  have hUβ (j : Fin J.size) (v) (z) :
      U j v z = quantize (productCutoffSymbol (β j) (κ j) ε) v z := by
    rw [hU]
    congr 2
    funext x ξ
    simp only [productCutoffSymbol, liftedProductSymbol, β, α, map_smul]
  -- The unregularized outputs reconstruct the same original local horizontal lift.
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
  let err (j : Fin J.size) := v j - U j (I j w)
  let energy (j : Fin J.size) : ℝ := ‖(I j w).toLp 2‖ ^ 2 +
    ∑ l : Fin r, ‖(LineDeriv.lineDerivOp
      (EuclideanSpace.single (Fin.natAdd n l) (1 : ℝ)) (I j w)).toLp 2‖ ^ 2
  have henergy (j : Fin J.size) : 0 ≤ energy j :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun l _ ↦ sq_nonneg _))
  have herrvalue (j : Fin J.size) (z : XY) :
      err j z = quantize (productCutoffErrorSymbol (β j) (κ j) ε) (I j w) z := by
    rw [quantize_productCutoffErrorSymbol (β j) (hβ j) (κ j) (hκ j) ε hε, hv, ← hUβ]
    rfl
  have herrbound (j : Fin J.size) :
      ‖Lo.smoothToSobolev 0 (O j (err j))‖ ^ 2 ≤ coefficient j * energy j := by
    have hlow := hEestimate j (I j w) (err j) (herrvalue j)
    have hret := hOestimate j (err j)
    have hsquare := pow_le_pow_left₀
      (norm_nonneg (Lo.smoothToSobolev 0 (O j (err j)))) hret 2
    have hscaled := mul_le_mul_of_nonneg_left hlow (sq_nonneg (cO j))
    rw [← mul_pow] at hscaled
    have hbound := hsquare.trans hscaled
    simpa only [coefficient, energy, mul_assoc] using hbound
  have herrsum : associatedSphereTensorLocalHorizontalLift (a := a)
      S E A σ E' L hσ b χ hχ hχsupport houtput w - ∑ j, O j (U j (I j w)) =
        ∑ j, O j (err j) := by
    rw [← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ ↦ (map_sub (O j) (v j) (U j (I j w))).symm)
  -- Finite norm comparison uses the original returned errors and no transition H1 estimate.
  have hmapped := congrArg (Lo.smoothToSobolev 0) herrsum
  have hmapSum := map_sum (Lo.smoothToSobolev 0) (fun j ↦ O j (err j)) Finset.univ
  have hmap := hmapped.trans hmapSum
  have hnorm := congrArg (fun v : Lo.SobolevSpace 0 ↦ ‖v‖ ^ 2) hmap
  have htriangle := norm_sum_le Finset.univ (fun j ↦ Lo.smoothToSobolev 0 (O j (err j)))
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (∑ j, Lo.smoothToSobolev 0 (O j (err j)))) htriangle 2
  have hcard := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun j : Fin J.size ↦ ‖Lo.smoothToSobolev 0 (O j (err j))‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hsumBound := hsquare.trans hcard
  have hcoef_le (j : Fin J.size) : coefficient j ≤ total :=
    Finset.single_le_sum (fun k _ ↦ hcoef k) (Finset.mem_univ j)
  have hsum₁ := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ herrbound j)
  have hsum₂ := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ mul_le_mul_of_nonneg_right (hcoef_le j) (henergy j))
  have hscaled := mul_le_mul_of_nonneg_left (hsum₁.trans hsum₂) (Nat.cast_nonneg J.size)
  have hresult := hsumBound.trans hscaled
  have hresult' := hnorm.trans_le hresult
  simpa only [← Finset.mul_sum, mul_assoc, energy] using hresult'

end AtiyahSinger
