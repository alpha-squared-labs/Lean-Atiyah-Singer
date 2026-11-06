/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductFiniteCotangentBounds
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalConicInverse
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalAxis
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalTransverseBound
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization
public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# The actual horizontal cutoff full symbol is invertible in a uniform cone

Public module ID: M0865.

The original compact supports give one common saturation cone for the actual
source-chart frequency cutoffs. On that cone the actual finite cutoff factor
is exactly its uncut factor, which has the original Hermitian inverse energy
bound. The cutoff parameter, cone and radius are chosen before every point
and covector, retaining inactive terms without demanding chart overlap.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable {V : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
  [TopologicalSpace (TotalSpace Unit V)]
  (A : SmoothComplexBundleAtlas (n := r) V)
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- The exact native axis and transverse energies are compared in their original metric fibers.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
/-- The actual horizontal cutoff factor has a uniform inverse energy bound in a high cone. -/
theorem exists_horizontalCutoffFullSymbol_conic_metric_inverse_bound
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic) (J : AtlasBundlePresentation A)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') E')
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (e₀ : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f₀ : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) E'))
    [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
    (K : Set H) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let Ci (i : Fin C.size) (j : Fin J.size) :=
      associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let x := fun z : H ↦ base (CP.symm z)
    (∀ z ∈ K, x z ∈ e₀.baseSet ∩ f₀.baseSet) →
    ∃ ε₀ δ R M : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < δ ∧ 0 < R ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K, ∀ (ξ : X) (η : Y), R ≤ ‖ξ‖ → ‖η‖ ≤ δ * ‖ξ‖ →
        let coefficient : ℝ := M / (1 + ‖ξ‖) ^ 2
        let z₀ := CP.symm z
        let Ξ := covectorFromChart CP z₀ (split.symm (ξ, η))
        let frequency (i : Fin C.size) (j : Fin J.size) :=
          split (covectorInChart (Ci i j) z₀ Ξ)
        let P := ∑ i, ∑ j,
          ((J.cutoff j (associatedSphereTrivialization S (C.center i) z₀).2 *
            productFrequencyCutoff ε ‖(frequency i j).1‖ ‖(frequency i j).2‖ : ℝ) : ℂ) •
            (C.piece i).globalSymbolFunction (x z)
              (covectorFromChart (C.piece i).chart (x z) (frequency i j).1)
        Function.Bijective P ∧ ∀ u : E (x z), (h.pairing (x z) u u).re ≤
          coefficient * (k.pairing (x z) (P u) (P u)).re :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro CP Ci base x hframe
  obtain ⟨δ₀, R, M, hδ₀, hR, hM, hinverse⟩ :=
    C.exists_horizontalFullSymbol_conic_metric_inverse_bound S E E' A hC J g h k
      b₀ c₀ hc₀ d₀ hd₀ e₀ f₀ K hK hKChart hframe
  -- The original common base cutoff and sphere partition supports give actual compact overlaps.
  let t (i : Fin C.size) := associatedSphereTrivialization S (C.center i)
  let baseSupport (i : Fin C.size) := (C.piece i).chart.symm ''
    (tsupport (C.piece i).output.cutoff ∩ tsupport (C.piece i).input.cutoff)
  have hbCompact (i : Fin C.size) : IsCompact (baseSupport i) :=
    ((C.piece i).output.compact_support.inter
      (C.piece i).input.compact_support).image_of_continuousOn
      ((C.piece i).chart.continuousOn_symm.mono (fun _ hz ↦
        ((C.piece i).output.support_subset hz.1).1))
  have hbChart (i : Fin C.size) (x : B) (hx : x ∈ baseSupport i) :
      x ∈ (C.piece i).chart.source ∧ x ∈ (C.piece i).input.frame.baseSet ∧
        x ∈ (C.piece i).output.frame.baseSet ∧ x ∈ (S.trivialization (C.center i)).baseSet := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(C.piece i).chart.map_target ((C.piece i).output.support_subset hy.1).1,
      ((C.piece i).input.support_subset hy.2).2,
      ((C.piece i).output.support_subset hy.1).2, C.piece_support i ⟨y, Or.inl hy.1, rfl⟩⟩
  have htBase (i : Fin C.size) : (t i).baseSet = (S.trivialization (C.center i)).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization (C.center i)) (S.equivariant (C.center i))).choose_spec.1
  let support (ij : Fin C.size × Fin J.size) :=
    (t ij.1).toOpenPartialHomeomorph.symm '' (baseSupport ij.1 ×ˢ tsupport (J.cutoff ij.2))
  have htTarget (ij : Fin C.size × Fin J.size) :
      baseSupport ij.1 ×ˢ tsupport (J.cutoff ij.2) ⊆ (t ij.1).target := by
    intro xy hxy
    exact (t ij.1).mem_target.mpr (htBase ij.1 ▸ (hbChart ij.1 xy.1 hxy.1).2.2.2)
  have hsCompact (ij : Fin C.size × Fin J.size) : IsCompact (support ij) :=
    ((hbCompact ij.1).prod (J.compact_support ij.2)).image_of_continuousOn
      ((t ij.1).toOpenPartialHomeomorph.continuousOn_symm.mono (htTarget ij))
  have hsChart (ij : Fin C.size × Fin J.size) : support ij ⊆ (Ci ij.1 ij.2).source := by
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    have ht := htTarget ij hxy
    have htvalue : (t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y)) = (x, y) :=
      (t ij.1).toOpenPartialHomeomorph.right_inv ht
    refine ⟨⟨(t ij.1).toOpenPartialHomeomorph.map_target ht, ?_, ?_⟩, Set.mem_univ _⟩
    · change ((t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y))).1 ∈
        (C.piece ij.1).chart.source
      rw [htvalue]
      exact (hbChart ij.1 x hxy.1).1
    · change ((t ij.1) ((t ij.1).toOpenPartialHomeomorph.symm (x, y))).2 ∈ (J.chart ij.2).source
      rw [htvalue]
      exact (J.support_subset ij.2 hxy.2).1
  let e := fun ij : Fin C.size × Fin J.size ↦ (Ci ij.1 ij.2).symm.trans CP
  let pr := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let qr := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
  let inx := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X Y)
  let iny := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ X Y)
  obtain ⟨D, hD, hbound⟩ := exists_associatedSphereProductChart_finite_cotangent_block_bounds S
    (fun ij : Fin C.size × Fin J.size ↦ C.center ij.1)
    (fun ij ↦ (C.piece ij.1).chart) (fun ij ↦ (C.piece ij.1).chart_mem_atlas)
    (fun ij ↦ J.chart ij.2) (fun ij ↦ J.chart_mem_atlas ij.2)
    b₀ c₀ hc₀ d₀ hd₀ support hsCompact hsChart K hK hKChart
  let Active := { iz : (Fin C.size × Fin J.size) × H //
    iz.2 ∈ K ∧ CP.symm iz.2 ∈ support iz.1 }
  let A₀ (iz : Active) :=
    (fderiv ℝ ((C.piece iz.val.1.1).chart.symm.trans c₀)
      (pr ((e iz.val.1).symm iz.val.2))).adjoint
  let B₀ (iz : Active) :=
    (qr.comp ((fderiv ℝ (e iz.val.1) ((e iz.val.1).symm iz.val.2)).comp inx)).adjoint
  let V₀ (iz : Active) :=
    (qr.comp ((fderiv ℝ (e iz.val.1) ((e iz.val.1).symm iz.val.2)).comp iny)).adjoint
  have hactive (iz : Active) :
      ‖A₀ iz‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖A₀ iz ξ‖) ∧ ‖B₀ iz‖ ≤ D ∧
        ‖V₀ iz‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖V₀ iz η‖ :=
    hbound iz.val.1 iz.val.2 iz.property.1 iz.property.2
  -- Saturation uses the same mixed cotangent block as the actual source covectors.
  obtain ⟨δ, ε₀, hδ, hδle, hε₀, hε₀one, hsat⟩ :=
    exists_productCutoffHomotopyWeight_eq_one_in_split_cones A₀ B₀ V₀ D δ₀ hD hδ₀
      (fun iz ↦ (hactive iz).1) (fun iz ↦ (hactive iz).2.1)
      (fun iz ↦ (hactive iz).2.2.1) (fun iz ↦ (hactive iz).2.2.2.1)
      (fun iz ↦ (hactive iz).2.2.2.2)
  refine ⟨ε₀, δ, R, M, hε₀, hε₀one, hδ, hR, hM, ?_⟩
  intro ε hε hεle z hz ξ η hξ hcone coefficient z₀ Ξ frequency P
  let U := ∑ i, ∑ j, (J.cutoff j (t i z₀).2 : ℂ) •
    (C.piece i).globalSymbolFunction (x z)
      (covectorFromChart (C.piece i).chart (x z) (frequency i j).1)
  have hsame : P = U := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hw : J.cutoff j (t i z₀).2 = 0
    · simp only [t] at hw ⊢
      simp only [hw, zero_mul, Complex.ofReal_zero, zero_smul]
    by_cases hx : base z₀ ∈ baseSupport i
    · have htz : z₀ ∈ (t i).source :=
        (t i).mem_source.mpr (htBase i ▸ (hbChart i (base z₀) hx).2.2.2)
      have hsupport : z₀ ∈ support (i, j) := by
        refine ⟨t i z₀, ⟨?_, subset_tsupport _ hw⟩,
          (t i).toOpenPartialHomeomorph.left_inv htz⟩
        rwa [(t i).coe_fst htz]
      let iz : Active := ⟨((i, j), z), hz, hsupport⟩
      have hcoord := covectorInChart_associatedSphereProductChart_split
        S (C.center i) b₀ (C.piece i).chart c₀ (C.piece i).chart_mem_atlas hc₀
          (J.chart j) d₀ (J.chart_mem_atlas j) hd₀ z ⟨hKChart hz, hsChart (i, j) hsupport⟩ ξ η
      have hfrequency : frequency i j = (A₀ iz ξ + B₀ iz η, V₀ iz η) := by
        change split (covectorInChart (Ci i j) z₀ Ξ) = _
        rw [hcoord, split.apply_symm_apply]
      have hone : productFrequencyCutoff ε ‖(frequency i j).1‖ ‖(frequency i j).2‖ = 1 := by
        rw [hfrequency]
        have hh := (hsat ε hε hεle (1 : unitInterval) iz ξ η).1 hcone
        simpa only [productCutoffHomotopyWeight, show ((1 : unitInterval) : ℝ) = 1 from rfl,
          one_smul, sub_self, zero_mul, one_mul, zero_add] using hh
      rw [hone, mul_one]
    · rw [(C.piece i).globalSymbolFunction_eq_zero (base z₀) hx]
      simp only [smul_zero]
  have hb := hinverse z hz ξ η hξ
    (hcone.trans (mul_le_mul_of_nonneg_right hδle (norm_nonneg ξ)))
  change Function.Bijective U ∧ ∀ u, (h.pairing (x z) u u).re ≤
    coefficient * (k.pairing (x z) (U u) (U u)).re at hb
  rwa [hsame]

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
