/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Analysis.CompactQuantization

/-!
# Fixed coordinate quantization on locally finite-rank bundle atlases

Public module ID: M0296.

A03: fix common coordinate charts, the original two bundle frames, a finite
output partition and input cutoffs equal to one near each output support.
These are geometric choices only. The local symbol is the original coordinate
symbol multiplied by the input cutoff and extended by zero; its exact Fourier
quantization is transported through those same localization and extension maps.
Their finite sum is the actual operator, linear in the original full symbol.

The transported leading symbol of each piece is output times input squared
times the original symbol. The plateau condition reduces it to the output
weight, and the partition recovers the original principal quotient class.
No symbol realization, continuity theorem or principal-class recovery is an
input field. The local source and target ranks remain independent.

Sources: SG III.3.15 and the coordinate assembly on pp.186--187; Definition
3.18 and Theorem 3.19 on pp.187--188. This is the fixed coordinate quantization
allowed by the selected A03 model. It is not the separate connection and
exponential-map formula (3.19)--(3.20). Parameter continuity is a subsequent
theorem about this same construction. The fixed presentation, local symbol
comparison and linear operator assembly retain the same full symbol.
Principal-class recovery uses the representation-independence theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- One common coordinate patch and its two fixed cutoff frame maps. -/
structure AtlasQuantizationPatch where
  /-- The original common manifold chart. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- This is a chart in the given smooth manifold atlas. -/
  chart_mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- The original input frame and its compact localization cutoff. -/
  input : AtlasChartCutoff A chart
  /-- The original output frame and its compact partition cutoff. -/
  output : AtlasChartCutoff B chart
  /-- The output partition weight is nonnegative in its coordinate domain. -/
  output_nonneg : ∀ x, 0 ≤ output.cutoff x
  /-- The input cutoff support lies in the original output frame domain. -/
  input_support_in_output_frame :
    tsupport input.cutoff ⊆ chart.symm ⁻¹' (B.chart output.frameIndex).baseSet
  /-- The output cutoff support lies in the original input frame domain. -/
  output_support_in_input_frame :
    tsupport output.cutoff ⊆ chart.symm ⁻¹' (A.chart input.frameIndex).baseSet
  /-- The input cutoff is one on an open neighborhood of the closed output support. -/
  input_eq_one : ∃ U : Set (EuclideanSpace ℝ (Fin n)),
    IsOpen U ∧ tsupport output.cutoff ⊆ U ∧ ∀ x ∈ U, input.cutoff x = 1

namespace AtlasQuantizationPatch

variable {A B} (R : AtlasQuantizationPatch A B)

/-- The actual output partition weight, extended by zero outside its manifold chart. -/
def weight (x : M) : ℝ := by
  classical
  exact if x ∈ R.chart.source then R.output.cutoff (R.chart x) else 0

/-- The actual input-cutoff coordinate symbol, extended by zero on the common domain boundary. -/
def localSymbol (p : AtlasSymbolFunction (n := n) E F) :
    SymbolFunction n (A.rank R.input.frameIndex) (B.rank R.output.frameIndex) :=
  zeroExtendedSymbol
    (atlasSymbolChartDomain A B R.chart R.input.frameIndex R.output.frameIndex)
    R.input.cutoff
    (atlasGlobalSymbolInChart A B p R.chart R.input.frameIndex R.output.frameIndex)

/-- The specified local symbol has compact spatial support and the same symbol order. -/
theorem localSymbol_properties {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    HasCompactSupport (R.localSymbol p.val) ∧
      IsSymbol Set.univ m (R.localSymbol p.val) := by
  /- Stage 1: both support-subordination conditions put the compact input
  support inside the common base-chart and two-frame domain. This domain
  is open, by continuity of the inverse chart on its open target.
  Stage 2: p's actual atlas estimates apply in that same domain. Apply
  isSymbol_zeroExtendedSymbol with the input cutoff and its support data.
  Its zero extension is smooth at the boundary because the support stays
  inside the open domain. The support inclusion in the compact input
  support gives the first conclusion. No global common rank is used. -/
  have hopen : IsOpen
      (atlasSymbolChartDomain A B R.chart R.input.frameIndex R.output.frameIndex) := by
    simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      R.chart.isOpen_inter_preimage_symm
        ((A.chart R.input.frameIndex).open_baseSet.inter
          (B.chart R.output.frameIndex).open_baseSet)
  have hs : tsupport R.input.cutoff ⊆
      atlasSymbolChartDomain A B R.chart R.input.frameIndex R.output.frameIndex := by
    intro z hz
    exact ⟨R.input.support_subset hz, R.input_support_in_output_frame hz⟩
  -- Both conclusions concern the input cutoff and the same two independent local ranks.
  exact ⟨hasCompactSupport_zeroExtendedSymbol _ R.input.cutoff _ R.input.compact_support,
    isSymbol_zeroExtendedSymbol _ hopen m R.input.cutoff R.input.smooth_cutoff
      R.input.compact_support hs _
      (p.property R.chart R.chart_mem_atlas R.input.frameIndex R.output.frameIndex)⟩

/-- The exact local Fourier piece, using the existing continuous Schwartz quantization. -/
def toPiece {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    AtlasPseudodifferentialPiece A B m where
  chart := R.chart
  chart_mem_atlas := R.chart_mem_atlas
  input := R.input
  output := R.output
  input_support_in_output_frame := R.input_support_in_output_frame
  output_support_in_input_frame := R.output_support_in_input_frame
  operator := quantizeSchwartz m (R.localSymbol p.val)
    (R.localSymbol_properties p).2 (R.localSymbol_properties p).1
  symbol := R.localSymbol p.val
  isSymbol := (R.localSymbol_properties p).2
  operator_apply := quantizeSchwartz_apply m (R.localSymbol p.val)
    (R.localSymbol_properties p).2 (R.localSymbol_properties p).1

end AtlasQuantizationPatch

/-- Fixed finite common coordinate data whose actual output weights form a partition of unity. -/
structure AtlasQuantizationPresentation where
  /-- The number of common coordinate patches. -/
  size : ℕ
  /-- The original frame and cutoff data of each local operator. -/
  patch : Fin size → AtlasQuantizationPatch A B
  /-- The displayed output weights sum to one at every original base point. -/
  sum_weight : ∀ x : M, ∑ j, (patch j).weight x = 1

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M]

variable {A B}

include hM hT in
set_option linter.unusedSectionVars false in
/-- The local piece transports to precisely the output weight times the original symbol. -/
theorem AtlasQuantizationPatch.globalSymbolFunction_toPiece
    (R : AtlasQuantizationPatch A B) {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    (R.toPiece p).globalSymbolFunction =
      fun x ξ ↦ (R.weight x : ℂ) • p.val x ξ := by
  /- Stage 1: on the common valid domain the original frame inverses and
  the two cotangent coordinate maps cancel. One input cutoff occurs in
  localSymbol and another in localization, while extension contributes
  the output cutoff. Thus the scalar is output times input squared.
  Stage 2: wherever the output is nonzero, its point lies in the closed
  output support, and input_eq_one makes both input factors one. Where
  output vanishes both sides are zero. The support conditions also make
  both sides vanish off the common chart/frame domain. This is an equality
  of original Hom-valued symbols before passage to the principal quotient. -/
  classical
  -- First cancel the two actual frame equivalences at an arbitrary inverse-chart point.
  have htransport (z : EuclideanSpace ℝ (Fin n)) (y : M) (hy : R.chart.symm z = y)
      (he : y ∈ (A.chart R.input.frameIndex).baseSet)
      (hf : y ∈ (B.chart R.output.frameIndex).baseSet)
      (η : EuclideanSpace ℝ (Fin n)) (v : E y) :
      (B.frameLinearEquiv R.output.frameIndex y hf).symm
          ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ)
            (atlasGlobalSymbolInChart A B p.val R.chart R.input.frameIndex
              R.output.frameIndex z η
                ((EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).symm
                  (A.frameLinearEquiv R.input.frameIndex y he v)))) =
        p.val y (covectorFromChart R.chart y η) v := by
    subst y
    dsimp only [atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨he, hf⟩]
    change (B.frameLinearEquiv R.output.frameIndex (R.chart.symm z) hf).symm
      ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ)
        ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ).symm
          (B.frameLinearEquiv R.output.frameIndex (R.chart.symm z) hf
            (p.val (R.chart.symm z) (covectorFromChart R.chart (R.chart.symm z) η)
              ((A.frameLinearEquiv R.input.frameIndex (R.chart.symm z) he).symm
                ((EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ)
                  ((EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).symm
                    (A.frameLinearEquiv R.input.frameIndex (R.chart.symm z) he v)))))))) = _
    rw [(EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).apply_symm_apply,
      (A.frameLinearEquiv R.input.frameIndex (R.chart.symm z) he).symm_apply_apply,
      (EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ).apply_symm_apply,
      (B.frameLinearEquiv R.output.frameIndex (R.chart.symm z) hf).symm_apply_apply]
  funext x ξ
  by_cases hx : x ∈ R.chart.source
  · by_cases hcut : R.output.cutoff (R.chart x) = 0
    · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, AtlasQuantizationPatch.toPiece,
        AtlasQuantizationPatch.weight, hx, hcut]
    · -- A nonzero output weight lies in both original frame domains and the input plateau.
      have hs : R.chart x ∈ tsupport R.output.cutoff := subset_tsupport _ hcut
      have he : x ∈ (A.chart R.input.frameIndex).baseSet := by
        have h := R.output_support_in_input_frame hs
        simpa only [Set.mem_preimage, R.chart.left_inv hx] using h
      have hf : x ∈ (B.chart R.output.frameIndex).baseSet := by
        have h := (R.output.support_subset hs).2
        simpa only [Set.mem_preimage, R.chart.left_inv hx] using h
      have hd : R.chart x ∈ atlasSymbolChartDomain A B R.chart
          R.input.frameIndex R.output.frameIndex := by
        exact ⟨⟨R.chart.map_source hx,
          by simpa only [Set.mem_preimage, R.chart.left_inv hx] using he⟩,
          by simpa only [Set.mem_preimage, R.chart.left_inv hx] using hf⟩
      obtain ⟨U, _, hsU, hU⟩ := R.input_eq_one
      have hin : R.input.cutoff (R.chart x) = 1 := hU _ (hsU hs)
      -- Both input factors become one, leaving exactly the original output partition weight.
      simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, AtlasQuantizationPatch.toPiece,
        AtlasQuantizationPatch.localSymbol, zeroExtendedSymbol, ite_eq_left hd,
        dite_eq_left (show x ∈ R.chart.source ∩ (A.chart R.input.frameIndex).baseSet ∩
          (B.chart R.output.frameIndex).baseSet from ⟨⟨hx, he⟩, hf⟩), hin, mul_one,
        Complex.ofReal_one, one_smul, AtlasQuantizationPatch.weight, ite_eq_left hx]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.smul_apply]
      congr 1
      change (B.frameLinearEquiv R.output.frameIndex x hf).symm
        ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ)
          (atlasGlobalSymbolInChart A B p.val R.chart R.input.frameIndex
            R.output.frameIndex (R.chart x) (covectorInChart R.chart x ξ)
              ((EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).symm
                (A.frameLinearEquiv R.input.frameIndex x he v)))) = p.val x ξ v
      simpa only [covectorFromChart_covectorInChart R.chart R.chart_mem_atlas x hx] using
        htransport (R.chart x) x (R.chart.left_inv hx) he hf (covectorInChart R.chart x ξ) v
  · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, AtlasQuantizationPatch.toPiece,
      AtlasQuantizationPatch.weight, hx]

variable (A B)

include hM hT in
/-- Compact smooth bases admit such fixed common data for two locally finite-rank atlases. -/
theorem nonempty_atlasQuantizationPresentation
    [SecondCountableTopology M] [CompactSpace M] :
    Nonempty (AtlasQuantizationPresentation A B) := by
  /- Stage 1: refine the original manifold charts by intersections with
  one covering frame from A and one from B. A finite smooth partition
  of unity with nonnegative compactly supported weights in these common
  regions gives the output weights; retain these actual weights on the base.
  Stage 2: in each coordinate domain choose a smooth compact input cutoff
  equal to one on an open neighborhood of the output support, with support
  still in the common domain. This supplies both cross-frame support
  conditions without comparing ranks on different components.
  Stage 3: index the finite family by Fin N. The partition identity is
  exactly sum_weight after coordinate zero extension. The empty base has
  the empty family; no base point or positive rank is selected. -/
  classical
  -- Choose one finite cover by the common source of the base chart and both frames.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  choose e he using A.covers
  choose f hf using B.covers
  let U (x : M) := ((c x).source ∩ (A.chart (e x)).baseSet) ∩ (B.chart (f x)).baseSet
  have hopen (x : M) : IsOpen (U x) :=
    ((c x).open_source.inter (A.chart (e x)).open_baseSet).inter (B.chart (f x)).open_baseSet
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, ⟨mem_chart_source _ x, he x⟩, hf x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (index j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
    (fun j ↦ hopen (index j)) hfinitecover
  -- Zero-extend each actual partition weight into its chosen Euclidean chart.
  let χ (j : Fin s.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let K (j : Fin s.card) := (c (index j)) '' tsupport (ρ j)
  have hK (j : Fin s.card) : IsCompact (K j) :=
    (HasCompactSupport.of_compactSpace (ρ j)).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ (hρ j hx).1.1))
  have hχ (j : Fin s.card) : tsupport (χ j) ⊆ K j := by
    apply closure_minimal ?_ (hK j).isClosed
    intro z hz
    have ht : z ∈ (c (index j)).target := by
      by_contra ht
      exact hz (by simp [χ, ht])
    have hr : (c (index j)).symm z ∈ tsupport (ρ j) := by
      by_contra hr
      exact hz (by simp [χ, ht, image_eq_zero_of_notMem_tsupport hr])
    exact ⟨(c (index j)).symm z, hr, (c (index j)).right_inv ht⟩
  have hχcompact (j : Fin s.card) : HasCompactSupport (χ j) :=
    (hK j).of_isClosed_subset (isClosed_tsupport _) (hχ j)
  have hχsmooth (j : Fin s.card) : ContDiff ℝ ∞ (χ j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K j
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (hρ j hx).1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ (index j : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · -- The compact coordinate support is closed, so the same extension is locally zero outside it.
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hK j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin s.card) :=
    atlasSymbolChartDomain A B (c (index j)) (e (index j)) (f (index j))
  have hD (j : Fin s.card) : IsOpen (D j) := by
    simpa only [D, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      (c (index j)).isOpen_inter_preimage_symm
        ((A.chart (e (index j))).open_baseSet.inter
          (B.chart (f (index j))).open_baseSet)
  have hKD (j : Fin s.card) : K j ⊆ D j := by
    rintro z ⟨x, hx, rfl⟩
    have hu := hρ j hx
    exact ⟨⟨(c (index j)).map_source hu.1.1,
      by simpa only [Set.mem_preimage, (c (index j)).left_inv hu.1.1] using hu.1.2⟩,
      by simpa only [Set.mem_preimage, (c (index j)).left_inv hu.1.1] using hu.2⟩
  -- Two nested compact neighborhoods give a plateau on an open set around the output support.
  have hinput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∃ W, IsOpen W ∧ tsupport (χ j) ⊆ W ∧
          ∀ z ∈ W, ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hD j) (hKD j)
    obtain ⟨V, hV, hWV, hVD, hVcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact (hD j) hWD
    obtain ⟨ψ, hψ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
    have hts : tsupport ψ = closure V := congrArg closure hsupp
    refine ⟨ψ, hψ, ?_, ?_, W, hW, (hχ j).trans hKW, ?_⟩
    · change IsCompact (tsupport ψ)
      rwa [hts]
    · rwa [hts]
    · intro z hz
      exact (hone z).mp (subset_closure hz)
  choose ψ hψsmooth hψcompact hψsupport hψone using hinput
  let patch (j : Fin s.card) : AtlasQuantizationPatch A B :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      input :=
        { frameIndex := e (index j)
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦ (hψsupport j hz).1 }
      output :=
        { frameIndex := f (index j)
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦ ⟨(hKD j (hχ j hz)).1.1, (hKD j (hχ j hz)).2⟩ }
      output_nonneg := by
        intro z
        dsimp only [χ]
        split_ifs
        · exact ρ.nonneg _ _
        · exact le_rfl
      input_support_in_output_frame := fun z hz ↦ (hψsupport j hz).2
      output_support_in_input_frame := fun z hz ↦ (hKD j (hχ j hz)).1.2
      input_eq_one := hψone j }
  refine ⟨{ size := s.card, patch := patch, sum_weight := ?_ }⟩
  intro x
  -- The specified output weights recover the original partition on every base point.
  have hweight (j : Fin s.card) : (patch j).weight x = ρ j x := by
    by_cases hx : x ∈ (c (index j)).source
    · simp only [AtlasQuantizationPatch.weight, patch, ite_eq_left hx, χ,
        ite_eq_left ((c (index j)).map_source hx), (c (index j)).left_inv hx]
    · have hzero : ρ j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ j h).1.1)
      simp only [AtlasQuantizationPatch.weight, patch, ite_eq_right hx, hzero]
  simp_rw [hweight]
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

namespace AtlasQuantizationPresentation

variable {A B} (R : AtlasQuantizationPresentation A B)

/-- The actual finite sum of localized Fourier operators on the original smooth sections. -/
def toLinearMap {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    A.smoothSections →ₗ[ℂ] B.smoothSections :=
  ∑ j, ((R.patch j).toPiece p).toLinearMap

include hM hT in
/-- With these geometric choices fixed, the original section action is linear in the full symbol. -/
theorem toLinearMap_linear (m : ℝ) :
    IsLinearMap ℂ (R.toLinearMap (m := m)) := by
  /- Stage 1: the original coordinate Hom maps, cutoff multiplication and
  zero extension preserve symbol sums and complex scalars exactly. The
  quantizeSchwartz additive and scalar identities identify the resulting
  continuous local operators by their actual Fourier integral actions.
  Stage 2: compose with the same input and output section maps and sum
  the same finite family. This gives linearity of actual smooth-section
  maps, including lower-order and smoothing terms, rather than linearity
  only in the principal quotient. No varying presentation is chosen. -/
  classical
  -- First retain linearity of every original coordinate symbol and its fixed zero extension.
  have hlocal (Q : AtlasQuantizationPatch A B) :
      IsLinearMap ℂ (Q.localSymbol : AtlasSymbolFunction (n := n) E F → _) := by
    constructor
    · intro p q
      funext x ξ
      apply ContinuousLinearMap.ext
      intro v
      by_cases hx : x ∈ atlasSymbolChartDomain A B Q.chart
        Q.input.frameIndex Q.output.frameIndex
      <;> by_cases hf : Q.chart.symm x ∈ (A.chart Q.input.frameIndex).baseSet ∧
        Q.chart.symm x ∈ (B.chart Q.output.frameIndex).baseSet
      <;> simp [AtlasQuantizationPatch.localSymbol, zeroExtendedSymbol, hx,
        atlasGlobalSymbolInChart, hf, smul_add]
    · intro z p
      funext x ξ
      apply ContinuousLinearMap.ext
      intro v
      by_cases hx : x ∈ atlasSymbolChartDomain A B Q.chart
        Q.input.frameIndex Q.output.frameIndex
      <;> by_cases hf : Q.chart.symm x ∈ (A.chart Q.input.frameIndex).baseSet ∧
        Q.chart.symm x ∈ (B.chart Q.output.frameIndex).baseSet
      <;> simp only [AtlasQuantizationPatch.localSymbol, zeroExtendedSymbol, hx,
        ↓reduceIte, atlasGlobalSymbolInChart, hf, and_self, ↓reduceDIte,
        ContinuousLinearEquiv.toLinearEquiv_symm, Pi.smul_apply, Complex.coe_smul,
        smul_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
        LinearEquiv.coe_coe, LinearMap.coe_smul, Function.comp_apply, LinearEquiv.trans_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv, map_smul,
        ContinuousLinearEquiv.coe_symm_toLinearEquiv, PiLp.continuousLinearEquiv_symm_apply,
        smul_zero, zero_apply]
      exact smul_comm _ _ _
  constructor
  · intro p q
    rw [toLinearMap, toLinearMap, toLinearMap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    let Q := R.patch j
    have hop : quantizeSchwartz m (Q.localSymbol (p + q).val)
        (Q.localSymbol_properties (p + q)).2 (Q.localSymbol_properties (p + q)).1 =
        quantizeSchwartz m (Q.localSymbol p.val)
          (Q.localSymbol_properties p).2 (Q.localSymbol_properties p).1 +
        quantizeSchwartz m (Q.localSymbol q.val)
          (Q.localSymbol_properties q).2 (Q.localSymbol_properties q).1 := by
      change quantizeSchwartz m (Q.localSymbol (p.val + q.val)) _ _ = _
      simp only [(hlocal Q).map_add p.val q.val]
      exact quantizeSchwartz_add m _ _ _ _ _ _ _ _
    -- Evaluate the same three maps, then distribute the fixed output extension.
    apply LinearMap.ext
    intro u
    have h := congrArg (fun T :
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Q.input.frameIndex)))
          →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n),
            EuclideanSpace ℂ (Fin (B.rank Q.output.frameIndex))) ↦
        Q.output.extend Q.chart_mem_atlas (T (Q.input.localize Q.chart_mem_atlas u))) hop
    exact h.trans ((Q.output.extendLinearMap Q.chart_mem_atlas).map_add _ _)
  · intro z p
    rw [toLinearMap, toLinearMap, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    let Q := R.patch j
    have hop : quantizeSchwartz m (Q.localSymbol (z • p).val)
        (Q.localSymbol_properties (z • p)).2 (Q.localSymbol_properties (z • p)).1 =
        z • quantizeSchwartz m (Q.localSymbol p.val)
          (Q.localSymbol_properties p).2 (Q.localSymbol_properties p).1 := by
      change quantizeSchwartz m (Q.localSymbol (z • p.val)) _ _ = _
      simp only [(hlocal Q).map_smul z p.val]
      exact quantizeSchwartz_smul m z _ _ _ _ _
    apply LinearMap.ext
    intro u
    have h := congrArg (fun T :
        𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Q.input.frameIndex)))
          →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n),
            EuclideanSpace ℂ (Fin (B.rank Q.output.frameIndex))) ↦
        Q.output.extend Q.chart_mem_atlas (T (Q.input.localize Q.chart_mem_atlas u))) hop
    exact h.trans ((Q.output.extendLinearMap Q.chart_mem_atlas).map_smul z _)

/-- The fixed full-symbol quantizer as a linear map into the original section operators. -/
def quantizationLinearMap (m : ℝ) : atlasGlobalSymbolSpace A B m →ₗ[ℂ]
    (A.smoothSections →ₗ[ℂ] B.smoothSections) :=
  IsLinearMap.mk' (R.toLinearMap (m := m)) (R.toLinearMap_linear m)

variable [SecondCountableTopology M] [CompactSpace M]

/-- The displayed finite sum is an atlas PDO, with exactly zero smoothing remainder. -/
theorem isAtlasPseudodifferentialOperator_toLinearMap
    {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    IsAtlasPseudodifferentialOperator A B m (R.toLinearMap p) := by
  /- Use the exact finite family j -> (R.patch j).toPiece p as the
  representation. Its difference from the defining sum is the zero
  smooth-section map. For every pair of actual Sobolev presentations and
  every pair of real orders, the zero continuous linear map extends that
  remainder. This supplies the existing all-order smoothing predicate. -/
  -- The actual defining family leaves exactly zero as the section-map remainder.
  refine ⟨R.size, fun j ↦ (R.patch j).toPiece p, ?_⟩
  change IsAtlasSmoothingOperator A B (R.toLinearMap p - R.toLinearMap p)
  rw [sub_self]
  -- The zero bounded map realizes that same remainder at every pair of orders.
  intro L K s t
  refine ⟨0, ?_⟩
  intro u
  simp

/-- The actual fixed-presentation coordinate quantization, retaining its exact section action. -/
def quantize {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    AtlasPseudodifferentialOperator A B m where
  toLinearMap := R.toLinearMap p
  isPseudodifferentialOperator := R.isAtlasPseudodifferentialOperator_toLinearMap p

/-- The principal class of this same quantized operator is the original symbol quotient. -/
theorem principalSymbol_quantize {m : ℝ} (p : atlasGlobalSymbolSpace A B m) :
    (R.quantize p).principalSymbol = atlasGlobalPrincipalSymbolClass A B m p := by
  /- Stage 1: apply principalSymbol_eq_of_representation to the actual
  pieces used in quantize and their zero remainder. Each piece's transported
  symbol is exactly its output weight times the original p, by the previous
  chart and cutoff calculation on the same input/output fiber maps.
  Stage 2: sum these symbols and apply R.sum_weight. This gives the exact
  original p as the leading-symbol sum, hence its specified quotient class.
  Full reduced local symbols can contain lower-order cutoff corrections;
  no equality of a full reduced symbol with p is asserted. -/
  classical
  -- This same defining finite family has the zero remainder at every Sobolev order.
  have hrem : IsAtlasSmoothingOperator A B
      ((R.quantize p).toLinearMap - ∑ j, ((R.patch j).toPiece p).toLinearMap) := by
    change IsAtlasSmoothingOperator A B (R.toLinearMap p - R.toLinearMap p)
    rw [sub_self]
    intro L K s t
    refine ⟨0, fun u ↦ ?_⟩
    simp
  -- The original output partition sums the actual transported symbols to p itself.
  have hsum : (∑ j, ((R.patch j).toPiece p).globalSymbol) = p := by
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    change (∑ j, ((R.patch j).toPiece p).globalSymbolFunction) = p.val
    funext x ξ
    simp only [Finset.sum_apply, AtlasQuantizationPatch.globalSymbolFunction_toPiece]
    rw [← Finset.sum_smul]
    have hweight : (∑ j, ((R.patch j).weight x : ℂ)) = 1 := by
      exact_mod_cast R.sum_weight x
    rw [hweight, one_smul]
  rw [(R.quantize p).principalSymbol_eq_of_representation
    R.size (fun j ↦ (R.patch j).toPiece p) hrem, hsum]

end AtlasQuantizationPresentation

end AtiyahSinger
