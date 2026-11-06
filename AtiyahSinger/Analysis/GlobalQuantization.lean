/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol

/-!
# Global quantization from a fixed finite presentation

Public module ID: M0675.

Implement the partition-of-unity construction discussed on SG p.187.
The chosen data consist only of actual charts, two bundle frames and compact
cutoffs; no symbol realization or analytic theorem is a structure field.
A cutoff coordinate symbol is quantized by its exact continuous Schwartz map,
then localized and extended using the existing section maps. The global principal
class recovers the input symbol. This choice-dependent construction does not claim
to implement SG's separate connection/exponential-map quantization (3.19)-(3.20).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Auxiliary common chart and cutoff data for quantizing between two bundles. -/
structure QuantizationPatch where
  /-- A common real coordinate chart for both bundles. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- The chart belongs to the given smooth atlas. -/
  chart_mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- Input frame and compact localization cutoff. -/
  input : BundleChartCutoff (r := r) E chart
  /-- Output frame and compact extension cutoff. -/
  output : BundleChartCutoff (r := q) F chart
  /-- The input support lies within the output frame. -/
  input_support_in_output_frame : tsupport input.cutoff ⊆ chart.symm ⁻¹' output.frame.baseSet
  /-- The output support lies within the input frame. -/
  output_support_in_input_frame : tsupport output.cutoff ⊆ chart.symm ⁻¹' input.frame.baseSet
  /-- The output cutoff equals one on the entire closed input support. -/
  output_eq_one : ∀ z ∈ tsupport input.cutoff, output.cutoff z = 1

namespace QuantizationPatch

variable {E F} (A : QuantizationPatch (n := n) (r := r) (q := q) E F)

/-- The input cutoff weight on the manifold, explicitly zero outside the chart. -/
def weight (x : M) : ℝ := by
  classical
  exact if x ∈ A.chart.source then A.input.cutoff (A.chart x) else 0

set_option linter.unusedSectionVars false in
/-- The output cutoff is supported inside the full common coordinate/frame domain. -/
theorem output_support_subset_domain :
    tsupport A.output.cutoff ⊆
      symbolChartDomain E F A.chart A.input.frame A.output.frame := by
  /- Combine output.support_subset with output_support_in_input_frame. The three
  resulting conditions are exactly membership in the common coordinate domain.
  This support condition is needed before extending a coordinate symbol by zero. -/
  intro z hz
  exact ⟨⟨(A.output.support_subset hz).1, A.output_support_in_input_frame hz⟩,
    (A.output.support_subset hz).2⟩

/-- The output-cutoff coordinate expression, extended by zero across chart boundaries. -/
def localSymbol (p : GlobalSymbolFunction (n := n) E F) : SymbolFunction n r q := by
  letI := A.input.frame_mem_atlas
  letI := A.output.frame_mem_atlas
  exact zeroExtendedSymbol
    (symbolChartDomain E F A.chart A.input.frame A.output.frame) A.output.cutoff
    (globalSymbolInChart E F p A.chart A.input.frame A.output.frame)

/-- The local symbol has compact spatial support, regardless of its input symbol's regularity. -/
theorem hasCompactSupport_localSymbol (p : GlobalSymbolFunction (n := n) E F) :
    HasCompactSupport (A.localSymbol p) := by
  /- Apply hasCompactSupport_zeroExtendedSymbol using the output cutoff's compact
  support. The support is in the spatial variable; frequency remains unrestricted. -/
  exact hasCompactSupport_zeroExtendedSymbol _ A.output.cutoff _ A.output.compact_support

/-- An order-m global symbol gives an order-m compact local symbol. -/
theorem isSymbol_localSymbol {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    IsSymbol Set.univ m (A.localSymbol p.val) := by
  /- The defining global estimates apply in A's chart and both atlas frames.
  The common coordinate domain is open. Use output_support_subset_domain,
  output.smooth_cutoff and compact_support in isSymbol_zeroExtendedSymbol.
  No coefficient or frame map is assumed smooth outside that domain. -/
  let := A.input.frame_mem_atlas
  let := A.output.frame_mem_atlas
  -- The estimates use precisely the frames and output cutoff in this original patch.
  exact isSymbol_zeroExtendedSymbol _ (isOpen_symbolChartDomain E F
    A.chart A.input.frame A.output.frame) m A.output.cutoff A.output.smooth_cutoff
    A.output.compact_support A.output_support_subset_domain _
    (p.property A.chart A.chart_mem_atlas A.input.frame A.output.frame)

/-- A concrete local PDO piece obtained from the exact compact-symbol Schwartz quantization. -/
def toPiece {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    PseudodifferentialPiece (n := n) (r := r) (q := q) E F m where
  chart := A.chart
  chart_mem_atlas := A.chart_mem_atlas
  input := A.input
  output := A.output
  input_support_in_output_frame := A.input_support_in_output_frame
  output_support_in_input_frame := A.output_support_in_input_frame
  operator := quantizeSchwartz m (A.localSymbol p.val) (A.isSymbol_localSymbol p)
    (A.hasCompactSupport_localSymbol p.val)
  symbol := A.localSymbol p.val
  isSymbol := A.isSymbol_localSymbol p
  operator_apply := quantizeSchwartz_apply m (A.localSymbol p.val) (A.isSymbol_localSymbol p)
    (A.hasCompactSupport_localSymbol p.val)

end QuantizationPatch

/-- Auxiliary finite common presentation whose input weights sum to one everywhere. -/
structure QuantizationPresentation where
  /-- The finite number of local quantization patches. -/
  size : ℕ
  /-- Common chart/frame/cutoff data for each summand. -/
  patch : Fin size → QuantizationPatch (n := n) (r := r) (q := q) E F
  /-- The actual manifold input weights sum to one everywhere. -/
  sum_weight : ∀ x, ∑ j, (patch j).weight x = 1

variable {E F}
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hS : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hS hE hF in
set_option linter.unusedSectionVars false in
/-- A closed base admits common finite quantization data for two possibly different ranks. -/
theorem nonempty_quantizationPresentation [CompactSpace M] :
    Nonempty (QuantizationPresentation (n := n) (r := r) (q := q) E F) := by
  /- Stage 1: cover M by common intersections of a base chart and two bundle
  frames. Choose a finite compactly supported smooth partition subordinate to
  this cover, retaining its weights summing to one.
  Stage 2: transfer the weights to coordinate space and extend by zero. Choose
  smooth output cutoffs equal to one near each compact input support, with compact
  support inside the same common domain. Both cross-frame support conditions hold.
  Reindex the finite family by Fin N. The empty base admits the empty family. -/
  classical
  -- Choose one finite cover by the common source of the base chart and both frames.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  let U (x : M) := ((c x).source ∩ (e x).baseSet) ∩ (f x).baseSet
  have hopen (x : M) : IsOpen (U x) :=
    ((c x).open_source.inter (e x).open_baseSet).inter (f x).open_baseSet
  have hcover : Set.univ ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, ⟨mem_chart_source _ x,
      mem_baseSet_trivializationAt _ _ x⟩, mem_baseSet_trivializationAt _ _ x⟩
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
    symbolChartDomain E F (c (index j)) (e (index j)) (f (index j))
  have hD (j : Fin s.card) : IsOpen (D j) :=
    isOpen_symbolChartDomain E F (c (index j)) (e (index j)) (f (index j))
  have hKD (j : Fin s.card) : K j ⊆ D j := by
    rintro z ⟨x, hx, rfl⟩
    have hu := hρ j hx
    exact ⟨⟨(c (index j)).map_source hu.1.1,
      by simpa only [Set.mem_preimage, (c (index j)).left_inv hu.1.1] using hu.1.2⟩,
      by simpa only [Set.mem_preimage, (c (index j)).left_inv hu.1.1] using hu.2⟩
  -- A relatively compact intermediate open set supplies the output cutoff without changing χ.
  have houtput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∀ z ∈ tsupport (χ j), ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hD j) (hKD j)
    obtain ⟨ψ, hψ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW (hK j).isClosed hKW
    have hts : tsupport ψ = closure W := congrArg closure hsupp
    refine ⟨ψ, hψ, ?_, ?_, ?_⟩
    · change IsCompact (tsupport ψ)
      rwa [hts]
    · rwa [hts]
    · intro z hz
      exact (hone z).mp (hχ j hz)
  choose ψ hψsmooth hψcompact hψsupport hψone using houtput
  let patch (j : Fin s.card) : QuantizationPatch (n := n) (r := r) (q := q) E F :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      input :=
        { frame := e (index j)
          frame_mem_atlas := inferInstance
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦ (hKD j (hχ j hz)).1 }
      output :=
        { frame := f (index j)
          frame_mem_atlas := inferInstance
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦ ⟨(hψsupport j hz).1.1, (hψsupport j hz).2⟩ }
      input_support_in_output_frame := fun z hz ↦ (hKD j (hχ j hz)).2
      output_support_in_input_frame := fun z hz ↦ (hψsupport j hz).1.2
      output_eq_one := hψone j }
  refine ⟨{ size := s.card, patch := patch, sum_weight := ?_ }⟩
  intro x
  -- Each original manifold weight is recovered exactly, including the zero branch off its chart.
  have hweight (j : Fin s.card) : (patch j).weight x = ρ j x := by
    by_cases hx : x ∈ (c (index j)).source
    · simp only [QuantizationPatch.weight, patch, ite_eq_left hx, χ,
        ite_eq_left ((c (index j)).map_source hx), (c (index j)).left_inv hx]
    · have hzero : ρ j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ j h).1.1)
      simp only [QuantizationPatch.weight, patch, ite_eq_right hx, hzero]
  simp_rw [hweight]
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)


set_option linter.unusedSectionVars false in
/-- The piece's global symbol is exactly the input weight times the original symbol. -/
theorem QuantizationPatch.globalSymbolFunction_toPiece
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F) {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (A.toPiece p).globalSymbolFunction = fun x ξ ↦ (A.weight x : ℂ) • p.val x ξ := by
  /- Stage 1: in the common valid domain, the fiber maps and coordinate covectors
  cancel their inverses. The three cutoff factors are output^2 * input, since
  localSymbol already contains one output cutoff. Stage 2: if the input cutoff
  is nonzero, output_eq_one makes both output factors one. Otherwise both sides
  vanish. Outside the chart or either frame, support subordination gives the same
  zero identity. The result is an equality of actual symbols before quotienting. -/
  classical
  let := A.input.frame_mem_atlas
  let := A.output.frame_mem_atlas
  funext x ξ
  by_cases hx : x ∈ A.chart.source
  · by_cases hcut : A.input.cutoff (A.chart x) = 0
    · simp [PseudodifferentialPiece.globalSymbolFunction, QuantizationPatch.toPiece,
        QuantizationPatch.weight, hx, hcut]
    · -- Nonzero input weight places the point in both original frames.
      have hsupport : A.chart x ∈ tsupport A.input.cutoff := subset_tsupport _ hcut
      have he : x ∈ A.input.frame.baseSet := by
        have h := (A.input.support_subset hsupport).2
        simpa only [Set.mem_preimage, A.chart.left_inv hx] using h
      have hf : x ∈ A.output.frame.baseSet := by
        have h := A.input_support_in_output_frame hsupport
        simpa only [Set.mem_preimage, A.chart.left_inv hx] using h
      have hdomain : A.chart x ∈
          symbolChartDomain E F A.chart A.input.frame A.output.frame := by
        exact ⟨⟨A.chart.map_source hx,
          by simpa only [Set.mem_preimage, A.chart.left_inv hx] using he⟩,
          by simpa only [Set.mem_preimage, A.chart.left_inv hx] using hf⟩
      have hout : A.output.cutoff (A.chart x) = 1 := A.output_eq_one _ hsupport
      -- The two output weights are one on this same input support; cancel the actual frames.
      simp only [PseudodifferentialPiece.globalSymbolFunction, QuantizationPatch.toPiece,
        QuantizationPatch.localSymbol, zeroExtendedSymbol, ite_eq_left hdomain,
        ite_eq_left (show x ∈ A.chart.source ∩ A.input.frame.baseSet ∩
          A.output.frame.baseSet from ⟨⟨hx, he⟩, hf⟩), hout, one_mul,
        Complex.ofReal_one, one_smul, QuantizationPatch.weight, ite_eq_left hx]
      rw [globalSymbolInChart_covectorInChart E F p.val A.chart A.chart_mem_atlas
        A.input.frame A.output.frame x hx ξ]
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, smul_apply]
      rw [A.input.frame.symmL_continuousLinearMapAt he,
        A.output.frame.symmL_continuousLinearMapAt hf]
  · simp [PseudodifferentialPiece.globalSymbolFunction, QuantizationPatch.toPiece,
      QuantizationPatch.weight, hx]

namespace QuantizationPresentation

variable (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) {m : ℝ}

/-- The finite sum of actual local section operators for the given global symbol. -/
def toLinearMap (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F :=
  ∑ j, ((A.patch j).toPiece p).toLinearMap

set_option linter.unusedSectionVars false in
/-- With the presentation fixed, quantization preserves addition of symbols exactly. -/
theorem toLinearMap_add (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    A.toLinearMap (p + p') = A.toLinearMap p + A.toLinearMap p' := by
  /- Zero extension and coordinate transport preserve sums. Apply the exact
  additive quantizeSchwartz formula in each patch, then compose with the same
  restriction and extension maps and distribute the finite sum. No modulo term occurs. -/
  classical
  -- Zero extension is additive with the same common domain and output weight.
  have hlocal (Q : QuantizationPatch (n := n) (r := r) (q := q) E F) :
      Q.localSymbol (p + p').val = Q.localSymbol p.val + Q.localSymbol p'.val := by
    let := Q.input.frame_mem_atlas
    let := Q.output.frame_mem_atlas
    funext x ξ
    simp only [Pi.add_apply, QuantizationPatch.localSymbol, zeroExtendedSymbol,
      Submodule.coe_add, globalSymbolInChart_add]
    split_ifs <;> simp [smul_add]
  rw [toLinearMap, toLinearMap, toLinearMap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let Q := A.patch j
  have hop : (Q.toPiece (p + p')).operator =
      (Q.toPiece p).operator + (Q.toPiece p').operator := by
    change quantizeSchwartz m (Q.localSymbol (p + p').val)
      (Q.isSymbol_localSymbol (p + p')) (Q.hasCompactSupport_localSymbol (p + p').val) = _
    simp only [hlocal Q]
    exact quantizeSchwartz_add m (Q.localSymbol p.val) (Q.localSymbol p'.val)
      (Q.isSymbol_localSymbol p) (Q.isSymbol_localSymbol p')
      (Q.hasCompactSupport_localSymbol p.val) (Q.hasCompactSupport_localSymbol p'.val) _ _
  -- Compose these exact Schwartz maps with the unchanged localization and extension maps.
  change (Q.output.extendLinearMap Q.chart_mem_atlas).comp
      ((Q.toPiece (p + p')).operator.toLinearMap.comp
        (Q.input.localizeLinearMap Q.chart_mem_atlas)) = _
  rw [hop]
  simp only [ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp, LinearMap.comp_add]
  rfl

set_option linter.unusedSectionVars false in
/-- With the presentation fixed, quantization preserves complex scalars exactly. -/
theorem toLinearMap_smul (a : ℂ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    A.toLinearMap (a • p) = a • A.toLinearMap p := by
  /- Coordinate transport, the real cutoff multipliers and Schwartz quantization
  are complex-linear in p. Pass the scalar through restriction, extension and sum.
  Fixing the same presentation is essential for this equality of actual maps. -/
  classical
  -- The coordinate frames and fixed zero extension preserve the original complex scalar.
  have hlocal (Q : QuantizationPatch (n := n) (r := r) (q := q) E F) :
      Q.localSymbol (a • p).val = a • Q.localSymbol p.val := by
    let := Q.input.frame_mem_atlas
    let := Q.output.frame_mem_atlas
    funext x ξ
    simp only [Pi.smul_apply, QuantizationPatch.localSymbol, zeroExtendedSymbol,
      Submodule.coe_smul, globalSymbolInChart_smul]
    split_ifs
    · exact smul_comm _ _ _
    · simp
  rw [toLinearMap, toLinearMap, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let Q := A.patch j
  have hop : (Q.toPiece (a • p)).operator = a • (Q.toPiece p).operator := by
    change quantizeSchwartz m (Q.localSymbol (a • p).val)
      (Q.isSymbol_localSymbol (a • p)) (Q.hasCompactSupport_localSymbol (a • p).val) = _
    simp only [hlocal Q]
    exact quantizeSchwartz_smul m a (Q.localSymbol p.val) (Q.isSymbol_localSymbol p)
      (Q.hasCompactSupport_localSymbol p.val) _ _
  -- Pass the same scalar through the two fixed section maps and the finite sum.
  change (Q.output.extendLinearMap Q.chart_mem_atlas).comp
      ((Q.toPiece (a • p)).operator.toLinearMap.comp
        (Q.input.localizeLinearMap Q.chart_mem_atlas)) = _
  rw [hop]
  simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp, LinearMap.comp_smul]
  rfl

/-- The chosen quantization as a linear map into actual operators on smooth sections. -/
def quantizationLinearMap : globalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
    (smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) where
  toFun := A.toLinearMap
  map_add' := A.toLinearMap_add
  map_smul' := A.toLinearMap_smul

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- The finite quantization sum is a PDO with zero smoothing remainder. -/
theorem isPseudodifferentialOperator_toLinearMap
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    IsPseudodifferentialOperator E F μ m (A.toLinearMap p) := by
  /- Use the very family j ↦ (A.patch j).toPiece p in the defining finite
  representation. The remainder is zero, represented by the zero smooth kernel.
  Every local piece uses the exact quantization and valid compact cutoff data. -/
  classical
  -- Retain the very local family in the definition, so its remainder is identically zero.
  refine ⟨A.size, fun j ↦ (A.patch j).toPiece p, ?_⟩
  change IsSmoothingOperator μ (A.toLinearMap p - A.toLinearMap p)
  rw [sub_self]
  let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun _ _ ↦ 0
      isSmooth := by
        intro e f _ _
        change ContMDiffOn _ _ ∞ (fun z : M × M ↦
          kernelInFrames E F (fun _ _ ↦ 0) e f z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
  refine ⟨K, ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  change (∫ y, (0 : E y →L[ℂ] F x) (u.val y) ∂μ) = 0
  simp

/-- The fixed-presentation global quantization, bundled with its proved-to-be PDO property. -/
def quantize (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m where
  toLinearMap := A.toLinearMap p
  isPseudodifferentialOperator := A.isPseudodifferentialOperator_toLinearMap μ p

/-- Global quantization recovers the original symbol's class modulo one lower order. -/
theorem principalSymbol_quantize
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (A.quantize μ p).principalSymbol = globalPrincipalSymbolClass E F m p := by
  /- Stage 1: the defining finite family has zero remainder, so use the existing
  principalSymbol_eq_of_representation. Stage 2: each piece's globalSymbolFunction
  equals weight_j * p exactly. The sum_weight identity identifies their sum with p.
  Apply the quotient projection. Full local symbols still contain cutoff derivative
  corrections; this theorem identifies principal classes of the actual operators. -/
  classical
  -- The defining local family is an exact representation, with the zero smooth kernel.
  have hrem : IsSmoothingOperator μ
      ((A.quantize μ p).toLinearMap - ∑ j, ((A.patch j).toPiece p).toLinearMap) := by
    change IsSmoothingOperator μ (A.toLinearMap p - A.toLinearMap p)
    rw [sub_self]
    let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E F (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  -- The original weights recover the same supplied global symbol before quotienting.
  have hsum : (∑ j, ((A.patch j).toPiece p).globalSymbol) = p := by
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    change (∑ j, ((A.patch j).toPiece p).globalSymbolFunction) = p.val
    funext x ξ
    simp only [Finset.sum_apply, QuantizationPatch.globalSymbolFunction_toPiece]
    rw [← Finset.sum_smul]
    have hweight : (∑ j, ((A.patch j).weight x : ℂ)) = 1 := by
      exact_mod_cast A.sum_weight x
    rw [hweight, one_smul]
  rw [(A.quantize μ p).principalSymbol_eq_of_representation
    A.size (fun j ↦ (A.patch j).toPiece p) hrem, hsum]

end QuantizationPresentation

/-- Every global principal class is the principal symbol of some actual global PDO. -/
theorem PseudodifferentialOperator.principalSymbol_surjective
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] (m : ℝ) :
    Function.Surjective
      (PseudodifferentialOperator.principalSymbol (n := n) (r := r) (q := q)
        (E := E) (F := F) (μ := μ) (m := m)) := by
  /- Choose a genuine global symbol representative of the given quotient element
  by globalPrincipalSymbolClass_surjective. Choose a finite quantization presentation
  on the closed base and apply principalSymbol_quantize to that representative.
  This proves existence; it does not choose a canonical inverse on the quotient. -/
  intro σ
  obtain ⟨p, hp⟩ := globalPrincipalSymbolClass_surjective E F m σ
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q) (E := E) (F := F)
  refine ⟨A.quantize μ p, ?_⟩
  exact (A.principalSymbol_quantize μ p).trans hp

end AtiyahSinger
