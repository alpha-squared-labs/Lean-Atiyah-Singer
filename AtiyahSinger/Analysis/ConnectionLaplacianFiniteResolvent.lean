/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFiniteParametrix
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.JointFrequencyQuantizationBound

/-!
# Fixed patches for the finite connection-Laplacian resolvent

Public module ID: M0382.

The patches retain the original coordinate expressions of the specified connection
Laplacian. Their symbols, first inverse, cutoffs and frames are chosen once, before
both the positive parameter and finite expansion length. The first term and its
high-frequency inverse identity remain available for subsequent integration.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

/-- The dummy-base cutoff is one near zero; the horizontal weight is unchanged. -/
def finiteResolventSourceSymbol {n r : ℕ}
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) : SymbolFunction (n + 1) r r :=
  fun z _ ↦
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
      ⟨1, 2, by norm_num, by norm_num⟩
    ((χ (split z).1 * ρ (split z).2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- A fixed supported finite-parametrix patch for the actual differential operator.
The same cutoff is used on input and output, and is one near the partition support. -/
structure FiniteResolventPatch
    (L : DifferentialOperator (n := n) (r := r) (q := r) E E 2) where
  /-- The original smooth coordinate chart. -/
  chart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  /-- Membership in the original smooth atlas. -/
  chart_mem_atlas : chart ∈ atlas (EuclideanSpace ℝ (Fin n)) M
  /-- A single specified frame and plateau for input and output. -/
  cutoff : BundleChartCutoff (r := r) E chart
  /-- Open domain on which the recorded differential expression is valid. -/
  domain : Set M
  /-- Openness is used for actual derivative germs. -/
  isOpen_domain : IsOpen domain
  /-- The specified coordinate expression, including all lower-order coefficients. -/
  coordinate : CoordinateDifferentialOperator n r r 2 (chart '' domain)
  /-- This expression acts on the same global operator and the same frame on both sides. -/
  hasCoordinateExpression :
    HasCoordinateExpression E E 2 L.toLinearMap chart cutoff.frame cutoff.frame domain coordinate
  /-- The plateau is supported strictly inside the expression domain. -/
  support_cutoff : tsupport cutoff.cutoff ⊆ chart '' domain
  /-- The original global partition weight. -/
  weight : M → ℝ
  /-- Its compact coordinate transfer. -/
  coordinateWeight : EuclideanSpace ℝ (Fin n) → ℝ
  /-- The transferred weight is smooth across the coordinate boundary. -/
  smooth_coordinateWeight : ContDiff ℝ ∞ coordinateWeight
  /-- Compactness of the transferred partition support. -/
  compact_coordinateWeight : HasCompactSupport coordinateWeight
  /-- The transferred partition is supported in the original expression domain. -/
  support_coordinateWeight : tsupport coordinateWeight ⊆ chart '' domain
  /-- The same original weight is recovered on the chart source. -/
  coordinateWeight_apply : ∀ x ∈ chart.source, coordinateWeight (chart x) = weight x
  /-- Global weights vanish off their specified domain. -/
  weight_eq_zero : ∀ x ∉ domain, weight x = 0
  /-- The fixed input and output cutoff preserves the partition support as a germ. -/
  cutoff_eq_one : ∃ O, IsOpen O ∧ tsupport coordinateWeight ⊆ O ∧
    ∀ z ∈ O, cutoff.cutoff z = 1
  /-- The fixed joint source is an order-zero symbol. -/
  isSymbol_source : IsSymbol
    ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
        (chart '' domain)) 0 (finiteResolventSourceSymbol (r := r) coordinateWeight)
  /-- The original high-frequency first inverse. -/
  firstInverse : SymbolFunction (n + 1) r r
  /-- The fixed recursive sequence; it is not reselected after choosing a parameter. -/
  symbol : ℕ → SymbolFunction (n + 1) r r
  /-- The first inverse lies in the joint symbol class of order -2. -/
  isSymbol_firstInverse : IsSymbol
    ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
        (chart '' domain)) (-2) firstInverse
  /-- Each recursive term lies in the prescribed decreasing joint symbol class. -/
  isSymbol_symbol : ∀ j : ℕ, IsSymbol
    ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
        (chart '' domain)) (-2 - (j : ℝ)) (symbol j)
  /-- Recursion retains the support of the fixed joint right-hand side. -/
  support_symbol : ∀ j : ℕ, tsupport (symbol j) ⊆
    tsupport (finiteResolventSourceSymbol (r := r) coordinateWeight)
  /-- The first inverse is exact at high joint frequency, on every compact base set. -/
  firstInverse_eq :
    ∀ K : Set (EuclideanSpace ℝ (Fin (n + 1))),
      K ⊆ ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
          (chart '' domain)) → IsCompact K →
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ ζ, R ≤ ‖ζ‖ →
        firstInverse z ζ = (coordinate.parameterLift.principalSymbol z ζ).inverse
  /-- The same first inverse multiplies the specified partition source. -/
  symbol_zero : symbol 0 =
    symbolComp firstInverse (finiteResolventSourceSymbol (r := r) coordinateWeight)
  /-- The actual horizontal correction, including the constant one. -/
  symbol_succ : ∀ j : ℕ, symbol (j + 1) = (-1 : ℂ) •
    symbolComp firstInverse (coordinate.parameterCorrectionSymbol (symbol j))
  /-- Every explicit finite defect has the corresponding joint order. -/
  isSymbol_remainder : ∀ N : ℕ, IsSymbol
    ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
        (chart '' domain)) (-(N : ℝ))
    ((∑ j ∈ Finset.range N,
      (symbolComp coordinate.parameterLift.principalSymbol (symbol j) +
        coordinate.parameterCorrectionSymbol (symbol j))) -
      finiteResolventSourceSymbol (r := r) coordinateWeight)

namespace FiniteResolventPatch

variable {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2}
  (P : FiniteResolventPatch L)

/-- The retained explicit joint remainder, with the original finite sequence. -/
def remainderSymbol (N : ℕ) : SymbolFunction (n + 1) r r :=
  (∑ j ∈ Finset.range N,
    (symbolComp P.coordinate.parameterLift.principalSymbol (P.symbol j) +
      P.coordinate.parameterCorrectionSymbol (P.symbol j))) -
    finiteResolventSourceSymbol (r := r) P.coordinateWeight

/-- A sliced joint symbol is realized by the same specified chart, frame and cutoffs. -/
def piece (m : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r r)
    (ha : IsSymbol
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹'
          (P.chart '' P.domain)) m a)
    (τ : ℝ) (hτ : 0 < τ) :
    PseudodifferentialPiece (n := n) (r := r) (q := r) E E m := by
  let D := P.chart '' P.domain
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun x hx ↦ (P.hasCoordinateExpression.1 hx).1.1)
  have hW : IsOpen ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' D) :=
    hD.preimage (continuous_fst.comp EuclideanSpace.finAddEquivProd.continuous)
  have hslice := (exists_uniform_quantizeSobolev_jointFrequencySymbolSlice _ hW m 0 hm a ha
    D hD (by intro x hx; simpa using hx) P.cutoff.cutoff P.cutoff.smooth_cutoff
    P.cutoff.compact_support P.support_cutoff).choose τ hτ
  let b := zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice a τ)
  have hb : IsSymbol Set.univ m b := isSymbol_zeroExtendedSymbol D hD m
    P.cutoff.cutoff P.cutoff.smooth_cutoff P.cutoff.compact_support
    P.support_cutoff _ hslice
  have hbc : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol D
    P.cutoff.cutoff _ P.cutoff.compact_support
  exact
    { chart := P.chart
      chart_mem_atlas := P.chart_mem_atlas
      input := P.cutoff
      output := P.cutoff
      input_support_in_output_frame := fun _ hz ↦ (P.cutoff.support_subset hz).2
      output_support_in_input_frame := fun _ hz ↦ (P.cutoff.support_subset hz).2
      operator := quantizeSchwartz m b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply m b hb hbc }

/-- The actual term acts on original smooth sections through the fixed Schwartz piece. -/
def term (j : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  (P.piece (-2 - (j : ℝ))
    (sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j))) (P.symbol j)
    (P.isSymbol_symbol j) τ hτ).toLinearMap

/-- The actual finite residual has the explicit joint remainder as its local symbol. -/
def remainder (N : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := r) E :=
  (P.piece (-(N : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg N)) (P.remainderSymbol N)
    (P.isSymbol_remainder N) τ hτ).toLinearMap

end FiniteResolventPatch

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

/-- The specified connection Laplacian has a fixed finite family of supported resolvent patches.
All recursive symbols and high-frequency inverse witnesses are retained. -/
theorem exists_connectionLaplacian_finite_resolvent_patches :
    ∃ k : ℕ, ∃ P : Fin k →
      FiniteResolventPatch (connectionLaplacian μ g h cov hcov hcomplex),
      ∀ x : M, ∑ j, (P j).weight x = 1 := by
  classical
  let L := connectionLaplacian μ g h cov hcov hcomplex
  -- Refine to genuine coordinate expressions before choosing a finite partition.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hexpr (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ Q : CoordinateDifferentialOperator n r r 2 (c x '' U),
        HasCoordinateExpression E E 2 L.toLinearMap (c x) (e x) (e x) U Q :=
    L.isDifferentialOperator (c x) (chart_mem_atlas _ x) (e x) (e x) x
      ⟨⟨mem_chart_source _ x, mem_baseSet_trivializationAt _ _ x⟩,
        mem_baseSet_trivializationAt _ _ x⟩
  choose U hU hxU Q hQ using hexpr
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (index j)
  have hfinitecover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
    (fun j ↦ hU (index j)) hfinitecover
  -- Transfer the output partition to the same coordinates, preserving its compact support.
  let χ (j : Fin s.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let K (j : Fin s.card) := (c (index j)) '' tsupport (ρ j)
  have hK (j : Fin s.card) : IsCompact (K j) :=
    (HasCompactSupport.of_compactSpace (ρ j)).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ ((hQ (index j)).1 (hρ j hx)).1.1))
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
      have hxsource := ((hQ (index j)).1 (hρ j hx)).1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ (index j : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hK j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin s.card) := c (index j) '' U (index j)
  have hD (j : Fin s.card) : IsOpen (D j) :=
    (c (index j)).isOpen_image_of_subset_source (hU (index j))
      (fun x hx ↦ ((hQ (index j)).1 hx).1.1)
  have hKD (j : Fin s.card) : K j ⊆ D j := Set.image_mono (hρ j)
  have hdomain (j : Fin s.card) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ D j) :
      z ∈ (c (index j)).target ∧
        (c (index j)).symm z ∈ (e (index j)).baseSet ∩ (e (index j)).baseSet := by
    obtain ⟨x, hx, rfl⟩ := hz
    have hu := (hQ (index j)).1 hx
    exact ⟨(c (index j)).map_source hu.1.1,
      by simpa only [(c (index j)).left_inv hu.1.1, Set.mem_inter_iff] using
        And.intro hu.1.2 hu.2⟩
  -- A smooth input cutoff is identically one on an open neighborhood of the output support.
  have hinput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∃ W, IsOpen W ∧ tsupport (χ j) ⊆ W ∧
          ∀ z ∈ W, ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hK j) (hD j) (hKD j)
    obtain ⟨O, hO, hWO, hOD, hOcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact (hD j) hWD
    obtain ⟨ψ, hψ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO isClosed_closure hWO
    have hts : tsupport ψ = closure O := congrArg closure hsupp
    refine ⟨ψ, hψ, ?_, ?_, W, hW, (hχ j).trans hKW, ?_⟩
    · change IsCompact (tsupport ψ)
      rwa [hts]
    · rwa [hts]
    · intro z hz
      exact (hone z).mp (subset_closure hz)
  choose ψ hψsmooth hψcompact hψsupport hψone using hinput
  -- The joint source is a smooth multiplication symbol, with an actual dummy bump.
  have hsource (j : Fin s.card) : IsSymbol
      ((fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1) z).1) ⁻¹' D j)
      0 (finiteResolventSourceSymbol (r := r) (χ j)) := by
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    let W := (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ (split z).1) ⁻¹' D j
    let ρ₀ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
      ⟨1, 2, by norm_num, by norm_num⟩
    have hW : IsOpen W := (hD j).preimage (continuous_fst.comp split.continuous)
    have hs : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
        ((χ j (split z).1 * ρ₀ (split z).2 : ℝ) : ℂ) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))) :=
      (Complex.ofRealCLM.contDiff.comp
        (((hχsmooth j).comp (contDiff_fst.comp split.contDiff)).mul
          (ρ₀.contDiff.comp (contDiff_snd.comp split.contDiff)))).smul contDiff_const
    let Q₀ : CoordinateDifferentialOperator (n + 1) r r 0 W :=
      { coefficient := fun _ _ z ↦
          ((χ j (split z).1 * ρ₀ (split z).2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _
        smooth_coefficient := fun _ _ ↦ hs.contDiffOn }
    have heq : Q₀.totalSymbol = finiteResolventSourceSymbol (r := r) (χ j) := by
      funext z ζ
      simp [CoordinateDifferentialOperator.totalSymbol, Q₀, finiteResolventSourceSymbol,
        split, ρ₀]
    simpa only [Nat.cast_zero, heq] using Q₀.isSymbol_totalSymbol hW
  -- Select each original inverse and recursive sequence once, retaining every certificate.
  have hfinite (j : Fin s.card) :=
    exists_connectionLaplacian_coordinate_finite_parametrix μ g h cov hcov hcomplex
      (c (index j)) (chart_mem_atlas _ (index j : M)) (e (index j))
      (U (index j)) (hU (index j)) (Q (index j)) (hQ (index j))
      (finiteResolventSourceSymbol (r := r) (χ j)) (hsource j)
  choose a₀ a ha₀ ha hsupport hinverse hzero hsucc hrem using hfinite
  let C (j : Fin s.card) : BundleChartCutoff (r := r) E (c (index j)) :=
    { frame := e (index j)
      frame_mem_atlas := inferInstance
      cutoff := ψ j
      smooth_cutoff := hψsmooth j
      compact_support := hψcompact j
      support_subset := fun z hz ↦
        ⟨(hdomain j (hψsupport j hz)).1, (hdomain j (hψsupport j hz)).2.1⟩ }
  let patches (j : Fin s.card) : FiniteResolventPatch L :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      cutoff := C j
      domain := U (index j)
      isOpen_domain := hU (index j)
      coordinate := Q (index j)
      hasCoordinateExpression := hQ (index j)
      support_cutoff := hψsupport j
      weight := ρ j
      coordinateWeight := χ j
      smooth_coordinateWeight := hχsmooth j
      compact_coordinateWeight := hχcompact j
      support_coordinateWeight := (hχ j).trans (hKD j)
      coordinateWeight_apply := by
        intro x hx
        simp only [χ, ite_eq_left ((c (index j)).map_source hx),
          (c (index j)).left_inv hx]
      weight_eq_zero := by
        intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hρ j ht))
      cutoff_eq_one := hψone j
      isSymbol_source := hsource j
      firstInverse := a₀ j
      symbol := a j
      isSymbol_firstInverse := ha₀ j
      isSymbol_symbol := ha j
      support_symbol := hsupport j
      firstInverse_eq := hinverse j
      symbol_zero := hzero j
      symbol_succ := hsucc j
      isSymbol_remainder := hrem j }
  refine ⟨s.card, patches, ?_⟩
  intro x
  change ∑ j, ρ j x = 1
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

end AtiyahSinger
