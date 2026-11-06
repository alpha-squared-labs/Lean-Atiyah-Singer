/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialSymbol
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import Mathlib.Topology.VectorBundle.FiniteDimensional

import AtiyahSinger.Analysis.CompactQuantization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Differential principal symbols in the global PDO quotient

Public module ID: M0436.

D03/D05/A02: compare SG III.1.2 with III.3.15 and III.3.18-3.19, using
the same D_j=-i∂_j convention throughout. The existing algebraic differential
symbol is made into a continuous fiber map, then an actual global order-m symbol.
On a closed base a single finite local representation retains both the exact
section action and its principal class. This identifies the symbol of the bundled
differential-to-PDO inclusion. These comparison results are project consequences
of the cited local formulas and assembly, not separately numbered book lemmas.

No ellipticity or nonvanishing top coefficient is required. The homogeneous
differential symbol is a representative of the PDO class, not a pointwise value
assigned to an arbitrary quotient element. Fiberwise continuity and the original
coordinate formula, global symbol estimates and exact finite PDO comparison
are proved below with the same chart, frame and cutoff witnesses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)

/-- The algebraic differential symbol is continuous on each finite-dimensional fiber. -/
theorem continuous_principalSymbol (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    Continuous (P.principalSymbol x ξ) := by
  /- A bundle trivialization at x gives E_x a linear equivalence with ℂ^r.
  Use VectorBundle.finiteDimensional to transfer finite-dimensionality, then
  continuity of linear maps from a finite-dimensional normed space. No Hermitian
  metric, completeness assumption, or compactness of the base is needed. -/
  -- The native bundle chart transfers its finite rank to this same source fiber.
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  exact (P.principalSymbol x ξ).continuous_of_finiteDimensional

/-- The existing differential symbol, with its fiberwise continuity certificate. -/
def principalSymbolFunction : GlobalSymbolFunction (n := n) E F :=
  fun x ξ ↦ { P.principalSymbol x ξ with cont := P.continuous_principalSymbol x ξ }

/-- Adding continuity does not change the underlying algebraic fiber map. -/
theorem principalSymbolFunction_toLinearMap (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    (P.principalSymbolFunction x ξ).toLinearMap = P.principalSymbol x ξ := by
  /- Unfold the continuous linear map constructor and project to its linear map.
  The continuity certificate changes no values or algebraic fields. -/
  -- The continuous map constructor keeps every original linear-map field.
  rfl

/-- A valid local expression computes the continuous differential symbol in those frames. -/
theorem globalSymbolInChart_principalSymbolFunction
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (U : Set M) (hU : IsOpen U)
    (Q : CoordinateDifferentialOperator n r q m (c '' U))
    (hQ : HasCoordinateExpression E F m P.toLinearMap c e f U Q)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c '' U)
    (η : EuclideanSpace ℝ (Fin n)) :
    globalSymbolInChart E F P.principalSymbolFunction c e f z η =
      Q.principalSymbol z η := by
  /- Stage 1: hQ places U in the common base/frame overlap. Thus c.symm z lies
  in U and both frames are valid there. Apply P.hasPrincipalSymbol to Q.
  Stage 2: compose with the inverse input frame and cancel the frame maps only
  on this overlap. The inverse-covector identity recovers η from covectorFromChart.
  Extensionality upgrades the algebraic equality to continuous linear maps. -/
  obtain ⟨x, hx, rfl⟩ := hz
  have hxsource : x ∈ c.source := (hQ.1 hx).1.1
  -- Evaluate the original principal-symbol characterization in these same frames.
  apply ContinuousLinearMap.ext
  intro v
  have hs := LinearMap.congr_fun
    (P.hasPrincipalSymbol c hc e f U hU Q hQ x hx (covectorFromChart c x η))
    (e.symmL ℂ x v)
  change f.continuousLinearMapAt ℂ x
    (P.principalSymbol x (covectorFromChart c x η) (e.symmL ℂ x v)) =
      Q.principalSymbol (c x) (covectorInChart c x (covectorFromChart c x η))
        (e.continuousLinearMapAt ℂ x (e.symmL ℂ x v)) at hs
  -- Inverse cotangent and input-frame transport cancel only on the given overlap.
  rw [covectorInChart_covectorFromChart c hc x hxsource,
    e.continuousLinearMapAt_symmL (hQ.1 hx).1.2] at hs
  change f.continuousLinearMapAt ℂ (c.symm (c x))
    (P.principalSymbol (c.symm (c x)) (covectorFromChart c (c.symm (c x)) η)
      (e.symmL ℂ (c.symm (c x)) v)) = Q.principalSymbol (c x) η v
  rw [c.left_inv hxsource]
  exact hs

open Filter in
open scoped Topology in
/-- The differential principal polynomial is a genuine global symbol of order at most m. -/
theorem isGlobalSymbol_principalSymbolFunction :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F (m : ℝ)
      P.principalSymbolFunction := by
  /- Stage 1: every point of each chart/frame overlap has an open differential
  expression. The preceding comparison identifies the symbol with its top
  polynomial there, so coordinate smoothness follows by locality.
  Stage 2: cover each compact spatial set by finitely many relatively compact
  subpatches of these expressions. Bound coefficient derivatives on their compact
  closures and use the degree-m frequency estimates. A finite sum gives the
  required estimate on the original compact set, for all frequencies and derivatives.
  This is local-in-space symbol regularity; M itself need not be compact. -/
  classical
  intro c hc e f _ _
  let U := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F P.principalSymbolFunction c e f
  -- Equality on an open spatial domain preserves the same total mixed derivatives.
  have hcongr {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
      (p₁ p₂ : SymbolFunction n r q) (hp₁ : IsSymbol V (m : ℝ) p₁)
      (heq : ∀ z ∈ V, ∀ η, p₁ z η = p₂ z η) : IsSymbol V (m : ℝ) p₂ := by
    refine ⟨hp₁.1.congr (fun z hz ↦ (heq z.1 hz.1 z.2).symm), ?_⟩
    intro K hKV hK i j
    obtain ⟨C, hC, hbound⟩ := hp₁.2 K hKV hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (p₁ y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (p₂ y) ξ) := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      rw [funext (heq y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  -- The actual local differential expression supplies the original polynomial estimate.
  have hlocal (z : U) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ z.val ∈ V ∧ IsSymbol V (m : ℝ) p := by
    have hx : c.symm z.val ∈ c.source ∩ e.baseSet ∩ f.baseSet :=
      ⟨⟨c.map_target z.property.1.1, z.property.1.2⟩, z.property.2⟩
    obtain ⟨O, hO, hxO, Q, hQ⟩ :=
      P.isDifferentialOperator c hc e f (c.symm z.val) hx
    have hOs : O ⊆ c.source := fun x hx ↦ (hQ.1 hx).1.1
    have hV : IsOpen (c '' O) := c.isOpen_image_of_subset_source hO hOs
    refine ⟨c '' O, hV, ⟨c.symm z.val, hxO, c.right_inv z.property.1.1⟩,
      hcongr hV Q.principalSymbol p (Q.isSymbol_principalSymbol hV) ?_⟩
    intro x hx ξ
    exact (P.globalSymbolInChart_principalSymbolFunction c hc e f O hO Q hQ x hx ξ).symm
  choose V hV hzV hpV using hlocal
  refine ⟨?_, ?_⟩
  · -- Smoothness is local in the same spatial-frequency product, including frequency zero.
    intro z hz
    exact ((hpV ⟨z.1, hz.1⟩).1.contDiffAt
      (((hV ⟨z.1, hz.1⟩).prod isOpen_univ).mem_nhds
        ⟨hzV ⟨z.1, hz.1⟩, Set.mem_univ z.2⟩)).contDiffWithinAt
  · intro K hKU hK i j
    -- Compact spatial neighborhoods combine finitely many estimates at every frequency.
    choose L hL hzL hLV using fun z : U ↦ exists_compact_subset (hV z) (hzV z)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (L z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzL ⟨x, hKU hx⟩⟩)
    choose C hC hbound using fun z : U ↦ (hpV z).2 (L z) (hLV z) (hL z) i j
    refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
    intro x hx ξ
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hbound z x (interior_subset hxz) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hC z) hzt

/-- The differential principal polynomial as an element of the global symbol submodule. -/
def principalGlobalSymbol : globalSymbolSpace (n := n) (r := r) (q := q) E F (m : ℝ) :=
  ⟨P.principalSymbolFunction, P.isGlobalSymbol_principalSymbolFunction⟩

/-- One finite representation retains the exact differential map and its principal class. -/
theorem exists_representation_principalSymbol [CompactSpace M] :
    ∃ (N : ℕ) (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q)
        E F (m : ℝ)),
      P.toLinearMap = ∑ j, (L j).toLinearMap ∧
        globalPrincipalSymbolClass E F (m : ℝ) (∑ j, (L j).globalSymbol) =
          globalPrincipalSymbolClass E F (m : ℝ) P.principalGlobalSymbol := by
  /- Stage 1: refine the actual differential expressions by a finite smooth output
  partition. An input plateau, also used to extend the full local polynomial,
  preserves the original coordinate germ on each output support. Polynomial
  quantization therefore gives exactly the weighted original section action.
  Stage 2: in the same chart, frames and cutoffs, quantize the full polynomial
  minus its degree-m part. This is an order-(m-1) piece, including m=0, where
  the difference is zero. Its transported symbol is the original piece symbol
  minus the partition weight times the given differential principal symbol.
  Summing the partition identity proves the required quotient equality for that
  very same family. Neither a measure nor a smoothing witness is used here. -/
  classical
  -- Use the actual differential expressions, refining the chart/frame cover before partitioning.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have hexpr (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ Q : CoordinateDifferentialOperator n r q m (c x '' U),
        HasCoordinateExpression E F m P.toLinearMap (c x) (e x) (f x) U Q :=
    P.isDifferentialOperator (c x) (chart_mem_atlas _ x) (e x) (f x) x
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
        (c (index j)).symm z ∈ (e (index j)).baseSet ∩ (f (index j)).baseSet := by
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
  let a (j : Fin s.card) := zeroExtendedSymbol (D j) (ψ j) (Q (index j)).totalSymbol
  have ha (j : Fin s.card) : IsSymbol Set.univ (m : ℝ) (a j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) m (ψ j) (hψsmooth j)
      (hψcompact j) (hψsupport j) _ ((Q (index j)).isSymbol_totalSymbol (hD j))
  have hacompact (j : Fin s.card) : HasCompactSupport (a j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (ψ j) _ (hψcompact j)
  let L (j : Fin s.card) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      input :=
        { frame := e (index j)
          frame_mem_atlas := inferInstance
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hψsupport j hz)).1, (hdomain j (hψsupport j hz)).2.1⟩ }
      output :=
        { frame := f (index j)
          frame_mem_atlas := inferInstance
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hKD j (hχ j hz))).1, (hdomain j (hKD j (hχ j hz))).2.2⟩ }
      input_support_in_output_frame := fun z hz ↦ (hdomain j (hψsupport j hz)).2.2
      output_support_in_input_frame := fun z hz ↦ (hdomain j (hKD j (hχ j hz))).2.1
      operator := quantizeSchwartz m (a j) (ha j) (hacompact j)
      symbol := a j
      isSymbol := ha j
      operator_apply := quantizeSchwartz_apply m (a j) (ha j) (hacompact j) }
  -- The remaining comparison uses the same local expression and the actual cutoff plateau.
  have hpiece (j : Fin s.card) (u : smoothSections (n := n) (r := r) E) (x : M) :
      ((L j).toLinearMap u).val x = (ρ j x : ℂ) • (P.toLinearMap u).val x := by
    have hχx (hx : x ∈ (c (index j)).source) : χ j (c (index j) x) = ρ j x := by
      simp only [χ, ite_eq_left ((c (index j)).map_source hx),
        (c (index j)).left_inv hx]
    by_cases hr : ρ j x = 0
    · -- Off the partition support the actual output cutoff makes this piece vanish.
      change (L j).output.extendedFunction
        ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) x = _
      by_cases hx : x ∈ (c (index j)).source
      · simp only [BundleChartCutoff.extendedFunction, L, ite_eq_left hx, hχx hx, hr,
          Complex.ofReal_zero, zero_smul]
      · simp only [BundleChartCutoff.extendedFunction, L, ite_eq_right hx, hr,
          Complex.ofReal_zero, zero_smul]
    · have hxU : x ∈ U (index j) := hρ j (subset_tsupport _ hr)
      have hu := (hQ (index j)).1 hxU
      have hxD : c (index j) x ∈ D j := ⟨x, hxU, rfl⟩
      have hxχ : c (index j) x ∈ tsupport (χ j) :=
        subset_tsupport _ (by
          change χ j (c (index j) x) ≠ 0
          rwa [hχx hu.1.1])
      obtain ⟨W, hW, hχW, hψW⟩ := hψone j
      have hψx := hψW _ (hχW hxχ)
      -- The localized input has exactly the original coordinate germ on this plateau.
      have hnear : ((L j).input.localize (L j).chart_mem_atlas u :
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)) =ᶠ[nhds (c (index j) x)]
            sectionInChart E (c (index j)) (e (index j)) u.val := by
        filter_upwards [hW.mem_nhds (hχW hxχ),
          (c (index j)).open_target.mem_nhds ((c (index j)).map_source hu.1.1)] with z hz hzT
        change (L j).input.localizedFunction u z = _
        simp only [BundleChartCutoff.localizedFunction, L, ite_eq_left hzT, hψW z hz,
          Complex.ofReal_one, one_smul]
      have hpoly : (Q (index j)).apply
          ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) =
          (Q (index j)).apply
            (sectionInChart E (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        simp only [CoordinateDifferentialOperator.apply]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro α _
        rw [(hnear.iteratedFDeriv ℝ l.val).eq_of_nhds]
      have haeq (ξ : EuclideanSpace ℝ (Fin n)) :
          a j (c (index j) x) ξ = (Q (index j)).totalSymbol (c (index j) x) ξ := by
        simp only [a, zeroExtendedSymbol, ite_eq_left hxD, hψx,
          Complex.ofReal_one, one_smul]
      have hquant : quantize (a j) ((L j).input.localize (L j).chart_mem_atlas u)
          (c (index j) x) = (Q (index j)).apply
            (sectionInChart E (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        calc
          _ = quantize (Q (index j)).totalSymbol
              ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) := by
            simp only [quantize, haeq]
          _ = _ := ((Q (index j)).quantize_totalSymbol _ _).trans hpoly
      -- The same output frame recovers the original fiber value, multiplied only by ρ.
      have hframe := (L j).toLinearMap_in_frame u x hu.1.1 hu.2
      change (f (index j) ⟨x, ((L j).toLinearMap u).val x⟩).2 =
        (χ j (c (index j) x) : ℂ) • quantize (a j)
          ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) at hframe
      rw [hχx hu.1.1, hquant, ← (hQ (index j)).2 u x hxU] at hframe
      apply ((f (index j)).linearEquivAt ℂ x hu.2).injective
      rw [map_smul]
      exact hframe
  have hsum : P.toLinearMap = ∑ j, (L j).toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, hpiece,
      ← Finset.sum_smul]
    have hρsum : ∑ j, ρ j x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    rw [← Complex.ofReal_sum, hρsum, Complex.ofReal_one, one_smul]
  -- The same piece with its lower-degree polynomial records the exact lower-order error.
  let b (j : Fin s.card) := zeroExtendedSymbol (D j) (ψ j)
    ((Q (index j)).totalSymbol - (Q (index j)).principalSymbol)
  have hb (j : Fin s.card) : IsSymbol Set.univ ((m : ℝ) - 1) (b j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) ((m : ℝ) - 1) (ψ j) (hψsmooth j)
      (hψcompact j) (hψsupport j) _
      ((Q (index j)).isSymbol_totalSymbol_sub_principalSymbol (hD j))
  have hbcompact (j : Fin s.card) : HasCompactSupport (b j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (ψ j) _ (hψcompact j)
  let R (j : Fin s.card) : PseudodifferentialPiece
      (n := n) (r := r) (q := q) E F ((m : ℝ) - 1) :=
    { chart := (L j).chart
      chart_mem_atlas := (L j).chart_mem_atlas
      input := (L j).input
      output := (L j).output
      input_support_in_output_frame := (L j).input_support_in_output_frame
      output_support_in_input_frame := (L j).output_support_in_input_frame
      operator := quantizeSchwartz _ (b j) (hb j) (hbcompact j)
      symbol := b j
      isSymbol := hb j
      operator_apply := quantizeSchwartz_apply _ (b j) (hb j) (hbcompact j) }
  have hprincipal (j : Fin s.card) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      (L j).globalSymbolFunction x ξ - (R j).globalSymbolFunction x ξ =
        (ρ j x : ℂ) • P.principalSymbolFunction x ξ := by
    have hχx (hx : x ∈ (c (index j)).source) : χ j (c (index j) x) = ρ j x := by
      simp only [χ, ite_eq_left ((c (index j)).map_source hx),
        (c (index j)).left_inv hx]
    by_cases hr : ρ j x = 0
    · -- Outside this partition weight both transported symbols are zero.
      by_cases hx : x ∈ (c (index j)).source
      · simp only [PseudodifferentialPiece.globalSymbolFunction, R, L, hχx hx, hr,
          zero_mul, Complex.ofReal_zero, zero_smul, ite_self, sub_self]
      · have hx' : x ∉ (c (index j)).source ∩ (e (index j)).baseSet ∩
            (f (index j)).baseSet := fun h ↦ hx h.1.1
        simp only [PseudodifferentialPiece.globalSymbolFunction, R, L, ite_eq_right hx',
          hr, Complex.ofReal_zero, zero_smul, sub_self]
    · -- On this support the plateau is one, so only the original top polynomial remains.
      have hxU : x ∈ U (index j) := hρ j (subset_tsupport _ hr)
      have hu := (hQ (index j)).1 hxU
      have hxD : c (index j) x ∈ D j := ⟨x, hxU, rfl⟩
      have hxχ : c (index j) x ∈ tsupport (χ j) :=
        subset_tsupport _ (by
          change χ j (c (index j) x) ≠ 0
          rwa [hχx hu.1.1])
      obtain ⟨W, hW, hχW, hψW⟩ := hψone j
      have hψx := hψW _ (hχW hxχ)
      apply ContinuousLinearMap.ext
      intro v
      simp only [PseudodifferentialPiece.globalSymbolFunction, R, L, ite_eq_left hu,
        sub_apply, smul_apply,
        ContinuousLinearMap.comp_apply, hχx hu.1.1, hψx, mul_one,
        a, b, zeroExtendedSymbol, ite_eq_left hxD, Complex.ofReal_one, one_smul,
        Pi.sub_apply]
      rw [← smul_sub, ← map_sub, sub_sub_cancel]
      congr 1
      apply ((f (index j)).linearEquivAt ℂ x hu.2).injective
      simp only [Trivialization.linearEquivAt_apply]
      rw [← (f (index j)).continuousLinearMapAt_apply_of_mem ℂ hu.2,
        (f (index j)).continuousLinearMapAt_symmL hu.2]
      rw [← (f (index j)).continuousLinearMapAt_apply_of_mem ℂ hu.2]
      exact (LinearMap.congr_fun (P.hasPrincipalSymbol (c (index j))
        (chart_mem_atlas _ (index j : M)) (e (index j)) (f (index j))
        (U (index j)) (hU (index j)) (Q (index j)) (hQ (index j)) x hxU ξ) v).symm
  refine ⟨s.card, L, hsum, ?_⟩
  apply (globalPrincipalSymbolClass_eq_iff E F (m : ℝ) _ _).mpr
  have hglobal : IsGlobalSymbol (n := n) (r := r) (q := q) E F ((m : ℝ) - 1)
      (∑ j, (R j).globalSymbolFunction) := by
    exact (globalSymbolSpace E F ((m : ℝ) - 1)).sum_mem
      (fun j _ ↦ (R j).isGlobalSymbol_globalSymbolFunction)
  convert hglobal using 1
  funext x ξ
  have hρsum : ∑ j, ρ j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  have heq := congrArg (fun g : Fin s.card → (E x →L[ℂ] F x) ↦ ∑ j, g j)
    (funext (fun j ↦ hprincipal j x ξ))
  simp only [Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum,
    hρsum, Complex.ofReal_one, one_smul] at heq
  simp only [Submodule.coe_sum, Finset.sum_apply, Pi.sub_apply]
  change (∑ j, (L j).globalSymbolFunction x ξ) - P.principalSymbolFunction x ξ =
    ∑ j, (R j).globalSymbolFunction x ξ
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp heq).trans (add_comm _ _))

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

/-- A differential operator regarded as a PDO of the same integer order bound. -/
def toPseudodifferentialOperator :
    PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m : ℝ) where
  toLinearMap := P.toLinearMap
  isPseudodifferentialOperator := P.isPseudodifferentialOperator (μ := μ)

/-- The differential-to-PDO inclusion retains exactly the original section action. -/
theorem toPseudodifferentialOperator_toLinearMap :
    (P.toPseudodifferentialOperator μ).toLinearMap = P.toLinearMap := by
  /- Project the explicit bundled constructor. No choice of a local representation
  or alteration by a smoothing operator is involved in this underlying map. -/
  -- The bundled inclusion has exactly the specified original section map.
  rfl

/-- The PDO principal class of a differential operator is the class of its top polynomial. -/
theorem principalSymbol_toPseudodifferentialOperator :
    (P.toPseudodifferentialOperator μ).principalSymbol =
      globalPrincipalSymbolClass E F (m : ℝ) P.principalGlobalSymbol := by
  /- Stage 1: take the shared finite representation above. Its exact map equality
  makes the remainder zero, which is a smoothing operator for the chosen density.
  Apply PseudodifferentialOperator.principalSymbol_eq_of_representation.
  Stage 2: use the principal-class equality of the same family. This identifies
  quotient elements, without claiming equality of the full local polynomials and
  their top-degree terms. The right side is independent of the positive density. -/
  obtain ⟨N, L, hmap, hclass⟩ := P.exists_representation_principalSymbol
  -- Exact equality of the original section maps leaves the actual zero kernel.
  have hzero : IsSmoothingOperator μ
      ((P.toPseudodifferentialOperator μ).toLinearMap - ∑ j, (L j).toLinearMap) := by
    change IsSmoothingOperator μ (P.toLinearMap - ∑ j, (L j).toLinearMap)
    rw [hmap, sub_self]
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
  -- Compute the class with the same family that supplied the exact differential action.
  exact ((P.toPseudodifferentialOperator μ).principalSymbol_eq_of_representation N L hzero).trans
    hclass

end DifferentialOperator

/-- Any PDO with the same differential section map has that differential principal class. -/
theorem PseudodifferentialOperator.principalSymbol_eq_of_differentialOperator
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ] {m : ℕ}
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m : ℝ))
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (h : Q.toLinearMap = P.toLinearMap) :
    Q.principalSymbol = globalPrincipalSymbolClass E F (m : ℝ) P.principalGlobalSymbol := by
  /- Identify Q's principal class with that of P.toPseudodifferentialOperator μ
  using equality of their actual maps, then apply the comparison theorem. The
  integer order bound is the same on both sides; no ellipticity is assumed. -/
  -- First retain the actual map, then use its already established differential class.
  exact (Q.principalSymbol_eq_of_toLinearMap_eq μ (P.toPseudodifferentialOperator μ) h).trans
    (P.principalSymbol_toPseudodifferentialOperator μ)

end AtiyahSinger
