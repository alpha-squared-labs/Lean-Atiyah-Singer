/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPrincipalSymbolRegularity
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.DifferentialSymbol

/-!
# Differential operators inside the atlas pseudodifferential calculus

Public module ID: M0239.

D05: the inclusion stated immediately after SG III.3.15, p.186, retains the
actual differential operator on the original smooth sections. The principal
quotient is the class of its already constructed intrinsic polynomial symbol,
with D_j = -i partial_j. Both local ranks remain independent. The polynomial
symbol is homogeneous of the prescribed degree, even when the operator has
strictly smaller order; no complete homogeneous expansion is required. The global
symbol estimate, actual PDO realization and principal quotient comparison are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

namespace AtlasDifferentialOperator

variable {A B} {k : ℕ} (P : AtlasDifferentialOperator A B k)

open Filter in
open scoped Topology in
/-- The existing intrinsic leading polynomial is an actual global symbol of its natural order. -/
theorem isAtlasGlobalSymbol_principalSymbol :
    IsAtlasGlobalSymbol A B (k : ℝ) P.principalSymbol := by
  /- In every original chart/frame pair the principalSymbol specification
  identifies the coordinate map with the finite leading polynomial of a
  local differential expression. Its coefficients are smooth. On each
  compact subset all coefficient derivatives are bounded; a frequency
  derivative lowers its polynomial degree by one, and derivatives beyond
  the degree vanish. A finite cover of the compact set combines the local
  estimates. This also includes zero-dimensional and zero-rank cases. -/
  classical
  intro c hc i j
  let U := atlasSymbolChartDomain A B c i j
  let p := atlasGlobalSymbolInChart A B P.principalSymbol c i j
  -- Equality on an open spatial domain preserves the same total mixed derivatives.
  have hcongr {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
      (p₁ p₂ : SymbolFunction n (A.rank i) (B.rank j)) (hp₁ : IsSymbol V (k : ℝ) p₁)
      (heq : ∀ z ∈ V, ∀ η, p₁ z η = p₂ z η) : IsSymbol V (k : ℝ) p₂ := by
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
  -- Keep the original local expression, chart, frame pair, and covector reconstruction.
  have hlocal (z : U) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ z.val ∈ V ∧ IsSymbol V (k : ℝ) p := by
    have hx : c.symm z.val ∈ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
      ⟨⟨c.map_target z.property.1.1, z.property.1.2⟩, z.property.2⟩
    obtain ⟨O, hO, hxO, Q, hQ⟩ :=
      P.isAtlasDifferentialOperator c hc i j (c.symm z.val) hx
    have hOs : O ⊆ c.source := fun x hx ↦ (hQ.1 hx).1.1
    have hV : IsOpen (c '' O) := c.isOpen_image_of_subset_source hO hOs
    refine ⟨c '' O, hV, ⟨c.symm z.val, hxO, c.right_inv z.property.1.1⟩,
      hcongr hV Q.principalSymbol p (Q.isSymbol_principalSymbol hV) ?_⟩
    intro x hx ξ
    have hxt : x ∈ c.target := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact c.map_source (hOs hy)
    have hy : c.symm x ∈ O := by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa only [c.left_inv (hOs hy)] using hy
    have hyc := hOs hy
    have hyi := (hQ.1 hy).1.2
    have hyj := (hQ.1 hy).2
    apply ContinuousLinearMap.ext
    intro v
    let eA := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    let eB := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
    let w := (A.frameLinearEquiv i (c.symm x) hyi).symm (eA v)
    have hs := P.hasAtlasPrincipalSymbol c hc i j O hO Q hQ (c.symm x) hy
      (covectorFromChart c (c.symm x) ξ) w
    rw [covectorInChart_covectorFromChart c hc (c.symm x) hyc, c.right_inv hxt] at hs
    have hw : (A.chart i ⟨c.symm x, w⟩).2 = eA v :=
      (A.frameLinearEquiv i (c.symm x) hyi).apply_symm_apply (eA v)
    rw [hw, eA.symm_apply_apply] at hs
    change Q.principalSymbol x ξ v =
      atlasGlobalSymbolInChart A B P.principalSymbol c i j x ξ v
    simp only [atlasGlobalSymbolInChart, hyi, hyj, and_self, dite_true]
    change Q.principalSymbol x ξ v = eB.symm
      ((B.frameLinearEquiv j (c.symm x) hyj)
        (P.principalSymbol (c.symm x) (covectorFromChart c (c.symm x) ξ) w))
    exact hs.symm
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

/-- The same intrinsic polynomial as an element of the atlas symbol module. -/
def principalGlobalSymbol : atlasGlobalSymbolSpace A B (k : ℝ) :=
  ⟨P.principalSymbol, P.isAtlasGlobalSymbol_principalSymbol⟩

variable [CompactSpace M]

open Filter in
open scoped Topology in
/-- One finite family retains both the differential action and its intrinsic principal class. -/
private theorem exists_representation_principalSymbol :
    ∃ (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A B (k : ℝ)),
      P.toLinearMap = ∑ j, (L j).toLinearMap ∧
        atlasGlobalPrincipalSymbolClass A B (k : ℝ) (∑ j, (L j).globalSymbol) =
          atlasGlobalPrincipalSymbolClass A B (k : ℝ) P.principalGlobalSymbol := by
  /- Choose one finite output partition in the original differential-expression
  domains and input cutoffs equal to one near each output support. The full local
  polynomials recover the exact section action. With the same cutoffs, their
  lower-degree parts form symbols of one lower order. Subtracting these parts
  leaves the partition-weighted intrinsic principal symbol in the original fibers. -/
  classical
  -- Use the actual differential expressions, refining the chart/frame cover before partitioning.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  choose e he using A.covers
  choose f hf using B.covers
  have hexpr (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ Q : CoordinateDifferentialOperator n (A.rank (e x)) (B.rank (f x)) k (c x '' U),
        HasAtlasCoordinateExpression A B k P.toLinearMap (c x) (e x) (f x) U Q :=
    P.isAtlasDifferentialOperator (c x) (chart_mem_atlas _ x) (e x) (f x) x
      ⟨⟨mem_chart_source _ x, he x⟩, hf x⟩
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
        (c (index j)).symm z ∈
          (A.chart (e (index j))).baseSet ∩ (B.chart (f (index j))).baseSet := by
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
  have ha (j : Fin s.card) : IsSymbol Set.univ (k : ℝ) (a j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) k (ψ j) (hψsmooth j)
      (hψcompact j) (hψsupport j) _ ((Q (index j)).isSymbol_totalSymbol (hD j))
  have hacompact (j : Fin s.card) : HasCompactSupport (a j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (ψ j) _ (hψcompact j)
  let L (j : Fin s.card) : AtlasPseudodifferentialPiece A B k :=
    { chart := c (index j)
      chart_mem_atlas := chart_mem_atlas _ (index j : M)
      input :=
        { frameIndex := e (index j)
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hψsupport j hz)).1, (hdomain j (hψsupport j hz)).2.1⟩ }
      output :=
        { frameIndex := f (index j)
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦
            ⟨(hdomain j (hKD j (hχ j hz))).1, (hdomain j (hKD j (hχ j hz))).2.2⟩ }
      input_support_in_output_frame := fun z hz ↦ (hdomain j (hψsupport j hz)).2.2
      output_support_in_input_frame := fun z hz ↦ (hdomain j (hKD j (hχ j hz))).2.1
      operator := quantizeSchwartz k (a j) (ha j) (hacompact j)
      symbol := a j
      isSymbol := ha j
      operator_apply := quantizeSchwartz_apply k (a j) (ha j) (hacompact j) }
  -- The remaining comparison uses the same local expression and the actual cutoff plateau.
  have hpiece (j : Fin s.card) (u : A.smoothSections) (x : M) :
      ((L j).toLinearMap u).val x = (ρ j x : ℂ) • (P.toLinearMap u).val x := by
    have hχx (hx : x ∈ (c (index j)).source) : χ j (c (index j) x) = ρ j x := by
      simp only [χ, ite_eq_left ((c (index j)).map_source hx),
        (c (index j)).left_inv hx]
    by_cases hr : ρ j x = 0
    · -- Off the partition support the actual output cutoff makes this piece vanish.
      change (L j).output.extendedFunction
        ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) x = _
      by_cases hx : x ∈ (c (index j)).source ∩ (B.chart (f (index j))).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, L, dite_eq_left hx, hχx hx.1, hr,
          Complex.ofReal_zero, zero_smul]
      · simp only [AtlasChartCutoff.extendedFunction, L, dite_eq_right hx, hr,
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
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin (A.rank (e (index j)))))
            =ᶠ[nhds (c (index j) x)]
            atlasSectionInChart A (c (index j)) (e (index j)) u.val := by
        filter_upwards [hW.mem_nhds (hχW hxχ),
          (c (index j)).open_target.mem_nhds ((c (index j)).map_source hu.1.1)] with z hz hzT
        change (L j).input.localizedFunction u z = _
        simp only [AtlasChartCutoff.localizedFunction, L, ite_eq_left hzT, hψW z hz,
          Complex.ofReal_one, one_smul]
      have hpoly : (Q (index j)).apply
          ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) =
          (Q (index j)).apply
            (atlasSectionInChart A (c (index j)) (e (index j)) u.val) (c (index j) x) := by
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
            (atlasSectionInChart A (c (index j)) (e (index j)) u.val) (c (index j) x) := by
        calc
          _ = quantize (Q (index j)).totalSymbol
              ((L j).input.localize (L j).chart_mem_atlas u) (c (index j) x) := by
            simp only [quantize, haeq]
          _ = _ := ((Q (index j)).quantize_totalSymbol _ _).trans hpoly
      -- The same output frame recovers the original fiber value, multiplied only by ρ.
      change (L j).output.extendedFunction
        ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u)) x = _
      have hframe : x ∈ (c (index j)).source ∩ (B.chart (f (index j))).baseSet :=
        ⟨hu.1.1, hu.2⟩
      simp only [AtlasChartCutoff.extendedFunction, L, dite_eq_left hframe]
      change (χ j (c (index j) x) : ℂ) •
        (B.frameLinearEquiv (f (index j)) x hu.2).symm
          ((EuclideanSpace.equiv (Fin (B.rank (f (index j)))) ℂ)
            ((L j).operator ((L j).input.localize (L j).chart_mem_atlas u)
              (c (index j) x))) = _
      rw [(L j).operator_apply, hχx hu.1.1, hquant, ← (hQ (index j)).2 u x hxU]
      change (ρ j x : ℂ) • (B.frameLinearEquiv (f (index j)) x hu.2).symm
        ((EuclideanSpace.equiv (Fin (B.rank (f (index j)))) ℂ)
          ((EuclideanSpace.equiv (Fin (B.rank (f (index j)))) ℂ).symm
            (B.frameLinearEquiv (f (index j)) x hu.2 ((P.toLinearMap u).val x)))) = _
      rw [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
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
  have hb (j : Fin s.card) : IsSymbol Set.univ ((k : ℝ) - 1) (b j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) ((k : ℝ) - 1) (ψ j) (hψsmooth j)
      (hψcompact j) (hψsupport j) _
      ((Q (index j)).isSymbol_totalSymbol_sub_principalSymbol (hD j))
  have hbcompact (j : Fin s.card) : HasCompactSupport (b j) :=
    hasCompactSupport_zeroExtendedSymbol (D j) (ψ j) _ (hψcompact j)
  let R (j : Fin s.card) : AtlasPseudodifferentialPiece A B ((k : ℝ) - 1) :=
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
        (ρ j x : ℂ) • P.principalSymbol x ξ := by
    have hχx (hx : x ∈ (c (index j)).source) : χ j (c (index j) x) = ρ j x := by
      simp only [χ, ite_eq_left ((c (index j)).map_source hx),
        (c (index j)).left_inv hx]
    by_cases hr : ρ j x = 0
    · -- Outside this partition weight both transported symbols are zero.
      by_cases hx : x ∈ (c (index j)).source
      · simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, R, L, hχx hx, hr,
          zero_mul, Complex.ofReal_zero, zero_smul, sub_self]
      · have hx' : x ∉ (c (index j)).source ∩ (A.chart (e (index j))).baseSet ∩
            (B.chart (f (index j))).baseSet := fun h ↦ hx h.1.1
        simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, R, L, dite_eq_right hx',
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
      apply LinearMap.ext
      intro v
      simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, R, L, dite_eq_left hu,
        LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, hχx hu.1.1, hψx, mul_one,
        a, b, zeroExtendedSymbol, ite_eq_left hxD, Complex.ofReal_one, one_smul,
        Pi.sub_apply]
      have hsub (S T : EuclideanSpace ℂ (Fin (A.rank (e (index j)))) →L[ℂ]
          EuclideanSpace ℂ (Fin (B.rank (f (index j))))) (w) :
          (S - T).toLinearMap w = S.toLinearMap w - T.toLinearMap w := rfl
      rw [← smul_sub, ← map_sub, ← map_sub, hsub, sub_sub_cancel]
      congr 1
      have hxA : x ∈ (A.chart (e (index j))).baseSet := hu.1.2
      have hxB : x ∈ (B.chart (f (index j))).baseSet := hu.2
      let eA := EuclideanSpace.equiv (Fin (A.rank (e (index j)))) ℂ
      let eB := EuclideanSpace.equiv (Fin (B.rank (f (index j)))) ℂ
      change (B.frameLinearEquiv (f (index j)) x hxB).symm
        (eB ((Q (index j)).principalSymbol (c (index j) x)
          (covectorInChart (c (index j)) x ξ)
            (eA.symm ((A.frameLinearEquiv (e (index j)) x hxA) v)))) = _
      apply (B.frameLinearEquiv (f (index j)) x hxB).injective
      rw [LinearEquiv.apply_symm_apply]
      have hp := P.hasAtlasPrincipalSymbol (c (index j))
        (chart_mem_atlas _ (index j : M)) (e (index j)) (f (index j))
        (U (index j)) (hU (index j)) (Q (index j)) (hQ (index j)) x hxU ξ v
      have hp' := congrArg eB hp.symm
      simpa only [eA, eB, SmoothComplexBundleAtlas.frameLinearEquiv,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearEquiv.apply_symm_apply] using hp'
  refine ⟨s.card, L, hsum, ?_⟩
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A B (k : ℝ) _ _).mpr
  have hglobal : IsAtlasGlobalSymbol A B ((k : ℝ) - 1)
      (∑ j, (R j).globalSymbolFunction) := by
    exact (atlasGlobalSymbolSpace A B ((k : ℝ) - 1)).sum_mem
      (fun j _ ↦ (R j).isAtlasGlobalSymbol_globalSymbolFunction)
  convert hglobal using 1
  funext x ξ
  have hρsum : ∑ j, ρ j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  have heq := congrArg (fun g : Fin s.card → (E x →ₗ[ℂ] F x) ↦ ∑ j, g j)
    (funext (fun j ↦ hprincipal j x ξ))
  simp only [Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum,
    hρsum, Complex.ofReal_one, one_smul] at heq
  simp only [Submodule.coe_sum, Finset.sum_apply, Pi.sub_apply]
  change (∑ j, (L j).globalSymbolFunction x ξ) - P.principalSymbol x ξ =
    ∑ j, (R j).globalSymbolFunction x ξ
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp heq).trans (add_comm _ _))

/-- SG p.186: the original atlas differential section map is a PDO of the same order bound. -/
theorem isAtlasPseudodifferentialOperator :
    IsAtlasPseudodifferentialOperator A B (k : ℝ) P.toLinearMap := by
  -- The shared construction represents exactly the original differential action.
  obtain ⟨N, L, hmap, _⟩ := P.exists_representation_principalSymbol
  refine ⟨N, L, ?_⟩
  rw [hmap, sub_self]
  intro T S s t
  exact ⟨0, by intro u; simp⟩

/-- The actual differential action regarded as a pseudodifferential operator. -/
def toAtlasPseudodifferentialOperator : AtlasPseudodifferentialOperator A B (k : ℝ) where
  toLinearMap := P.toLinearMap
  isPseudodifferentialOperator := P.isAtlasPseudodifferentialOperator

/-- The PDO principal class is precisely the class of the original leading polynomial. -/
theorem principalSymbol_toAtlasPseudodifferentialOperator :
    P.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass A B (k : ℝ) P.principalGlobalSymbol := by
  /- Reuse the finite family that already represents the differential action
  and its intrinsic leading class. The remainder of that same section map
  is zero, hence smoothing. Representation independence and the shared
  principal-class comparison give the displayed equality, preserving the
  original covector and D_j = -i partial_j convention. -/
  obtain ⟨N, L, hmap, hclass⟩ := P.exists_representation_principalSymbol
  -- The same finite family has zero remainder on the actual smooth section map.
  have hzero : IsAtlasSmoothingOperator A B
      (P.toAtlasPseudodifferentialOperator.toLinearMap - ∑ j, (L j).toLinearMap) := by
    change IsAtlasSmoothingOperator A B (P.toLinearMap - ∑ j, (L j).toLinearMap)
    rw [hmap, sub_self]
    intro T S s t
    exact ⟨0, by intro u; simp⟩
  exact (P.toAtlasPseudodifferentialOperator.principalSymbol_eq_of_representation N L hzero).trans
    hclass

end AtlasDifferentialOperator

end AtiyahSinger
