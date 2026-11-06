/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Geometry.AtlasSectionMaps

import AtiyahSinger.Analysis.AtlasPseudodifferentialCutoff
import AtiyahSinger.Analysis.CosphereRegularity
import AtiyahSinger.Analysis.DifferentialSymbol
import all AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol

/-!
# Relative finite Fourier quantization on the original atlas bundles

Public module ID: M0299.

Only the correction to a specified exterior bundle map has compact base
support. It is quantized by finitely many original chart/frame pieces, while
the original bundle map acts pointwise on the whole noncompact base. The
operator is their actual sum on the original smooth section spaces.

The principal representative is the bundle-map symbol plus the sum of those
pieces' actual leading symbols. Their class is independent of the finite
presentation of the same actual operator. This is the finite
Fourier presentation needed for relative localization, not the compact-base global
AtlasPseudodifferentialOperator carrier.

Relative regularization is rho(a-c), with c added back afterwards. Its
principal class equals that of rho a because the difference (1-rho)c has
bounded frequency support on every compact spatial chart region. Only the
original off-zero symbol values are used. In dimension zero every principal
quotient is zero, but the actual bundle map and original bundles remain.

Sources: SG III.3.15, III.3.18--3.19 and the construction in III.13.4,
pp.248--249. The variable-rank atlas adaptation and the explicit common
cutoff control are project supplements. The original bundle-map symbol, supported
quantization, relative quantization and exact two-sided localization are proved.
Independence for arbitrary finite presentations of the same map is also proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM in
/-- A smooth original bundle map is the frequency-independent order-zero full symbol. -/
theorem isAtlasGlobalSymbol_zeroOrder
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c) :
    IsAtlasGlobalSymbol A B 0 (fun x _ ↦ c x) := by
  /- In each original common chart the symbol is the smooth local matrix
  of c, independent of frequency. Positive frequency derivatives vanish.
  On compact spatial subsets all derivatives of its finitely many matrix
  entries are bounded, giving exactly the order-zero estimates. Local
  ranks remain independent and may vary between separate components. -/
  classical
  intro d hd i j
  let P := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let W := EuclideanSpace ℂ (Fin (B.rank j))
  let Ω := atlasSymbolChartDomain A B d i j
  let a : P → V →L[ℂ] W := fun z ↦ atlasGlobalSymbolInChart A B (fun x _ ↦ c x) d i j z 0
  have hopen : IsOpen Ω := by
    simpa only [Ω, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      d.isOpen_inter_preimage_symm ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  -- The prescribed smooth local columns remain smooth after the actual inverse base chart.
  have hcolumn (k : Fin (A.rank i)) :
      ContDiffOn ℝ ∞ (fun z ↦ a z (EuclideanSpace.single k 1)) Ω := by
    let col (x : M) := if hx : x ∈ (A.chart i).baseSet then
      (B.chart j ⟨x, c x ((A.frameLinearEquiv i x hx).symm (Pi.single k 1))⟩).2 else 0
    let e := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
    have hcol : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞ col
        ((A.chart i).baseSet ∩ (B.chart j).baseSet) := hc.2 i j k
    have hcoord : ContDiffOn ℝ ∞ (fun z ↦ e.symm (col (d.symm z))) Ω := by
      intro z hz
      have hs := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
        |>.comp_contMDiffOn hcol
      have hi := contMDiffAt_symm_of_mem_maximalAtlas
        (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hd) hz.1.1
      exact (contMDiffAt_iff_contDiffAt.mp
        ((hs.contMDiffAt (((A.chart i).open_baseSet.inter
          (B.chart j).open_baseSet).mem_nhds ⟨hz.1.2, hz.2⟩)).comp z hi)).contDiffWithinAt
    apply hcoord.congr
    intro z hz
    have hzi : d.symm z ∈ (A.chart i).baseSet := hz.1.2
    have hzj : d.symm z ∈ (B.chart j).baseSet := hz.2
    have hsingle : (EuclideanSpace.equiv (Fin (A.rank i)) ℂ)
        (EuclideanSpace.single k 1) = Pi.single k 1 := rfl
    simp [a, atlasGlobalSymbolInChart, hzi, hzj, col, e, hsingle,
      SmoothComplexBundleAtlas.frameLinearEquiv, EuclideanSpace.single]
  -- Reconstruct the same local Hom map from its finite original-frame columns.
  have hs : ContDiffOn ℝ ∞ a Ω := by
    have hsum : ContDiffOn ℝ ∞
        (fun z ↦ ∑ k : Fin (A.rank i), (EuclideanSpace.proj (𝕜 := ℂ) k).smulRight
          (a z (EuclideanSpace.single k 1))) Ω := by
      apply ContDiffOn.sum
      intro k _
      exact ((ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj k)).restrictScalars
        ℝ).contDiff.comp_contDiffOn (hcolumn k)
    have heq : (fun z ↦ ∑ k : Fin (A.rank i), (EuclideanSpace.proj (𝕜 := ℂ) k).smulRight
        (a z (EuclideanSpace.single k 1))) = a := by
      funext z
      apply ContinuousLinearMap.ext
      intro v
      have hv : ∑ k : Fin (A.rank i), v k • EuclideanSpace.single k 1 = v := by
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).toBasis.sum_repr v
      simpa only [sum_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj,
        PiLp.proj_apply, ← map_smul, ← map_sum] using congrArg (a z) hv
    rwa [heq] at hsum
  have heq : atlasGlobalSymbolInChart A B (fun x _ ↦ c x) d i j = fun z _ ↦ a z := rfl
  rw [heq]
  refine ⟨hs.comp contDiffOn_fst (fun _ h ↦ h.1), ?_⟩
  intro K hK hcompact l k
  -- Positive frequency derivatives vanish; derivative order zero uses a compact bound.
  by_cases hk : k = 0
  · subst k
    have hderiv : ContinuousOn (iteratedFDeriv ℝ l a) Ω := by
      have h := hs.continuousOn_iteratedFDerivWithin (m := l) (by simp) hopen.uniqueDiffOn
      exact h.congr (fun z hz ↦ (iteratedFDerivWithin_of_isOpen _ hopen hz).symm)
    obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn (hderiv.mono hK).norm).bddAbove
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro x hx ξ
    have hn : ‖symbolDerivative (fun z _ ↦ a z) l 0 x ξ‖ =
        ‖iteratedFDeriv ℝ l a x‖ := by
      change ‖iteratedFDeriv ℝ l
        ((continuousMultilinearCurryFin0 ℝ P (V →L[ℂ] W)).symm ∘ a) x‖ = _
      exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _
    rw [hn]
    simpa only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one] using
      (hC ⟨x, hx, rfl⟩).trans (le_max_left C 0)
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx ξ
    simp [symbolDerivative, iteratedFDeriv_const_of_ne hk]

/-- The actual frequency-independent symbol of the original zero-order section action. -/
def atlasZeroOrderSymbol (c : ∀ x : M, E x →ₗ[ℂ] F x)
    (hc : IsSmoothAtlasBundleMap A B c) : atlasGlobalSymbolSpace A B 0 :=
  ⟨fun x _ ↦ c x, isAtlasGlobalSymbol_zeroOrder A B c hc⟩

variable [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC

/-- Compact base support permits finite actual Fourier pieces in any specified neighborhood. -/
theorem exists_atlas_supported_quantization_pieces {m : ℝ}
    (b : atlasGlobalSymbolSpace A B m) (K : Set M) (hK : IsCompact K)
    (hzero : ∀ x : M, x ∉ K → ∀ ξ, b.val x ξ = 0)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B m),
      (∑ j, (T j).globalSymbol) = b ∧
      ∃ L : Set M, IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
        (∀ j, (T j).chart.symm ''
          (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L) ∧
        HasAtlasSectionOperatorSupport A B L (∑ j, (T j).toLinearMap) := by
  /- Stage 1: cover only K by finitely many relatively compact common
  manifold/source-frame/target-frame neighborhoods inside U. A smooth
  finite partition sums to one near K. Choose compact output weights and
  nested input cutoffs equal to one near their output supports, retaining
  the two actual original frame indices and their independent local ranks.
  Stage 2: these are AtlasQuantizationPatch data. Apply toPiece to the
  original b in each patch; its operator is the actual quantizeSchwartz
  of its specified compact spatial coordinate symbol. The exact leading
  symbol formula is the output weight times b, not a full reduced-symbol
  identity that discards derivative corrections. The finite weights sum
  to one where b may be nonzero, giving the displayed symbol equality.
  Stage 3: the union of K and the finitely many original input and output
  support images is compact and lies in U. Each actual output vanishes
  off L, and an input supported away from L has zero localized input in
  every piece. Summing gives both support conditions on the original map.
  No finite covering of all M, global rank bound, finite CW hypothesis or
  compactness of M is used. Empty K and zero local ranks are included. -/
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  -- Choose one finite cover by the common source of the base chart and both frames.
  let c (x : K) := chartAt (EuclideanSpace ℝ (Fin n)) (x : M)
  choose e he using fun x : K ↦ A.covers (x : M)
  choose f hf using fun x : K ↦ B.covers (x : M)
  let O (x : K) := (((c x).source ∩ (A.chart (e x)).baseSet) ∩ (B.chart (f x)).baseSet) ∩ U
  have hopen (x : K) : IsOpen (O x) :=
    (((c x).open_source.inter (A.chart (e x)).open_baseSet).inter
      (B.chart (f x)).open_baseSet).inter hU
  have hxO (x : K) : (x : M) ∈ O x :=
    ⟨⟨⟨mem_chart_source _ (x : M), he x⟩,
      hf x⟩, hKU x.property⟩
  have hshrink (x : K) : ∃ V : Set M, IsOpen V ∧ (x : M) ∈ V ∧
      closure V ⊆ O x ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (x : M))) (hopen x) (Set.singleton_subset_iff.mpr (hxO x))
    exact ⟨V, hV, hxV (Set.mem_singleton _), hVO, hVc⟩
  choose V₀ hV₀ hxV₀ hV₀O hV₀c using hshrink
  have hcover : K ⊆ ⋃ x : K, V₀ x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV₀ ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V₀ hV₀ hcover
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := V₀ (index j)
  have hfinitecover : K ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hK.isClosed V
    (fun j ↦ hV₀ (index j)) hfinitecover
  have hρcompact (j : Fin s.card) : HasCompactSupport (ρ j) :=
    (hV₀c (index j)).of_isClosed_subset (isClosed_tsupport _) (fun x hx ↦
      subset_closure (hρ j hx))
  have hρO (j : Fin s.card) : tsupport (ρ j) ⊆ O (index j) :=
    fun x hx ↦ hV₀O (index j) (subset_closure (hρ j hx))
  -- Zero-extend each actual partition weight into its chosen Euclidean chart.
  let χ (j : Fin s.card) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if z ∈ (c (index j)).target then ρ j ((c (index j)).symm z) else 0
  let Kc (j : Fin s.card) := (c (index j)) '' tsupport (ρ j)
  have hKc (j : Fin s.card) : IsCompact (Kc j) :=
    (hρcompact j).image_of_continuousOn
      ((c (index j)).continuousOn.mono (fun x hx ↦ (hρO j hx).1.1.1))
  have hχ (j : Fin s.card) : tsupport (χ j) ⊆ Kc j := by
    apply closure_minimal ?_ (hKc j).isClosed
    intro z hz
    have ht : z ∈ (c (index j)).target := by
      by_contra ht
      exact hz (by simp [χ, ht])
    have hr : (c (index j)).symm z ∈ tsupport (ρ j) := by
      by_contra hr
      exact hz (by simp [χ, ht, image_eq_zero_of_notMem_tsupport hr])
    exact ⟨(c (index j)).symm z, hr, (c (index j)).right_inv ht⟩
  have hχcompact (j : Fin s.card) : HasCompactSupport (χ j) :=
    (hKc j).of_isClosed_subset (isClosed_tsupport _) (hχ j)
  have hχsmooth (j : Fin s.card) : ContDiff ℝ ∞ (χ j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ Kc j
    · obtain ⟨x, hx, rfl⟩ := hz
      have hxsource := (hρO j hx).1.1.1
      have ht := (c (index j)).map_source hxsource
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) (chart_mem_atlas _ ((index j : K) : M))) ht
      have hlocal := ((ρ j).contMDiff.contMDiffAt.comp _ hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [(c (index j)).open_target.mem_nhds ht] with y hy
      simp only [χ, ite_eq_left hy]
      rfl
    · -- The compact coordinate support is closed, so the same extension is locally zero outside it.
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hKc j).isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hχ j h))
  let D (j : Fin s.card) :=
    (c (index j)).target ∩ (c (index j)).symm ⁻¹'
      ((A.chart (e (index j))).baseSet ∩ (B.chart (f (index j))).baseSet ∩ U)
  have hD (j : Fin s.card) : IsOpen (D j) :=
    (c (index j)).continuousOn_symm.isOpen_inter_preimage (c (index j)).open_target
      ((A.chart (e (index j))).open_baseSet.inter (B.chart (f (index j))).open_baseSet |>.inter hU)
  have hKD (j : Fin s.card) : Kc j ⊆ D j := by
    rintro z ⟨x, hx, rfl⟩
    have hu := hρO j hx
    refine ⟨(c (index j)).map_source hu.1.1.1, ?_⟩
    change (c (index j)).symm ((c (index j)) x) ∈
      (A.chart (e (index j))).baseSet ∩ (B.chart (f (index j))).baseSet ∩ U
    rw [(c (index j)).left_inv hu.1.1.1]
    exact ⟨⟨hu.1.1.2, hu.1.2⟩, hu.2⟩
  -- Choose a genuine input plateau around the output support, still wholly inside U.
  have hinput (j : Fin s.card) :
      ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ D j ∧ ∃ W, IsOpen W ∧ tsupport (χ j) ⊆ W ∧
          ∀ z ∈ W, ψ z = 1 := by
    obtain ⟨W, hW, hKW, hWD, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure (hKc j) (hD j) (hKD j)
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
      chart_mem_atlas := chart_mem_atlas _ ((index j : K) : M)
      input :=
        { frameIndex := e (index j)
          cutoff := ψ j
          smooth_cutoff := hψsmooth j
          compact_support := hψcompact j
          support_subset := fun z hz ↦ ⟨(hψsupport j hz).1, (hψsupport j hz).2.1.1⟩ }
      output :=
        { frameIndex := f (index j)
          cutoff := χ j
          smooth_cutoff := hχsmooth j
          compact_support := hχcompact j
          support_subset := fun z hz ↦ ⟨(hKD j (hχ j hz)).1, (hKD j (hχ j hz)).2.1.2⟩ }
      output_nonneg := by
        intro z
        dsimp only [χ]
        split_ifs
        · exact ρ.nonneg _ _
        · exact le_rfl
      input_support_in_output_frame := fun z hz ↦ (hψsupport j hz).2.1.2
      output_support_in_input_frame := fun z hz ↦ (hKD j (hχ j hz)).2.1.1
      input_eq_one := hψone j }
  -- The same weights are recovered exactly, including the zero branch off each chart.
  have hweight (x : M) (j : Fin s.card) : (patch j).weight x = ρ j x := by
    by_cases hx : x ∈ (c (index j)).source
    · simp only [AtlasQuantizationPatch.weight, patch, ite_eq_left hx, χ,
        ite_eq_left ((c (index j)).map_source hx), (c (index j)).left_inv hx]
    · have hzero : ρ j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρO j h).1.1.1)
      simp only [AtlasQuantizationPatch.weight, patch, ite_eq_right hx, hzero]
  let T (j : Fin s.card) := (patch j).toPiece b
  have hsum : (∑ j, (T j).globalSymbol) = b := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (∑ j, ((patch j).toPiece b).globalSymbolFunction) = b.val
    funext x ξ
    simp only [Finset.sum_apply, AtlasQuantizationPatch.globalSymbolFunction_toPiece, hweight]
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← Complex.ofReal_sum]
      have hsum : ∑ j, ρ j x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, Complex.ofReal_one, one_smul]
    · simp [hzero x hx ξ]
  -- The same finite union controls both actual cutoffs and contains the original compact set.
  let C := ⋃ j : Fin s.card, (c (index j)).symm ''
    (tsupport (ψ j) ∪ tsupport (χ j))
  have hsupports (j : Fin s.card) :
      tsupport (ψ j) ∪ tsupport (χ j) ⊆ D j := by
    intro z hz
    exact hz.elim (fun h ↦ hψsupport j h) (fun h ↦ hKD j (hχ j h))
  have hC : IsCompact C := by
    apply isCompact_iUnion
    intro j
    exact ((hψcompact j).union (hχcompact j)).image_of_continuousOn
      ((c (index j)).continuousOn_symm.mono (fun z hz ↦ (hsupports j hz).1))
  have hCU : C ⊆ U := by
    intro x hx
    obtain ⟨j, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    exact (hsupports j hz).2.2
  let L := K ∪ C
  have hL : IsCompact L := hK.union hC
  have hTL (j : Fin s.card) : (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L := by
    exact (Set.subset_iUnion (fun j : Fin s.card ↦ (c (index j)).symm ''
      (tsupport (ψ j) ∪ tsupport (χ j))) j).trans subset_union_right
  have houtput (u : A.smoothSections) (x : M) (hx : x ∉ L) :
      ((∑ j, (T j).toLinearMap) u).val x = 0 := by
    rw [LinearMap.sum_apply]
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply ((T j).output.extendedFunction_properties (T j).chart_mem_atlas _).2
    intro hx'
    exact hx (hTL j (Set.image_mono subset_union_right hx'))
  refine ⟨s.card, T, hsum, L, hL, subset_union_left, union_subset hKU hCU, hTL, ?_, ?_⟩
  · intro u
    apply closure_minimal ?_ hL.isClosed
    intro x hx
    by_contra hxL
    exact hx (houtput u x hxL)
  · intro u hu
    have hinput (j : Fin s.card) : (T j).input.localize (T j).chart_mem_atlas u = 0 := by
      apply DFunLike.ext
      intro z
      change (T j).input.localizedFunction u z = 0
      by_cases hz : z ∈ tsupport (T j).input.cutoff
      · have hxL : (T j).chart.symm z ∈ L := hTL j ⟨z, Or.inl hz, rfl⟩
        have huzero : u.val ((T j).chart.symm z) = 0 := by
          by_contra hne
          exact Set.disjoint_left.mp hu (subset_closure hne) hxL
        have hfzero : ((A.chart (T j).input.frameIndex)
            ⟨(T j).chart.symm z, (0 : E _)⟩).2 = 0 :=
          (A.frameLinearEquiv (T j).input.frameIndex _
            ((T j).input.support_subset hz).2).map_zero
        simp [AtlasChartCutoff.localizedFunction, atlasSectionInChart, huzero, hfzero]
      · simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    change (T j).output.extendLinearMap (T j).chart_mem_atlas
      ((T j).operator ((T j).input.localize (T j).chart_mem_atlas u)) = 0
    rw [hinput, map_zero, map_zero]

/-- The principal class is independent of the finite Fourier presentation of the same map. -/
theorem atlasRelativePrincipalSymbol_independent
    (c d : ∀ x : M, E x →ₗ[ℂ] F x)
    (hc : IsSmoothAtlasBundleMap A B c) (hd : IsSmoothAtlasBundleMap A B d)
    (N L : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B 0)
    (S : Fin L → AtlasPseudodifferentialPiece A B 0)
    (h : atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap =
      atlasSmoothSectionMap A B d hd + ∑ j, (S j).toLinearMap) :
    atlasGlobalPrincipalSymbolClass A B 0
        (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol) =
      atlasGlobalPrincipalSymbolClass A B 0
        (atlasZeroOrderSymbol A B d hd + ∑ j, (S j).globalSymbol) := by
  classical
  -- A common compact plateau handles the finite family on a possibly noncompact base.
  have hcommon {m : ℝ} {ι : Type} [Finite ι]
      (J : ι → AtlasPseudodifferentialPiece A B m)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : A.Index) (f : B.Index)
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ atlasSymbolChartDomain A B c e f) :
      ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
        (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
        D₀.frameIndex = e ∧ K₀.frameIndex = f ∧
        HasCompactSupport χ ∧
        tsupport χ ⊆ c.source ∩ (A.chart e).baseSet ∩ (B.chart f).baseSet ∧
        D₀.cutoff = K₀.cutoff ∧ (∀ y ∈ c '' tsupport χ, D₀.cutoff y = 1) ∧
        ∃ (V : Set (EuclideanSpace ℝ (Fin n)))
          (p : ι → SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)),
          IsOpen V ∧ z ∈ V ∧ V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
            (∀ y ∈ V, χ (c.symm y) = 1) ∧
            (∀ j, IsSymbol Set.univ m (p j)) ∧
            (∀ j, IsSymbol V (m - 1) (p j - atlasGlobalSymbolInChart A B
              (J j).globalSymbolFunction c D₀.frameIndex K₀.frameIndex)) ∧
            ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
                EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
              quantize (p j) u y = K₀.localize hc
                (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
                  ((J j).toLinearMap
                    (atlasSectionMul A (fun x ↦ (χ x : ℂ))
                      (Complex.ofRealCLM.contMDiff.comp hχ) (D₀.extend hc u)))) y := by
    classical
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n)) M
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let x := c.symm z
    let D := c.source ∩ (A.chart e).baseSet ∩ (B.chart f).baseSet
    let D' (j : ι) := (J j).chart.source ∩ (A.chart (J j).input.frameIndex).baseSet ∩
      (B.chart (J j).output.frameIndex).baseSet
    let K (j : ι) := (J j).chart.symm ''
      (tsupport (J j).output.cutoff ∪ tsupport (J j).input.cutoff)
    have hK (j : ι) : IsCompact (K j) :=
      ((J j).output.compact_support.union (J j).input.compact_support).image_of_continuousOn
        ((J j).chart.continuousOn_symm.mono (by
          intro y hy
          rcases hy with hy | hy
          · exact ((J j).output.support_subset hy).1
          · exact ((J j).input.support_subset hy).1))
    have hKD (j : ι) : K j ⊆ D' j := by
      rintro y ⟨w, hw, rfl⟩
      rcases hw with hw | hw
      · exact ⟨⟨(J j).chart.map_target ((J j).output.support_subset hw).1,
          (J j).output_support_in_input_frame hw⟩, ((J j).output.support_subset hw).2⟩
      · exact ⟨⟨(J j).chart.map_target ((J j).input.support_subset hw).1,
          ((J j).input.support_subset hw).2⟩, (J j).input_support_in_output_frame hw⟩
    -- One finite intersection handles every active piece and removes every inactive piece.
    let W' (j : ι) := if x ∈ K j then D' j else (K j)ᶜ
    have hW' (j : ι) : IsOpen (W' j) := by
      by_cases hj : x ∈ K j
      · simpa only [W', ite_eq_left hj] using
          (((J j).chart.open_source.inter (A.chart (J j).input.frameIndex).open_baseSet).inter
            (B.chart (J j).output.frameIndex).open_baseSet)
      · simpa only [W', ite_eq_right hj] using (hK j).isClosed.isOpen_compl
    have hxW' (j : ι) : x ∈ W' j := by
      by_cases hj : x ∈ K j
      · simpa only [W', ite_eq_left hj] using hKD j hj
      · simpa only [W', ite_eq_right hj, mem_compl_iff] using hj
    let W := D ∩ ⋂ j, W' j
    have hW : IsOpen W :=
      ((c.open_source.inter (A.chart e).open_baseSet).inter (B.chart f).open_baseSet).inter
      (isOpen_iInter_of_finite hW')
    have hxW : x ∈ W := ⟨⟨⟨c.map_target hz.1.1, hz.1.2⟩, hz.2⟩, mem_iInter.mpr hxW'⟩
    obtain ⟨C, hC, hxC, hCW⟩ := exists_compact_subset hW hxW
    obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (n := ⊤) isClosed_singleton
      (show ({x} : Set M) ⊆ interior C from singleton_subset_iff.mpr hxC)
    have hχC : tsupport χ ⊆ C := by
      apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra hyC
      exact hy (hχzero y hyC)
    have hcχ : HasCompactSupport χ := hC.of_isClosed_subset (isClosed_tsupport _) hχC
    have hχW : tsupport χ ⊆ W := hχC.trans hCW
    have hχD : tsupport χ ⊆ D := hχW.trans inter_subset_left
    have hxOne : x ∈ interior {y | χ y = 1} := by
      apply mem_interior_iff_mem_nhds.mpr
      change ∀ᶠ y in nhds x, χ y = 1
      simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hχone
    let T := c.target ∩ c.symm ⁻¹' W
    have hT : IsOpen T := c.isOpen_inter_preimage_symm hW
    have himage : c '' tsupport χ ⊆ T := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hχD hy).1.1, by
        change c.symm (c y) ∈ W
        rw [c.left_inv (hχD hy).1.1]
        exact hχW hy⟩
    have hcimage : IsCompact (c '' tsupport χ) := hcχ.image_of_continuousOn
      (c.continuousOn.mono (fun y hy ↦ (hχD hy).1.1))
    -- The common chart cutoff is one near the entire new support and remains in W.
    obtain ⟨O, hOo, hKO, hOT, hOc⟩ :=
      exists_open_between_and_isCompact_closure hcimage hT himage
    obtain ⟨O', hO'o, hOO', hO'T, hO'c⟩ :=
      exists_open_between_and_isCompact_closure hOc hT hOT
    obtain ⟨ρ, hρ, _, hsρ, honeρ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
    have hρsupport : tsupport ρ = closure O' := congrArg closure hsρ
    have hcρ : HasCompactSupport ρ := by simpa [HasCompactSupport, hρsupport] using hO'c
    have hρT : tsupport ρ ⊆ T := by rwa [hρsupport]
    have hρone : c '' tsupport χ ⊆ interior {y | ρ y = 1} := by
      intro y hy
      apply mem_interior.mpr
      refine ⟨O, ?_, hOo, hKO hy⟩
      intro w hw
      exact (honeρ w).mp (subset_closure hw)
    let D₀ : AtlasChartCutoff A c :=
      { frameIndex := e
        cutoff := ρ
        smooth_cutoff := hρ
        compact_support := hcρ
        support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.1.2⟩ }
    let K₀ : AtlasChartCutoff B c :=
      { frameIndex := f
        cutoff := ρ
        smooth_cutoff := hρ
        compact_support := hcρ
        support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.2⟩ }
    let V := c.target ∩ c.symm ⁻¹' (W ∩ interior {y | χ y = 1})
    have hV : IsOpen V := c.isOpen_inter_preimage_symm (hW.inter isOpen_interior)
    have hzV : z ∈ V := ⟨hz.1.1, hxW, hxOne⟩
    have hVU : V ⊆ atlasSymbolChartDomain A B c e f :=
      fun y hy ↦ ⟨⟨hy.1, hy.2.1.1.1.2⟩, hy.2.1.1.2⟩
    let Tin := atlasSectionMul A (fun y ↦ (χ y : ℂ))
      (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
    let Tout := atlasSectionMul B (fun y ↦ (χ y : ℂ))
      (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
    -- Absorb the same global cutoff into the existing input and output coordinate cutoffs.
    have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ atlas X M)
        (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
        ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      by_cases hy : y ∈ tsupport a
      · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) (hs hy)
        exact ha.contDiffAt.mul ((χ.contMDiff.contMDiffAt.comp y hchart).contDiffAt)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    let input (j : ι) : AtlasChartCutoff A (J j).chart :=
      { (J j).input with
        cutoff := fun y ↦ (J j).input.cutoff y * χ ((J j).chart.symm y)
        smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).input.smooth_cutoff
          (fun y hy ↦ ((J j).input.support_subset hy).1)
        compact_support := (J j).input.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans (J j).input.support_subset }
    let output (j : ι) : AtlasChartCutoff B (J j).chart :=
      { (J j).output with
        cutoff := fun y ↦ (J j).output.cutoff y * χ ((J j).chart.symm y)
        smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).output.smooth_cutoff
          (fun y hy ↦ ((J j).output.support_subset hy).1)
        compact_support := (J j).output.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans (J j).output.support_subset }
    let R (j : ι) : AtlasPseudodifferentialPiece A B m :=
      { J j with
        input := input j
        output := output j
        input_support_in_output_frame :=
          tsupport_mul_subset_left.trans (J j).input_support_in_output_frame
        output_support_in_input_frame :=
          tsupport_mul_subset_left.trans (J j).output_support_in_input_frame }
    have hinput (j : ι) (u : A.smoothSections) :
        (input j).localize (J j).chart_mem_atlas u =
          (J j).input.localize (J j).chart_mem_atlas (Tin u) := by
      apply DFunLike.ext
      intro y
      by_cases hy : y ∈ tsupport (J j).input.cutoff
      · have hyc := ((J j).input.support_subset hy).1
        have hyf := ((J j).input.support_subset hy).2
        change (input j).localizedFunction u y = (J j).input.localizedFunction (Tin u) y
        simp only [AtlasChartCutoff.localizedFunction, hyc, ↓reduceIte]
        dsimp only [input]
        change _ = ((J j).input.cutoff y : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank (J j).input.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv (J j).input.frameIndex ((J j).chart.symm y) hyf)
              ((χ ((J j).chart.symm y) : ℂ) • u.val ((J j).chart.symm y)))
        rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
        rfl
      · simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
          input, image_eq_zero_of_notMem_tsupport hy]
    have houtput (j : ι)
        (v : 𝓢(X, EuclideanSpace ℂ (Fin (B.rank (J j).output.frameIndex)))) :
        (output j).extend (J j).chart_mem_atlas v =
          Tout ((J j).output.extend (J j).chart_mem_atlas v) := by
      apply Subtype.ext
      funext y
      change (output j).extendedFunction v y = (χ y : ℂ) • (J j).output.extendedFunction v y
      by_cases hy : y ∈ (J j).chart.source ∩ (B.chart (J j).output.frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, output, dite_eq_left hy]
        rw [(J j).chart.left_inv hy.1, Complex.ofReal_mul, smul_smul, mul_comm]
      · simp [AtlasChartCutoff.extendedFunction, output, hy]
    have hpiece (j : ι) : (R j).toLinearMap = Tout.comp ((J j).toLinearMap.comp Tin) := by
      apply LinearMap.ext
      intro u
      change (output j).extend (J j).chart_mem_atlas
        ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = _
      rw [hinput, houtput]
      rfl
    have hproductSupport (d : OpenPartialHomeomorph M X) (a : X → ℝ)
        (hs : tsupport a ⊆ d.target) :
        d.symm '' tsupport (fun y ↦ a y * χ (d.symm y)) ⊆ tsupport χ := by
      rintro _ ⟨y, hy, rfl⟩
      by_contra hout
      have hy' : y ∈ d.target := hs (tsupport_mul_subset_left hy)
      have hzero := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
        (d.continuousOn_symm.continuousAt (d.open_target.mem_nhds hy'))
      have hprod : (fun w ↦ a w * χ (d.symm w)) =ᶠ[nhds y] 0 := by
        filter_upwards [hzero] with w hw
        simp only [Function.comp_def, Pi.zero_apply] at hw
        simp [hw]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hy
    have hRsupp (j : ι) : (R j).chart.symm ''
        (tsupport (R j).output.cutoff ∪ tsupport (R j).input.cutoff) ⊆ tsupport χ := by
      rw [image_union]
      apply union_subset
      · exact hproductSupport _ _ (fun y hy ↦ ((J j).output.support_subset hy).1)
      · exact hproductSupport _ _ (fun y hy ↦ ((J j).input.support_subset hy).1)
    have hglobal (j : ι) (y : M) (hy : χ y = 1) (ξ) :
        (R j).globalSymbolFunction y ξ = (J j).globalSymbolFunction y ξ := by
      unfold AtlasPseudodifferentialPiece.globalSymbolFunction
      dsimp only [R, input, output]
      split_ifs with hdomain
      · rw [(J j).chart.left_inv hdomain.1.1, hy]
        simp
      · rfl
    -- Equality on an open set retains the complete mixed-derivative symbol estimates.
    have congrSymbol (a b : SymbolFunction n (A.rank e) (B.rank f)) (ha : IsSymbol V (m - 1) a)
        (hab : ∀ y ∈ V, ∀ η, a y η = b y η) : IsSymbol V (m - 1) b := by
      refine ⟨ha.1.congr (fun w hw ↦ (hab w.1 hw.1 w.2).symm), ?_⟩
      intro C hCV hC i j
      obtain ⟨K₀, hB, hbound⟩ := ha.2 C hCV hC i j
      refine ⟨K₀, hB, fun y hy η ↦ ?_⟩
      have hnear : (fun w ↦ iteratedFDeriv ℝ j (a w) η) =ᶠ[nhds y]
          (fun w ↦ iteratedFDeriv ℝ j (b w) η) := by
        filter_upwards [hV.mem_nhds (hCV hy)] with w hw
        rw [funext (hab w hw)]
      change ‖iteratedFDeriv ℝ i _ y‖ ≤ _
      rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
      exact hbound y hy η
    have hsymbols (j : ι) : ∃ p : SymbolFunction n (A.rank e) (B.rank f), IsSymbol Set.univ m p ∧
        IsSymbol V (m - 1) (p - atlasGlobalSymbolInChart A B (J j).globalSymbolFunction c e f) ∧
        ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank e)))) y,
          quantize p u y = K₀.localize hc (Tout ((J j).toLinearMap (Tin (D₀.extend hc u)))) y := by
      by_cases hj : x ∈ K j
      · have hactive : W ⊆ D' j := by
          intro y hy
          simpa only [W', ite_eq_left hj] using mem_iInter.mp hy.2 j
        obtain ⟨p, hp, hpaction, hplower⟩ := (R j).exists_localized_symbol c hc D₀ K₀ rfl
          ((hRsupp j).trans hχD)
          ((image_mono (hRsupp j)).trans hρone)
          (fun y hy ↦ hactive (hρT hy).2)
        refine ⟨p, hp, ?_, ?_⟩
        · apply congrSymbol _ _ (hplower.restrict (fun y hy ↦ ⟨hVU hy, hactive hy.2.1⟩))
          intro y hy η
          have hχy : χ (c.symm y) = 1 := by
            have hmem : c.symm y ∈ {w | χ w = 1} := interior_subset hy.2.2
            exact hmem
          simp only [Pi.sub_apply, atlasGlobalSymbolInChart, hglobal j _ hχy]
          rfl
        · intro u y
          rw [hpaction, hpiece]
          rfl
      · have hzeroInput : (input j).cutoff = 0 := by
          funext y
          by_cases hy : (J j).input.cutoff y = 0
          · simp [input, hy]
          · have hyK : (J j).chart.symm y ∈ K j :=
              ⟨y, Or.inr (subset_tsupport _ hy), rfl⟩
            have hχy : χ ((J j).chart.symm y) = 0 :=
              image_eq_zero_of_notMem_tsupport (by
                intro hyχ
                have hnot := mem_iInter.mp (hχW hyχ).2 j
                exact (show (J j).chart.symm y ∉ K j by
                  simpa only [W', ite_eq_right hj, mem_compl_iff] using hnot) hyK)
            simp [input, hχy]
        have hRzero : (R j).toLinearMap = 0 := by
          apply LinearMap.ext
          intro u
          have hin : (input j).localize (J j).chart_mem_atlas u = 0 := by
            apply SchwartzMap.ext
            intro y
            change (input j).localizedFunction u y = 0
            simp [AtlasChartCutoff.localizedFunction, hzeroInput]
          change (output j).extendLinearMap (J j).chart_mem_atlas
            ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = 0
          rw [hin, map_zero, map_zero]
        refine ⟨0, isSymbol_zero _ _, ?_, ?_⟩
        · apply congrSymbol 0 _ (isSymbol_zero _ _)
          intro y hy η
          have hyK : c.symm y ∉ K j := by
            simpa only [W', ite_eq_right hj, mem_compl_iff] using mem_iInter.mp hy.2.1.2 j
          have hzero (ξ) : (J j).globalSymbolFunction (c.symm y) ξ = 0 := by
            by_cases hvalid : c.symm y ∈ D' j
            · have hcut : (J j).chart (c.symm y) ∉ tsupport (J j).output.cutoff := by
                intro hmem
                exact hyK ⟨(J j).chart (c.symm y), Or.inl hmem,
                  (J j).chart.left_inv hvalid.1.1⟩
              simp [AtlasPseudodifferentialPiece.globalSymbolFunction, D', hvalid,
                image_eq_zero_of_notMem_tsupport hcut]
            · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, D', hvalid]
          simp [atlasGlobalSymbolInChart, hzero]
        · intro u y
          change quantize 0 u y = K₀.localize hc
            ((Tout.comp ((J j).toLinearMap.comp Tin)) (D₀.extend hc u)) y
          rw [← hpiece, hRzero]
          change quantize 0 u y = (K₀.localizeLinearMap hc) 0 y
          simp [quantize]
    choose p hp hplower hpaction using hsymbols
    refine ⟨χ, χ.contMDiff, D₀, K₀, rfl, rfl, hcχ, hχD, rfl, ?_,
      V, p, hV, hzV, hVU, ?_, hp, hplower, hpaction⟩
    · intro y hy
      exact (interior_subset (s := {y | ρ y = 1})) (hρone hy)
    · intro y hy
      exact (interior_subset (s := {y | χ y = 1})) hy.2.2
  -- The original pointwise map supplies the exact localized multiplication symbol.
  have hzeroOrder
      (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
      (a : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (ha : a ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (D : AtlasChartCutoff A a) (K : AtlasChartCutoff B a)
      (hDK : D.cutoff = K.cutoff)
      (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
      let Ω := atlasSymbolChartDomain A B a D.frameIndex K.frameIndex
      let ψ := fun y ↦ (D.cutoff y * χ (a.symm y)) ^ 2
      let p := zeroExtendedSymbol Ω ψ (atlasGlobalSymbolInChart A B (fun x _ ↦ c x)
        a D.frameIndex K.frameIndex)
      IsSymbol Set.univ 0 p ∧ ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n),
          EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) y,
        quantize p u y = K.localize ha
          (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
            (atlasSmoothSectionMap A B c hc
              (atlasSectionMul A (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
                (D.extend ha u)))) y := by
    classical
    let X := EuclideanSpace ℝ (Fin n)
    let Ω := atlasSymbolChartDomain A B a D.frameIndex K.frameIndex
    let w := fun y ↦ D.cutoff y * χ (a.symm y)
    let ψ := fun y ↦ (w y) ^ 2
    let p := zeroExtendedSymbol Ω ψ (atlasGlobalSymbolInChart A B (fun x _ ↦ c x)
      a D.frameIndex K.frameIndex)
    have hΩ : IsOpen Ω := isOpen_atlasSymbolChartDomain A B a D.frameIndex K.frameIndex
    have hDΩ : tsupport D.cutoff ⊆ Ω := by
      intro y hy
      have hyK : y ∈ tsupport K.cutoff := by rwa [← hDK]
      exact ⟨D.support_subset hy, (K.support_subset hyK).2⟩
    have hw : ContDiff ℝ ∞ w := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      by_cases hy : y ∈ tsupport D.cutoff
      · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) ha)
            (D.support_subset hy).1
        exact D.smooth_cutoff.contDiffAt.mul ((hχ.contMDiffAt.comp y hchart).contDiffAt)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport D.cutoff).isOpen_compl.mem_nhds hy] with z hz
        simp [w, image_eq_zero_of_notMem_tsupport hz]
    have hwD : tsupport w ⊆ tsupport D.cutoff := tsupport_mul_subset_left
    have hψD : tsupport ψ ⊆ tsupport D.cutoff := by
      simpa only [ψ, pow_two] using
        (tsupport_mul_subset_left (f := w) (g := w)).trans hwD
    have hp : IsSymbol Set.univ 0 p :=
      isSymbol_zeroExtendedSymbol Ω hΩ 0 ψ (hw.pow 2)
        (D.compact_support.of_isClosed_subset isClosed_closure hψD) (hψD.trans hDΩ)
        _ ((isAtlasGlobalSymbol_zeroOrder A B c hc) a ha D.frameIndex K.frameIndex)
    have hconst (y η : X) : p y η = p y 0 := rfl
    have hcoeff : ContDiffOn ℝ ∞ (fun y ↦ p y 0) Set.univ := by
      have hp' : ContDiff ℝ ∞ (Function.uncurry p) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
      exact (hp'.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
    let Q : CoordinateDifferentialOperator n (A.rank D.frameIndex)
        (B.rank K.frameIndex) 0 Set.univ :=
      { coefficient := fun _ _ y ↦ p y 0
        smooth_coefficient := fun _ _ ↦ hcoeff }
    have hQ : Q.totalSymbol = p := by
      funext y η
      simp [CoordinateDifferentialOperator.totalSymbol, Q, hconst]
    have hquant (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) (y : X) :
        quantize p u y = p y 0 (u y) := by
      rw [← hQ, Q.quantize_totalSymbol]
      simp [CoordinateDifferentialOperator.apply, CoordinateDifferentialOperator.totalSymbol, Q]
    refine ⟨hp, ?_⟩
    intro u y
    rw [hquant]
    by_cases hy : y ∈ Ω
    · have hyA : a.symm y ∈ (A.chart D.frameIndex).baseSet := hy.1.2
      have hyB : a.symm y ∈ (B.chart K.frameIndex).baseSet := hy.2
      have hyS := a.map_target hy.1.1
      have hBchart (v : F (a.symm y)) :
          ((B.chart K.frameIndex) ⟨a.symm y, v⟩).2 =
            B.frameLinearEquiv K.frameIndex (a.symm y) hyB v := rfl
      simp only [p, zeroExtendedSymbol_apply_of_mem _ _ _ _ _ hy]
      simp only [mul_pow, Complex.ofReal_mul, Complex.ofReal_pow, atlasGlobalSymbolInChart,
        hyA, hyB, and_self, ↓reduceDIte, ContinuousLinearEquiv.toLinearEquiv_symm,
        smul_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.coe_symm_toLinearEquiv, PiLp.continuousLinearEquiv_symm_apply,
        AtlasChartCutoff.localize, atlasSectionMul, Complex.coe_smul, atlasSmoothSectionMap,
        AtlasChartCutoff.extend, LinearMap.coe_mk, AddHom.coe_mk, AtlasChartCutoff.extendedFunction,
        mem_inter_iff, smul_dite, smul_smul, smul_zero, HasCompactSupport.toSchwartzMap_toFun,
        AtlasChartCutoff.localizedFunction, hy.1.1, ↓reduceIte, ← hDK, atlasSectionInChart,
        hyS, a.right_inv hy.1.1, LinearMap.map_smul_of_tower, hBchart, ψ, w]
      have hsmul (t : ℂ) (v : F (a.symm y)) :
          B.frameLinearEquiv K.frameIndex (a.symm y) hyB (t • v) =
            t • B.frameLinearEquiv K.frameIndex (a.symm y) hyB v :=
        (B.frameLinearEquiv K.frameIndex (a.symm y) hyB).map_smul t v
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [hsmul, WithLp.toLp_smul]
      simp only [smul_smul]
      push_cast
      module
    · have hDzero : D.cutoff y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hDΩ h))
      have hKzero : K.cutoff y = 0 := by rw [← hDK, hDzero]
      simp [p, zeroExtendedSymbol, hy, AtlasChartCutoff.localize,
        AtlasChartCutoff.localizedFunction, hKzero]
  rw [atlasGlobalPrincipalSymbolClass_eq_iff]
  intro a ha e f
  let X := EuclideanSpace ℝ (Fin n)
  let Ω := atlasSymbolChartDomain A B a e f
  have hΩ : IsOpen Ω := isOpen_atlasSymbolChartDomain A B a e f
  apply IsSymbol.of_locally hΩ
  intro z hz
  -- Localize the same finite family and original bundle-map terms by one common plateau.
  let J : Fin N ⊕ Fin L → AtlasPseudodifferentialPiece A B 0 := Sum.elim T S
  obtain ⟨χ, hχ, D, K, rfl, rfl, _, _, hDK, hDone, V, p, hV, hzV, hVΩ,
    hχone, hp, hplower, hpaction⟩ :=
    hcommon J a ha e f z hz
  let r := A.rank D.frameIndex
  let q := B.rank K.frameIndex
  let ψ := fun y ↦ (D.cutoff y * χ (a.symm y)) ^ 2
  let q₀ (b : ∀ x : M, E x →ₗ[ℂ] F x) := zeroExtendedSymbol
    (atlasSymbolChartDomain A B a D.frameIndex K.frameIndex) ψ
    (atlasGlobalSymbolInChart A B (fun x _ ↦ b x) a D.frameIndex K.frameIndex)
  have hqc := hzeroOrder c hc a ha D K hDK χ hχ
  have hqd := hzeroOrder d hd a ha D K hDK χ hχ
  let qc : symbolSpace Set.univ isOpen_univ 0 r q := ⟨q₀ c, hqc.1⟩
  let qd : symbolSpace Set.univ isOpen_univ 0 r q := ⟨q₀ d, hqd.1⟩
  let ps (j : Fin N ⊕ Fin L) : symbolSpace Set.univ isOpen_univ 0 r q := ⟨p j, hp j⟩
  let b : symbolSpace Set.univ isOpen_univ 0 r q :=
    (qc + ∑ j : Fin N, ps (Sum.inl j)) - (qd + ∑ j : Fin L, ps (Sum.inr j))
  -- Every symbol integral is absolutely convergent before addition or subtraction is used.
  have hInt (a₀ : SymbolFunction n r q) (ha₀ : IsSymbol Set.univ 0 a₀)
      (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        a₀ x ξ (fourierSG u ξ)) := by
    let Er := EuclideanSpace ℂ (Fin r)
    let Eq := EuclideanSpace ℂ (Fin q)
    have hg : (a₀ x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry a₀) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha₀.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := ha₀.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈0 - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have hbound' := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hbound'
        apply hbound'.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : X ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let d₀ : X ≃L[ℝ] X :=
      (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d₀ (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (Er →L[ℂ] Eq)).flip (hphase.smul hg) w).integrable
  have hbzero : b.val = 0 := by
    apply symbol_eq_of_quantize_eq 0 0 b.val 0 b.property (isSymbol_zero Set.univ 0)
    intro u y
    let Q : symbolSpace Set.univ isOpen_univ 0 r q →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
      { toFun := fun a₀ ↦ quantize a₀.val u y
        map_add' := by
          intro a₀ b₀
          simp only [quantize, Submodule.coe_add, Pi.add_apply, add_apply, smul_add]
          rw [integral_add (hInt a₀.val a₀.property u y) (hInt b₀.val b₀.property u y), smul_add]
        map_smul' := by
          intro t a₀
          simp only [quantize, Submodule.coe_smul, Pi.smul_apply, smul_apply,
            RingHom.id_apply, smul_comm (Complex.exp _), integral_smul]
          exact smul_comm _ _ _ }
    have hQ : Q b = (Q qc + ∑ j : Fin N, Q (ps (Sum.inl j))) -
        (Q qd + ∑ j : Fin L, Q (ps (Sum.inr j))) := by
      simp only [b, map_sub, map_add, map_sum]
    change Q b = quantize 0 u y
    rw [hQ]
    have hlocal (v : B.smoothSections) : K.localizeLinearMap ha v = K.localize ha v := rfl
    have haction := congrArg (fun R : A.smoothSections →ₗ[ℂ] B.smoothSections ↦
      K.localizeLinearMap ha
        (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
          (R (atlasSectionMul A (fun x ↦ (χ x : ℂ))
            (Complex.ofRealCLM.contMDiff.comp hχ) (D.extend ha u)))) y) h
    have hqcact : Q qc = K.localize ha
        (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
          (atlasSmoothSectionMap A B c hc
            (atlasSectionMul A (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
              (D.extend ha u)))) y := hqc.2 u y
    have hqdact : Q qd = K.localize ha
        (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
          (atlasSmoothSectionMap A B d hd
            (atlasSectionMul A (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
              (D.extend ha u)))) y := hqd.2 u y
    have hpact (j : Fin N ⊕ Fin L) : Q (ps j) = K.localize ha
        (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
          ((J j).toLinearMap
            (atlasSectionMul A (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
              (D.extend ha u)))) y := hpaction j u y
    simp only [quantize, Pi.zero_apply, zero_apply, smul_zero, integral_zero]
    apply sub_eq_zero.mpr
    rw [hqcact, hqdact]
    simp_rw [hpact]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
      add_apply, sum_apply] at haction
    simpa only [hlocal, J, Sum.elim_inl, Sum.elim_inr] using haction
  -- On the plateau, the localized multiplier is precisely the original zero-order symbol.
  have hq₀ (a₀ : ∀ x : M, E x →ₗ[ℂ] F x) (y : X) (hy : y ∈ V) (η : X) :
      q₀ a₀ y η = atlasGlobalSymbolInChart A B (fun x _ ↦ a₀ x)
        a D.frameIndex K.frameIndex y η := by
    have hyΩ := hVΩ hy
    have hχmem : a.symm y ∈ tsupport χ := by
      apply subset_closure
      rw [Function.mem_support, hχone y hy]
      exact one_ne_zero
    have hD : D.cutoff y = 1 := hDone y ⟨a.symm y, hχmem, a.right_inv hyΩ.1.1⟩
    simp only [q₀, zeroExtendedSymbol_apply_of_mem _ _ _ _ _ hyΩ, ψ, hD,
      hχone y hy, one_mul, one_pow, Complex.ofReal_one, one_smul]
  let g : SymbolFunction n r q := atlasGlobalSymbolInChart A B
    ((atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol).val -
      (atlasZeroOrderSymbol A B d hd + ∑ j, (S j).globalSymbol).val)
      a D.frameIndex K.frameIndex
  have hrem : IsSymbol V (0 - 1) (b.val - g) := by
    have hh : IsSymbol V (0 - 1)
        ((∑ j : Fin N, (p (Sum.inl j) -
          atlasGlobalSymbolInChart A B (J (Sum.inl j)).globalSymbolFunction a
            D.frameIndex K.frameIndex)) -
        ∑ j : Fin L, (p (Sum.inr j) -
          atlasGlobalSymbolInChart A B (J (Sum.inr j)).globalSymbolFunction a
            D.frameIndex K.frameIndex)) :=
      (symbolSpace V hV (0 - 1) r q).sub_mem
      ((symbolSpace V hV (0 - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inl j)))
      ((symbolSpace V hV (0 - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inr j)))
    apply hh.congr_on hV
    intro y hy
    funext η
    have hframes : a.symm y ∈ (A.chart D.frameIndex).baseSet ∧
        a.symm y ∈ (B.chart K.frameIndex).baseSet := ⟨(hVΩ hy).1.2, (hVΩ hy).2⟩
    simp only [b, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_sum, qc, qd, ps,
      Pi.sub_apply, Pi.add_apply, Finset.sum_apply]
    rw [hq₀ c y hy η, hq₀ d y hy η]
    ext v
    simp [g, J, atlasGlobalSymbolInChart, AtlasPseudodifferentialPiece.globalSymbol,
      atlasZeroOrderSymbol, Finset.sum_sub_distrib, hframes]
    abel
  have hbLower : IsSymbol V (0 - 1) b.val := by
    rw [hbzero]
    exact isSymbol_zero V (0 - 1)
  refine ⟨V, hV, hzV, hVΩ, ?_⟩
  have hdiff := (symbolSpace V hV (0 - 1) r q).sub_mem hbLower hrem
  change IsSymbol V (0 - 1) (b.val - (b.val - g)) at hdiff
  change IsSymbol V (0 - 1) g
  simpa only [sub_sub_cancel] using hdiff

/-- The relative homogeneous symbol has finite quantization with its exact exterior action. -/
theorem exists_atlas_relative_quantization
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol 0 a)
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
    (K : Set M) (hK : IsCompact K)
    (ha : ∀ x : M, x ∉ K → ∀ ξ, ξ ≠ 0 → a x ξ = c x)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ (N : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B 0),
      (∀ (x : M) (ξ : CotangentFiber (n := n) x),
        (∑ j, (T j).globalSymbol).val x ξ =
          atlasRegularizedSymbolFunction g (fun y η ↦ a y η - c y) x ξ) ∧
      atlasGlobalPrincipalSymbolClass A B 0
          (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol) =
        atlasGlobalPrincipalSymbolClass A B 0 (atlasRegularizedSymbol A B g 0 a hs hh) ∧
      ∃ L : Set M, IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
        (∀ j, (T j).chart.symm ''
          (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L) ∧
        HasAtlasSectionOperatorSupport A B L (∑ j, (T j).toLinearMap) ∧
        ∀ (u : A.smoothSections) (x : M), x ∉ L →
          ((atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) u).val x =
            c x (u.val x) := by
  /- Stage 1: a-c is smooth off zero and homogeneous of degree zero.
  Regularize this actual correction by the given g and the original
  cutoff rho. The result b=rho(a-c) is an order-zero atlas symbol and
  vanishes over M minus K. At zero rho vanishes, so arbitrary original
  values a(x,0) cause no smoothness or support assumption, also when n=0.
  Stage 2: apply exists_atlas_supported_quantization_pieces to this same
  b and U. Its exact original leading-symbol sum gives the first formula.
  Add back the original pointwise map c on all of M. The resulting actual
  section action is precisely the displayed c plus finite sum; its
  correction has the same two-sided support L, hence its exterior action
  is exactly c, with no quantization of c or replacement operator involved.
  Stage 3: the sum's full principal representative is c+rho(a-c). Its
  difference from rho a is (1-rho)c. On each compact spatial chart region
  this smooth difference has bounded frequency support, so has every
  symbol order and in particular order minus one. The original principal
  quotient therefore gives the displayed equality for this same constructed
  family. Independence for arbitrary presentations of the same actual
  action is the separate theorem atlasRelativePrincipalSymbol_independent.
  Neither ellipticity, finite topological type, a global constant rank,
  a source measure nor compactness of M is required by quantization. -/
  classical
  have hcs : IsSmoothOffZeroAtlasSymbol A B (fun x _ ↦ c x) := by
    intro d hd i j
    exact ((isAtlasGlobalSymbol_zeroOrder A B c hc) d hd i j).1.mono
      (Set.prod_mono subset_rfl (Set.subset_univ _))
  have hch : IsHomogeneousAtlasSymbol (n := n) 0 (fun x _ ↦ c x) := by
    intro x ξ _ t _
    simp
  let δ : AtlasSymbolFunction (n := n) E F := fun x ξ ↦ a x ξ - c x
  have hδs : IsSmoothOffZeroAtlasSymbol A B δ := by
    intro d hd i j
    have hsub : atlasGlobalSymbolInChart A B δ d i j =
        atlasGlobalSymbolInChart A B a d i j -
          atlasGlobalSymbolInChart A B (fun x _ ↦ c x) d i j := by
      ext z η v
      by_cases hz : d.symm z ∈ (A.chart i).baseSet ∧ d.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, δ, hz]
      · simp [atlasGlobalSymbolInChart, hz]
    rw [hsub]
    exact (hs d hd i j).sub (hcs d hd i j)
  have hδh : IsHomogeneousAtlasSymbol 0 δ := by
    intro x ξ hξ t ht
    have h := hh x ξ hξ t ht
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at h ⊢
    exact congrArg (fun b ↦ b - c x) h
  let b := atlasRegularizedSymbol A B g 0 δ hδs hδh
  have hbzero : ∀ x : M, x ∉ K → ∀ ξ, b.val x ξ = 0 := by
    intro x hx ξ
    by_cases hξ : ξ = 0
    · subst ξ
      apply (atlasRegularizedSymbolFunction_cutoff g δ).1
      have hzero := (g.length_eq_zero_iff x 0).mpr rfl
      linarith
    · change (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1)
        (g.length x ξ)) : ℂ) • (a x ξ - c x) = 0
      rw [ha x hx ξ hξ, sub_self, smul_zero]
  -- The finite family is fixed once, for this exact radial correction and neighborhood.
  obtain ⟨N, T, hsum, L, hL, hKL, hLU, hTL, hsupport⟩ :=
    exists_atlas_supported_quantization_pieces A B b K hK hbzero U hU hKU
  refine ⟨N, T, ?_, ?_, L, hL, hKL, hLU, hTL, hsupport, ?_⟩
  · intro x ξ
    rw [hsum]
    rfl
  · -- The principal difference is precisely the low-frequency part of the original multiplier.
    rw [hsum]
    apply (atlasGlobalPrincipalSymbolClass_eq_iff A B 0 _ _).mpr
    have hraw : (atlasZeroOrderSymbol A B c hc + b).val -
        (atlasRegularizedSymbol A B g 0 a hs hh).val =
          fun x ξ ↦ c x - atlasRegularizedSymbolFunction g (fun y _ ↦ c y) x ξ := by
      funext x ξ
      change c x + (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1)
        (g.length x ξ)) : ℂ) • (a x ξ - c x) -
        (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1)
          (g.length x ξ)) : ℂ) • a x ξ = _
      simp only [atlasRegularizedSymbolFunction, smul_sub]
      abel
    rw [hraw]
    have hcov_smul (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
        covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
      ext v
      change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
        t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
      exact real_inner_smul_left η _ t
    have hcov_ne (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
        (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
        (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
        covectorFromChart c (c.symm z) η ≠ 0 := by
      intro hzero
      have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
      rw [hzero] at h
      have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext u; rfl
      exact hη (h.symm.trans hzero')
    have hrecovery (ℓ : SmoothCotangentMetric (n := n) (M := M))
        (p : AtlasSymbolFunction (n := n) E F)
        (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
        (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
        (hKV : K ⊆ atlasSymbolChartDomain A B c i j) :
        ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
          atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction ℓ p) c i j z η =
            atlasGlobalSymbolInChart A B p c i j z η := by
      let L (z η : EuclideanSpace ℝ (Fin n)) :=
        ℓ.length (c.symm z) (covectorFromChart c (c.symm z) η)
      let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
      have hne (η : EuclideanSpace ℝ (Fin n))
          (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
        intro hz
        simp [hz] at hη
      have hcont : ContinuousOn (Function.uncurry L) S :=
        (ℓ.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
          (fun z hz ↦ ⟨(hKV hz.1).1.1, hne z.2 hz.2⟩)
      obtain ⟨d, hd, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
        intro z hz
        exact ℓ.length_pos _ _ (hcov_ne c hc z.1 (hKV hz.1).1.1 z.2 (hne z.2 hz.2)))
      refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
      intro z hz η hη
      have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hd) hη
      have hηne : η ≠ 0 := norm_pos_iff.mp hηpos
      let v := ‖η‖⁻¹ • η
      have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
      have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
      have hlen : L z η = ‖η‖ * L z v := by
        dsimp [L]
        conv_lhs => rw [← hscale, hcov_smul, ℓ.length_smul]
        rw [abs_of_nonneg (norm_nonneg η)]
      have hlength : 1 ≤ L z η := by
        rw [hlen]
        have h := mul_le_mul_of_nonneg_left hη hd.le
        rw [mul_inv_cancel₀ hd.ne'] at h
        have hl := mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
        exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)
      have heq := (AtiyahSinger.atlasRegularizedSymbolFunction_cutoff ℓ p).2
        (c.symm z) (covectorFromChart c (c.symm z) η) hlength
      simp only [atlasGlobalSymbolInChart, heq]
    intro d hd i j
    let V := atlasSymbolChartDomain A B d i j
    let p := atlasGlobalSymbolInChart A B (fun x _ ↦ c x) d i j
    let r := atlasGlobalSymbolInChart A B
      (atlasRegularizedSymbolFunction g (fun x _ ↦ c x)) d i j
    have hopen : IsOpen V := by
      simpa only [V, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        d.continuousOn_symm.isOpen_inter_preimage d.open_target
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    have hsub : atlasGlobalSymbolInChart A B
        (fun x ξ ↦ c x - atlasRegularizedSymbolFunction g (fun y _ ↦ c y) x ξ)
          d i j = p - r := by
      ext z η v
      by_cases hz : d.symm z ∈ (A.chart i).baseSet ∧ d.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, p, r, hz]
      · simp [atlasGlobalSymbolInChart, p, r, hz]
    rw [hsub]
    have hp := (isAtlasGlobalSymbol_zeroOrder A B c hc) d hd i j
    have hr := (isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B g 0
      (fun x _ ↦ c x) hcs hch) d hd i j
    have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry (p - r)) (V ×ˢ Set.univ) :=
      hp.1.sub hr.1
    refine ⟨hsmooth, ?_⟩
    intro C hCV hC α β
    obtain ⟨C', hC', hCC', hC'V⟩ := exists_compact_between hC hopen hCV
    obtain ⟨R, _, hR⟩ := hrecovery g (fun x _ ↦ c x) d hd i j C' hC' hC'V
    have hint : interior C' ⊆ V := interior_subset.trans hC'V
    have hsupp : ∀ z ∈ interior C', ∀ η, R ≤ ‖η‖ → (p - r) z η = 0 := by
      intro z hz η hη
      change p z η - r z η = 0
      dsimp only [p, r]
      rw [hR z (interior_subset hz) η hη, sub_self]
    have horder := isSmoothingSymbol_of_frequency_support isOpen_interior (p - r) R
      (hsmooth.mono (Set.prod_mono hint subset_rfl)) hsupp (0 - 1)
    exact horder.2 C hCC' hC α β
  · intro u x hx
    have hzero : ((∑ j, (T j).toLinearMap) u).val x = 0 := by
      by_contra hne
      exact hx (hsupport.1 u (subset_closure hne))
    change c x (u.val x) + ((∑ j, (T j).toLinearMap) u).val x = c x (u.val x)
    rw [hzero, add_zero]

/-- Two-sided localization keeps the original relative principal class and exact section action. -/
theorem exists_atlas_localized_representative
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
    (N : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B 0)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol 0 a)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hprincipal : atlasGlobalPrincipalSymbolClass A B 0
        (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol) =
      atlasGlobalPrincipalSymbolClass A B 0 (atlasRegularizedSymbol A B g 0 a hs hh))
    (K : Set M) (hK : IsCompact K)
    (ha : ∀ x : M, x ∉ K → ∀ ξ, ξ ≠ 0 → a x ξ = c x)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : M → ℝ)
      (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ),
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ x ∈ K, χ x = 1) ∧
      ∃ (L : ℕ) (S : Fin L → AtlasPseudodifferentialPiece A B 0),
        (∑ j, (S j).toLinearMap) =
          twoSidedAtlasSectionCutoff A B (∑ j, (T j).toLinearMap) χ hχ ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x),
          (∑ j, (S j).globalSymbol).val x ξ =
            (χ x : ℂ) ^ 2 • (∑ j, (T j).globalSymbol).val x ξ) ∧
        atlasGlobalPrincipalSymbolClass A B 0
            (atlasZeroOrderSymbol A B c hc + ∑ j, (S j).globalSymbol) =
          atlasGlobalPrincipalSymbolClass A B 0
            (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol) ∧
        HasAtlasSectionOperatorSupport A B (tsupport χ) (∑ j, (S j).toLinearMap) := by
  /- First choose a smooth real cutoff χ, equal to one near K and
  compactly supported in U. Multiply the input and output cutoffs of each
  supplied piece by χ while retaining its internal symbol and Schwartz
  operator. Their sum is exactly χ (sum T) χ, their transported leading
  sum is χ² times the old sum, and their two-sided support is controlled
  by tsupport χ.
  For the principal comparison, use the constructed radial correction R
  only as a reference. The supplied class equality makes the discrepancy
  between the leading sums of T and R one order lower. The factor χ²-1
  annihilates R: it is zero on K, while R is zero outside K, including at
  frequency zero. Multiplying the lower-order discrepancy by χ²-1 preserves
  its order, so the original principal class is unchanged. This argument
  retains the zero-dimensional case without turning quotient equality
  into pointwise equality with the homogeneous symbol. The action of S
  remains the exact sandwich of the supplied pieces T. -/
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- Fix one real cutoff, with its support inside the requested open neighborhood.
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hK.isClosed hKK'
  have hχK (x : M) (hx : x ∈ K) : χ x = 1 := hχone.self_of_nhdsSet x hx
  have hχsupport : tsupport χ ⊆ K' := by
    apply closure_minimal ?_ hK'.isClosed
    intro x hx
    by_contra hxK
    exact hx (hχzero x hxK)
  have hχcompact : HasCompactSupport χ :=
    hK'.of_isClosed_subset isClosed_closure hχsupport
  let S (j : Fin N) := (T j).cutoff χ χ χ.contMDiff χ.contMDiff
  have haction : (∑ j, (S j).toLinearMap) =
      twoSidedAtlasSectionCutoff A B (∑ j, (T j).toLinearMap) χ χ.contMDiff := by
    apply LinearMap.ext
    intro u
    simp [S, AtlasPseudodifferentialPiece.toLinearMap_cutoff,
      twoSidedAtlasSectionCutoff, LinearMap.sum_apply, map_sum]
  have hpiece (j : Fin N) (x : M) (ξ : CotangentFiber (n := n) x) :
      (S j).globalSymbol.val x ξ = (χ x : ℂ) ^ 2 • (T j).globalSymbol.val x ξ := by
    change (S j).globalSymbolFunction x ξ = (χ x : ℂ) ^ 2 •
      (T j).globalSymbolFunction x ξ
    by_cases hx : x ∈ (T j).chart.source ∩ (A.chart (T j).input.frameIndex).baseSet ∩
        (B.chart (T j).output.frameIndex).baseSet
    · simp only [S, AtlasPseudodifferentialPiece.cutoff,
        AtlasPseudodifferentialPiece.globalSymbolFunction, AtlasChartCutoff.mulSmooth,
        dite_eq_left hx, (T j).chart.left_inv hx.1.1, Complex.ofReal_mul, smul_smul]
      congr 1
      ring
    · simp [S, AtlasPseudodifferentialPiece.cutoff,
        AtlasPseudodifferentialPiece.globalSymbolFunction, AtlasChartCutoff.mulSmooth, hx]
  have hsymbol (x : M) (ξ : CotangentFiber (n := n) x) :
      (∑ j, (S j).globalSymbol).val x ξ =
        (χ x : ℂ) ^ 2 • (∑ j, (T j).globalSymbol).val x ξ := by
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece, Finset.smul_sum]
  refine ⟨χ, χ.contMDiff, hχcompact, hχsupport.trans hK'U, hχK, N, S, haction,
    hsymbol, ?_, ?_⟩
  · -- Use the already proved radial correction only as a reference for the principal class.
    -- The new actual operator S remains the sandwich of the supplied original pieces T.
    obtain ⟨N₀, R, hRval, hRclass, _⟩ :=
      exists_atlas_relative_quantization A B a hs hh c hc K hK ha U hU hKU g
    let p := (∑ j, (T j).globalSymbol).val - (∑ j, (R j).globalSymbol).val
    have hp : IsAtlasGlobalSymbol A B (0 - 1) p := by
      have h := (atlasGlobalPrincipalSymbolClass_eq_iff A B 0 _ _).mp
        (hprincipal.trans hRclass.symm)
      have heq : (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol).val -
          (atlasZeroOrderSymbol A B c hc + ∑ j, (R j).globalSymbol).val = p := by
        simp only [Submodule.coe_add, p]
        abel
      rwa [heq] at h
    let w (x : M) : ℂ := (χ x : ℂ) ^ 2 - 1
    have hRzero (x : M) (ξ : CotangentFiber (n := n) x) :
        w x • (∑ j, (R j).globalSymbol).val x ξ = 0 := by
      by_cases hx : x ∈ K
      · simp [w, hχK x hx]
      · rw [hRval]
        by_cases hξ : ξ = 0
        · subst ξ
          rw [(atlasRegularizedSymbolFunction_cutoff g (fun y η ↦ a y η - c y)).1 x 0
            (by rw [(g.length_eq_zero_iff x 0).mpr rfl]; norm_num), smul_zero]
        · simp [atlasRegularizedSymbolFunction, ha x hx ξ hξ]
    apply (atlasGlobalPrincipalSymbolClass_eq_iff A B 0 _ _).mpr
    have hraw : (atlasZeroOrderSymbol A B c hc + ∑ j, (S j).globalSymbol).val -
        (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol).val =
          fun x ξ ↦ w x • p x ξ := by
      funext x ξ
      change c x + (∑ j, (S j).globalSymbol).val x ξ -
        (c x + (∑ j, (T j).globalSymbol).val x ξ) = _
      rw [hsymbol]
      change c x + (χ x : ℂ) ^ 2 • (∑ j, (T j).globalSymbol).val x ξ -
        (c x + (∑ j, (T j).globalSymbol).val x ξ) =
          w x • ((∑ j, (T j).globalSymbol).val x ξ - (∑ j, (R j).globalSymbol).val x ξ)
      rw [smul_sub, hRzero, sub_zero]
      dsimp only [w]
      rw [sub_smul, one_smul]
      abel
    rw [hraw]
    intro d hd i j
    let V := atlasSymbolChartDomain A B d i j
    have hopen : IsOpen V := by
      simpa only [V, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        d.continuousOn_symm.isOpen_inter_preimage d.open_target
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    have hχd : ContDiffOn ℝ ∞ (fun z ↦ χ (d.symm z)) V := by
      apply ContMDiffOn.contDiffOn
      exact χ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd)).mono
          (fun z hz ↦ hz.1.1))
    have hw : ContDiffOn ℝ ∞ (fun z ↦ w (d.symm z)) V :=
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hχd).pow 2).sub contDiffOn_const
    let W := EuclideanSpace ℂ (Fin (B.rank j))
    let Z := EuclideanSpace ℂ (Fin (A.rank i))
    have hmul := isSymbol_matrixSymbol V hopen (0 - 1)
      (atlasGlobalSymbolInChart A B p d i j) (hp d hd i j)
      (fun z ↦ w (d.symm z) • ContinuousLinearMap.id ℂ W)
      (fun _ ↦ ContinuousLinearMap.id ℂ Z) (hw.smul contDiffOn_const) contDiffOn_const
    have hcoord : atlasGlobalSymbolInChart A B (fun x ξ ↦ w x • p x ξ) d i j =
        matrixSymbol (fun z ↦ w (d.symm z) • ContinuousLinearMap.id ℂ W)
          (fun _ ↦ ContinuousLinearMap.id ℂ Z) (atlasGlobalSymbolInChart A B p d i j) := by
      ext z η v
      by_cases hz : d.symm z ∈ (A.chart i).baseSet ∧ d.symm z ∈ (B.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, matrixSymbol, hz, W, Z]
      · simp [atlasGlobalSymbolInChart, matrixSymbol, hz]
    rwa [hcoord]
  · rw [haction]
    exact (twoSidedAtlasSectionCutoff_properties A B _ χ χ.contMDiff).1

end AtiyahSinger
