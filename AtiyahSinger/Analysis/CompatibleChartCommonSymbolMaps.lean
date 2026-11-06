/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompatibleChartLocalizedSymbolMaps
public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization

import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Common full symbols in a specified compatible target chart

A finite family has one common localization in any specified chart of the
maximal smooth atlas. The two actual cutoff maps are returned with their
pointwise formulas. The final common cutoffs absorb the same auxiliary scalar
on both sides; complete Fourier actions and all lower-order remainders remain.

This is the compatible-target version of finite smooth localization, needed
for actual associated product charts. Source: SG III.3.18--3.19.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]

set_option maxHeartbeats 1200000 in

open scoped Classical in
/-- One common complete local form retains the same input and output plateau cutoffs. -/
theorem exists_common_local_symbols_with_plateaus_of_compatible_charts
    {m : ℝ} {ι : Type*} [Finite ι]
    (d : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : ∀ j, d j ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : ∀ j, AtlasChartCutoff A (d j)) (Dout : ∀ j, AtlasChartCutoff B (d j))
    (hio : ∀ j, tsupport (Din j).cutoff ⊆ (d j).symm ⁻¹' (B.chart (Dout j).frameIndex).baseSet)
    (hoi : ∀ j, tsupport (Dout j).cutoff ⊆ (d j).symm ⁻¹' (A.chart (Din j).frameIndex).baseSet)
    (T : ∀ j, 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex))))
    (a : ∀ j, SymbolFunction n (A.rank (Din j).frameIndex) (B.rank (Dout j).frameIndex))
    (ha : ∀ j, IsSymbol univ m (a j)) (hT : ∀ j u x, T j u x = quantize (a j) u x)
    (Lin : ∀ j, A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex))))
    (Lout : ∀ j,
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex)))
        →ₗ[ℂ] B.smoothSections)
    (hLin : ∀ j u z, Lin j u z = (Din j).localizedFunction u z)
    (hLout : ∀ j v x, (Lout j v).val x = (Dout j).extendedFunction v x)
    (g : ι → AtlasSymbolFunction (n := n) E F)
    (hg : ∀ j x ξ, g j x ξ =
      if h : x ∈ (d j).source ∩ (A.chart (Din j).frameIndex).baseSet ∩
          (B.chart (Dout j).frameIndex).baseSet then
        (((Dout j).cutoff (d j x) * (Din j).cutoff (d j x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv (Dout j).frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank (Dout j).frameIndex)) ℂ).toLinearMap).comp
            ((a j (d j x) (covectorInChart (d j) x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank (Din j).frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv (Din j).frameIndex x h.1.2).toLinearMap))
      else 0)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (e : A.Index) (f : B.Index)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ atlasSymbolChartDomain A B c e f) :
    ∃ (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
      ∃ (I₀ : B.smoothSections →ₗ[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex))))
        (O₀ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))
          →ₗ[ℂ] A.smoothSections),
        (∀ v y, I₀ v y = K₀.localizedFunction v y) ∧
        (∀ u x, (O₀ u).val x = D₀.extendedFunction u x) ∧
        D₀.frameIndex = e ∧ K₀.frameIndex = f ∧ D₀.cutoff = K₀.cutoff ∧
      ∃ (V : Set (EuclideanSpace ℝ (Fin n)))
        (p : ι → SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)),
        IsOpen V ∧ z ∈ V ∧ V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
          (∀ y ∈ V, D₀.cutoff y = 1) ∧ (∀ j, IsSymbol Set.univ m (p j)) ∧
          (∀ j, IsSymbol V (m - 1) (p j - atlasGlobalSymbolInChart A B
            (g j) c D₀.frameIndex K₀.frameIndex)) ∧
          ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
              EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
            quantize (p j) u y = I₀
              (((Lout j).comp ((T j).toLinearMap.comp (Lin j))) (O₀ u)) y := by
  classical
  let Jmap (j : ι) := (Lout j).comp ((T j).toLinearMap.comp (Lin j))
  have common :
      ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
        (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
        ∃ (I₀ : B.smoothSections →ₗ[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex))))
        (O₀ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))
          →ₗ[ℂ] A.smoothSections),
        (∀ v y, I₀ v y = K₀.localizedFunction v y) ∧
        (∀ u x, (O₀ u).val x = D₀.extendedFunction u x) ∧
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
              (g j) c D₀.frameIndex K₀.frameIndex)) ∧
            ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
                EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
              quantize (p j) u y = I₀
                (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
                  ((Jmap j)
                    (atlasSectionMul A (fun x ↦ (χ x : ℂ))
                      (Complex.ofRealCLM.contMDiff.comp hχ) (O₀ u)))) y
  := by
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let x := c.symm z
    let D := c.source ∩ (A.chart e).baseSet ∩ (B.chart f).baseSet
    let D' (j : ι) := (d j).source ∩ (A.chart (Din j).frameIndex).baseSet ∩
      (B.chart (Dout j).frameIndex).baseSet
    let K (j : ι) := (d j).symm ''
      (tsupport (Dout j).cutoff ∪ tsupport (Din j).cutoff)
    have hK (j : ι) : IsCompact (K j) :=
      ((Dout j).compact_support.union (Din j).compact_support).image_of_continuousOn
        ((d j).continuousOn_symm.mono (by
          intro y hy
          rcases hy with hy | hy
          · exact ((Dout j).support_subset hy).1
          · exact ((Din j).support_subset hy).1))
    have hKD (j : ι) : K j ⊆ D' j := by
      rintro y ⟨w, hw, rfl⟩
      rcases hw with hw | hw
      · exact ⟨⟨(d j).map_target ((Dout j).support_subset hw).1,
          (hoi j) hw⟩, ((Dout j).support_subset hw).2⟩
      · exact ⟨⟨(d j).map_target ((Din j).support_subset hw).1,
          ((Din j).support_subset hw).2⟩, (hio j) hw⟩
    -- One finite intersection handles every active piece and removes every inactive piece.
    let W' (j : ι) := if x ∈ K j then D' j else (K j)ᶜ
    have hW' (j : ι) : IsOpen (W' j) := by
      by_cases hj : x ∈ K j
      · simpa only [W', ite_eq_left hj] using
          (((d j).open_source.inter (A.chart (Din j).frameIndex).open_baseSet).inter
            (B.chart (Dout j).frameIndex).open_baseSet)
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
    let Wchart := c.target ∩ c.symm ⁻¹' W
    have hWchart : IsOpen Wchart := c.isOpen_inter_preimage_symm hW
    have himage : c '' tsupport χ ⊆ Wchart := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨c.map_source (hχD hy).1.1, by
        change c.symm (c y) ∈ W
        rw [c.left_inv (hχD hy).1.1]
        exact hχW hy⟩
    have hcimage : IsCompact (c '' tsupport χ) := hcχ.image_of_continuousOn
      (c.continuousOn.mono (fun y hy ↦ (hχD hy).1.1))
    -- The common chart cutoff is one near the entire new support and remains in W.
    obtain ⟨O, hOo, hKO, hOT, hOc⟩ :=
      exists_open_between_and_isCompact_closure hcimage hWchart himage
    obtain ⟨O', hO'o, hOO', hO'Wchart, hO'c⟩ :=
      exists_open_between_and_isCompact_closure hOc hWchart hOT
    obtain ⟨ρ, hρ, _, hsρ, honeρ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
    have hρsupport : tsupport ρ = closure O' := congrArg closure hsρ
    have hcρ : HasCompactSupport ρ := by simpa [HasCompactSupport, hρsupport] using hO'c
    have hρT : tsupport ρ ⊆ Wchart := by rwa [hρsupport]
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
    -- The original compatible-chart Sobolev maps supply these exact cutoff formulas.
    obtain ⟨I₀, hI₀, _⟩ := K₀.exists_localize_sobolev_of_mem_maximalAtlas hc
      (Classical.choice (nonempty_atlasBundlePresentation B)) 0
    obtain ⟨O₀, hO₀, _⟩ := D₀.exists_extend_sobolev_of_mem_maximalAtlas hc
      (Classical.choice (nonempty_atlasBundlePresentation A)) 0
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
    have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ maximalAtlas I ∞ M)
        (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
        ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      by_cases hy : y ∈ tsupport a
      · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          hd (hs hy)
        exact ha.contDiffAt.mul ((χ.contMDiff.contMDiffAt.comp y hchart).contDiffAt)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    let input (j : ι) : AtlasChartCutoff A (d j) :=
      { (Din j) with
        cutoff := fun y ↦ (Din j).cutoff y * χ ((d j).symm y)
        smooth_cutoff := hcutoff _ (hd j) _ (Din j).smooth_cutoff
          (fun y hy ↦ ((Din j).support_subset hy).1)
        compact_support := (Din j).compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans (Din j).support_subset }
    let output (j : ι) : AtlasChartCutoff B (d j) :=
      { (Dout j) with
        cutoff := fun y ↦ (Dout j).cutoff y * χ ((d j).symm y)
        smooth_cutoff := hcutoff _ (hd j) _ (Dout j).smooth_cutoff
          (fun y hy ↦ ((Dout j).support_subset hy).1)
        compact_support := (Dout j).compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans (Dout j).support_subset }
    let Rmap (j : ι) := Tout.comp ((Jmap j).comp Tin)
    have hinput (j : ι) (u : A.smoothSections) (y : X) :
        ((Lin j).comp Tin) u y = (input j).localizedFunction u y := by
      rw [LinearMap.comp_apply, hLin]
      by_cases hy : y ∈ tsupport (Din j).cutoff
      · have hyc := ((Din j).support_subset hy).1
        have hyf := ((Din j).support_subset hy).2
        simp only [AtlasChartCutoff.localizedFunction, input, ite_eq_left hyc]
        change ((Din j).cutoff y : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank (Din j).frameIndex)) ℂ).symm
            ((A.frameLinearEquiv (Din j).frameIndex ((d j).symm y) hyf)
              ((χ ((d j).symm y) : ℂ) • u.val ((d j).symm y))) =
          (((Din j).cutoff y * χ ((d j).symm y) : ℝ) : ℂ) •
            (EuclideanSpace.equiv (Fin (A.rank (Din j).frameIndex)) ℂ).symm
              ((A.frameLinearEquiv (Din j).frameIndex ((d j).symm y) hyf)
                (u.val ((d j).symm y)))
        rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
      · simp [AtlasChartCutoff.localizedFunction, input, image_eq_zero_of_notMem_tsupport hy]
    have houtput (j : ι)
        (v : 𝓢(X, EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex)))) (y : M) :
        (Tout.comp (Lout j) v).val y = (output j).extendedFunction v y := by
      change (χ y : ℂ) • (Lout j v).val y = _
      rw [hLout]
      by_cases hy : y ∈ (d j).source ∩ (B.chart (Dout j).frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, output, dite_eq_left hy]
        rw [(d j).left_inv hy.1, Complex.ofReal_mul, smul_smul, mul_comm]
      · simp [AtlasChartCutoff.extendedFunction, output, hy]
    let gR (j : ι) : AtlasSymbolFunction (n := n) E F := fun y ξ ↦
      if h : y ∈ (d j).source ∩ (A.chart (input j).frameIndex).baseSet ∩
          (B.chart (output j).frameIndex).baseSet then
        (((output j).cutoff (d j y) * (input j).cutoff (d j y) : ℝ) : ℂ) •
          ((B.frameLinearEquiv (output j).frameIndex y h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank (output j).frameIndex)) ℂ).toLinearMap).comp
            ((a j (d j y) (covectorInChart (d j) y ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank (input j).frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv (input j).frameIndex y h.1.2).toLinearMap))
      else 0
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
    have hRsupp (j : ι) : (d j).symm ''
        (tsupport (output j).cutoff ∪ tsupport (input j).cutoff) ⊆ tsupport χ := by
      rw [image_union]
      apply union_subset
      · exact hproductSupport _ _ (fun y hy ↦ ((Dout j).support_subset hy).1)
      · exact hproductSupport _ _ (fun y hy ↦ ((Din j).support_subset hy).1)
    have hglobal (j : ι) (y : M) (hy : χ y = 1) (ξ) :
        (gR j) y ξ = (g j) y ξ := by
      rw [hg]
      dsimp only [gR, input, output]
      split_ifs with hdomain
      · rw [(d j).left_inv hdomain.1.1, hy]
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
        IsSymbol V (m - 1) (p - atlasGlobalSymbolInChart A B (g j) c e f) ∧
        ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank e)))) y,
          quantize p u y = I₀ (Tout ((Jmap j) (Tin (O₀ u)))) y := by
      by_cases hj : x ∈ K j
      · have hactive : W ⊆ D' j := by
          intro y hy
          simpa only [W', ite_eq_left hj] using mem_iInter.mp hy.2 j
        obtain ⟨p, hp, hpaction, hplower⟩ := exists_localized_symbol_of_compatible_charts
          A B (d j) (hd j) (input j) (output j)
          (tsupport_mul_subset_left.trans (hio j)) (tsupport_mul_subset_left.trans (hoi j))
          (T j) (a j) (ha j) (hT j) ((Lin j).comp Tin) (Tout.comp (Lout j))
          (hinput j) (houtput j) (gR j) (fun _ _ ↦ rfl) c hc D₀ K₀ I₀ O₀ hI₀ hO₀ rfl
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
          rw [hpaction]
          rfl
      · have hzeroInput : (input j).cutoff = 0 := by
          funext y
          by_cases hy : (Din j).cutoff y = 0
          · simp [input, hy]
          · have hyK : (d j).symm y ∈ K j :=
              ⟨y, Or.inr (subset_tsupport _ hy), rfl⟩
            have hχy : χ ((d j).symm y) = 0 :=
              image_eq_zero_of_notMem_tsupport (by
                intro hyχ
                have hnot := mem_iInter.mp (hχW hyχ).2 j
                exact (show (d j).symm y ∉ K j by
                  simpa only [W', ite_eq_right hj, mem_compl_iff] using hnot) hyK)
            simp [input, hχy]
        have hRzero : Rmap j = 0 := by
          apply LinearMap.ext
          intro u
          have hin : (Lin j) (Tin u) = 0 := by
            apply SchwartzMap.ext
            intro y
            rw [show (Lin j) (Tin u) y = (input j).localizedFunction u y from hinput j u y]
            simp [AtlasChartCutoff.localizedFunction, hzeroInput]
          change Tout ((Lout j) ((T j) ((Lin j) (Tin u)))) = 0
          rw [hin, map_zero, map_zero, map_zero]
        refine ⟨0, isSymbol_zero _ _, ?_, ?_⟩
        · apply congrSymbol 0 _ (isSymbol_zero _ _)
          intro y hy η
          have hyK : c.symm y ∉ K j := by
            simpa only [W', ite_eq_right hj, mem_compl_iff] using mem_iInter.mp hy.2.1.2 j
          have hzero (ξ) : (g j) (c.symm y) ξ = 0 := by
            by_cases hvalid : c.symm y ∈ D' j
            · have hcut : (d j) (c.symm y) ∉ tsupport (Dout j).cutoff := by
                intro hmem
                exact hyK ⟨(d j) (c.symm y), Or.inl hmem,
                  (d j).left_inv hvalid.1.1⟩
              rw [hg]
              simp [D', hvalid, image_eq_zero_of_notMem_tsupport hcut]
            · rw [hg]
              simp [D', hvalid]
          simp [atlasGlobalSymbolInChart, hzero]
        · intro u y
          change quantize 0 u y = I₀
            ((Tout.comp ((Jmap j).comp Tin)) (O₀ u)) y
          change quantize 0 u y = I₀ ((Rmap j) (O₀ u)) y
          rw [hRzero]
          change quantize 0 u y = I₀ 0 y
          simp [quantize]
    choose p hp hplower hpaction using hsymbols
    refine ⟨χ, χ.contMDiff, D₀, K₀, I₀, O₀, hI₀, hO₀, rfl, rfl, hcχ, hχD, rfl, ?_,
      V, p, hV, hzV, hVU, ?_, hp, hplower, hpaction⟩
    · intro y hy
      exact (interior_subset (s := {y | ρ y = 1})) (hρone hy)
    · intro y hy
      exact (interior_subset (s := {y | χ y = 1})) hy.2.2
  obtain ⟨χ, hχ, D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, _, _, hDK, hDOne, V, p, hV, hzV,
    hVU, hχOne, hp, hplower, hpaction⟩ := common
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let Tin := atlasSectionMul A (fun y ↦ (χ y : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
  let Tout := atlasSectionMul B (fun y ↦ (χ y : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
  have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ maximalAtlas I ∞ M)
      (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
      ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport a
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        hd (hs hy)
      exact ha.contDiffAt.mul ((hχ.contMDiffAt.comp y hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  -- Absorb the same scalar χ into the returned two atlas cutoffs. Their frame
  -- indices are exactly e and f, so the original local symbol has these ranks.
  let Dχ : AtlasChartCutoff A c :=
    { D₀ with
      cutoff := fun y ↦ D₀.cutoff y * χ (c.symm y)
      smooth_cutoff := hcutoff c hc _ D₀.smooth_cutoff (fun y hy ↦ (D₀.support_subset hy).1)
      compact_support := D₀.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans D₀.support_subset }
  let Kχ : AtlasChartCutoff B c :=
    { K₀ with
      cutoff := fun y ↦ K₀.cutoff y * χ (c.symm y)
      smooth_cutoff := hcutoff c hc _ K₀.smooth_cutoff (fun y hy ↦ (K₀.support_subset hy).1)
      compact_support := K₀.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans K₀.support_subset }
  let Oχ := Tin.comp O₀
  let Iχ := I₀.comp Tout
  have hOχ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) (x : M) :
      (Oχ u).val x = Dχ.extendedFunction u x := by
    change (χ x : ℂ) • (O₀ u).val x = Dχ.extendedFunction u x
    rw [hO₀]
    symm
    by_cases hx : x ∈ c.source ∩ (A.chart D₀.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, Dχ, dite_eq_left hx]
      rw [c.left_inv hx.1, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [AtlasChartCutoff.extendedFunction, Dχ, hx]
  have hIχ (v : B.smoothSections) (y : X) : Iχ v y = Kχ.localizedFunction v y := by
    change I₀ (Tout v) y = Kχ.localizedFunction v y
    rw [hI₀]
    symm
    by_cases hy : y ∈ tsupport K₀.cutoff
    · have hyc := (K₀.support_subset hy).1
      have hyf := (K₀.support_subset hy).2
      simp only [AtlasChartCutoff.localizedFunction, ite_eq_left hyc, atlasSectionInChart]
      dsimp only [Kχ]
      change _ = (K₀.cutoff y : ℂ) •
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.frameLinearEquiv K₀.frameIndex (c.symm y) hyf)
            ((χ (c.symm y) : ℂ) • v.val (c.symm y)))
      rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · simp [AtlasChartCutoff.localizedFunction, Kχ, image_eq_zero_of_notMem_tsupport hy]
  have hDKχ : Dχ.cutoff = Kχ.cutoff := by
    funext y
    change D₀.cutoff y * χ (c.symm y) = K₀.cutoff y * χ (c.symm y)
    rw [hDK]
  have hDχOne (y : X) (hy : y ∈ V) : Dχ.cutoff y = 1 := by
    have hχy : χ (c.symm y) = 1 := hχOne y hy
    have hyχ : c.symm y ∈ tsupport χ := subset_tsupport χ (by
      change χ (c.symm y) ≠ 0
      rw [hχy]
      norm_num)
    have hDy : D₀.cutoff y = 1 := hDOne y ⟨c.symm y, hyχ, c.right_inv (hVU hy).1.1⟩
    change D₀.cutoff y * χ (c.symm y) = 1
    rw [hDy, hχy, one_mul]
  refine ⟨Dχ, Kχ, Iχ, Oχ, hIχ, hOχ, he, hf, hDKχ, V, p, hV, hzV, hVU,
    hDχOne, hp, hplower, ?_⟩
  intro j u y
  exact hpaction j u y

set_option maxHeartbeats 1200000 in

open scoped Classical in
/-- One specified compatible chart and two actual maps localize the complete finite family. -/
theorem exists_common_local_symbols_of_compatible_charts {m : ℝ} {ι : Type*} [Finite ι]
    (d : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : ∀ j, d j ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : ∀ j, AtlasChartCutoff A (d j)) (Dout : ∀ j, AtlasChartCutoff B (d j))
    (hio : ∀ j, tsupport (Din j).cutoff ⊆ (d j).symm ⁻¹' (B.chart (Dout j).frameIndex).baseSet)
    (hoi : ∀ j, tsupport (Dout j).cutoff ⊆ (d j).symm ⁻¹' (A.chart (Din j).frameIndex).baseSet)
    (T : ∀ j, 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex))))
    (a : ∀ j, SymbolFunction n (A.rank (Din j).frameIndex) (B.rank (Dout j).frameIndex))
    (ha : ∀ j, IsSymbol univ m (a j)) (hT : ∀ j u x, T j u x = quantize (a j) u x)
    (Lin : ∀ j, A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank (Din j).frameIndex))))
    (Lout : ∀ j,
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank (Dout j).frameIndex)))
        →ₗ[ℂ] B.smoothSections)
    (hLin : ∀ j u z, Lin j u z = (Din j).localizedFunction u z)
    (hLout : ∀ j v x, (Lout j v).val x = (Dout j).extendedFunction v x)
    (g : ι → AtlasSymbolFunction (n := n) E F)
    (hg : ∀ j x ξ, g j x ξ =
      if h : x ∈ (d j).source ∩ (A.chart (Din j).frameIndex).baseSet ∩
          (B.chart (Dout j).frameIndex).baseSet then
        (((Dout j).cutoff (d j x) * (Din j).cutoff (d j x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv (Dout j).frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank (Dout j).frameIndex)) ℂ).toLinearMap).comp
            ((a j (d j x) (covectorInChart (d j) x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank (Din j).frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv (Din j).frameIndex x h.1.2).toLinearMap))
      else 0)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (e : A.Index) (f : B.Index)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ atlasSymbolChartDomain A B c e f) :
    ∃ (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
      ∃ (I₀ : B.smoothSections →ₗ[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex))))
        (O₀ : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))
          →ₗ[ℂ] A.smoothSections),
        (∀ v y, I₀ v y = K₀.localizedFunction v y) ∧
        (∀ u x, (O₀ u).val x = D₀.extendedFunction u x) ∧
        D₀.frameIndex = e ∧ K₀.frameIndex = f ∧
      ∃ (V : Set (EuclideanSpace ℝ (Fin n)))
        (p : ι → SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)),
        IsOpen V ∧ z ∈ V ∧ V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
          (∀ j, IsSymbol Set.univ m (p j)) ∧
          (∀ j, IsSymbol V (m - 1) (p j - atlasGlobalSymbolInChart A B
            (g j) c D₀.frameIndex K₀.frameIndex)) ∧
          ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
              EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
            quantize (p j) u y = I₀
              (((Lout j).comp ((T j).toLinearMap.comp (Lin j))) (O₀ u)) y := by
  classical
  obtain ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, _, V, p, hV, hzV, hVU, _, hp,
      hplower, hpaction⟩ :=
    exists_common_local_symbols_with_plateaus_of_compatible_charts
      A B d hd Din Dout hio hoi T a ha hT
      Lin Lout hLin hLout g hg c hc e f z hz
  exact ⟨D₀, K₀, I₀, O₀, hI₀, hO₀, he, hf, V, p, hV, hzV, hVU, hp, hplower, hpaction⟩

end AtiyahSinger
