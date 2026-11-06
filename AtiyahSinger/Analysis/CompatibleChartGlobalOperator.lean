/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration
public import AtiyahSinger.Analysis.CompatibleChartOffDiagonal
public import AtiyahSinger.Analysis.CompatibleChartPseudodifferential
public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Compatible-chart Fourier operators in the original atlas

Public module ID: M0368.

On a compact base, finite output localization separates the specified map into
near-diagonal pieces contained in raw atlas charts and actual smoothing remainders.
Full coordinate change gives the former, and all-order cutoff estimates give the
latter. A finite smooth partition reconstructs the original section map.

The statement retains the original atlas, bundle model and full operator action.
Source: SG III.3.12--3.17, coordinate invariance of the PDO class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option maxHeartbeats 1200000 in

/-- A full Fourier operator in any compatible chart is a PDO in the unchanged original atlas. -/
theorem isAtlasPseudodifferentialOperator_of_mem_maximalAtlas {m : ℝ}
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (hio : tsupport Din.cutoff ⊆ c.symm ⁻¹' (B.chart Dout.frameIndex).baseSet)
    (hoi : tsupport Dout.cutoff ⊆ c.symm ⁻¹' (A.chart Din.frameIndex).baseSet)
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : IsSymbol univ m a)
    (hT : ∀ u x, T u x = quantize a u x)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x) :
    IsAtlasPseudodifferentialOperator A B m (O.comp (T.toLinearMap.comp I)) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let S := O.comp (T.toLinearMap.comp I)
  let IA := 𝓘(ℝ, X)
  let K := c.symm '' tsupport Dout.cutoff
  have hK : IsCompact K := Dout.compact_support.image_of_continuousOn
    (c.continuousOn_symm.mono (fun z hz ↦ (Dout.support_subset hz).1))
  let mulA (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) :=
    atlasSectionMul A (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)
  let mulB (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) :=
    atlasSectionMul B (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)
  -- Scalar localization changes only the cutoff functions, retaining both frame indices.
  have hcutoff (f : X → ℝ) (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ c.target)
      (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) :
      ContDiff ℝ ∞ (fun z ↦ f z * ψ (c.symm z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport f
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas hc (hs hz)
      exact hf.contDiffAt.mul ((hψ.contMDiffAt.comp z hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hz] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
  let Di (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) : AtlasChartCutoff A c :=
    { Din with
      cutoff := fun z ↦ Din.cutoff z * ψ (c.symm z)
      smooth_cutoff := hcutoff _ Din.smooth_cutoff (fun z hz ↦ (Din.support_subset hz).1) ψ hψ
      compact_support := Din.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans Din.support_subset }
  let Do (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) : AtlasChartCutoff B c :=
    { Dout with
      cutoff := fun z ↦ Dout.cutoff z * ψ (c.symm z)
      smooth_cutoff := hcutoff _ Dout.smooth_cutoff (fun z hz ↦ (Dout.support_subset hz).1) ψ hψ
      compact_support := Dout.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans Dout.support_subset }
  have hinput (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) (u : A.smoothSections) (z : X) :
      (I.comp (mulA ψ hψ)) u z = (Di ψ hψ).localizedFunction u z := by
    rw [LinearMap.comp_apply, hI]
    by_cases hz : z ∈ tsupport Din.cutoff
    · have hzt := (Din.support_subset hz).1
      have hzf := (Din.support_subset hz).2
      simp only [AtlasChartCutoff.localizedFunction, Di, ite_eq_left hzt]
      change (Din.cutoff z : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm
          ((A.frameLinearEquiv Din.frameIndex (c.symm z) hzf)
            ((ψ (c.symm z) : ℂ) • u.val (c.symm z))) =
        ((Din.cutoff z * ψ (c.symm z) : ℝ) : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv Din.frameIndex (c.symm z) hzf) (u.val (c.symm z)))
      rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
    · simp [AtlasChartCutoff.localizedFunction, Di, image_eq_zero_of_notMem_tsupport hz]
  have houtput (ψ : M → ℝ) (hψ : ContMDiff IA 𝓘(ℝ) ∞ ψ) (v) (x : M) :
      ((mulB ψ hψ).comp O v).val x = (Do ψ hψ).extendedFunction v x := by
    change (ψ x : ℂ) • (O v).val x = _
    rw [hO]
    by_cases hx : x ∈ c.source ∩ (B.chart Dout.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, Do, dite_eq_left hx]
      rw [c.left_inv hx.1, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [AtlasChartCutoff.extendedFunction, Do, hx]
  have hproductSupport (f : X → ℝ) (hs : tsupport f ⊆ c.target) (ψ : M → ℝ) :
      c.symm '' tsupport (fun z ↦ f z * ψ (c.symm z)) ⊆ tsupport ψ := by
    rintro _ ⟨z, hz, rfl⟩
    by_contra hout
    have hzt := hs (tsupport_mul_subset_left hz)
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
      (c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hzt))
    have hprod : (fun y ↦ f y * ψ (c.symm y)) =ᶠ[nhds z] 0 := by
      filter_upwards [hzero] with y hy
      simp only [Function.comp_def, Pi.zero_apply] at hy
      simp [hy]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hz
  have hsmooth (R : A.smoothSections →ₗ[ℂ] B.smoothSections)
      (hR : IsAtlasSmoothingOperator A B R) : IsAtlasPseudodifferentialOperator A B m R := by
    refine ⟨0, Fin.elim0, ?_⟩
    simpa only [Fin.sum_univ_zero, sub_zero] using hR
  -- Localize near each output point. The far part keeps its actual smoothing action.
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ (φ : M → ℝ) (hφ : ContMDiff IA 𝓘(ℝ) ∞ φ), tsupport φ ⊆ U →
        IsAtlasPseudodifferentialOperator A B m ((mulB φ hφ).comp S) := by
    by_cases hxK : x ∈ K
    · let d := chartAt X x
      let W := (c.source ∩ d.source) ∩
        ((A.chart Din.frameIndex).baseSet ∩ (B.chart Dout.frameIndex).baseSet)
      have hW : IsOpen W := (c.open_source.inter d.open_source).inter
        ((A.chart Din.frameIndex).open_baseSet.inter (B.chart Dout.frameIndex).open_baseSet)
      have hxW : x ∈ W := by
        obtain ⟨z, hz, rfl⟩ := hxK
        exact ⟨⟨c.map_target (Dout.support_subset hz).1, mem_chart_source _ _⟩,
          hoi hz, (Dout.support_subset hz).2⟩
      obtain ⟨C, hC, hxC, hCW⟩ := exists_compact_subset hW hxW
      obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
        (I := IA) (n := ⊤) isClosed_singleton
        (show ({x} : Set M) ⊆ interior C from singleton_subset_iff.mpr hxC)
      have hχC : tsupport χ ⊆ C := by
        apply closure_minimal _ hC.isClosed
        intro y hy
        by_contra hyC
        exact hy (hχzero y hyC)
      have hχW : tsupport χ ⊆ W := hχC.trans hCW
      have hxOne : x ∈ interior {y | χ y = 1} := by
        apply mem_interior_iff_mem_nhds.mpr
        change ∀ᶠ y in nhds x, χ y = 1
        simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hχone
      let U := W ∩ interior {y | χ y = 1}
      refine ⟨U, hW.inter isOpen_interior, ⟨hxW, hxOne⟩, ?_⟩
      intro φ hφ hφU
      have hnearBase : c.symm ''
          (tsupport (Do φ hφ).cutoff ∪ tsupport (Di χ χ.contMDiff).cutoff) ⊆ d.source := by
        rw [image_union]
        apply union_subset
        · exact (hproductSupport _ (fun z hz ↦ (Dout.support_subset hz).1) φ).trans
            (fun y hy ↦ (hφU hy).1.1.2)
        · exact (hproductSupport _ (fun z hz ↦ (Din.support_subset hz).1) χ).trans
            (fun y hy ↦ (hχW hy).1.2)
      obtain ⟨R, _, hR⟩ := exists_piece_of_supported_compatible_chart A B c d hc
        (chart_mem_atlas _ x) (Di χ χ.contMDiff) (Do φ hφ)
        (tsupport_mul_subset_left.trans hio) (tsupport_mul_subset_left.trans hoi) hnearBase
        T a ha hT (I.comp (mulA χ χ.contMDiff)) ((mulB φ hφ).comp O)
        (hinput χ χ.contMDiff) (houtput φ hφ)
      have hnear : IsAtlasPseudodifferentialOperator A B m
          (((mulB φ hφ).comp S).comp (mulA χ χ.contMDiff)) := by
        have hpiece : IsAtlasPseudodifferentialOperator A B m R.toLinearMap := by
          refine ⟨1, fun _ ↦ R, ?_⟩
          simp only [Fin.sum_univ_one, sub_self]
          intro L H s t
          exact ⟨0, by intro u; simp⟩
        rw [hR] at hpiece
        simpa only [S, LinearMap.comp_assoc] using hpiece
      have hψ : ContMDiff IA 𝓘(ℝ) ∞ (fun y ↦ 1 - χ y) := contMDiff_const.sub χ.contMDiff
      have hz (y : M) : φ y * (1 - χ y) = 0 := by
        by_cases hy : χ y = 1
        · simp [hy]
        · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦
            hy ((interior_subset (s := {y | χ y = 1})) (hφU h).2))
          simp [hφy]
      have hzero (z : X) : (Do φ hφ).cutoff z * (Di (fun y ↦ 1 - χ y) hψ).cutoff z = 0 := by
        change (Dout.cutoff z * φ (c.symm z)) * (Din.cutoff z * (1 - χ (c.symm z))) = 0
        calc
          _ = (Dout.cutoff z * Din.cutoff z) * (φ (c.symm z) * (1 - χ (c.symm z))) := by ring
          _ = 0 := by rw [hz, mul_zero]
      have hfarSmooth := isAtlasSmoothingOperator_of_compatible_chart_cutoff_eq_zero A B c hc
        (Di (fun y ↦ 1 - χ y) hψ) (Do φ hφ)
        (tsupport_mul_subset_left.trans hio) (tsupport_mul_subset_left.trans hoi) hzero
        T a ha hT (I.comp (mulA (fun y ↦ 1 - χ y) hψ)) ((mulB φ hφ).comp O)
        (hinput _ hψ) (houtput φ hφ)
      have hfar : IsAtlasPseudodifferentialOperator A B m
          (((mulB φ hφ).comp S).comp (mulA (fun y ↦ 1 - χ y) hψ)) := by
        simpa only [S, LinearMap.comp_assoc] using hsmooth _ hfarSmooth
      have hsum : mulA χ χ.contMDiff + mulA (fun y ↦ 1 - χ y) hψ = LinearMap.id := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        funext y
        change (χ y : ℂ) • u.val y + ((1 - χ y : ℝ) : ℂ) • u.val y = u.val y
        rw [← add_smul, ← Complex.ofReal_add]
        simp
      have h := (isAtlasPseudodifferentialOperator_closure A B m).2.1 _ _ hnear hfar
      rwa [← LinearMap.comp_add, hsum, LinearMap.comp_id] at h
    · refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hxK, ?_⟩
      intro φ hφ hφK
      have heq : (mulB φ hφ).comp S = 0 := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        funext y
        change (φ y : ℂ) • (O (T (I u))).val y = 0
        by_cases hyK : y ∈ K
        · have hφy := image_eq_zero_of_notMem_tsupport (fun hy ↦ hφK hy hyK)
          simp [hφy]
        · rw [hO]
          by_cases hy : y ∈ c.source ∩ (B.chart Dout.frameIndex).baseSet
          · have hz : c y ∉ tsupport Dout.cutoff := fun hz ↦ hyK ⟨c y, hz, c.left_inv hy.1⟩
            simp [AtlasChartCutoff.extendedFunction, hy, image_eq_zero_of_notMem_tsupport hz]
          · simp [AtlasChartCutoff.extendedFunction, hy]
      rw [heq]
      exact (isAtlasPseudodifferentialOperator_closure A B m).1
  -- One finite output partition reconstructs the original section map exactly.
  choose U hU hxU hcut using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let index : Fin s.card ≃ s := s.equivFin.symm
  let V (j : Fin s.card) := U (index j)
  have hcover : Set.univ ⊆ ⋃ j, V j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate IA isClosed_univ V
    (fun j ↦ hU (index j)) hcover
  let R (j : Fin s.card) := (mulB (ρ j) (ρ j).contMDiff).comp S
  have hR (j : Fin s.card) : IsAtlasPseudodifferentialOperator A B m (R j) :=
    hcut (index j) (ρ j) (ρ j).contMDiff (hρ j)
  have hsum : (∑ j, R j) = S := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext y
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    change (∑ j, (ρ j y : ℂ) • (S u).val y) = (S u).val y
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
      ρ.sum_eq_one (Set.mem_univ y)]
    simp
  change S ∈ atlasPseudodifferentialSpace A B m
  rw [← hsum]
  exact (atlasPseudodifferentialSpace A B m).sum_mem (fun j _ ↦ hR j)

end AtiyahSinger
