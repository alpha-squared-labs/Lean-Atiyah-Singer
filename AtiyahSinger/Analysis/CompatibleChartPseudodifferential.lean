/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Analysis.CoordinateChange

/-!
# Local Fourier operators in compatible charts

Public module ID: M0373.

A Fourier operator supported in a smooth compatible chart can be transferred
to a specified original atlas chart containing its two supports. The resulting
piece has exactly the same section action and uses the same bundle frames.
This is the supported coordinate-change step in the atlas invariance of PDOs;
the original manifold atlas and section spaces remain fixed throughout.

Source: SG III.3.12--3.15, using the full coordinate-pushforward symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option maxHeartbeats 800000 in

/-- A supported compatible-chart action is a piece in the prescribed original chart. -/
theorem exists_piece_of_supported_compatible_chart {m : ℝ}
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (Din : AtlasChartCutoff A c) (Dout : AtlasChartCutoff B c)
    (hio : tsupport Din.cutoff ⊆ c.symm ⁻¹' (B.chart Dout.frameIndex).baseSet)
    (hoi : tsupport Dout.cutoff ⊆ c.symm ⁻¹' (A.chart Din.frameIndex).baseSet)
    (hbase : c.symm '' (tsupport Dout.cutoff ∪ tsupport Din.cutoff) ⊆ d.source)
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : IsSymbol univ m a) (hT : ∀ u x, T u x = quantize a u x)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x) :
    ∃ L : AtlasPseudodifferentialPiece A B m,
      L.chart = d ∧ L.toLinearMap = O.comp (T.toLinearMap.comp I) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let K := tsupport Dout.cutoff ∪ tsupport Din.cutoff
  let U := c.source ∩ (A.chart Din.frameIndex).baseSet ∩ (B.chart Dout.frameIndex).baseSet
  have hU : IsOpen U :=
    (c.open_source.inter (A.chart Din.frameIndex).open_baseSet).inter
      (B.chart Dout.frameIndex).open_baseSet
  have hK : IsCompact K := Dout.compact_support.union Din.compact_support
  have hKU : c.symm '' K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact ⟨⟨c.map_target (Dout.support_subset hz).1, hoi hz⟩,
        (Dout.support_subset hz).2⟩
    · exact ⟨⟨c.map_target (Din.support_subset hz).1, (Din.support_subset hz).2⟩, hio hz⟩
  let e := c.symm.trans d
  have he : ContDiffOn ℝ ∞ e e.source := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas (subset_maximalAtlas hd) hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz.1)).contDiffAt).contDiffWithinAt
  have hes : ContDiffOn ℝ ∞ e.symm e.target := by
    intro z hz
    have hdm := subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hd
    have hds := contMDiffAt_symm_of_mem_maximalAtlas hdm hz.1
    exact (((contMDiffAt_of_mem_maximalAtlas hc hz.2).comp z hds).contDiffAt).contDiffWithinAt
  have hKe : K ⊆ e.source := by
    intro z hz
    refine ⟨?_, hbase ⟨z, hz, rfl⟩⟩
    rcases hz with hz | hz
    · exact (Dout.support_subset hz).1
    · exact (Din.support_subset hz).1
  let V := d.target ∩ d.symm ⁻¹' U
  have hV : IsOpen V := d.continuousOn_symm.isOpen_inter_preimage d.open_target hU
  have hVe : V ⊆ e.target := fun z hz ↦ ⟨hz.1, hz.2.1.1⟩
  have hKV : e '' K ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    have hzbase := hbase ⟨z, hz, rfl⟩
    refine ⟨d.map_source hzbase, ?_⟩
    change d.symm (d (c.symm z)) ∈ U
    rw [d.left_inv hzbase]
    exact hKU ⟨z, hz, rfl⟩
  have heK : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  -- Select two plateaus around the same whole operator support, in the two coordinates.
  have plateau {W C : Set X} (hW : IsOpen W) (hC : IsCompact C) (hCW : C ⊆ W) :
      ∃ (χ : X → ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ W ∧ C ⊆ interior {z | χ z = 1} := by
    obtain ⟨V₀, hV₀, hCV₀, hV₀W, hV₀c⟩ :=
      exists_open_between_and_isCompact_closure hC hW hCW
    obtain ⟨V₁, hV₁, hV₀V₁, hV₁W, hV₁c⟩ :=
      exists_open_between_and_isCompact_closure hV₀c hW hV₀W
    obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hV₁ hV₀c.isClosed hV₀V₁
    have hs : tsupport χ = closure V₁ := congrArg closure hsχ
    refine ⟨χ, hχ, ?_, ?_, ?_⟩
    · simpa [HasCompactSupport, hs] using hV₁c
    · rwa [hs]
    intro z hz
    exact mem_interior.mpr ⟨V₀, fun w hw ↦ (honeχ w).mp (subset_closure hw),
      hV₀, hCV₀ hz⟩
  obtain ⟨χ, hχ, hcχ, hχe, hχone⟩ := plateau e.open_source hK hKe
  obtain ⟨β, hβ, hcβ, hβV, hβone⟩ := plateau hV heK hKV
  let Di : AtlasChartCutoff A d :=
    ⟨Din.frameIndex, β, hβ, hcβ, fun z hz ↦ ⟨(hβV hz).1, (hβV hz).2.1.2⟩⟩
  let Do : AtlasChartCutoff B d :=
    ⟨Dout.frameIndex, β, hβ, hcβ, fun z hz ↦ ⟨(hβV hz).1, (hβV hz).2.2⟩⟩
  let p := cutoffSymbol Dout.cutoff Din.cutoff a
  have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m a ha _ _
    Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support
  let P := amplitudeOperator m (cutoffAmplitude Dout.cutoff Din.cutoff a)
    (isAmplitude_cutoffAmplitude m a ha _ _ Dout.smooth_cutoff Din.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude a _ _ Dout.compact_support Din.compact_support)
  have hP : ∀ u z, P u z = quantize p u z := by
    intro u z
    rw [amplitudeOperator_apply]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m a ha _ _ Dout.smooth_cutoff Din.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude a _ _ Dout.compact_support Din.compact_support) u)
        z).symm
  have hPK : HasOperatorSupport K P := hasOperatorSupport_cutoff m a ha _ _
    Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support
  have hPa (u) (z) : P u z = Dout.cutoff z • T
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
        (fun w ↦ (Din.cutoff w : ℂ)) u) z := by
    rw [amplitudeOperator_apply, amplitudeApply_cutoffAmplitude m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support, hT]
  let R := coordinatePushforward e he hes χ β hχ hcχ hχe hβ hcβ (hβV.trans hVe) P
  obtain ⟨q, hq, hRq, _⟩ := exists_symbol_coordinatePushforward e he hes χ β hχ hcχ hχe
    hβ hcβ (hβV.trans hVe) m p hp P hP K hK hKe hPK hχone hβone
  have hRK : HasOperatorSupport (e '' K) R := hasOperatorSupport_coordinatePushforward
    e he hes χ β hχ hcχ hχe hβ hcβ (hβV.trans hVe) P K hK hKe hPK
  let L : AtlasPseudodifferentialPiece A B m :=
    ⟨d, hd, Di, Do, fun z hz ↦ (hβV hz).2.2,
      fun z hz ↦ (hβV hz).2.1.2, R, q, hq, hRq⟩
  refine ⟨L, rfl, ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  -- The original input multiplier cancels both plateaus on its entire support.
  let v := cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχe (Di.localize hd u)
  have hin : SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      (fun w ↦ (Din.cutoff w : ℂ)) v = I u := by
    apply SchwartzMap.ext
    intro z
    have hg : (fun z ↦ (Din.cutoff z : ℂ)).HasTemperateGrowth :=
      (Din.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp Din.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, hI]
    by_cases hz : z ∈ tsupport Din.cutoff
    · have hzK : z ∈ K := Or.inr hz
      have hdz := hbase ⟨z, hzK, rfl⟩
      have hχz : χ z = 1 := (interior_subset (s := {z | χ z = 1})) (hχone hzK)
      have hβz : β (d (c.symm z)) = 1 :=
        (interior_subset (s := {z | β z = 1})) (hβone ⟨z, hzK, rfl⟩)
      have hv : v z = Di.localizedFunction u (e z) := by
        rw [show v z = χ z • Di.localize hd u (e z) from
          cutoffPullbackCLM_apply _ _ _ _ _ _ _ _ _ _, hχz, one_smul]
        rfl
      rw [hv]
      simp only [AtlasChartCutoff.localizedFunction, Di,
        ite_eq_left (Din.support_subset hz).1]
      change (Din.cutoff z : ℂ) •
        (if d (c.symm z) ∈ d.target then (β (d (c.symm z)) : ℂ) •
          atlasSectionInChart A d Din.frameIndex u.val (d (c.symm z)) else 0) = _
      rw [ite_eq_left (d.map_source hdz), hβz, Complex.ofReal_one, one_smul]
      exact congrArg (fun y : M ↦ (Din.cutoff z : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm
          ((A.chart Din.frameIndex) ⟨y, u.val y⟩).2) (d.left_inv hdz)
    · simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  have hR (hx : x ∈ d.source) (hxc : x ∈ c.source) :
      R (Di.localize hd u) (d x) = Dout.cutoff (c x) • T (I u) (c x) := by
    have hdx : d x ∈ e.target := ⟨d.map_source hx, by simpa [d.left_inv hx] using hxc⟩
    rw [show R (Di.localize hd u) (d x) = P v (e.symm (d x)) from
      coordinatePushforward_apply e he hes χ β hχ hcχ hχe hβ hcβ (hβV.trans hVe)
        P K hKe hPK (fun z hz ↦ (interior_subset (s := {z | β z = 1}))
          (hβone hz)) _ _ hdx, hPa, hin]
    change Dout.cutoff (c (d.symm (d x))) • T (I u) (c (d.symm (d x))) = _
    rw [d.left_inv hx]
  have hout (hx : x ∉ c.symm '' tsupport Dout.cutoff) : Dout.extendedFunction (T (I u)) x = 0 := by
    by_cases hxf : x ∈ c.source ∩ (B.chart Dout.frameIndex).baseSet
    · have hz : c x ∉ tsupport Dout.cutoff := fun hz ↦ hx ⟨c x, hz, c.left_inv hxf.1⟩
      simp [AtlasChartCutoff.extendedFunction, hxf, image_eq_zero_of_notMem_tsupport hz]
    · simp [AtlasChartCutoff.extendedFunction, hxf]
  change Do.extendedFunction (R (Di.localize hd u)) x = (O (T (I u))).val x
  rw [hO]
  by_cases hxd : x ∈ d.source ∩ (B.chart Dout.frameIndex).baseSet
  · by_cases hxc : x ∈ c.source
    · rw [AtlasChartCutoff.extendedFunction, dite_eq_left hxd, hR hxd.1 hxc]
      have hβcancel : β (d x) * Dout.cutoff (c x) = Dout.cutoff (c x) := by
        by_cases hz : c x ∈ tsupport Dout.cutoff
        · have hez : d x ∈ e '' K := ⟨c x, Or.inl hz, by simp [e, c.left_inv hxc]⟩
          rw [show β (d x) = 1 from (interior_subset (s := {z | β z = 1}))
            (hβone hez), one_mul]
        · simp [image_eq_zero_of_notMem_tsupport hz]
      simp only [Do, ← Complex.coe_smul, map_smul, smul_smul, ← Complex.ofReal_mul,
        hβcancel]
      simp [AtlasChartCutoff.extendedFunction, hxc, hxd.2]
    · have hz : d x ∉ e '' K := by
        rintro ⟨z, hz, hez⟩
        have hsource := (hKU ⟨z, hz, rfl⟩).1.1
        have heq : c.symm z = x := d.injOn (hbase ⟨z, hz, rfl⟩) hxd.1 hez
        exact hxc (heq ▸ hsource)
      have hzero : R (Di.localize hd u) (d x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hRK.1 _ h))
      simp [AtlasChartCutoff.extendedFunction, Do, hxd, hxc, hzero]
  · have hxout : x ∉ c.symm '' tsupport Dout.cutoff := by
      rintro ⟨z, hz, rfl⟩
      exact hxd ⟨hbase ⟨z, Or.inl hz, rfl⟩, (Dout.support_subset hz).2⟩
    rw [hout hxout]
    simp [AtlasChartCutoff.extendedFunction, Do, hxd]

end AtiyahSinger
