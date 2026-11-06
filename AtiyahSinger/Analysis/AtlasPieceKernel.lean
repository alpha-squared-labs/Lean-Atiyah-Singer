/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasKernelPairing
public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator
public import AtiyahSinger.Analysis.AtlasSchwartzKernel

/-!
# Actual distributional kernels of the noncompact finite-piece construction

Public module ID: M0274.

The original section map is a specified smooth bundle multiplier plus a finite
sum of the already constructed atlas Fourier pieces. Both that precise map
and its precise difference from the multiplier have actual Schwartz kernels.
Existence is a conclusion, without a supplied kernel or a compact ambient
manifold. Every original local rank and chart inverse is retained.

The local Schwartz kernel theorem is the explicit additional analysis input;
continuity of these pairings follows from the concrete finite-piece maps.
Sources: SG III.3 local Fourier construction and III.13.4 localization. The
metric-pairing atlas realization is a standard project supplement. The proved
continuous pairings retain the original operators, frames, density and local ranks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option backward.isDefEq.respectTransparency false in
/-- The same multiplier-plus-pieces operator and its actual residual have genuine unique kernels. -/
theorem exists_atlasSchwartzKernels_of_pieces
    (hF : ComplexBundle.ContinuousHermitianMetric F) (hhF : B.IsSmoothHermitianMetric hF)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
    {m : ℝ} (N : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B m) :
    (∃! κ : AtlasSchwartzKernel A B,
      IsAtlasSchwartzKernel A B hF μ
        (atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) κ) ∧
    (∃! κ : AtlasSchwartzKernel A B,
      IsAtlasSchwartzKernel A B hF μ
        ((atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap) -
          atlasSmoothSectionMap A B c hc) κ) := by
  classical
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let V := EuclideanSpace ℝ (Fin n)
  let P₀ := atlasSmoothSectionMap A B c hc
  let R : A.smoothSections →ₗ[ℂ] B.smoothSections := ∑ j, (T j).toLinearMap
  -- Every output test has its fixed compact support, for any smooth second section.
  have hI (d : OpenPartialHomeomorph M V) (hd : d ∈ atlas V M)
      (D : AtlasChartCutoff B d)
      (v : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex)))) (u : B.smoothSections) :
      Integrable (fun x ↦ (hF.toCore x).inner ((D.extend hd v).val x) (u.val x)) μ := by
    have hK : IsCompact (d.symm '' tsupport D.cutoff) :=
      D.compact_support.image_of_continuousOn
        (d.continuousOn_symm.mono (fun z hz ↦ (D.support_subset hz).1))
    have hs : Function.support
        (fun x ↦ (hF.toCore x).inner ((D.extend hd v).val x) (u.val x)) ⊆
          d.symm '' tsupport D.cutoff := by
      intro x hx
      by_contra hxK
      apply hx
      change (hF.toCore x).inner (D.extendedFunction v x) (u.val x) = 0
      rw [(D.extendedFunction_properties hd v).2 x hxK]
      let : InnerProductSpace.Core ℂ (F x) := hF.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    exact (B.contMDiff_pairing hF hhF (D.extend hd v) u).continuous.integrable_of_hasCompactSupport
      (hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed))
  have hid : IsSmoothAtlasBundleMap B B (fun x ↦ LinearMap.id (R := ℂ) (M := F x)) := by
    refine ⟨contMDiff_id, ?_⟩
    intro i j a
    apply (B.contMDiffOn_coordChange i j a).congr
    intro x hx
    simp only [dite_eq_left hx.1, LinearMap.id_apply, id_eq]
    have heq : (⟨x, (B.frameLinearEquiv i x hx.1).symm (Pi.single a 1)⟩ : TotalSpace Unit F) =
        (B.chart i).toPartialEquiv.symm (x, Pi.single a 1) :=
      TotalSpace.mk_cast (F := Unit) (E := F) ((B.chart i).proj_symm_apply' hx.1) _
    rw [heq]
  -- Each piece factors through the original continuous input transfer and Fourier operator.
  have hpieces (d e : OpenPartialHomeomorph M V) (hd : d ∈ atlas V M) (he : e ∈ atlas V M)
      (D : AtlasChartCutoff B d) (E' : AtlasChartCutoff A e) :
      ∃ Q : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) →ₗ⋆[ℂ]
          𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) →ₗ[ℂ] ℂ,
        Continuous (fun z : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) ×
            𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) ↦ Q z.1 z.2) ∧ ∀ v w,
          Q v w = ∫ x : M, (hF.toCore x).inner ((D.extend hd v).val x)
            ((R (E'.extend he w)).val x) ∂μ := by
    have hpiece (j : Fin N) :
        ∃ Q : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) →ₗ⋆[ℂ]
            𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) →ₗ[ℂ] ℂ,
          Continuous (fun z : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) ×
              𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) ↦ Q z.1 z.2) ∧ ∀ v w,
            Q v w = ∫ x : M, (hF.toCore x).inner ((D.extend hd v).val x)
              (((T j).toLinearMap (E'.extend he w)).val x) ∂μ := by
      obtain ⟨Q, hQ, hQval⟩ := exists_atlasCutoffPairing B B hF hhF μ
        (fun x ↦ LinearMap.id (R := ℂ) (M := F x)) hid hd (T j).chart_mem_atlas D (T j).output
      obtain ⟨S, hS⟩ := E'.exists_localize_extendCLM he (T j).input (T j).chart_mem_atlas
      let U := (T j).operator.comp S
      refine ⟨Q.compl₂ U.toLinearMap,
        hQ.comp (continuous_fst.prodMk (U.continuous.comp continuous_snd)), ?_⟩
      intro v w
      change Q v (U w) = _
      rw [hQval]
      apply integral_congr_ae
      filter_upwards with x
      change (hF.toCore x).inner ((D.extend hd v).val x)
        (((T j).output.extend (T j).chart_mem_atlas ((T j).operator (S w))).val x) = _
      rw [hS w]
      rfl
    choose Q hQ hQval using hpiece
    refine ⟨∑ j, Q j, ?_, ?_⟩
    · simpa only [LinearMap.sum_apply] using continuous_finsetSum Finset.univ (fun j _ ↦ hQ j)
    intro v w
    simp only [LinearMap.sum_apply]
    simp_rw [hQval]
    rw [← integral_finsetSum Finset.univ (fun j _ ↦ hI d hd D v
      ((T j).toLinearMap (E'.extend he w)))]
    apply integral_congr_ae
    filter_upwards with x
    let : InnerProductSpace.Core ℂ (F x) := hF.toCore x
    let L : F x →ₗ[ℂ] ℂ :=
      { toFun := (hF.toCore x).inner ((D.extend hd v).val x)
        map_add' := fun u w ↦ InnerProductSpace.Core.inner_add_right _ u w
        map_smul' := fun a u ↦ InnerProductSpace.Core.inner_smul_right _ _ }
    change (∑ j, L (((T j).toLinearMap (E'.extend he w)).val x)) =
      L ((R (E'.extend he w)).val x)
    simp only [R, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, map_sum]
  -- Sum the actual pairings, keeping the prescribed multiplier and its literal residual.
  have hfull : ∃! κ : AtlasSchwartzKernel A B,
      IsAtlasSchwartzKernel A B hF μ (P₀ + R) κ := by
    apply exists_atlasSchwartzKernel_of_pairings A B hF μ (P₀ + R)
    intro d e hd he D E'
    obtain ⟨Q₀, hQ₀, hQ₀val⟩ := exists_atlasCutoffPairing A B hF hhF μ c hc hd he D E'
    obtain ⟨Q₁, hQ₁, hQ₁val⟩ := hpieces d e hd he D E'
    refine ⟨Q₀ + Q₁, ?_, ?_⟩
    · simpa only [LinearMap.add_apply] using hQ₀.fun_add hQ₁
    intro v w
    simp only [LinearMap.add_apply]
    have hIc : Integrable (fun x : M ↦ (hF.toCore x).inner
        ((D.extend hd v).val x) (c x ((E'.extend he w).val x))) μ :=
      hI d hd D v (P₀ (E'.extend he w))
    rw [hQ₀val, hQ₁val, ← integral_add hIc (hI d hd D v (R (E'.extend he w)))]
    apply integral_congr_ae
    filter_upwards with x
    let : InnerProductSpace.Core ℂ (F x) := hF.toCore x
    change (hF.toCore x).inner ((D.extend hd v).val x) ((P₀ (E'.extend he w)).val x) +
      (hF.toCore x).inner ((D.extend hd v).val x) ((R (E'.extend he w)).val x) =
      (hF.toCore x).inner ((D.extend hd v).val x)
        (((P₀ (E'.extend he w)).val x) + ((R (E'.extend he w)).val x))
    exact (InnerProductSpace.Core.inner_add_right _ _ _).symm
  have hresidual : ∃! κ : AtlasSchwartzKernel A B,
      IsAtlasSchwartzKernel A B hF μ R κ :=
    exists_atlasSchwartzKernel_of_pairings A B hF μ R hpieces
  refine ⟨hfull, ?_⟩
  simpa only [add_sub_cancel_left] using hresidual

end AtiyahSinger
