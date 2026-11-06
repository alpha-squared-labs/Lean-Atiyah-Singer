/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactBaseQuantization
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology
public import AtiyahSinger.Analysis.SectionOperatorSupport
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Relative zero-order quantization by finite supported pieces

Public module ID: M0922.

UL03: the realization assertion in SG III.13.4, p.248, before (13.10).
Subtract the given exterior zero-order map, regularize this compactly based
correction, and quantize it by one finite family. The source need not be compact
or of finite topological type once these symbol data have been supplied.
The finite sum acts on the actual section carrier. Its displayed globalSymbol
sum is a principal representative; lower-order cutoff terms are not discarded
from the actual operators. Ambient ellipticity and symbol-class extension still
require the open-extension and geometric-assembly stages.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  (E F : SmoothFiniteComplexBundle (n := n) M)

include hM hT hSC

/-- Relative degree-zero data admit finite quantization with the given exterior action. -/
theorem exists_relative_quantization_pieces
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (K : Set M) (hK : IsCompact K) (ha : ∀ x, x ∉ K → ∀ ξ, a.val x ξ = c x)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ b : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0,
      (∀ x, x ∉ K → ∀ ξ, b.val x ξ = 0) ∧
      (∀ x ξ, 1 ≤ g.length x ξ → b.val x ξ + c x = a.val x ξ) ∧
      ∃ (d : ℕ) (T : Fin d → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber 0),
        (∑ j, (T j).globalSymbol) = b ∧
        ∃ L : Set M, IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
          (∀ j, (T j).chart.symm ''
            (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L) ∧
          HasSectionOperatorSupport L (∑ j, (T j).toLinearMap) ∧
          ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber) (x : M), x ∉ L →
            ((smoothSectionMap (fun x ↦ (c x).toLinearMap) hc +
              ∑ j, (T j).toLinearMap) u).val x = c x (u.val x) := by
  /- Stage 1: a-c is smooth off zero and homogeneous of degree zero, and it
  vanishes over M minus K. Apply compact-base regularization with the supplied
  metric. This gives b with exact high-frequency recovery of a after adding c.
  Stage 2: quantize b by finitely many pieces with both cutoff supports in U.
  Adjoin K to their common compact support to get L. Their specified principal
  representatives sum to b; the actual cutoff operators retain all lower orders.
  Stage 3: the two cutoff supports give the two-sided operator support of the
  sum. In particular its output is zero outside L, so adding the pointwise map
  c gives exactly c there. This single source family can now be transported
  into multiple compact environments by the preceding finite-piece extension.
  No ellipticity, source measure or source compactness is needed for realization;
  elliptic data will be used at the later ambient assembly step. -/
  classical
  -- The original exterior multiplier is a smooth, degree-zero symbol in the same frames.
  have hcs : IsSmoothOffZeroGlobalSymbol (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber (fun x _ ↦ c x) := by
    intro d hd e f _ _
    let V := EuclideanSpace ℂ (Fin E.rank)
    let W := EuclideanSpace ℂ (Fin F.rank)
    let H := EuclideanSpace ℝ (Fin n)
    let C (x : M) : V →L[ℂ] W :=
      (f.continuousLinearMapAt ℂ x).comp ((c x).comp (e.symmL ℂ x))
    have hC : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V →L[ℂ] W) ∞ C
        (e.baseSet ∩ f.baseSet) := by
      have hsum : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V →L[ℂ] W) ∞
          (fun x ↦ ∑ j : Fin E.rank,
            (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
              ((f ⟨x, c x (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2))
          (e.baseSet ∩ f.baseSet) := by
        apply contMDiffOn_finsetSum
        intro j _
        exact ((ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj j)).restrictScalars
          ℝ).contMDiff.comp_contMDiffOn (hc e f j)
      apply hsum.congr
      intro x hx
      apply ContinuousLinearMap.ext
      intro v
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
      change C x v = ∑ j : Fin E.rank, v j •
        (f ⟨x, c x (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2
      have h := congrArg (C x) ((EuclideanSpace.basisFun (Fin E.rank) ℂ).sum_repr v)
      simpa [C, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hx.2] using h.symm
    have hcoord : ContDiffOn ℝ ∞ (fun z ↦ C (d.symm z))
        (symbolChartDomain E.Fiber F.Fiber d e f) := by
      apply ContMDiffOn.contDiffOn
      apply hC.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd)).mono
          (fun z hz ↦ hz.1.1))
        (fun z hz ↦ ⟨hz.1.2, hz.2⟩)
    exact hcoord.comp contDiffOn_fst (fun _ hz ↦ hz.1)
  have hds : IsSmoothOffZeroGlobalSymbol (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber (fun x ξ ↦ a.val x ξ - c x) := by
    have heq : (fun x ξ ↦ a.val x ξ - c x) =
        a.val + (-1 : ℂ) • (fun x _ ↦ c x) := by
      funext x ξ
      simp [sub_eq_add_neg]
    rw [heq]
    exact a.property.1.add (hcs.smul (-1))
  have hdh : IsHomogeneousGlobalSymbol E.Fiber F.Fiber 0
      (fun x ξ ↦ a.val x ξ - c x) := by
    intro x ξ hξ t ht
    have h := a.property.2 x ξ hξ t ht
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at h ⊢
    rw [h]
  obtain ⟨b, hbzero, hbrecover⟩ := exists_compactBase_regularization 0
    (fun x ξ ↦ a.val x ξ - c x) hds hdh K hK
      (fun x hx ξ _ ↦ by rw [ha x hx ξ, sub_self]) g
  -- A single finite family realizes this correction and retains both original cutoff supports.
  obtain ⟨d, T, hsymbol, C, hC, hCU, hTC⟩ :=
    exists_supported_quantization_pieces b K hK hbzero U hU hKU
  let L := K ∪ C
  have hL : IsCompact L := hK.union hC
  have hTL (j : Fin d) : (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L := by
    rw [Set.union_comm]
    exact (hTC j).trans subset_union_right
  have houtput (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (x : M) (hx : x ∉ L) : ((∑ j, (T j).toLinearMap) u).val x = 0 := by
    rw [LinearMap.sum_apply]
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply (T j).output.extendedFunction_eq_zero
    intro hx'
    exact hx (hTL j (Set.image_mono subset_union_right hx'))
  have hsupport : HasSectionOperatorSupport L (∑ j, (T j).toLinearMap) := by
    constructor
    · intro u
      apply closure_minimal ?_ hL.isClosed
      intro x hx
      by_contra hxL
      exact hx (houtput u x hxL)
    · intro u hu
      have hinput (j : Fin d) : (T j).input.localize (T j).chart_mem_atlas u = 0 := by
        let := (T j).input.frame_mem_atlas
        apply DFunLike.ext
        intro z
        change (T j).input.localizedFunction u z = 0
        by_cases hz : z ∈ tsupport (T j).input.cutoff
        · have hxL : (T j).chart.symm z ∈ L := hTL j ⟨z, Or.inl hz, rfl⟩
          have huzero : u.val ((T j).chart.symm z) = 0 := by
            by_contra hne
            exact Set.disjoint_left.mp hu (subset_closure hne) hxL
          have hzframe := ((T j).input.support_subset hz).2
          have hfzero : ((T j).input.frame ⟨(T j).chart.symm z, (0 : E.Fiber _)⟩).2 = 0 :=
            ((T j).input.frame.linearEquivAt ℂ _ hzframe).map_zero
          simp only [BundleChartCutoff.localizedFunction,
            ite_eq_left ((T j).input.support_subset hz).1, sectionInChart, huzero, hfzero,
            smul_zero]
        · simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
      rw [LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      change (T j).output.extendLinearMap (T j).chart_mem_atlas
        ((T j).operator ((T j).input.localize (T j).chart_mem_atlas u)) = 0
      rw [hinput, map_zero, map_zero]
  refine ⟨b, hbzero, ?_, d, T, hsymbol, L, hL, subset_union_left,
    union_subset hKU hCU, hTL, hsupport, ?_⟩
  · intro x ξ hξ
    rw [hbrecover x ξ hξ, sub_add_cancel]
  · intro u x hx
    change c x (u.val x) + ((∑ j, (T j).toLinearMap) u).val x = c x (u.val x)
    rw [houtput u x hx, add_zero]

end AtiyahSinger
