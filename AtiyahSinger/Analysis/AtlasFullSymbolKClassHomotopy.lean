/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolKClass
public import AtiyahSinger.Analysis.FullSymbolKClassHomotopy

/-!
# Principal-representative independence for original general atlas symbols

Public module ID: M2301.

A genuine one-order-lower difference has a single compact exterior for its entire
original affine family. The actual source and target atlas frames give the local inverse
estimates, and their finite chart cover gives the metric exterior. Affine homotopy of the
same original boundary triples proves independence of the principal representative.

Sources: SG III.4.1, III.4.7 and III.13 (13.1); the explicit affine exterior and atlas
transport are project supplements. No homogeneous representative is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle IsManifold
open scoped Manifold ContDiff unitInterval

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- A lower-order atlas difference has one metric exterior for its entire affine family. -/
theorem IsEllipticFullAtlasSymbol.exists_metric_radius_affine_of_lowerOrder {m : ℝ}
    {a b : AtlasSymbolFunction (n := n) E F} (ha : IsEllipticFullAtlasSymbol A B m a)
    (hab : IsAtlasGlobalSymbol A B (m - 1) (b - a))
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (t : unitInterval) x (ξ : CotangentFiber (n := n) x),
      R < g.length x ξ → Function.Bijective ((1 - (t : ℂ)) • a x ξ + (t : ℂ) • b x ξ) := by
  /- Choose each compact-local inverse radius before quantifying over the affine parameter.
  The original finite chart cover combines these into one metric exterior for the whole
  interval. The same two frames recover the actual affine map on the original fibers. -/
  classical
  obtain ⟨C⟩ := nonempty_atlasQuantizationPresentation A B
  let K (i : Fin C.size) := tsupport (C.patch i).output.cutoff
  have hKU (i : Fin C.size) : K i ⊆ atlasSymbolChartDomain A B (C.patch i).chart
      (C.patch i).input.frameIndex (C.patch i).output.frameIndex := by
    intro z hz
    exact ⟨⟨((C.patch i).output.support_subset hz).1,
      (C.patch i).output_support_in_input_frame hz⟩,
      ((C.patch i).output.support_subset hz).2⟩
  -- The local difference uses exactly the same original source and target frames.
  have hlocal (i : Fin C.size) : ∃ R : ℝ, ∀ (t : unitInterval) z, z ∈ K i →
      ∀ η : EuclideanSpace ℝ (Fin n), R ≤ ‖η‖ →
        ((1 - (t : ℂ)) • atlasGlobalSymbolInChart A B a (C.patch i).chart
            (C.patch i).input.frameIndex (C.patch i).output.frameIndex z η +
          (t : ℂ) • atlasGlobalSymbolInChart A B b (C.patch i).chart
            (C.patch i).input.frameIndex (C.patch i).output.frameIndex z η).IsInvertible := by
    have hdiff := hab (C.patch i).chart (C.patch i).chart_mem_atlas
      (C.patch i).input.frameIndex (C.patch i).output.frameIndex
    have hcoord : atlasGlobalSymbolInChart A B (b - a) (C.patch i).chart
        (C.patch i).input.frameIndex (C.patch i).output.frameIndex =
          atlasGlobalSymbolInChart A B b (C.patch i).chart
            (C.patch i).input.frameIndex (C.patch i).output.frameIndex -
              atlasGlobalSymbolInChart A B a (C.patch i).chart
                (C.patch i).input.frameIndex (C.patch i).output.frameIndex := by
      ext z η v
      by_cases h : (C.patch i).chart.symm z ∈ (A.chart (C.patch i).input.frameIndex).baseSet ∧
          (C.patch i).chart.symm z ∈ (B.chart (C.patch i).output.frameIndex).baseSet
      · simp [atlasGlobalSymbolInChart, h]
      · simp [atlasGlobalSymbolInChart, h]
    rw [hcoord] at hdiff
    obtain ⟨R, _, hbound⟩ :=
      (ha (C.patch i).chart (C.patch i).chart_mem_atlas
        (C.patch i).input.frameIndex
        (C.patch i).output.frameIndex).exists_radius_affine_of_lowerOrder
          hdiff (K i) (hKU i) (C.patch i).output.compact_support
    exact ⟨R, hbound⟩
  choose R hbound using hlocal
  have hcover (x : M) : ∃ i : Fin C.size,
      x ∈ (C.patch i).chart.source ∧ (C.patch i).chart x ∈ K i := by
    have hactive : ∃ i : Fin C.size, (C.patch i).weight x ≠ 0 := by
      by_contra h
      push Not at h
      have hsum := C.sum_weight x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hactive
    have hx : x ∈ (C.patch i).chart.source := by
      by_contra hx
      exact hi (by simp [AtlasQuantizationPatch.weight, hx])
    have hcut : (C.patch i).output.cutoff ((C.patch i).chart x) ≠ 0 := by
      simpa only [AtlasQuantizationPatch.weight, ite_eq_left hx] using hi
    exact ⟨i, hx, subset_tsupport _ hcut⟩
  -- The finite cotangent chart theorem retains the actual inverse chart covectors.
  obtain ⟨L, hL, hlarge⟩ := exists_metric_radius_of_cotangent_chart_cover g
    (fun i : Fin C.size ↦ (C.patch i).chart)
    (fun i ↦ subset_maximalAtlas («I» := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (n := ∞) (C.patch i).chart_mem_atlas)
    K (fun i ↦ (C.patch i).output.compact_support)
    (fun i z hz ↦ ((C.patch i).output.support_subset hz).1) hcover R
  refine ⟨L, hL, ?_⟩
  intro t x ξ hξ
  obtain ⟨i, hx, hwindow, hfreq⟩ := hlarge x ξ hξ.le
  have he : x ∈ (A.chart (C.patch i).input.frameIndex).baseSet := by
    have h := (C.patch i).output_support_in_input_frame hwindow
    simpa only [Set.mem_preimage, (C.patch i).chart.left_inv hx] using h
  have hf : x ∈ (B.chart (C.patch i).output.frameIndex).baseSet := by
    have h := ((C.patch i).output.support_subset hwindow).2
    simpa only [Set.mem_preimage, (C.patch i).chart.left_inv hx] using h
  let e := (A.frameLinearEquiv (C.patch i).input.frameIndex x he).trans
    (EuclideanSpace.equiv (Fin (A.rank (C.patch i).input.frameIndex)) ℂ).symm.toLinearEquiv
  let f := (B.frameLinearEquiv (C.patch i).output.frameIndex x hf).trans
    (EuclideanSpace.equiv (Fin (B.rank (C.patch i).output.frameIndex)) ℂ).symm.toLinearEquiv
  let η := covectorInChart (C.patch i).chart x ξ
  let P : AtlasSymbolFunction (n := n) E F := (1 - (t : ℂ)) • a + (t : ℂ) • b
  let d := atlasGlobalSymbolInChart A B P (C.patch i).chart
    (C.patch i).input.frameIndex (C.patch i).output.frameIndex ((C.patch i).chart x) η
  have hinv : d.IsInvertible := by
    have hcoeff : atlasGlobalSymbolInChart A B P (C.patch i).chart
        (C.patch i).input.frameIndex (C.patch i).output.frameIndex =
          (1 - (t : ℂ)) • atlasGlobalSymbolInChart A B a (C.patch i).chart
              (C.patch i).input.frameIndex (C.patch i).output.frameIndex +
            (t : ℂ) • atlasGlobalSymbolInChart A B b (C.patch i).chart
              (C.patch i).input.frameIndex (C.patch i).output.frameIndex := by
      ext z η v
      by_cases h : (C.patch i).chart.symm z ∈ (A.chart (C.patch i).input.frameIndex).baseSet ∧
          (C.patch i).chart.symm z ∈ (B.chart (C.patch i).output.frameIndex).baseSet
      · simp [P, atlasGlobalSymbolInChart, h]
        simp only [← Complex.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]
      · simp [atlasGlobalSymbolInChart, h]
    dsimp only [d]
    rw [hcoeff]
    exact hbound i t ((C.patch i).chart x) hwindow η hfreq
  have hchartFormula (z : EuclideanSpace ℝ (Fin n)) (y : M)
      (hy : (C.patch i).chart.symm z = y)
      (he : y ∈ (A.chart (C.patch i).input.frameIndex).baseSet)
      (hf : y ∈ (B.chart (C.patch i).output.frameIndex).baseSet)
      (η : EuclideanSpace ℝ (Fin n))
      (v : EuclideanSpace ℂ (Fin (A.rank (C.patch i).input.frameIndex))) :
      atlasGlobalSymbolInChart A B P (C.patch i).chart
          (C.patch i).input.frameIndex (C.patch i).output.frameIndex z η v =
        (EuclideanSpace.equiv (Fin (B.rank (C.patch i).output.frameIndex)) ℂ).symm
          (B.frameLinearEquiv (C.patch i).output.frameIndex y hf
            (P y (covectorFromChart (C.patch i).chart y η)
              ((A.frameLinearEquiv (C.patch i).input.frameIndex y he).symm
                ((EuclideanSpace.equiv (Fin (A.rank (C.patch i).input.frameIndex)) ℂ) v)))) := by
    subst y
    dsimp only [atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨he, hf⟩]
    rfl
  have hmatrix (v : EuclideanSpace ℂ (Fin (A.rank (C.patch i).input.frameIndex))) :
      d v = f (P x ξ (e.symm v)) := by
    simpa only [d, e, f, η, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
      ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      covectorFromChart_covectorInChart (C.patch i).chart
      (C.patch i).chart_mem_atlas x hx] using
        hchartFormula ((C.patch i).chart x) x ((C.patch i).chart.left_inv hx) he hf η v
  -- The exact original map is recovered, rather than a coordinate replacement.
  have hb := hinv.bijective
  change Function.Bijective (P x ξ)
  constructor
  · intro u v huv
    apply e.injective
    apply hb.1
    rw [hmatrix (e u), hmatrix (e v), e.symm_apply_apply, e.symm_apply_apply, huv]
  · intro w
    obtain ⟨v, hv⟩ := hb.2 (f w)
    exact ⟨e.symm v, f.injective ((hmatrix v).symm.trans hv)⟩

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- Equal genuine principal quotient classes determine the same general atlas symbol K class. -/
theorem atlasFullSymbolKClass_eq_of_principalClass_eq {m : ℝ}
    (a b : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (hb : IsEllipticFullAtlasSymbol A B m b.val)
    (hab : atlasGlobalPrincipalSymbolClass A B m a = atlasGlobalPrincipalSymbolClass A B m b) :
    atlasFullSymbolKClass A B a ha = atlasFullSymbolKClass A B b hb := by
  /- Principal equality supplies the actual one-order-lower difference.
  One compact metric disk controls its entire affine interval. Enlarge both original
  triples to include that disk and compare their actual boundary maps by the existing
  affine homotopy theorem, retaining the original fibers in dimension zero as well. -/
  let := A.isFiniteRank
  let := B.isFiniteRank
  have hdiff : IsAtlasGlobalSymbol A B (m - 1) (b.val - a.val) :=
    (atlasGlobalPrincipalSymbolClass_eq_iff A B m b a).mp hab.symm
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  obtain ⟨R, _, hfamily⟩ := ha.exists_metric_radius_affine_of_lowerOrder A B hdiff g
  let D : Set (CotangentTotalSpace (n := n) (M := M)) := {z | g.length z.proj z.snd ≤ R}
  let T := atlasFullSymbolTriple A B a ha
  let U := atlasFullSymbolTriple A B b hb
  let K := (T.control ∪ U.control) ∪ D
  have hK : IsCompact K :=
    (T.isCompact_control.union U.isCompact_control).union (g.isCompact_sublevel R)
  have hT : T.control ⊆ K := Set.subset_union_left.trans Set.subset_union_left
  have hU : U.control ⊆ K := Set.subset_union_right.trans Set.subset_union_left
  have hhom : T.Homotopic U := by
    apply T.homotopic_of_affine U K hK hT hU
    intro t z
    have hzD : z.val ∉ D := fun hz ↦ z.property (Set.subset_union_right hz)
    have hinv := hfamily t z.val.proj z.val.snd (lt_of_not_ge hzD)
    change Function.Bijective (fun v : E z.val.proj ↦
      (1 - (t : ℂ)) • ((T.enlarge K hK hT).boundary.linearEquiv z v : F z.val.proj) +
        (t : ℂ) • ((U.enlarge K hK hU).boundary.linearEquiv z v : F z.val.proj))
    have hfun : (fun v : E z.val.proj ↦
        (1 - (t : ℂ)) • ((T.enlarge K hK hT).boundary.linearEquiv z v : F z.val.proj) +
          (t : ℂ) • ((U.enlarge K hK hU).boundary.linearEquiv z v : F z.val.proj)) =
        ⇑((1 - (t : ℂ)) • a.val z.val.proj z.val.snd +
          (t : ℂ) • b.val z.val.proj z.val.snd) := by
      funext v
      let zT : ↥(T.controlᶜ) := ⟨z.val, fun hz ↦ z.property (hT hz)⟩
      let zU : ↥(U.controlᶜ) := ⟨z.val, fun hz ↦ z.property (hU hz)⟩
      have hleft : ((T.enlarge K hK hT).boundary.linearEquiv z v : F z.val.proj) =
          a.val z.val.proj z.val.snd v :=
        (T.enlarge_apply K hK hT z v).trans
          (atlasFullSymbolTriple_boundary_apply A B a ha zT v)
      have hright : ((U.enlarge K hK hU).boundary.linearEquiv z v : F z.val.proj) =
          b.val z.val.proj z.val.snd v :=
        (U.enlarge_apply K hK hU z v).trans
          (atlasFullSymbolTriple_boundary_apply A B b hb zU v)
      exact congrArg₂ (fun v w ↦ (1 - (t : ℂ)) • v + (t : ℂ) • w) hleft hright
    exact hfun.symm ▸ hinv
  change T.compactSupportClass = U.compactSupportClass
  exact T.compactSupportClass_eq_of_homotopic U hhom

end AtiyahSinger
