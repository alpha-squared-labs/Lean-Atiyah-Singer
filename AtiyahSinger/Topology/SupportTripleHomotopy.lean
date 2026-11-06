/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopyRotation
public import AtiyahSinger.Topology.SupportBundleTriple
public import Mathlib.Topology.UrysohnsLemma

/-!
# Cut off a homotopy near compact control

Public module ID: M2194.

D07/K02. A homotopy at infinity can be changed to a global isomorphism after
allowing a larger compact control. This uses a spatial time cutoff on a locally
compact Hausdorff space, not exact lifting from an arbitrary noncompact closed set.
Sources: SG I.9.26; KA II.2.14–2.16. The cutoff argument is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

attribute [local instance] sumTopology isFiniteRank_sum

variable {X : Type*} [TopologicalSpace X]


/-- A compact set has a time cutoff that is zero nearby and one at infinity. -/
theorem exists_time_cutoff [LocallyCompactSpace X] [T2Space X]
    (K : Set X) (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∃ L : Set X, IsCompact L ∧ U ⊆ L ∧
        ∃ ρ : C(X, I), (∀ x ∈ U, ρ x = 0) ∧ ∀ x ∉ L, ρ x = 1 := by
  /- Choose two nested compact neighborhoods of K. The locally compact version of Urysohn's
  lemma gives a compactly supported function equal to one near the inner neighborhood and
  valued in [0,1]. Subtract it from one and regard the result as an interval-valued
  continuous map. No global normality or paracompactness is required. -/
  -- A compact neighborhood supplies a region where the compactly supported bump is one.
  obtain ⟨C, hC, _, hKC, _⟩ := exists_compact_closed_between hK isOpen_univ
    (Set.subset_univ K)
  obtain ⟨f, hf, hfc, _, hfrange⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC isOpen_univ (Set.subset_univ C)
  have hrange (x : X) : 1 - f x ∈ I := by
    have hx := hfrange x
    constructor <;> linarith [hx.1, hx.2]
  let ρ : C(X, I) :=
    ⟨fun x ↦ ⟨1 - f x, hrange x⟩,
      (continuous_const.sub f.continuous).subtype_mk hrange⟩
  refine ⟨interior C, isOpen_interior, hKC, tsupport f, hfc, ?_, ρ, ?_, ?_⟩
  · intro x hx
    apply subset_closure
    change f x ≠ 0
    rw [hf (interior_subset hx)]
    exact one_ne_zero
  · intro x hx
    apply Subtype.ext
    change 1 - f x = 0
    simpa only [Pi.one_apply, sub_self] using
      congrArg (fun y : ℝ ↦ 1 - y) (hf (interior_subset hx))
  · intro x hx
    apply Subtype.ext
    change 1 - f x = 1
    rw [image_eq_zero_of_notMem_tsupport hx, sub_zero]

variable [hL : LocallyCompactSpace X] [hT : T2Space X]
include hL hT

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An elementary boundary homotopy extends after enlarging the compact control. -/
theorem exists_iso_at_infinity (E : FiniteBundle X) (K : Set X) (hK : IsCompact K)
    (a : RelativeTriple E.Fiber E.Fiber Kᶜ)
    (H : IsoHomotopy (RelativeTriple.identity E.Fiber Kᶜ) a) :
    ∃ L : Set X, ∃ hL : IsCompact L, ∃ hKL : K ⊆ L, ∃ e : Iso E.Fiber E.Fiber,
      ∀ x : (Lᶜ : Set X), ∀ v : E.Fiber x,
        e.linearEquiv x v = a.linearEquiv ⟨x, fun hx ↦ x.property (hKL hx)⟩ v := by
  /- Choose a continuous time cutoff zero on an open neighborhood of K and one outside a larger
  compact L. On the complement of K evaluate H at this time; on the inner neighborhood use
  identity. The maps agree on the overlap and glue over the open cover. The original
  finite-rank inverse-map theorem proves continuity of these same fiberwise inverses.
  The resulting global isomorphism equals the endpoint boundary map outside L. -/
  classical
  obtain ⟨U, hU, hKU, L, hL, hUL, ρ, hρzero, hρone⟩ := exists_time_cutoff K hK
  have hKL : K ⊆ L := hKU.trans hUL
  let eFiber (x : X) : E.Fiber x ≃ₗ[ℂ] E.Fiber x :=
    if hx : x ∈ K then LinearEquiv.refl ℂ (E.Fiber x) else
      H.iso.linearEquiv (ρ x, ⟨x, hx⟩)
  have hidentity (x : X) (hx : x ∈ U) (v : E.Fiber x) : eFiber x v = v := by
    dsimp only [eFiber]
    split_ifs with hKx
    · rfl
    · rw [hρzero x hx]
      exact H.map_zero ⟨x, hKx⟩ v
  -- Off K, insert the spatially varying time into the actual cylinder pullback.
  let R : Set (TotalSpace Unit E.Fiber) := {z | z.proj ∉ K}
  let base (z : R) : (Kᶜ : Set X) := ⟨z.val.proj, z.property⟩
  have hbase : Continuous base :=
    ((continuous_proj (E := E.Fiber)).comp continuous_subtype_val).subtype_mk _
  let restricted (z : R) : TotalSpace Unit (Restrict E.Fiber Kᶜ) :=
    ⟨base z, z.val.snd⟩
  have hrestricted : Continuous restricted := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber
      (Subtype.val : (Kᶜ : Set X) → X)).continuous_iff]
    exact hbase.prodMk continuous_subtype_val
  let cylinder (z : R) : TotalSpace Unit
      ((Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X)) *ᵖ (Restrict E.Fiber Kᶜ)) :=
    ⟨(ρ z.val.proj, base z), z.val.snd⟩
  have hcylinder : Continuous cylinder := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict E.Fiber Kᶜ)
      (Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X))).continuous_iff]
    exact ((ρ.continuous.comp ((continuous_proj (E := E.Fiber)).comp
      continuous_subtype_val)).prodMk hbase).prodMk hrestricted
  have hout := (Pullback.continuous_lift Unit E.Fiber
    (Subtype.val : (Kᶜ : Set X) → X)).comp
      ((Pullback.continuous_lift Unit (Restrict E.Fiber Kᶜ)
        (Prod.snd : I × (Kᶜ : Set X) → (Kᶜ : Set X))).comp
          (H.iso.continuous_total.comp hcylinder))
  have hexterior : ContinuousOn (fun z : TotalSpace Unit E.Fiber ↦
      (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit E.Fiber)) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply hout.congr
    intro z
    change (⟨z.val.proj, H.iso.linearEquiv (ρ z.val.proj, base z) z.val.snd⟩ :
      TotalSpace Unit E.Fiber) = ⟨z.val.proj, eFiber z.val.proj z.val.snd⟩
    dsimp only [eFiber]
    rw [dite_eq_right z.property]
    rfl
  -- On U the exact formula is identity; these two open regions cover the total space.
  have hcontinuous : Continuous (fun z : TotalSpace Unit E.Fiber ↦
      (⟨z.proj, eFiber z.proj z.snd⟩ : TotalSpace Unit E.Fiber)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ U
    · apply continuousAt_id.congr_of_eventuallyEq
      filter_upwards [(hU.preimage (continuous_proj (E := E.Fiber))).mem_nhds hz] with w hw
      exact congrArg (TotalSpace.mk w.proj) (hidentity w.proj hw w.snd)
    · have hzK : z.proj ∉ K := fun h ↦ hz (hKU h)
      exact hexterior.continuousAt
        ((hK.isClosed.isOpen_compl.preimage (continuous_proj (E := E.Fiber))).mem_nhds hzK)
  let e : Hom E.Fiber E.Fiber :=
    { linearMap := fun x ↦ (eFiber x).toLinearMap, continuous_total := hcontinuous }
  -- Local finite bundle charts prove continuity of the inverse of these same fiber maps.
  refine ⟨L, hL, hKL, e.toIso (fun x ↦ (eFiber x).bijective), ?_⟩
  intro x v
  have hxK : (x : X) ∉ K := fun hx ↦ x.property (hKL hx)
  change eFiber x v = _
  dsimp only [eFiber]
  rw [dite_eq_right hxK, hρone x x.property]
  exact H.map_one ⟨x, hxK⟩ v

set_option backward.isDefEq.respectTransparency.types false in
/-- Uniform boundary homotopy gives an isomorphism of germs at infinity. -/
theorem supportBundleTriple_isIsomorphic_of_homotopic (E F : FiniteBundle X)
    (a b : CompactSupportTriple E.Fiber F.Fiber) (H : a.Homotopic b) :
    (SupportBundleTriple.ofBoundary E F a).IsIsomorphic
      (SupportBundleTriple.ofBoundary E F b) := by
  /- On the complement of the common compact control compose the homotopy with the inverse of
  its initial boundary map. This is a target-bundle automorphism homotopy starting at
  identity. The cutoff extension theorem gives a global target isomorphism with its
  prescribed endpoint outside a larger compact set. Together with the source identity it
  supplies the required commuting square there. -/
  classical
  obtain ⟨K, hK, ha, hb, ⟨H⟩⟩ := H
  let aK := (a.enlarge K hK ha).boundary
  let bK := (b.enlarge K hK hb).boundary
  -- Normalize the original path by its initial boundary on the target bundle.
  let J : IsoHomotopy (RelativeTriple.identity F.Fiber Kᶜ) (aK.symm.trans bK) :=
    { iso := (aK.symm.pullback ⟨Prod.snd, continuous_snd⟩).trans H.iso
      map_zero := by
        intro x v
        change H.iso.linearEquiv (0, x) ((aK.linearEquiv x).symm v) = v
        rw [H.map_zero]
        exact (aK.linearEquiv x).apply_symm_apply v
      map_one := by
        intro x v
        exact H.map_one x ((aK.linearEquiv x).symm v) }
  obtain ⟨L, hL, hKL, e, he⟩ := exists_iso_at_infinity F K hK (aK.symm.trans bK) J
  refine ⟨L, hL, ha.trans hKL, hb.trans hKL, Iso.refl E.Fiber, e, ?_⟩
  intro x v
  let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
  have hleft : (a.enlarge L hL (ha.trans hKL)).boundary.linearEquiv x v =
      aK.linearEquiv y v :=
    (a.enlarge_apply L hL (ha.trans hKL) x v).trans (a.enlarge_apply K hK ha y v).symm
  have hright : (b.enlarge L hL (hb.trans hKL)).boundary.linearEquiv x v =
      bK.linearEquiv y v :=
    (b.enlarge_apply L hL (hb.trans hKL) x v).trans (b.enlarge_apply K hK hb y v).symm
  -- The extended target map gives the exact original boundary square outside L.
  change e.linearEquiv x ((a.enlarge L hL (ha.trans hKL)).boundary.linearEquiv x v) =
    (b.enlarge L hL (hb.trans hKL)).boundary.linearEquiv x v
  rw [hleft, he]
  change bK.linearEquiv y ((aK.linearEquiv y).symm (aK.linearEquiv y v)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact hright.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- A triple plus its inverse is isomorphic at infinity to an identity triple. -/
theorem SupportBundleTriple.isIsomorphic_sum_inverse (a : SupportBundleTriple X) :
    (a.sum a.inverse).IsIsomorphic
      (SupportBundleTriple.identity (a.source.sum a.target)) := by
  /- Use a signed permutation to identify the target sum with the source sum. The standard
  elementary-matrix path from KA II.2.14 contracts the resulting boundary automorphism to
  identity outside the original compact control. Spatially cut off the path to a global
  isomorphism, allowing a larger compact control. -/
  let E := a.source.Fiber
  let F := a.target.Fiber
  let S := E ×ᵇ F
  let K := a.datum.control
  let : IsFiniteRank (Restrict E Kᶜ) := isFiniteRank_restrict Kᶜ
  let : IsFiniteRank (Restrict F Kᶜ) := isFiniteRank_restrict Kᶜ
  obtain ⟨d₀, hd₀, ⟨H⟩⟩ := a.datum.boundary.exists_signed_swap_homotopy
  let c : Iso (Restrict S Kᶜ) (Restrict E Kᶜ ×ᵇ Restrict F Kᶜ) := restrictSumIso Kᶜ
  let d : RelativeTriple S S Kᶜ := (c.trans d₀).trans c.symm
  let πK : C(I × (Kᶜ : Set X), (Kᶜ : Set X)) := ⟨Prod.snd, continuous_snd⟩
  -- Conjugate the actual rotation through the vector-preserving restriction comparison.
  let J : IsoHomotopy (RelativeTriple.identity S Kᶜ) d :=
    { iso := ((c.pullback πK).trans H.iso).trans (c.symm.pullback πK)
      map_zero := by
        intro x v
        change (c.linearEquiv x).symm
          (H.iso.linearEquiv (0, x) (c.linearEquiv x v)) = v
        exact (congrArg (c.linearEquiv x).symm (H.map_zero x _)).trans
          ((c.linearEquiv x).symm_apply_apply v)
      map_one := by
        intro x v
        exact congrArg (c.linearEquiv x).symm (H.map_one x _) }
  have hd (x : (Kᶜ : Set X)) (v : S x) : d.linearEquiv x v =
      (-(a.datum.boundary.linearEquiv x).symm v.2,
        a.datum.boundary.linearEquiv x v.1) := by
    apply (c.linearEquiv x).injective
    change (c.linearEquiv x) ((c.linearEquiv x).symm
      (d₀.linearEquiv x (c.linearEquiv x v))) = _
    rw [LinearEquiv.apply_symm_apply]
    erw [restrictSumIso_apply, hd₀, restrictSumIso_apply]
  obtain ⟨L, hL, hKL, e, he⟩ :=
    exists_iso_at_infinity (a.source.sum a.target) K a.datum.isCompact_control d J
  -- The global signed swap uses negation on the original first summand.
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E → X) *ᵖ E) := isFiniteRank_pullback p
  have hi : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hn : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, -z.snd⟩ : TotalSpace Unit E)) := by
    have hs := continuous_smul_section ((p : TotalSpace Unit E → X) *ᵖ E)
      (ContinuousMap.const _ (-1 : ℂ)) _ hi
    have hc := (Pullback.continuous_lift Unit E p).comp hs
    change Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, (-1 : ℂ) • z.snd⟩ : TotalSpace Unit E)) at hc
    simpa only [neg_one_smul] using hc
  let n : Iso E E :=
    { linearEquiv := fun _ ↦ LinearEquiv.neg ℂ
      continuous_total := hn
      continuous_symm := hn }
  let swap : Iso (F ×ᵇ E) S := sumCommIso.trans (n.sum (Iso.refl F))
  have hsum : (a.sum a.inverse).datum.control ⊆ L := Set.union_subset hKL hKL
  refine ⟨L, hL, hsum, Set.empty_subset _, e, swap, ?_⟩
  intro x v
  let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
  have hs : ((a.sum a.inverse).datum.enlarge L hL hsum).boundary.linearEquiv x v =
      (a.datum.boundary.linearEquiv y v.1,
        (a.datum.boundary.linearEquiv y).symm v.2) := by
    simp only [SupportBundleTriple.sum, SupportBundleTriple.ofBoundary,
      SupportBundleTriple.inverse, CompactSupportTriple.sum, CompactSupportTriple.inverse,
      CompactSupportTriple.enlarge, Iso.restrictTo_apply, RelativeTriple.sum_apply]
    rfl
  -- Outside this same enlarged control, the extended rotation is the required square.
  change swap.linearEquiv x
    (((a.sum a.inverse).datum.enlarge L hL hsum).boundary.linearEquiv x v) = _
  rw [hs]
  have hr := he x v
  simp only [SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
    CompactSupportTriple.enlarge, Iso.restrictTo_apply, CompactSupportTriple.ofIso]
  change (-(a.datum.boundary.linearEquiv y).symm v.2,
    a.datum.boundary.linearEquiv y v.1) = e.linearEquiv x v
  exact (hd y v).symm.trans hr.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition of boundary maps agrees with addition after identity stabilization. -/
theorem supportBundleTriple_isIsomorphic_sum_compose (E F G : FiniteBundle X)
    (a : CompactSupportTriple E.Fiber F.Fiber) (b : CompactSupportTriple F.Fiber G.Fiber) :
    ((SupportBundleTriple.ofBoundary E F a).sum
      (SupportBundleTriple.ofBoundary F G b)).IsIsomorphic
      ((SupportBundleTriple.ofBoundary E G (a.compose b)).sum
        (SupportBundleTriple.identity F)) := by
  /- Work outside the union of the two compact controls. The block-matrix path of KA II.2.16
  relates the direct-sum boundary map to the composite plus identity, after a signed
  permutation. Cut off its relative automorphism homotopy near the compact control to obtain
  the required global square at infinity. -/
  let K := a.control ∪ b.control
  have hK : IsCompact K := a.isCompact_control.union b.isCompact_control
  let aK := (a.enlarge K hK Set.subset_union_left).boundary
  let bK := (b.enlarge K hK Set.subset_union_right).boundary
  let S := G.Fiber ×ᵇ F.Fiber
  let : IsFiniteRank (Restrict G.Fiber Kᶜ) := isFiniteRank_restrict Kᶜ
  let : IsFiniteRank (Restrict F.Fiber Kᶜ) := isFiniteRank_restrict Kᶜ
  obtain ⟨d₀, hd₀, ⟨H⟩⟩ := bK.symm.exists_signed_swap_homotopy
  let c : Iso (Restrict S Kᶜ)
      (Restrict G.Fiber Kᶜ ×ᵇ Restrict F.Fiber Kᶜ) := restrictSumIso Kᶜ
  let d : RelativeTriple S S Kᶜ := (c.trans d₀).trans c.symm
  let πK : C(I × (Kᶜ : Set X), (Kᶜ : Set X)) := ⟨Prod.snd, continuous_snd⟩
  -- Karoubi's relative automorphism is the signed rotation for the same b⁻¹.
  let J : IsoHomotopy (RelativeTriple.identity S Kᶜ) d :=
    { iso := ((c.pullback πK).trans H.iso).trans (c.symm.pullback πK)
      map_zero := by
        intro x v
        change (c.linearEquiv x).symm
          (H.iso.linearEquiv (0, x) (c.linearEquiv x v)) = v
        exact (congrArg (c.linearEquiv x).symm (H.map_zero x _)).trans
          ((c.linearEquiv x).symm_apply_apply v)
      map_one := by
        intro x v
        exact congrArg (c.linearEquiv x).symm (H.map_one x _) }
  have hd (x : (Kᶜ : Set X)) (v : S x) : d.linearEquiv x v =
      (-bK.linearEquiv x v.2, (bK.linearEquiv x).symm v.1) := by
    apply (c.linearEquiv x).injective
    change (c.linearEquiv x) ((c.linearEquiv x).symm
      (d₀.linearEquiv x (c.linearEquiv x v))) = _
    rw [LinearEquiv.apply_symm_apply]
    erw [restrictSumIso_apply, hd₀, restrictSumIso_apply]
    rfl
  obtain ⟨L, hL, hKL, e, he⟩ := exists_iso_at_infinity (G.sum F) K hK d J
  -- The global signed swap matches the book's fixed target permutation.
  let p : C(TotalSpace Unit G.Fiber, X) := ⟨π Unit G.Fiber, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit G.Fiber → X) *ᵖ G.Fiber) :=
    isFiniteRank_pullback p
  have hi : Continuous (fun z : TotalSpace Unit G.Fiber ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit G.Fiber → X) *ᵖ G.Fiber))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit G.Fiber p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hn : Continuous (fun z : TotalSpace Unit G.Fiber ↦
      (⟨z.proj, -z.snd⟩ : TotalSpace Unit G.Fiber)) := by
    have hs := continuous_smul_section ((p : TotalSpace Unit G.Fiber → X) *ᵖ G.Fiber)
      (ContinuousMap.const _ (-1 : ℂ)) _ hi
    have hc := (Pullback.continuous_lift Unit G.Fiber p).comp hs
    change Continuous (fun z : TotalSpace Unit G.Fiber ↦
      (⟨z.proj, (-1 : ℂ) • z.snd⟩ : TotalSpace Unit G.Fiber)) at hc
    simpa only [neg_one_smul] using hc
  let n : Iso G.Fiber G.Fiber :=
    { linearEquiv := fun _ ↦ LinearEquiv.neg ℂ
      continuous_total := hn
      continuous_symm := hn }
  let swap : Iso (F.Fiber ×ᵇ G.Fiber) S :=
    sumCommIso.trans (n.sum (Iso.refl F.Fiber))
  have hright : (a.compose b).control ∪ (CompactSupportTriple.ofIso
      (Iso.refl F.Fiber)).control ⊆ L := Set.union_subset hKL (Set.empty_subset _)
  refine ⟨L, hL, hKL, hright, Iso.refl (E.sum F).Fiber, swap.trans e.symm, ?_⟩
  intro x v
  let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
  have hs : ((a.sum b).enlarge L hL hKL).boundary.linearEquiv x v =
      (aK.linearEquiv y v.1, bK.linearEquiv y v.2) := by
    simp only [CompactSupportTriple.sum, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.sum_apply, aK, bK]
    rfl
  have hc : (((a.compose b).sum (CompactSupportTriple.ofIso (Iso.refl F.Fiber))).enlarge
      L hL hright).boundary.linearEquiv x v =
      (bK.linearEquiv y (aK.linearEquiv y v.1), v.2) := by
    simp only [CompactSupportTriple.sum, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.sum_apply, CompactSupportTriple.compose,
      CompactSupportTriple.ofIso, Iso.trans, LinearEquiv.trans_apply, aK, bK]
    rfl
  -- Cancel the same extended automorphism, then check the literal block-matrix identity.
  change (e.linearEquiv x).symm (swap.linearEquiv x
    (((a.sum b).enlarge L hL hKL).boundary.linearEquiv x v)) =
    (((a.compose b).sum (CompactSupportTriple.ofIso (Iso.refl F.Fiber))).enlarge
      L hL hright).boundary.linearEquiv x v
  rw [hs, hc]
  apply (e.linearEquiv x).injective
  rw [LinearEquiv.apply_symm_apply, he]
  rw [hd]
  change (-bK.linearEquiv y v.2, aK.linearEquiv y v.1) =
    (-bK.linearEquiv y v.2, (bK.linearEquiv y).symm
      (bK.linearEquiv y (aK.linearEquiv y v.1)))
  rw [LinearEquiv.symm_apply_apply]

end AtiyahSinger.ComplexBundle
