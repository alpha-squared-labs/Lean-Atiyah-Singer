/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedCompactControl
public import AtiyahSinger.Topology.AssociatedEquivariantBundle
public import AtiyahSinger.Topology.EquivariantSupportTriple
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Associated descent of the original support boundary

Public module ID: M1549.

An equivariant compact-support triple descends to the actual associated vector
families over P associated Y. Its boundary is characterized on every original
representative by [p,(y,v)] mapped to the class of its original boundary
image in the same principal coordinates. The selected boundary is packaged
with the actual image of P times the original control.

The boundary construction uses no compactness or separation. Compact Hausdorff
B is used only to prove compactness of the descended invariant control. Neither
P nor G is required to be compact. In particular we do not form an intermediate
compact-support pullback to P times Y: its inverse-image control need not be
compact. Original varying ranks and arbitrary fiber universes are retained.

Sources: SG III.13, pp.251--253, and ASI I Section 2 for associated descent;
HU IV.5--7 for principal and associated local charts. The explicit boundary
uniqueness and arbitrary-group compact-control version are project supplements.
The construction certificates below retain these original boundary maps and quotients.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : Y → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant

set_option backward.isDefEq.respectTransparency.types false in
/-- The original equivariant boundary descends uniquely on the exact associated exterior. -/
theorem existsUnique_associatedSupportBoundary (hP : IsPrincipalBundle G projection)
    (a : CompactSupportTriple E F) (σ : EquivariantStructure G E)
    (τ : EquivariantStructure G F) (ha : a.IsEquivariant σ τ) :
    ∃! α : RelativeTriple (AssociatedEquivariantFiber hP σ)
        (AssociatedEquivariantFiber hP τ) (associatedControl G P Y a.control)ᶜ,
      ∀ (p : P) (y : (a.controlᶜ : Set Y)) (v : E y),
        α.linearEquiv
            ⟨associatedBundleMk G P Y p y, fun hz ↦ y.property
              ((associatedControl_mk_mem_iff a.control ha.invariant_control p y).mp hz)⟩
            (associatedEquivariantFiberMk hP σ p y rfl v) =
          associatedEquivariantFiberMk hP τ p y rfl (a.boundary.linearEquiv y v) := by
  /- Stage 1: invariance identifies the associated exterior on every original
  representative. Extend the boundary by zero only as an algebraic map outside
  that exterior. Intertwining makes the resulting quotient function well-defined.
  No continuity of that extension across the control is asserted or used.
  Stage 2: each actual associated fiber has the specified linear, bijective
  representative coordinates. The descended boundary is the original boundary
  in those coordinates, hence is linear and bijective with no rank alteration.
  Stage 3: the original diagonal orbit quotient is open. Its restriction to the
  exact inverse image of any subspace remains a quotient map, even when the
  control is not closed. On these representatives the map is the continuous
  original boundary. The native pullback topologies therefore give a continuous
  bundle map on the exact associated exterior. The finite-rank bundle criterion
  supplies continuity of this same map's inverse.
  Stage 4: every exterior fiber is covered by any of its original representative
  maps, so the specified formula determines the full Iso uniquely. -/
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : MulAction G (TotalSpace Unit F) := τ.toMulAction
  let : ContinuousSMul G (TotalSpace Unit E) := ⟨σ.continuous_action⟩
  let : ContinuousSMul G (TotalSpace Unit F) := ⟨τ.continuous_action⟩
  let A := (associatedControl G P Y a.control)ᶜ
  let E' := AssociatedEquivariantFiber hP σ
  let F' := AssociatedEquivariantFiber hP τ
  let : IsFiniteRank E' := isFiniteRank_associatedEquivariant hP σ
  let : IsFiniteRank F' := isFiniteRank_associatedEquivariant hP τ
  let : IsFiniteRank (Restrict E' A) := isFiniteRank_restrict A
  let : IsFiniteRank (Restrict F' A) := isFiniteRank_restrict A
  let HE := associatedEquivariantTotalHomeomorph hP σ
  let HF := associatedEquivariantTotalHomeomorph hP τ
  -- A zero extension defines an algebraic quotient map only; continuity is proved on A below.
  let f (w : TotalSpace Unit E) : TotalSpace Unit F :=
    if hy : w.proj ∈ a.controlᶜ then
      ⟨w.proj, a.boundary.linearEquiv ⟨w.proj, hy⟩ w.snd⟩ else ⟨w.proj, 0⟩
  have hfp (w : TotalSpace Unit E) : (f w).proj = w.proj := by
    dsimp only [f]
    split <;> rfl
  have hfeq (g : G) (w : TotalSpace Unit E) : f (g • w) = g • f w := by
    by_cases hy : w.proj ∈ a.controlᶜ
    · have hgy : (g • w).proj ∈ a.controlᶜ :=
        fun h ↦ hy ((ha.invariant_control g w.proj).mp h)
      dsimp only [f]
      rw [dite_eq_left hy, dite_eq_left hgy]
      exact congrArg (fun v : F (g • w.proj) ↦
        (⟨g • w.proj, v⟩ : TotalSpace Unit F)) (ha.boundary_intertwines g ⟨_, hy⟩ w.snd)
    · have hgy : (g • w).proj ∉ a.controlᶜ := by
        intro h
        exact hy (fun hk ↦ h ((ha.invariant_control g w.proj).mpr hk))
      dsimp only [f]
      rw [dite_eq_right hy, dite_eq_right hgy]
      change (⟨g • w.proj, 0⟩ : TotalSpace Unit F) = ⟨g • w.proj, τ.linearMap g w.proj 0⟩
      rw [map_zero]
  let qmap : AssociatedBundle G P (TotalSpace Unit E) →
      AssociatedBundle G P (TotalSpace Unit F) :=
    Quotient.map (fun t : P × TotalSpace Unit E ↦ (t.1, f t.2)) (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      exact ⟨g, Prod.ext rfl (hfeq g⁻¹ x.2)⟩)
  have hproj (q : AssociatedBundle G P (TotalSpace Unit E)) :
      associatedEquivariantProjection τ (qmap q) = associatedEquivariantProjection σ q := by
    induction q using Quotient.inductionOn with
    | h w => exact congrArg (associatedBundleMk G P Y w.1) (hfp w.2)
  let fiberMap (z : A) (v : E' z) : F' z :=
    ⟨qmap v.val, (hproj v.val).trans v.property⟩
  have hformula (p : P) (y : (a.controlᶜ : Set Y)) {z : A}
      (hz : associatedBundleMk G P Y p y = z.val) (v : E y) :
      fiberMap z (associatedEquivariantFiberMk hP σ p y hz v) =
        associatedEquivariantFiberMk hP τ p y hz (a.boundary.linearEquiv y v) := by
    apply Subtype.ext
    change associatedBundleMk G P (TotalSpace Unit F) p (f ⟨y, v⟩) = _
    dsimp only [f]
    rw [dite_eq_left y.property]
    rfl
  have hexterior (z : A) : (Quotient.out z.val).2 ∈ a.controlᶜ := by
    intro h
    apply z.property
    rw [← Quotient.out_eq z.val]
    exact (associatedControl_mk_mem_iff a.control ha.invariant_control _ _).mpr h
  -- Each original representative is linear and bijective for the already specified fiber algebra.
  have hlinear (z : A) : IsLinearMap ℂ (fiberMap z) := by
    let p := (Quotient.out z.val).1
    let y : (a.controlᶜ : Set Y) := ⟨(Quotient.out z.val).2, hexterior z⟩
    have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
    have hE := associatedEquivariantFiberMk_isLinear hP σ p y hz
    have hF := associatedEquivariantFiberMk_isLinear hP τ p y hz
    have hsurj := (associatedEquivariantFiberMk_bijective hP σ p y hz).2
    constructor
    · intro u v
      obtain ⟨u₀, rfl⟩ := hsurj u
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_add, hformula, hformula, hformula]
      exact (congrArg (associatedEquivariantFiberMk hP τ p y hz)
        ((a.boundary.linearEquiv y).map_add u₀ v₀)).trans (hF.map_add _ _)
    · intro c v
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_smul, hformula, hformula]
      exact (congrArg (associatedEquivariantFiberMk hP τ p y hz)
        ((a.boundary.linearEquiv y).map_smul c v₀)).trans (hF.map_smul _ _)
  have hbij (z : A) : Function.Bijective (fiberMap z) := by
    let p := (Quotient.out z.val).1
    let y : (a.controlᶜ : Set Y) := ⟨(Quotient.out z.val).2, hexterior z⟩
    have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
    have hE := associatedEquivariantFiberMk_bijective hP σ p y hz
    have hF := associatedEquivariantFiberMk_bijective hP τ p y hz
    constructor
    · intro u v huv
      obtain ⟨u₀, rfl⟩ := hE.2 u
      obtain ⟨v₀, rfl⟩ := hE.2 v
      rw [hformula, hformula] at huv
      exact congrArg (associatedEquivariantFiberMk hP σ p y hz)
        ((a.boundary.linearEquiv y).injective (hF.1 huv))
    · intro v
      obtain ⟨v₀, rfl⟩ := hF.2 v
      refine ⟨associatedEquivariantFiberMk hP σ p y hz
        ((a.boundary.linearEquiv y).symm v₀), ?_⟩
      rw [hformula, LinearEquiv.apply_symm_apply]
  -- The original diagonal orbit quotient is open, so arbitrary subspace restrictions descend.
  let q : P × TotalSpace Unit E → AssociatedBundle G P (TotalSpace Unit E) := Quotient.mk _
  have hq : IsOpenQuotientMap q := by
    refine ⟨Quotient.mk_surjective, continuous_quot_mk, ?_⟩
    intro U hU
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    change IsOpen (q ⁻¹' (q '' U))
    have hs : q ⁻¹' (q '' U) = ⋃ g : G,
        (fun t : P × TotalSpace Unit E ↦ (MulOpposite.op g • t.1, g⁻¹ • t.2)) ⁻¹' U := by
      ext t
      constructor
      · rintro ⟨u, hu, hqu⟩
        obtain ⟨g, hg⟩ := Quotient.exact hqu.symm
        refine Set.mem_iUnion.mpr ⟨g, ?_⟩
        change (MulOpposite.op g • t.1, g⁻¹ • t.2) ∈ U
        rw [← hg]
        exact hu
      · intro ht
        obtain ⟨g, hg⟩ := Set.mem_iUnion.mp ht
        refine ⟨(MulOpposite.op g • t.1, g⁻¹ • t.2), hg, ?_⟩
        apply Eq.symm
        exact Quotient.sound ⟨g, rfl⟩
    rw [hs]
    apply isOpen_iUnion
    intro g
    apply hU.preimage
    have hc₁ : Continuous (fun t : P × TotalSpace Unit E ↦ MulOpposite.op g • t.1) :=
      continuous_const.smul continuous_fst
    have hc₂ : Continuous (fun t : P × TotalSpace Unit E ↦ g⁻¹ • t.2) :=
      σ.continuous_action.comp (continuous_const.prodMk continuous_snd)
    exact hc₁.prodMk hc₂
  let S : Set (AssociatedBundle G P (TotalSpace Unit E)) :=
    associatedEquivariantProjection σ ⁻¹' A
  let qS : (q ⁻¹' S) → S := S.restrictPreimage q
  have hqS : Topology.IsQuotientMap qS := by
    apply isQuotientMap_of_isOpenQuotientMap_of_isInducing
      (Subtype.val : (q ⁻¹' S) → P × TotalSpace Unit E)
      (Subtype.val : S → AssociatedBundle G P (TotalSpace Unit E)) qS q rfl
      Topology.IsInducing.subtypeVal (hq.surjective.restrictPreimage S)
      hq Topology.IsEmbedding.subtypeVal
    rintro t ⟨u, ⟨w, rfl⟩, hu⟩
    refine ⟨⟨t, ?_⟩, rfl⟩
    change q t ∈ S
    rw [← hu]
    exact w.property
  have hcontinuous : Continuous (fun w : TotalSpace Unit (Restrict E' A) ↦
      (⟨w.proj, fiberMap w.proj w.snd⟩ : TotalSpace Unit (Restrict F' A))) := by
    -- On quotient representatives the restricted map is exactly the continuous original boundary.
    have hQ : Continuous (fun w : S ↦ qmap w.val) := by
      apply hqS.continuous_iff.mpr
      let lift (w : (q ⁻¹' S)) : TotalSpace Unit (Restrict E a.controlᶜ) :=
        ⟨⟨w.val.2.proj, fun hy ↦ w.property
          ((associatedControl_mk_mem_iff a.control ha.invariant_control _ _).mpr hy)⟩,
          w.val.2.snd⟩
      have hclift : Continuous lift := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E
          (Subtype.val : (a.controlᶜ : Set Y) → Y)).continuous_iff]
        exact (((continuous_proj (E := E)).comp (continuous_snd.comp
          continuous_subtype_val)).subtype_mk _).prodMk
          (continuous_snd.comp continuous_subtype_val)
      have hcq : Continuous
          (Quotient.mk (associatedBundleSetoid G P (TotalSpace Unit F))) := continuous_quot_mk
      have hc := hcq.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((Pullback.continuous_lift Unit F Subtype.val).comp
            (a.boundary.continuous_total.comp hclift)))
      apply hc.congr
      intro w
      change associatedBundleMk G P (TotalSpace Unit F) w.val.1
        ⟨w.val.2.proj, a.boundary.linearEquiv (lift w).proj w.val.2.snd⟩ =
          associatedBundleMk G P (TotalSpace Unit F) w.val.1 (f w.val.2)
      dsimp only [f]
      rw [dite_eq_left (lift w).proj.property]
    -- The native pullback topology records the exterior base and the original quotient vector.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' (Subtype.val : A → _)).continuous_iff]
    apply (Pullback.continuous_proj Unit E' Subtype.val).prodMk
    have hinmem (w : TotalSpace Unit (Restrict E' A)) :
        HE (Pullback.lift Subtype.val w) ∈ S := by
      change associatedEquivariantProjection σ w.snd.val ∈ A
      rw [w.snd.property]
      exact w.proj.property
    have hin : Continuous (fun w : TotalSpace Unit (Restrict E' A) ↦
        (⟨HE (Pullback.lift Subtype.val w), hinmem w⟩ : S)) :=
      (HE.continuous_toFun.comp (Pullback.continuous_lift Unit E' Subtype.val)).subtype_mk _
    have hc := HF.symm.continuous_toFun.comp (hQ.comp hin)
    apply hc.congr
    intro w
    apply HF.injective
    exact HF.apply_symm_apply (qmap w.snd.val)
  let α : Hom (Restrict E' A) (Restrict F' A) :=
    { linearMap z := IsLinearMap.mk' (fiberMap z) (hlinear z)
      continuous_total := hcontinuous }
  let e := α.toIso hbij
  refine ⟨e, ?_, ?_⟩
  · intro p y v
    exact hformula p y rfl v
  · -- Every actual exterior fiber is covered by one original representative map.
    intro β hβ
    have hβformula (p : P) (y : (a.controlᶜ : Set Y)) {z : A}
        (hz : associatedBundleMk G P Y p y = z.val) (v : E y) :
        β.linearEquiv z (associatedEquivariantFiberMk hP σ p y hz v) =
          associatedEquivariantFiberMk hP τ p y hz (a.boundary.linearEquiv y v) := by
      rcases z with ⟨z, hzA⟩
      cases hz
      exact hβ p y v
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    let p := (Quotient.out z.val).1
    let y : (a.controlᶜ : Set Y) := ⟨(Quotient.out z.val).2, hexterior z⟩
    have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
    obtain ⟨v₀, rfl⟩ := (associatedEquivariantFiberMk_bijective hP σ p y hz).2 v
    exact (hβformula p y hz v₀).trans (hformula p y hz v₀).symm

/-- Select the unique boundary with the specified original-vector formula. -/
def associatedSupportBoundary (hP : IsPrincipalBundle G projection)
    (a : CompactSupportTriple E F) (σ : EquivariantStructure G E)
    (τ : EquivariantStructure G F) (ha : a.IsEquivariant σ τ) :
    RelativeTriple (AssociatedEquivariantFiber hP σ)
      (AssociatedEquivariantFiber hP τ) (associatedControl G P Y a.control)ᶜ :=
  (existsUnique_associatedSupportBoundary hP a σ τ ha).choose

/-- The selected boundary retains the original boundary value on every representative. -/
theorem associatedSupportBoundary_apply (hP : IsPrincipalBundle G projection)
    (a : CompactSupportTriple E F) (σ : EquivariantStructure G E)
    (τ : EquivariantStructure G F) (ha : a.IsEquivariant σ τ)
    (p : P) (y : (a.controlᶜ : Set Y)) (v : E y) :
    (associatedSupportBoundary hP a σ τ ha).linearEquiv
        ⟨associatedBundleMk G P Y p y, fun hz ↦ y.property
          ((associatedControl_mk_mem_iff a.control ha.invariant_control p y).mp hz)⟩
        (associatedEquivariantFiberMk hP σ p y rfl v) =
      associatedEquivariantFiberMk hP τ p y rfl (a.boundary.linearEquiv y v) := by
  /- Read the representative formula from the same unique-existence witness
  used in associatedSupportBoundary. Neither the control nor either quotient
  family is changed when selecting the boundary. -/
  exact (existsUnique_associatedSupportBoundary hP a σ τ ha).choose_spec.1 p y v

/-- Descend the original triple using its actual associated control and selected boundary. -/
def associatedSupportTriple [CompactSpace B] [T2Space B]
    (hP : IsPrincipalBundle G projection) (a : CompactSupportTriple E F)
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F)
    (ha : a.IsEquivariant σ τ) :
    CompactSupportTriple (AssociatedEquivariantFiber hP σ)
      (AssociatedEquivariantFiber hP τ) where
  control := associatedControl G P Y a.control
  isCompact_control :=
    isCompact_associatedControl hP a.control a.isCompact_control ha.invariant_control
  boundary := associatedSupportBoundary hP a σ τ ha

end AtiyahSinger
