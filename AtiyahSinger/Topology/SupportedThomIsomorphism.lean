/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.KOrientation
public import AtiyahSinger.Topology.ThomDirectSum
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# The supported Thom isomorphism

Public module ID: M2215.

The proof retains the prescribed tensor operator. Compact Thom and the split
infinity fiber prove the trivial-bundle case. Finite complements and the ordered
direct-sum formula then treat bundles on compact base windows. Finally the
representation and vanishing criteria for the original compact-support groups
pass to arbitrary locally compact Hausdorff bases.

Sources: Spin Geometry C.13; Karoubi IV.1.10--1.11 and II.4.21.
-/

@[expose] public noncomputable section

/- This local command assigns the supplied hierarchical names to anonymous instance
parameters and bundle-product lambda binders in the four public interfaces below.
It stops at declaration values. Building names component by component supports their
internal `_@` parts. -/
local syntax "legacy_binder_names " "[" str,* "]" " in " command : command
local macro_rules
  | `(legacy_binder_names [$names:str,*] in $cmd:command) => do
    let names := names.getElems
    let (cmd, i) ← (cmd.raw.replaceM (m := StateT Nat Lean.MacroM) fun stx => do
      let i ← get
      if stx.isOfKind ``Lean.Parser.Command.declValSimple then
        return some stx
      else if stx.isOfKind ``Lean.Parser.Term.instBinder then
        if stx[1].getNumArgs != 0 then
          liftM (Lean.Macro.throwErrorAt stx "expected an anonymous instance binder")
        if i ≥ names.size then
          liftM (Lean.Macro.throwErrorAt stx "too many instance binders")
        let name := names[i]!.getString.splitOn "." |>.foldl (fun name part =>
          match part.toNat? with
          | some k => Lean.Name.num name k
          | none => Lean.Name.str name part) Lean.Name.anonymous
        let id := Lean.mkIdent name
        set (i + 1)
        let type : Lean.TSyntax `term := ⟨stx[2]⟩
        return some (← `(bracketedBinder| [$id:ident : $type:term])).raw
      else
        match stx with
        | `(term| $left:term ×ᵇ $right:term) => do
          if i ≥ names.size then
            liftM (Lean.Macro.throwErrorAt stx "missing bundle-product binder name")
          let name := names[i]!.getString.splitOn "." |>.foldl (fun name part =>
            match part.toNat? with
            | some k => Lean.Name.num name k
            | none => Lean.Name.str name part) Lean.Name.anonymous
          let id := Lean.mkIdent name
          set (i + 1)
          return some (← `(term| fun $id:ident ↦ $left $id × $right $id)).raw
        | _ => return none).run 0
    if i != names.size then
      Lean.Macro.throwError "unused instance names"
    return cmd

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle Topology

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

private theorem supportedThomHom_bijective_compact {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {E : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) : Function.Bijective h.supportedThomHom := by
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  change Function.Bijective (ComplexBundle.supportedThomHom E h.continuous_pairing)
  rw [supportedThomHom_compact]
  exact (exteriorThomHom_bijective E h.continuous_pairing).comp
    (compactSupportKZeroCompactEquiv X).bijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the specified Thom map and its compactification restriction square.
/-- Restricting the constant bundle on the compactification gives the native Thom isomorphism. -/
private theorem supportedThomHom_bijective_compactification_trivial
    (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    let T := Bundle.Trivial (OnePoint X) V
    letI := modelTopology V T
    letI := isFiniteRank_model V T
    let f : C(X, OnePoint X) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
    ∀ h : ContinuousHermitianMetric T,
      Function.Bijective (h.pullback f).supportedThomHom := by
  classical
  let B := OnePoint X
  let T := Bundle.Trivial B V
  let := modelTopology V T
  let := isFiniteRank_model V T
  let := FiniteDimensional.proper ℂ V
  let f : C(X, B) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  dsimp only
  intro h
  let R := f *ᵖ T
  let := isFiniteRank_pullback (E := T) f
  let q := pullbackTotalMap T f
  have hf : IsOpenEmbedding f := OnePoint.isOpenEmbedding_coe
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties T f).2 hf
  let A : Set B := (Set.range f)ᶜ
  let N : Set (TotalSpace Unit T) := (Set.range q)ᶜ
  have hA : IsClosed A := hf.isOpen_range.isClosed_compl
  have hN : IsClosed N := hq.isOpen_range.isClosed_compl
  let := hA.locallyCompactSpace
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let := hN.locallyCompactSpace
  let a₀ : A := ⟨OnePoint.infty, by rintro ⟨x, hx⟩; cases hx⟩
  have hpoint (a : A) : a.val = OnePoint.infty := by
    rcases a with ⟨a, ha⟩
    cases a using OnePoint.rec with
    | infty => rfl
    | coe x => exact (ha ⟨x, rfl⟩).elim
  have hbase (z : N) : z.val.proj ∈ A := by
    rintro ⟨x, hx⟩
    apply z.property
    refine ⟨⟨x, z.val.snd⟩, ?_⟩
    exact TotalSpace.ext hx (by rfl)
  have hinfty (v : V) : (⟨OnePoint.infty, v⟩ : TotalSpace Unit T) ∈ N := by
    rintro ⟨z, hz⟩
    have hp := congrArg TotalSpace.proj hz
    cases hp
  let eB := (unitTotalHomeomorph V T).trans (Bundle.Trivial.homeomorphProd B V)
  let r : C(B, A) := ContinuousMap.const B a₀
  have hr (a : A) : r a.val = a := by
    apply Subtype.ext
    exact (hpoint a).symm
  let rN : C(TotalSpace Unit T, N) :=
    ⟨fun z ↦ ⟨⟨OnePoint.infty, z.snd⟩, hinfty z.snd⟩,
      (eB.symm.continuous.comp (continuous_const.prodMk eB.continuous.snd)).subtype_mk _⟩
  have hrN (z : N) : rN z.val = z := by
    apply Subtype.ext
    exact TotalSpace.ext (hpoint ⟨z.val.proj, hbase z⟩).symm (by rfl)
  have hproperN : IsProperMap rN :=
    isProperMap_of_comp_of_t2 rN.continuous
      (eB.continuous.snd.comp continuous_subtype_val)
      (show IsProperMap ((fun z : N ↦ z.val.snd) ∘ rN) from
        isProperMap_snd_of_compactSpace.comp eB.isProperMap)
  let J := compactSupportKZeroOpenPushforward f hf
  let Q := compactSupportKZeroOpenPushforward q hq
  have hJ : Function.Injective J :=
    compactSupportKZeroOpenPushforward_injective_of_retraction f hf r
      r.continuous.isProperMap hr
  have hQ : Function.Injective Q :=
    compactSupportKZeroOpenPushforward_injective_of_retraction q hq rN hproperN hrN
  -- The first square is the actual extension formula, with the same tensor operator.
  have hsquare (a : CompactSupportKZero X) :
      Q ((h.pullback f).supportedThomHom a) = h.supportedThomHom (J a) :=
    DFunLike.congr_fun (h.supportedThomHom_openPushforward f hf) a
  have hB := supportedThomHom_bijective_compact h
  constructor
  · intro a b hab
    apply hJ
    apply hB.injective
    rw [← hsquare, ← hsquare, hab]
  · intro u
    obtain ⟨v, hv⟩ := hB.surjective (Q u)
    let i : C(A, B) := ⟨Subtype.val, continuous_subtype_val⟩
    let j : C(N, TotalSpace Unit T) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : IsProperMap i := hA.isClosedEmbedding_subtypeVal.isProperMap
    have hj : IsProperMap j := hN.isClosedEmbedding_subtypeVal.isProperMap
    let S := i *ᵖ T
    let := isFiniteRank_pullback (E := T) i
    have hkmem (z : TotalSpace Unit S) :
        (⟨z.proj.val, z.snd⟩ : TotalSpace Unit T) ∈ N := by
      rintro ⟨w, hw⟩
      exact z.proj.property ⟨w.proj, congrArg TotalSpace.proj hw⟩
    let k : C(TotalSpace Unit S, N) :=
      ⟨fun z ↦ ⟨⟨z.proj.val, z.snd⟩, hkmem z⟩,
        (Pullback.continuous_lift Unit T i).subtype_mk hkmem⟩
    have hk : IsProperMap k :=
      isProperMap_of_comp_of_t2 k.continuous continuous_subtype_val
        ((pullbackTotalMap_properties T i).1 hi)
    have hz : compactSupportKZeroPullback j hj (Q u) = 0 :=
      (mem_range_compactSupportKZeroOpenPushforward_iff q hq (Q u)).mp ⟨u, rfl⟩
    rw [← hv] at hz
    have hz' := congrArg (compactSupportKZeroPullback k hk) hz
    rw [map_zero, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp] at hz'
    have hrestriction := DFunLike.congr_fun (h.supportedThomHom_pullback i hi) v
    have hzero : (h.pullback i).supportedThomHom
        (compactSupportKZeroPullback i hi v) = 0 :=
      hrestriction.trans hz'
    have hAv : compactSupportKZeroPullback i hi v = 0 := by
      apply (supportedThomHom_bijective_compact (h.pullback i)).injective
      exact hzero.trans (map_zero _).symm
    -- Exactness supplies an original input, and the split target extension verifies it.
    obtain ⟨a, ha⟩ := (mem_range_compactSupportKZeroOpenPushforward_iff f hf v).mpr hAv
    refine ⟨a, hQ ?_⟩
    rw [hsquare, ha, hv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the same trivial bundle and the metric-specified Thom homomorphism.
private theorem supportedThomHom_bijective_trivial
    (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    let T := Bundle.Trivial X V
    letI := modelTopology V T
    letI := isFiniteRank_model V T
    ∀ h : ContinuousHermitianMetric T, Function.Bijective h.supportedThomHom := by
  let B := OnePoint X
  let TB := Bundle.Trivial B V
  let TX := Bundle.Trivial X V
  let := modelTopology V TB
  let := modelTopology V TX
  let := isFiniteRank_model V TB
  let := isFiniteRank_model V TX
  let eB := (unitTotalHomeomorph V TB).trans (Bundle.Trivial.homeomorphProd B V)
  let eX := (unitTotalHomeomorph V TX).trans (Bundle.Trivial.homeomorphProd X V)
  dsimp only
  intro h
  have hinner : Continuous (fun z : TotalSpace Unit (TB ×ᵇ TB) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (eB.continuous.snd.comp (continuous_sum_fst (E := TB) (F := TB))).inner
      (eB.continuous.snd.comp (continuous_sum_snd (E := TB) (F := TB)))
  let hB := ofInnerProduct TB hinner
  let f : C(X, B) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let R := f *ᵖ TB
  let := isFiniteRank_pullback (E := TB) f
  let d : Hom R TX :=
    { linearMap _ := LinearMap.id
      continuous_total := eX.symm.continuous.comp
        (continuous_proj.prodMk
          (eB.continuous.snd.comp (Pullback.continuous_lift Unit TB f))) }
  let e := d.toIso (fun _ ↦ Function.bijective_id)
  have hR : Function.Bijective (hB.pullback f).supportedThomHom :=
    supportedThomHom_bijective_compactification_trivial X V hB
  have hsquare := (hB.pullback f).supportedThomHom_iso h e
  rw [← hsquare]
  exact (compactSupportKZeroHomeomorph_bijective e.totalHomeomorph).comp hR

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the original trivialization and its specified Thom naturality square.
private theorem supportedThomHom_bijective_of_trivialization
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (n : ℕ) :
    letI := trivialTopology (X := X) n
    Iso E (Bundle.Trivial X (Fin n → ℂ)) → Function.Bijective h.supportedThomHom := by
  let := trivialTopology (X := X) n
  let := isFiniteRank_trivial (X := X) n
  intro e
  let V := EuclideanSpace ℂ (Fin n)
  let T := Bundle.Trivial X V
  let := modelTopology V T
  let := isFiniteRank_model V T
  let eT := (unitTotalHomeomorph V T).trans (Bundle.Trivial.homeomorphProd X V)
  let c : (Fin n → ℂ) ≃L[ℂ] V := (EuclideanSpace.equiv (Fin n) ℂ).symm
  let d : Hom (Bundle.Trivial X (Fin n → ℂ)) T :=
    { linearMap _ := c.toLinearMap
      continuous_total := by
        have hc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ)) ↦
            (z.proj, z.snd)) := continuous_induced_dom
        exact eT.symm.continuous.comp (hc.fst.prodMk (c.continuous.comp hc.snd)) }
  let j := e.trans (d.toIso (fun _ ↦ c.bijective))
  have hinner : Continuous (fun z : TotalSpace Unit (T ×ᵇ T) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (eT.continuous.snd.comp (continuous_sum_fst (E := T) (F := T))).inner
      (eT.continuous.snd.comp (continuous_sum_snd (E := T) (F := T)))
  let hT := ofInnerProduct T hinner
  have hTbij := supportedThomHom_bijective_trivial X V hT
  have hsquare := h.supportedThomHom_iso hT j
  rw [← hsquare] at hTbij
  exact Function.Bijective.of_comp_left
    (f := compactSupportKZeroHomeomorph j.totalHomeomorph) (g := h.supportedThomHom) hTbij
    (compactSupportKZeroHomeomorph_bijective j.totalHomeomorph).injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the pullback of the original direct-sum trivialization.
private def pullbackSumTrivialization
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {E F : Y → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (f : C(X, Y)) (n : ℕ) :
    letI := trivialTopology (X := Y) n
    letI := trivialTopology (X := X) n
    Iso (E ×ᵇ F) (Bundle.Trivial Y (Fin n → ℂ)) →
      Iso ((f *ᵖ E) ×ᵇ (f *ᵖ F)) (Bundle.Trivial X (Fin n → ℂ)) := by
  let := trivialTopology (X := Y) n
  let := trivialTopology (X := X) n
  let := isFiniteRank_trivial (X := Y) n
  let := isFiniteRank_trivial (X := X) n
  intro e
  let s : Hom ((f *ᵖ E) ×ᵇ (f *ᵖ F)) (f *ᵖ (E ×ᵇ F)) :=
    { linearMap _ := LinearMap.id
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ F) f).continuous_iff]
        apply continuous_proj.prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit E f).comp
          (continuous_sum_fst (E := f *ᵖ E) (F := f *ᵖ F))).prodMk
            ((Pullback.continuous_lift Unit F f).comp
              (continuous_sum_snd (E := f *ᵖ E) (F := f *ᵖ F))) }
  exact ((s.toIso (fun _ ↦ Function.bijective_id)).trans (e.pullback f)).trans
    (pullbackTrivialIso f n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supportedThomHom_injective_of_trivial_sum
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F) (n : ℕ) :
    letI := trivialTopology (X := X) n
    Iso (E ×ᵇ F) (Bundle.Trivial X (Fin n → ℂ)) →
      Function.Injective hE.supportedThomHom := by
  let := trivialTopology (X := X) n
  intro e
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let := isFiniteRank_pullback (E := F) p
  have hsum := supportedThomHom_bijective_of_trivialization (hE.sum hF) n e
  have hcomp := (compactSupportKZeroHomeomorph_bijective
    (sumTotalPullbackHomeomorph (E := E) (F := F))).comp hsum
  have hformula := supportedThomHom_sum hE hF
  change Function.Bijective
    ((compactSupportKZeroHomeomorph (sumTotalPullbackHomeomorph (E := E) (F := F))).comp
      (hE.sum hF).supportedThomHom) at hcomp
  rw [hformula] at hcomp
  exact Function.Injective.of_comp (f := (hF.pullback p).supportedThomHom) hcomp.injective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the same finite complement and the ordered composite Thom maps.
/-- A finite trivial complement makes the specified supported Thom operator bijective. -/
theorem supportedThomHom_bijective_of_trivial_sum
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F) (n : ℕ) :
    letI := trivialTopology (X := X) n
    Iso (E ×ᵇ F) (Bundle.Trivial X (Fin n → ℂ)) →
      Function.Bijective hE.supportedThomHom := by
  let := trivialTopology (X := X) n
  intro e
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let := isFiniteRank_pullback (E := F) p
  let := isFiniteRank_pullback (E := E) p
  -- The total sum is trivial, so its actual ordered composite is bijective.
  have hsum := supportedThomHom_bijective_of_trivialization (hE.sum hF) n e
  have hcomp := (compactSupportKZeroHomeomorph_bijective
    (sumTotalPullbackHomeomorph (E := E) (F := F))).comp hsum
  have hformula := supportedThomHom_sum hE hF
  change Function.Bijective
    ((compactSupportKZeroHomeomorph (sumTotalPullbackHomeomorph (E := E) (F := F))).comp
      (hE.sum hF).supportedThomHom) at hcomp
  rw [hformula] at hcomp
  -- The pulled-back complement has the pulled-back E as its own finite complement.
  let := trivialTopology (X := TotalSpace Unit E) n
  let c := pullbackSumTrivialization p n ((sumCommIso (E := F) (F := E)).trans e)
  have hsecond := supportedThomHom_injective_of_trivial_sum
    (hF.pullback p) (hE.pullback p) n c
  exact Function.Bijective.of_comp_left (f := (hF.pullback p).supportedThomHom)
    (g := hE.supportedThomHom) hcomp hsecond

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the original restriction bundle and its compact-window complement.
private theorem supportedThomHom_bijective_on_compact_window
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (U : Set X) (hU : IsOpen U)
    (hK : IsCompact (closure U)) :
    letI := hU.locallyCompactSpace
    let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
    Function.Bijective (h.pullback f).supportedThomHom := by
  classical
  let := hU.locallyCompactSpace
  let K := closure U
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let i : C(K, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(U, K) :=
    ⟨fun x ↦ ⟨x.val, subset_closure x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let EC := i *ᵖ E
  let := isFiniteRank_pullback (E := E) i
  obtain ⟨P, ⟨eC⟩⟩ := exists_complement_bundle (E := EC)
  let FC : K → Type _ := fun x ↦ P.complement.fiber x
  let : TopologicalSpace (TotalSpace Unit FC) :=
    IdempotentMatrix.fiberTotalSpaceTopology P.complement
  let : IsFiniteRank FC := IdempotentMatrix.isFiniteRank_fiber P.complement
  let hF : ContinuousHermitianMetric FC :=
    Classical.choice (nonempty_continuousHermitianMetric FC)
  let := isFiniteRank_pullback (E := E) f
  let := isFiniteRank_pullback (E := EC) g
  let := isFiniteRank_pullback (E := FC) g
  let := trivialTopology (X := K) P.size
  let := trivialTopology (X := U) P.size
  let c := pullbackSumTrivialization g P.size eC
  let j : Iso (f *ᵖ E) (g *ᵖ EC) := (pullbackCompIso (E := E) i g).symm
  let e := (j.sum (Iso.refl (g *ᵖ FC))).trans c
  exact supportedThomHom_bijective_of_trivial_sum (h.pullback f) (hF.pullback g) P.size e

private def restrictedTotalHomeomorph
    {X : Type*} [TopologicalSpace X] {E : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E] (U : Set X) :
    TotalSpace Unit ((Subtype.val : U → X) *ᵖ E) ≃ₜ ((π Unit E) ⁻¹' U) where
  toFun z := ⟨⟨z.proj.val, z.snd⟩, z.proj.property⟩
  invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (Pullback.continuous_lift Unit E (Subtype.val : U → X)).subtype_mk _
  continuous_invFun := by
    apply (inducing_pullbackTotalSpaceEmbedding Unit E (Subtype.val : U → X)).continuous_iff.mpr
    exact (((continuous_proj (E := E)).comp continuous_subtype_val).subtype_mk _).prodMk
      continuous_subtype_val

/-- The canonical subtype coordinates needed by the existing support-continuity theorem. -/
private def restrictedSupportedThomHom
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    letI := (hU.preimage (continuous_proj (E := E))).locallyCompactSpace
    CompactSupportKZero U →+ CompactSupportKZero ((π Unit E) ⁻¹' U) :=
  letI := hU.locallyCompactSpace
  letI := (hU.preimage (continuous_proj (E := E))).locallyCompactSpace
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  letI := isFiniteRank_pullback (E := E) f
  (compactSupportKZeroHomeomorph (restrictedTotalHomeomorph (E := E) U)).comp
    (h.pullback f).supportedThomHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the restricted Thom map and the same open-extension square.
private theorem restrictedSupportedThomHom_natural
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (U W : Set X) (hU : IsOpen U) (hW : IsOpen W)
    (hUW : U ⊆ W) :
    letI := hU.locallyCompactSpace
    letI := hW.locallyCompactSpace
    letI := (hU.preimage (continuous_proj (E := E))).locallyCompactSpace
    letI := (hW.preimage (continuous_proj (E := E))).locallyCompactSpace
    let k : U → W := Set.inclusion hUW
    let hk : IsOpenEmbedding k := .inclusion hUW (hU.preimage continuous_subtype_val)
    let l : ((π Unit E) ⁻¹' U) → ((π Unit E) ⁻¹' W) := Set.inclusion (fun _ hx ↦ hUW hx)
    let hl : IsOpenEmbedding l := .inclusion _
      ((hU.preimage (continuous_proj (E := E))).preimage continuous_subtype_val)
    (restrictedSupportedThomHom h W hW).comp (compactSupportKZeroOpenPushforward k hk) =
      (compactSupportKZeroOpenPushforward l hl).comp (restrictedSupportedThomHom h U hU) := by
  let := hU.locallyCompactSpace
  let := hW.locallyCompactSpace
  let := (hU.preimage (continuous_proj (E := E))).locallyCompactSpace
  let := (hW.preimage (continuous_proj (E := E))).locallyCompactSpace
  let fU : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let fW : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let k : C(U, W) := ⟨Set.inclusion hUW, continuous_subtype_val.subtype_mk _⟩
  have hk : IsOpenEmbedding k := .inclusion hUW (hU.preimage continuous_subtype_val)
  let l : ((π Unit E) ⁻¹' U) → ((π Unit E) ⁻¹' W) := Set.inclusion (fun _ hx ↦ hUW hx)
  have hl : IsOpenEmbedding l := .inclusion _
    ((hU.preimage (continuous_proj (E := E))).preimage continuous_subtype_val)
  let := isFiniteRank_pullback (E := E) fU
  let := isFiniteRank_pullback (E := E) fW
  let := isFiniteRank_pullback (E := fW *ᵖ E) k
  let c : Iso (k *ᵖ (fW *ᵖ E)) (fU *ᵖ E) := pullbackCompIso (E := E) fW k
  let q := pullbackTotalMap (fW *ᵖ E) k
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties (fW *ᵖ E) k).2 hk
  let eU := restrictedTotalHomeomorph (E := E) U
  let eW := restrictedTotalHomeomorph (E := E) W
  have hcomp : l ∘ eU ∘ c.totalHomeomorph = eW ∘ q := by
    funext z
    apply Subtype.ext
    change (⟨z.proj.val, c.linearEquiv z.proj z.snd⟩ : TotalSpace Unit E) =
      ⟨z.proj.val, z.snd⟩
    exact congrArg (fun v ↦ (⟨z.proj.val, v⟩ : TotalSpace Unit E))
      (pullbackCompIso_apply (E := E) fW k z.proj z.snd)
  have hiso := ((h.pullback fW).pullback k).supportedThomHom_iso (h.pullback fU) c
  have hopen := (h.pullback fW).supportedThomHom_openPushforward k hk
  apply AddMonoidHom.ext
  intro a
  change compactSupportKZeroHomeomorph eW
      ((h.pullback fW).supportedThomHom (compactSupportKZeroOpenPushforward k hk a)) =
    compactSupportKZeroOpenPushforward l hl
      (compactSupportKZeroHomeomorph eU ((h.pullback fU).supportedThomHom a))
  have hopen' := DFunLike.congr_fun hopen a
  have hiso' := DFunLike.congr_fun hiso a
  simp only [AddMonoidHom.comp_apply] at hopen' hiso'
  rw [← hopen', ← hiso']
  rw [← compactSupportKZeroOpenPushforward_homeomorph eW,
    ← compactSupportKZeroOpenPushforward_homeomorph eU,
    ← compactSupportKZeroOpenPushforward_homeomorph c.totalHomeomorph]
  generalize ((h.pullback fW).pullback k).supportedThomHom a = b
  calc
    _ = compactSupportKZeroOpenPushforward (eW ∘ q) (eW.isOpenEmbedding.comp hq) b :=
      (DFunLike.congr_fun
        (compactSupportKZeroOpenPushforward_comp q hq eW eW.isOpenEmbedding) b).symm
    _ = compactSupportKZeroOpenPushforward ((l ∘ eU) ∘ c.totalHomeomorph)
        ((hl.comp eU.isOpenEmbedding).comp c.totalHomeomorph.isOpenEmbedding) b := by
      congr 2
      exact hcomp.symm
    _ = compactSupportKZeroOpenPushforward (l ∘ eU) (hl.comp eU.isOpenEmbedding)
        (compactSupportKZeroOpenPushforward c.totalHomeomorph
          c.totalHomeomorph.isOpenEmbedding b) :=
      DFunLike.congr_fun (compactSupportKZeroOpenPushforward_comp
        c.totalHomeomorph c.totalHomeomorph.isOpenEmbedding (l ∘ eU)
        (hl.comp eU.isOpenEmbedding)) b
    _ = _ := DFunLike.congr_fun
      (compactSupportKZeroOpenPushforward_comp eU eU.isOpenEmbedding l hl)
      (compactSupportKZeroOpenPushforward c.totalHomeomorph c.totalHomeomorph.isOpenEmbedding b)

private theorem openPushforward_subtype
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    compactSupportKZeroOpenPushforward (Subtype.val : U → X) hU.isOpenEmbedding_subtypeVal =
      compactSupportKZeroOpenExtension U hU := by
  let := hU.locallyCompactSpace
  let j : U → X := Subtype.val
  have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal
  let := hj.isOpen_range.locallyCompactSpace
  let er := hj.isEmbedding.toHomeomorph
  let i : C(Set.range j, U) := ⟨er.symm, er.symm.continuous⟩
  let c : C(OnePoint X, OnePoint (Set.range j)) :=
    ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
  let d : C(OnePoint X, OnePoint U) := ⟨onePointCollapse U, continuous_onePointCollapse U hU⟩
  have hmap : (properOnePointMap i er.symm.isProperMap).comp c = d := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      by_cases hx : x ∈ U
      · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
        change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
        rw [onePointCollapse_coe_of_mem _ _ hrange,
          onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
        apply congrArg OnePoint.some
        apply Subtype.ext
        exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
      · have hrange : x ∉ Set.range j := by
          rintro ⟨x', rfl⟩
          exact hx x'.property
        change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
        rw [onePointCollapse_coe_of_notMem _ _ hrange,
          onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback c
      (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) a.val) =
    complexKZeroPullback d a.val
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedSupportedThomHom_extension
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) (U : Set X) (hU : IsOpen U) :
    letI := hU.locallyCompactSpace
    letI := (hU.preimage (continuous_proj (E := E))).locallyCompactSpace
    (compactSupportKZeroOpenExtension ((π Unit E) ⁻¹' U)
      (hU.preimage (continuous_proj (E := E)))).comp (restrictedSupportedThomHom h U hU) =
      h.supportedThomHom.comp (compactSupportKZeroOpenExtension U hU) := by
  let := hU.locallyCompactSpace
  let V := (π Unit E) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_proj (E := E))
  let := hV.locallyCompactSpace
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let := isFiniteRank_pullback (E := E) f
  let e := restrictedTotalHomeomorph (E := E) U
  let q := pullbackTotalMap E f
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties E f).2 hU.isOpenEmbedding_subtypeVal
  have hopen := h.supportedThomHom_openPushforward f hU.isOpenEmbedding_subtypeVal
  apply AddMonoidHom.ext
  intro a
  have hopen' := DFunLike.congr_fun hopen a
  simp only [AddMonoidHom.comp_apply] at hopen'
  have hsub : compactSupportKZeroOpenPushforward f hU.isOpenEmbedding_subtypeVal =
      compactSupportKZeroOpenExtension U hU := openPushforward_subtype U hU
  rw [hsub] at hopen'
  change compactSupportKZeroOpenExtension V hV
      (compactSupportKZeroHomeomorph e ((h.pullback f).supportedThomHom a)) =
    h.supportedThomHom (compactSupportKZeroOpenExtension U hU a)
  rw [← hopen', ← openPushforward_subtype V hV,
    ← compactSupportKZeroOpenPushforward_homeomorph e,
    ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the compact-window support construction for the specified global Thom map.
legacy_binder_names
  ["inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.3",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.15",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.24",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.36",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3239443600._hygCtx._hyg.43"] in
/-- The supported Thom theorem applies to the same metric-specified tensor homomorphism. -/
theorem supportedThomHom_bijective {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) :
    Function.Bijective h.supportedThomHom := by
  /- Every compact base window has an actual finite complement, so its supported
  Thom map is bijective. The original support groups satisfy representation and
  eventual vanishing on directed open covers. Apply both criteria to these
  windows and their full inverse images in the bundle; the latter need not be
  relatively compact in the total space. -/
  classical
  let ι := {U : Set X // IsOpen U ∧ IsCompact (closure U)}
  let U : ι → Set X := Subtype.val
  have hU (i : ι) : IsOpen (U i) := i.property.1
  let : Nonempty ι := ⟨⟨∅, isOpen_empty, by simp⟩⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨⟨U i ∪ U j, (hU i).union (hU j), ?_⟩,
      Set.subset_union_left, Set.subset_union_right⟩
    simpa only [closure_union] using i.property.2.union j.property.2
  have hcover : ⋃ i, U i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
    have hcl : IsCompact (closure (interior K)) :=
      hK.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hK.isClosed)
    exact Set.mem_iUnion.mpr
      ⟨⟨interior K, isOpen_interior, hcl⟩, mem_interior_iff_mem_nhds.mpr hx⟩
  let V (i : ι) : Set (TotalSpace Unit E) := (π Unit E) ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) := (hU i).preimage (continuous_proj (E := E))
  have hvdir : Directed (· ⊆ ·) V := by
    intro i j
    obtain ⟨k, hi, hj⟩ := hdir i j
    exact ⟨k, fun _ hx ↦ hi hx, fun _ hx ↦ hj hx⟩
  have hvcover : ⋃ i, V i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show z.proj ∈ ⋃ i, U i by rw [hcover]; trivial)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  let : ∀ i, LocallyCompactSpace (U i) := fun i ↦ (hU i).locallyCompactSpace
  let : ∀ i, LocallyCompactSpace (V i) := fun i ↦ (hV i).locallyCompactSpace
  let τ (i : ι) := restrictedSupportedThomHom h (U i) (hU i)
  have hτ (i : ι) : Function.Bijective (τ i) := by
    let f : C(U i, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let := isFiniteRank_pullback (E := E) f
    exact (compactSupportKZeroHomeomorph_bijective
      (restrictedTotalHomeomorph (E := E) (U i))).comp
        (supportedThomHom_bijective_on_compact_window h (U i) (hU i) i.property.2)
  have hsquare (i : ι) (a : CompactSupportKZero (U i)) :
      compactSupportKZeroOpenExtension (V i) (hV i) (τ i a) =
        h.supportedThomHom (compactSupportKZeroOpenExtension (U i) (hU i) a) :=
    DFunLike.congr_fun (restrictedSupportedThomHom_extension h (U i) (hU i)) a
  -- Vanishing passes to one larger window on the total space and then on the base.
  have hzero (a : CompactSupportKZero X) (ha : h.supportedThomHom a = 0) : a = 0 := by
    obtain ⟨i, b, hb⟩ := exists_compactSupportKZero_openExtension U hU hdir hcover a
    have hz : compactSupportKZeroOpenExtension (V i) (hV i) (τ i b) = 0 := by
      rw [hsquare, hb, ha]
    obtain ⟨j, hij, hj⟩ :=
      (compactSupportKZeroOpenExtension_eq_zero_iff V hV hvdir hvcover i (τ i b)).mp hz
    have hbase : U i ⊆ U j := by
      intro x hx
      exact hij (show (⟨x, 0⟩ : TotalSpace Unit E) ∈ V i from hx)
    let k : U i → U j := Set.inclusion hbase
    have hk : IsOpenEmbedding k := .inclusion hbase ((hU i).preimage continuous_subtype_val)
    have hn := DFunLike.congr_fun
      (restrictedSupportedThomHom_natural h (U i) (U j) (hU i) (hU j) hbase) b
    have hlocal : τ j (compactSupportKZeroOpenPushforward k hk b) = 0 := hn.trans hj
    have hzbase : compactSupportKZeroOpenPushforward k hk b = 0 := by
      apply (hτ j).injective
      exact hlocal.trans (map_zero _).symm
    have hglobal :=
      (compactSupportKZeroOpenExtension_eq_zero_iff U hU hdir hcover i b).mpr
        ⟨j, hbase, hzbase⟩
    exact hb.symm.trans hglobal
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  · -- Every original output has compact support in one full inverse-image window.
    intro z
    obtain ⟨i, b, hb⟩ := exists_compactSupportKZero_openExtension V hV hvdir hvcover z
    obtain ⟨a, ha⟩ := (hτ i).surjective b
    refine ⟨compactSupportKZeroOpenExtension (U i) (hU i) a, ?_⟩
    rw [← hsquare, ha, hb]

legacy_binder_names
  ["inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.3",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.15",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.24",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.36",
    "inst._@.AtiyahSinger.Topology.HermitianSupportedThom.3984624783._hygCtx._hyg.43"] in
/-- The additive Thom equivalence retains the metric-specified tensor map as its forward map. -/
def supportedThomEquiv {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h : ContinuousHermitianMetric E) :
    CompactSupportKZero X ≃+ CompactSupportKZero (TotalSpace Unit E) :=
  AddEquiv.ofBijective h.supportedThomHom h.supportedThomHom_bijective

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology t2Space_totalSpace locallyCompactSpace_totalSpace

legacy_binder_names
  ["inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.3",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.15",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.24",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.36",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.43",
    "x._@.AtiyahSinger.Topology.SupportedBundleThom.3239443600._hygCtx._hyg.58"] in
/-- KA IV.1.11 / SG C.13: the prescribed supported Thom map is an isomorphism. -/
theorem supportedThomHom_bijective {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X]
    (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2)) :
    Function.Bijective (supportedThomHom E hinner) := by
  -- Exposing the installed pairing as metric data preserves the exact tensor homomorphism.
  let h := ContinuousHermitianMetric.ofInnerProduct E hinner
  have hh : h.supportedThomHom = supportedThomHom E hinner :=
    ContinuousHermitianMetric.supportedThomHom_ofInnerProduct E hinner
  rw [← hh]
  exact h.supportedThomHom_bijective

legacy_binder_names
  ["inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.3",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.6",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.9",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.15",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.24",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.36",
    "inst._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.43",
    "x._@.AtiyahSinger.Topology.SupportedBundleThom.3984624783._hygCtx._hyg.58"] in
/-- The supported Thom equivalence retains the specified tensor-product operator. -/
def supportedThomEquiv {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2)) :
    CompactSupportKZero X ≃+ CompactSupportKZero (TotalSpace Unit E) :=
  AddEquiv.ofBijective (supportedThomHom E hinner) (supportedThomHom_bijective E hinner)

end AtiyahSinger.ComplexBundle
