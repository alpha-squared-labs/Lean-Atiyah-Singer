/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import Mathlib.LinearAlgebra.Prod

/-!
# Finite direct sums of actual continuous bundles

Public module ID: M1594.

D07/K01. The total space has the topology induced by its diagonal inclusion
into the product of the two original total spaces. Only the phantom parameter
is Unit; the actual fiber at x is E(x) × F(x). Ranks may vary locally.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- The standard direct-sum total-space topology, with a fixed phantom parameter. -/
@[instance_reducible]
def sumTopology : TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F))) inferInstance

attribute [local instance] sumTopology

/-- Finite direct sum preserves local finite rank. -/
theorem isFiniteRank_sum [IsFiniteRank E] [IsFiniteRank F] : IsFiniteRank (E ×ᵇ F) := by
  /- Intersect two trivializing neighborhoods. The product of the two linear charts
  is a chart for the induced total topology; reindex the product of coordinate spaces
  by Fin(r+s). This is local and does not require either rank to be constant globally. -/
  classical
  constructor
  intro x
  obtain ⟨r, e, he, hlinearE⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  obtain ⟨s, d, hd, hlinearF⟩ := IsFiniteRank.exists_linear_trivialization (E := F) x
  -- Use the two original chart inverses on their common open base set.
  let invE (y : X) (v : Fin r → ℂ) : E y :=
    if hy : y ∈ e.baseSet then
      cast (congrArg E (e.proj_symm_apply' hy)) (e.toPartialEquiv.symm (y, v)).snd
    else 0
  let invF (y : X) (v : Fin s → ℂ) : F y :=
    if hy : y ∈ d.baseSet then
      cast (congrArg F (d.proj_symm_apply' hy)) (d.toPartialEquiv.symm (y, v)).snd
    else 0
  have hpointE (y : X) (v : Fin r → ℂ) (hy : y ∈ e.baseSet) :
      (⟨y, invE y v⟩ : TotalSpace Unit E) = e.toPartialEquiv.symm (y, v) := by
    dsimp only [invE]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  have hpointF (y : X) (v : Fin s → ℂ) (hy : y ∈ d.baseSet) :
      (⟨y, invF y v⟩ : TotalSpace Unit F) = d.toPartialEquiv.symm (y, v) := by
    dsimp only [invF]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := F) (d.proj_symm_apply' hy) _
  have hinverseE (y : X) (hy : y ∈ e.baseSet) (v : E y) :
      invE y (e ⟨y, v⟩).2 = v := by
    have hp := (hpointE y (e ⟨y, v⟩).2 hy).trans
      (e.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace Unit E)) (e.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) hp)
  have hinverseF (y : X) (hy : y ∈ d.baseSet) (v : F y) :
      invF y (d ⟨y, v⟩).2 = v := by
    have hp := (hpointF y (d ⟨y, v⟩).2 hy).trans
      (d.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace Unit F)) (d.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit F ↦ z.snd) hp)
  -- Continuity is proved in the original direct-sum topology, not transported from a chart.
  let pairMap : TotalSpace Unit (E ×ᵇ F) → TotalSpace Unit E × TotalSpace Unit F :=
    fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
  have hinducing : Topology.IsInducing pairMap := ⟨rfl⟩
  have hprojE : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) := continuous_fst.comp hinducing.continuous
  have hprojF : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F)) := continuous_snd.comp hinducing.continuous
  have hbase : Continuous (π Unit (E ×ᵇ F)) := (continuous_proj (E := E)).comp hprojE
  let t : Trivialization ((Fin r → ℂ) × (Fin s → ℂ)) (π Unit (E ×ᵇ F)) :=
    { toFun := fun z ↦ (z.proj, (e ⟨z.proj, z.snd.1⟩).2, (d ⟨z.proj, z.snd.2⟩).2)
      invFun := fun y ↦ ⟨y.1, invE y.1 y.2.1, invF y.1 y.2.2⟩
      source := π Unit (E ×ᵇ F) ⁻¹' (e.baseSet ∩ d.baseSet)
      baseSet := e.baseSet ∩ d.baseSet
      target := (e.baseSet ∩ d.baseSet) ×ˢ Set.univ
      map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
      map_target' := fun _ h ↦ h.1
      left_inv' := by
        intro z hz
        exact TotalSpace.ext rfl (heq_of_eq (Prod.ext
          (hinverseE z.proj hz.1 z.snd.1) (hinverseF z.proj hz.2 z.snd.2)))
      right_inv' := by
        intro y hy
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change (e ⟨y.1, invE y.1 y.2.1⟩).2 = y.2.1
            rw [hpointE y.1 y.2.1 hy.1.1]
            exact congrArg Prod.snd (e.apply_symm_apply' hy.1.1)
          · change (d ⟨y.1, invF y.1 y.2.2⟩).2 = y.2.2
            rw [hpointF y.1 y.2.2 hy.1.2]
            exact congrArg Prod.snd (d.apply_symm_apply' hy.1.2)
      open_source := (e.open_baseSet.inter d.open_baseSet).preimage hbase
      open_target := (e.open_baseSet.inter d.open_baseSet).prod isOpen_univ
      open_baseSet := e.open_baseSet.inter d.open_baseSet
      continuousOn_toFun := hbase.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn
          (e.toOpenPartialHomeomorph.continuousOn.comp hprojE.continuousOn
            (fun _ h ↦ e.mem_source.mpr h.1))).prodMk
          (continuous_snd.comp_continuousOn
            (d.toOpenPartialHomeomorph.continuousOn.comp hprojF.continuousOn
              (fun _ h ↦ d.mem_source.mpr h.2))))
      continuousOn_invFun := by
        rw [hinducing.continuousOn_iff]
        have hE : ContinuousOn (fun y : X × (Fin r → ℂ) × (Fin s → ℂ) ↦
            e.toPartialEquiv.symm (y.1, y.2.1)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          e.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1.1)
        have hF : ContinuousOn (fun y : X × (Fin r → ℂ) × (Fin s → ℂ) ↦
            d.toPartialEquiv.symm (y.1, y.2.2)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          d.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
          (fun y hy ↦ d.mem_target.mpr hy.1.2)
        refine (hE.prodMk hF).congr ?_
        intro y hy
        exact Prod.ext (hpointE y.1 y.2.1 hy.1.1) (hpointF y.1 y.2.2 hy.1.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Concatenate the two finite coordinate families by the standard Fin-sum equivalence.
  let c : ((Fin r → ℂ) × (Fin s → ℂ)) ≃L[ℂ] (Fin (r + s) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (r + s) ↦ ℂ) finSumFinEquiv)).toContinuousLinearEquiv
  refine ⟨r + s, t.transFiberHomeomorph c.toHomeomorph, ⟨he, hd⟩, ?_⟩
  intro y hy
  constructor
  · intro v w
    change c ((e ⟨y, v.1 + w.1⟩).2, (d ⟨y, v.2 + w.2⟩).2) =
      c ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2) + c ((e ⟨y, w.1⟩).2, (d ⟨y, w.2⟩).2)
    rw [(hlinearE y hy.1).map_add, (hlinearF y hy.2).map_add]
    exact c.map_add ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)
      ((e ⟨y, w.1⟩).2, (d ⟨y, w.2⟩).2)
  · intro a v
    change c ((e ⟨y, a • v.1⟩).2, (d ⟨y, a • v.2⟩).2) =
      a • c ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)
    rw [(hlinearE y hy.1).map_smul, (hlinearF y hy.2).map_smul]
    exact c.map_smul a ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)

attribute [local instance] isFiniteRank_sum

set_option linter.unusedSectionVars false in
/-- Continuity of the fst projection from the direct sum. -/
theorem continuous_sum_fst :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) := by
  /- The direct-sum topology is induced by the pair of original total-space maps.
  Composing its inducing map with the fst product projection gives this map. -/
  have hpair : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F))) := continuous_induced_dom
  exact continuous_fst.comp hpair

/-- The fst projection as an actual bundle map. -/
def sumFst : Hom (E ×ᵇ F) E where
  linearMap x := LinearMap.fst ℂ (E x) (F x)
  continuous_total := continuous_sum_fst

set_option linter.unusedSectionVars false in
/-- Continuity of the snd projection from the direct sum. -/
theorem continuous_sum_snd :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F)) := by
  /- The direct-sum topology is induced by the pair of original total-space maps.
  Composing its inducing map with the snd product projection gives this map. -/
  have hpair : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit E),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F))) := continuous_induced_dom
  exact continuous_snd.comp hpair

/-- The snd projection as an actual bundle map. -/
def sumSnd : Hom (E ×ᵇ F) F where
  linearMap x := LinearMap.snd ℂ (E x) (F x)
  continuous_total := continuous_sum_snd

/-- Continuity of the inl inclusion into the direct sum. -/
theorem continuous_sum_inl [IsFiniteRank E] [IsFiniteRank F] :
    Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, (z.snd, 0)⟩ : TotalSpace Unit (E ×ᵇ F))) := by
  /- Test continuity against the two components of the induced topology. One is
  the identity total map; the other is the zero section of F composed with the
  continuous base projection. Local linear triviality supplies these continuous maps. -/
  -- Test the original inducing pair: the identity and the zero section over its base.
  apply continuous_induced_rng.mpr
  exact continuous_id.prodMk
    ((continuous_zero_section F).comp (continuous_proj (E := E)))

/-- The inl inclusion as an actual bundle map. -/
def sumInl [IsFiniteRank E] [IsFiniteRank F] : Hom E (E ×ᵇ F) where
  linearMap x := LinearMap.inl ℂ (E x) (F x)
  continuous_total := continuous_sum_inl

/-- Continuity of the inr inclusion into the direct sum. -/
theorem continuous_sum_inr [IsFiniteRank E] [IsFiniteRank F] :
    Continuous (fun z : TotalSpace Unit F ↦
      (⟨z.proj, (0, z.snd)⟩ : TotalSpace Unit (E ×ᵇ F))) := by
  /- Test continuity against the two components of the induced topology. One is
  the identity total map; the other is the zero section of E composed with the
  continuous base projection. Local linear triviality supplies these continuous maps. -/
  -- Test the original inducing pair in the opposite order.
  apply continuous_induced_rng.mpr
  exact ((continuous_zero_section E).comp (continuous_proj (E := F))).prodMk
    continuous_id

/-- The inr inclusion as an actual bundle map. -/
def sumInr [IsFiniteRank E] [IsFiniteRank F] : Hom F (E ×ᵇ F) where
  linearMap x := LinearMap.inr ℂ (E x) (F x)
  continuous_total := continuous_sum_inr

variable {H : X → Type*} [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]

/-- The direct sum of continuous fiber maps is continuous on total spaces. -/
theorem Hom.continuous_sum (a : Hom E F) (b : Hom G H) :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ G) ↦
      (⟨z.proj, (a.linearMap z.proj z.snd.1, b.linearMap z.proj z.snd.2)⟩ :
        TotalSpace Unit (F ×ᵇ H))) := by
  /- Each component into an original target total space is a source projection
  followed by a continuous bundle map. The pair is continuous, and the target
  direct-sum topology is induced by exactly these two components. -/
  -- Both components keep the same base point as the original input.
  apply continuous_induced_rng.mpr
  exact (a.continuous_total.comp continuous_sum_fst).prodMk
    (b.continuous_total.comp continuous_sum_snd)

/-- Direct sum of two bundle maps over the same base. -/
def Hom.sum (a : Hom E F) (b : Hom G H) : Hom (E ×ᵇ G) (F ×ᵇ H) where
  linearMap x := (a.linearMap x).prodMap (b.linearMap x)
  continuous_total := a.continuous_sum b

/-- Direct sum of actual bundle isomorphisms. -/
def Iso.sum (a : Iso E F) (b : Iso G H) : Iso (E ×ᵇ G) (F ×ᵇ H) where
  linearEquiv x := (a.linearEquiv x).prodCongr (b.linearEquiv x)
  continuous_total := a.toHom.continuous_sum b.toHom
  continuous_symm := a.symm.toHom.continuous_sum b.symm.toHom

/-- Swapping the two summands is continuous in their actual total topologies. -/
theorem continuous_sum_comm :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, (z.snd.2, z.snd.1)⟩ : TotalSpace Unit (F ×ᵇ E))) := by
  /- The two components of the output inducing map are the two input projections
  in reverse order. Product commutation is continuous, and hence so is the displayed map. -/
  -- The target inducing pair is precisely the original pair with its factors reversed.
  apply continuous_induced_rng.mpr
  exact continuous_sum_snd.prodMk continuous_sum_fst

/-- The canonical symmetry of a binary direct sum. -/
def sumCommIso : Iso (E ×ᵇ F) (F ×ᵇ E) where
  linearEquiv x := LinearEquiv.prodComm ℂ (E x) (F x)
  continuous_total := continuous_sum_comm
  continuous_symm := continuous_sum_comm

attribute [local instance] sectionModule

variable [IsFiniteRank E] [IsFiniteRank F]

/-- Pairing actual continuous sections yields a continuous sum section. -/
theorem continuous_sum_section (s : continuousSections E) (t : continuousSections F) :
    Continuous (fun x ↦ (⟨x, (s.val x, t.val x)⟩ : TotalSpace Unit (E ×ᵇ F))) := by
  /- The two components of the inducing map are exactly the original continuous
  sections s and t. Their product is continuous, which proves continuity in the induced topology. -/
  -- The two components of the induced topology are the original continuous sections.
  apply continuous_induced_rng.mpr
  exact s.property.prodMk t.property

/-- Pairing sections as a map of C(X,ℂ)-modules. -/
def sumSectionMap : (continuousSections E × continuousSections F) →ₗ[C(X, ℂ)]
    continuousSections (E ×ᵇ F) where
  toFun s := ⟨fun x ↦ (s.1.val x, s.2.val x), continuous_sum_section s.1 s.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every direct-sum section has a unique pair of component sections. -/
theorem sumSectionMap_bijective : Function.Bijective (sumSectionMap (E := E) (F := F)) := by
  /- The inverse applies the two continuous bundle projections to a section.
  The product and projection identities on each fiber show that this is a two-sided
  inverse, proving bijectivity without compactness or partitions of unity. -/
  -- Projection of a continuous total-space section gives each component section.
  have hfst (s : continuousSections (E ×ᵇ F)) :
      Continuous (fun x ↦ (⟨x, (s.val x).1⟩ : TotalSpace Unit E)) :=
    continuous_sum_fst.comp s.property
  have hsnd (s : continuousSections (E ×ᵇ F)) :
      Continuous (fun x ↦ (⟨x, (s.val x).2⟩ : TotalSpace Unit F)) :=
    continuous_sum_snd.comp s.property
  constructor
  · intro s t h
    apply Prod.ext
    · apply Subtype.ext
      funext x
      exact congrArg (fun u : continuousSections (E ×ᵇ F) ↦ (u.val x).1) h
    · apply Subtype.ext
      funext x
      exact congrArg (fun u : continuousSections (E ×ᵇ F) ↦ (u.val x).2) h
  · intro s
    refine ⟨(⟨fun x ↦ (s.val x).1, hfst s⟩, ⟨fun x ↦ (s.val x).2, hsnd s⟩), ?_⟩
    apply Subtype.ext
    funext x
    exact Prod.eta (s.val x)

/-- The natural section-module equivalence for finite direct sums. -/
def sumSectionEquiv : (continuousSections E × continuousSections F) ≃ₗ[C(X, ℂ)]
    continuousSections (E ×ᵇ F) :=
  LinearEquiv.ofBijective sumSectionMap sumSectionMap_bijective

/-- The first projection splits the first inclusion. -/
theorem sumFst_comp_sumInl :
    (sumFst (E := E) (F := F)).comp sumInl = Hom.id E := by
  /- Evaluate on a fiber vector: first include v as (v,0), then project to v.
  Fiber-map extensionality upgrades this equality to equality of continuous bundle maps. -/
  apply Hom.ext
  intro x
  rfl

/-- The second projection splits the second inclusion. -/
theorem sumSnd_comp_sumInr :
    (sumSnd (E := E) (F := F)).comp sumInr = Hom.id F := by
  /- Evaluate on a fiber vector: include v as (0,v) and then project to v.
  These equalities on all fibers prove equality of the specified bundle maps. -/
  apply Hom.ext
  intro x
  rfl

end AtiyahSinger.ComplexBundle
