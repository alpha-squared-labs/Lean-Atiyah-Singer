/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.FiniteBundleTopology

/-!
# Gluing continuous bundle actions on invariant open sets

Public module ID: M1763.

Compatible continuous actions on the two actual restrictions of a bundle
glue to an action on that same bundle. Both local moving-fiber maps are
retained. Joint continuity is checked on the original open total-space
cover, and the group laws are checked in the same invariant piece.
This is used to retain an exterior representation in relative equivariant
bundle extension for analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option maxHeartbeats 1600000 in
-- Retain both dependent pullbacks and their moving-base transports in the gluing laws.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible actions on an invariant open cover glue on the same original vector bundle. -/
theorem EquivariantStructure.exists_gluing
    (U V : Opens X) (hcover : (U : Set X) ∪ (V : Set X) = Set.univ)
    [MulAction G U] [ContinuousSMul G U] [MulAction G V] [ContinuousSMul G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : X) = g • (x : X))
    (hV : ∀ (g : G) (x : V), ((g • x : V) : X) = g • (x : X))
    (σ : EquivariantStructure G ((Subtype.val : U → X) *ᵖ E))
    (τ : EquivariantStructure G ((Subtype.val : V → X) *ᵖ E))
    (hagree : ∀ (g : G) (x : X) (hx : x ∈ U) (hy : x ∈ V) (v : E x),
      (⟨((g • (⟨x, hx⟩ : U) : U) : X), σ.linearMap g ⟨x, hx⟩ v⟩ : TotalSpace Unit E) =
        ⟨((g • (⟨x, hy⟩ : V) : V) : X), τ.linearMap g ⟨x, hy⟩ v⟩) :
    ∃ ρ : EquivariantStructure G E,
      (∀ (g : G) (x : U) (v : E x),
        (⟨g • (x : X), ρ.linearMap g x.val v⟩ : TotalSpace Unit E) =
          ⟨((g • x : U) : X), σ.linearMap g x v⟩) ∧
      (∀ (g : G) (x : V) (v : E x),
        (⟨g • (x : X), ρ.linearMap g x.val v⟩ : TotalSpace Unit E) =
          ⟨((g • x : V) : X), τ.linearMap g x v⟩) := by
  classical
  let extend (W : Opens X) [MulAction G W] [ContinuousSMul G W]
      (hW : ∀ (g : G) (x : W), ((g • x : W) : X) = g • (x : X))
      (a : EquivariantStructure G ((Subtype.val : W → X) *ᵖ E))
      (g : G) (x : X) (hx : x ∈ W) : E x →ₗ[ℂ] E (g • x) :=
    (LinearEquiv.cast (R := ℂ) (M := E) (hW g ⟨x, hx⟩)).toLinearMap.comp
      (a.linearMap g ⟨x, hx⟩)
  have hlift (W : Opens X) [MulAction G W] [ContinuousSMul G W]
      (hW : ∀ (g : G) (x : W), ((g • x : W) : X) = g • (x : X))
      (a : EquivariantStructure G ((Subtype.val : W → X) *ᵖ E))
      (g : G) (x : X) (hx : x ∈ W) (v : E x) :
      (⟨g • x, extend W hW a g x hx v⟩ : TotalSpace Unit E) =
        ⟨((g • (⟨x, hx⟩ : W) : W) : X), a.linearMap g ⟨x, hx⟩ v⟩ := by
    exact TotalSpace.mk_cast (F := Unit) (E := E) (hW g ⟨x, hx⟩) _
  have hother (x : X) (hx : x ∉ U) : x ∈ V := by
    have hh : x ∈ (U : Set X) ∪ V := by rw [hcover]; trivial
    exact hh.resolve_left hx
  let L (g : G) (x : X) : E x →ₗ[ℂ] E (g • x) :=
    if hx : x ∈ U then extend U hU σ g x hx else extend V hV τ g x (hother x hx)
  have hLU (g : G) (x : U) (v : E x) :
      (⟨g • x.val, L g x.val v⟩ : TotalSpace Unit E) =
        ⟨((g • x : U) : X), σ.linearMap g x v⟩ := by
    dsimp only [L]
    rw [dite_eq_left x.property]
    exact hlift U hU σ g x.val x.property v
  have hLV (g : G) (x : V) (v : E x) :
      (⟨g • x.val, L g x.val v⟩ : TotalSpace Unit E) =
        ⟨((g • x : V) : X), τ.linearMap g x v⟩ := by
    by_cases hx : x.val ∈ U
    · exact (hLU g ⟨x.val, hx⟩ v).trans (hagree g x.val hx x.property v)
    · dsimp only [L]
      rw [dite_eq_right hx]
      exact hlift V hV τ g x.val x.property v
  let act (g : G) (z : TotalSpace Unit E) : TotalSpace Unit E :=
    ⟨g • z.proj, L g z.proj z.snd⟩
  have hlocal (W : Opens X) [MulAction G W] [ContinuousSMul G W]
      (a : EquivariantStructure G ((Subtype.val : W → X) *ᵖ E))
      (ha : ∀ (g : G) (x : W) (v : E x),
        act g ⟨x.val, v⟩ = ⟨((g • x : W) : X), a.linearMap g x v⟩) :
      ContinuousOn (fun z : G × TotalSpace Unit E ↦ act z.1 z.2)
        {z | z.2.proj ∈ W} := by
    let S : Set (G × TotalSpace Unit E) := {z | z.2.proj ∈ W}
    let f (z : S) : TotalSpace Unit ((Subtype.val : W → X) *ᵖ E) :=
      ⟨⟨z.val.2.proj, z.property⟩, z.val.2.snd⟩
    have hf : Continuous f := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E (Subtype.val : W → X)).continuous_iff]
      exact (((continuous_proj (E := E)).comp
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _).prodMk
          (continuous_snd.comp continuous_subtype_val)
    have hc := (Pullback.continuous_lift Unit E (Subtype.val : W → X)).comp
      (a.continuous_action.comp ((continuous_fst.comp continuous_subtype_val).prodMk hf))
    rw [continuousOn_iff_continuous_domRestrict]
    exact hc.congr (fun z ↦ (ha z.val.1 ⟨z.val.2.proj, z.property⟩ z.val.2.snd).symm)
  have hcontinuous : Continuous (fun z : G × TotalSpace Unit E ↦ act z.1 z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.2.proj ∈ U
    · exact (hlocal U σ hLU).continuousAt
        ((U.isOpen.preimage ((continuous_proj (E := E)).comp continuous_snd)).mem_nhds hz)
    · exact (hlocal V τ hLV).continuousAt
        ((V.isOpen.preimage ((continuous_proj (E := E)).comp continuous_snd)).mem_nhds
          (hother z.2.proj hz))
  have hlaws (W : Opens X) [MulAction G W] [ContinuousSMul G W]
      (a : EquivariantStructure G ((Subtype.val : W → X) *ᵖ E))
      (ha : ∀ (g : G) (x : W) (v : E x),
        act g ⟨x.val, v⟩ = ⟨((g • x : W) : X), a.linearMap g x v⟩)
      (x : W) (v : E x) :
      act 1 ⟨x.val, v⟩ = ⟨x.val, v⟩ ∧
      ∀ g h : G, act (g * h) ⟨x.val, v⟩ = act g (act h ⟨x.val, v⟩) := by
    constructor
    · exact (ha 1 x v).trans
        (congrArg (Pullback.lift (Subtype.val : W → X)) (a.one_map x v))
    · intro g h
      rw [ha, ha, ha]
      exact congrArg (Pullback.lift (Subtype.val : W → X)) (a.mul_map g h x v)
  refine ⟨{ linearMap := L
            one_map := ?_
            mul_map := ?_
            continuous_action := hcontinuous }, hLU, hLV⟩
  · intro x v
    by_cases hx : x ∈ U
    · exact (hlaws U σ hLU ⟨x, hx⟩ v).1
    · exact (hlaws V τ hLV ⟨x, hother x hx⟩ v).1
  · intro g h x v
    by_cases hx : x ∈ U
    · exact (hlaws U σ hLU ⟨x, hx⟩ v).2 g h
    · exact (hlaws V τ hLV ⟨x, hother x hx⟩ v).2 g h

end AtiyahSinger.ComplexBundle
