/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# The actual total-space lift of a bundle pullback

Public module ID: M1600.

The map is mathlib's `Bundle.Pullback.lift`, packaged as a continuous map with
the existing induced pullback topology. It sends `(x,v)` to `(f(x),v)` in the
original total space. The proper and open-embedding certificates are the usual
base-change properties, stated in the locally compact Hausdorff scope used by
compact-support K theory. The bundle projection itself need not be proper.

These are geometric interfaces for the standard pullback construction and the
naturality of the Thom operator. They introduce neither a new pullback bundle
nor a replacement total-space topology. Same-base bundle isomorphisms already
have `Iso.totalHomeomorph`; that original construction is reused downstream.
The pullback properties are proved on these original maps and topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (E : Y → Type*) [TopologicalSpace (TotalSpace Unit E)]

/-- The continuous map of original total spaces induced by the actual pullback lift. -/
def pullbackTotalMap (f : C(X, Y)) :
    C(TotalSpace Unit ((f : X → Y) *ᵖ E), TotalSpace Unit E) :=
  ⟨Bundle.Pullback.lift f, _root_.Pullback.continuous_lift Unit E f⟩

variable [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]

set_option linter.unusedSectionVars false in
/-- Proper maps and open embeddings retain those properties under this same total pullback. -/
theorem pullbackTotalMap_properties [IsFiniteRank E]
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    (f : C(X, Y)) :
    (IsProperMap f → IsProperMap (pullbackTotalMap E f)) ∧
      (IsOpenEmbedding f → IsOpenEmbedding (pullbackTotalMap E f)) := by
  /- The original pullback embeds as the closed fiber product in X times Total(E).
  For properness, compose this closed embedding with the proper product of f and
  the identity. Its factorization through the graph of the old projection proves
  properness of the actual lift. For an open embedding, the same factorization
  gives an embedding, whose image is the inverse image of range(f). This argument
  uses the original induced topology and does not require a proper bundle projection. -/
  let j : TotalSpace Unit ((f : X → Y) *ᵖ E) → X × TotalSpace Unit E :=
    pullbackTotalSpaceEmbedding f
  have hj : IsEmbedding j := by
    refine ⟨inducing_pullbackTotalSpaceEmbedding Unit E f, ?_⟩
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    have hxy : x = y := congrArg Prod.fst h
    subst y
    have hvw : v = w := TotalSpace.mk_injective (f x) (congrArg Prod.snd h)
    subst w
    rfl
  -- The fiber-product equation describes the range in the original product space.
  have hrange : Set.range j = {p : X × TotalSpace Unit E | f p.1 = p.2.proj} := by
    ext ⟨x, y, v⟩
    constructor
    · rintro ⟨⟨a, w⟩, h⟩
      have ha : a = x := congrArg Prod.fst h
      have hb : f a = y := congrArg (fun p : X × TotalSpace Unit E ↦ p.2.proj) h
      change f x = y
      simpa only [ha] using hb
    · intro h
      change f x = y at h
      subst y
      exact ⟨⟨x, v⟩, rfl⟩
  let graph : TotalSpace Unit E → Y × TotalSpace Unit E := fun z ↦ (z.proj, z)
  have hgraph : Continuous graph := (continuous_proj (E := E)).prodMk continuous_id
  constructor
  · intro hf
    -- Closedness uses the Hausdorff base; product properness then descends through the graph.
    have hjclosed : IsClosedEmbedding j := by
      refine ⟨hj, ?_⟩
      rw [hrange]
      exact isClosed_eq (f.continuous.comp continuous_fst)
        ((continuous_proj (E := E)).comp continuous_snd)
    have hcomp : IsProperMap (graph ∘ pullbackTotalMap E f) :=
      (hf.prodMap isProperMap_id).comp hjclosed.isProperMap
    exact isProperMap_of_comp_of_inj (pullbackTotalMap E f).continuous hgraph hcomp
      (fun _ _ h ↦ congrArg Prod.snd h)
  · intro hf
    -- Product embedding detects the original lift, not a newly chosen inverse map.
    have hcomp : IsEmbedding (graph ∘ pullbackTotalMap E f) :=
      (hf.isEmbedding.prodMap IsEmbedding.id).comp hj
    have hlift : IsEmbedding (pullbackTotalMap E f) :=
      IsEmbedding.of_comp (pullbackTotalMap E f).continuous hgraph hcomp
    refine ⟨hlift, ?_⟩
    have hliftRange : Set.range (pullbackTotalMap E f) =
        (π Unit E) ⁻¹' Set.range f := by
      ext ⟨y, v⟩
      constructor
      · rintro ⟨⟨x, w⟩, h⟩
        exact ⟨x, congrArg (π Unit E) h⟩
      · rintro ⟨x, h⟩
        change f x = y at h
        subst y
        exact ⟨⟨x, v⟩, rfl⟩
    rw [hliftRange]
    exact hf.isOpen_range.preimage (continuous_proj (E := E))

end AtiyahSinger.ComplexBundle
