/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Transport of the original equivariant support class

Public module ID: M1816.

Conjugating the original boundary by two specified equivariant global bundle
isomorphisms keeps the compact control, gives the specified target actions,
and represents precisely the original equivariant K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact conjugated boundary retains the original equivariant support class. -/
theorem exists_equivariantSupportTransport
    (a : EquivariantSupportBundleTriple G X) (S T : FiniteBundle X)
    (ρS : EquivariantStructure G S.Fiber) (ρT : EquivariantStructure G T.Fiber)
    (e : Iso a.1.source.Fiber S.Fiber) (f : Iso a.1.target.Fiber T.Fiber)
    (he : e.IsEquivariant a.2.sourceAction ρS)
    (hf : f.IsEquivariant a.2.targetAction ρT) :
    ∃ h : (a.1.datum.congr e f).IsEquivariant ρS ρT,
      (EquivariantSupportBundleTriple.ofBoundary S T (a.1.datum.congr e f)
        ρS ρT h).kZeroClass = a.kZeroClass := by
  dsimp only [Iso.IsEquivariant, Hom.IsEquivariant, Iso.toHom] at he hf
  -- Equivariance of the prescribed inverse follows by canceling its forward isomorphism.
  have hinv (g : G) (x : X) (v : S.Fiber x) :
      (e.linearEquiv (g • x)).symm (ρS.linearMap g x v) =
        a.2.sourceAction.linearMap g x ((e.linearEquiv x).symm v) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (ρS.linearMap g x) ((e.linearEquiv x).apply_symm_apply v)).symm.trans
      (he g x ((e.linearEquiv x).symm v)).symm
  have h : (a.1.datum.congr e f).IsEquivariant ρS ρT := by
    refine ⟨a.2.isEquivariant.invariant_control, ?_⟩
    intro g x v
    let gx : (a.1.datum.controlᶜ : Set X) :=
      ⟨g • x.val, fun hx ↦ x.property ((a.2.isEquivariant.invariant_control g x).mp hx)⟩
    change f.linearEquiv (g • x.val)
      (a.1.datum.boundary.linearEquiv gx
        ((e.linearEquiv (g • x.val)).symm (ρS.linearMap g x.val v))) =
      ρT.linearMap g x.val
        (f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x
          ((e.linearEquiv x.val).symm v)))
    rw [hinv, a.2.isEquivariant.boundary_intertwines]
    exact hf g x.val (a.1.datum.boundary.linearEquiv x ((e.linearEquiv x.val).symm v))
  refine ⟨h, ?_⟩
  -- The same global isomorphisms witness the defining relation at the unchanged control.
  apply Eq.symm
  apply (equivariantSupportTripleKZero_generator_relations).1
  refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
    a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _, e, f,
    he, hf, ?_⟩
  intro x v
  simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply,
    EquivariantSupportBundleTriple.ofBoundary, SupportBundleTriple.ofBoundary]
  change f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x v) =
    f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x
      ((e.linearEquiv x.val).symm (e.linearEquiv x.val v)))
  rw [LinearEquiv.symm_apply_apply]

end AtiyahSinger.ComplexBundle
