/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundleTensor
public import AtiyahSinger.Topology.EquivariantSupportIsomorphism
public import AtiyahSinger.Topology.SupportTripleTensor
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensor action on the original equivariant support triples

Public module ID: M1815.

An arbitrary finite equivariant bundle tensors both original bundles on the
left. The control and its invariance are unchanged; the boundary is exactly
identity tensor the original boundary, and the two actions are the original
tensor actions. Equivariant isomorphism, arbitrary equivariant stabilization,
direct sum and identity are respected by this same operation.

Sources: SG I.9 for ordinary bundle multiplication and relative triples;
KA II.5.11 and II.5.14 for the relative module and explicit tensor boundary;
ASI I, Section 2, for equivariant compact-support K theory and its tensor
action by representations. The explicit action by arbitrary finite equivariant
bundles on this direct triple presentation is a project supplement. No compact
group, locally compact base or Hausdorffness is needed for these constructions.
This module supplies geometric relations, not a new quotient or an R(G) action.
The original equivariance and all four geometric relation certificates are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F H : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum

set_option backward.isDefEq.respectTransparency.types false in
/-- The unchanged control and actual tensor boundary intertwine the specified tensor actions. -/
theorem CompactSupportTriple.IsEquivariant.tensorLeft {a : CompactSupportTriple F H}
    {ρF : EquivariantStructure G F} {ρH : EquivariantStructure G H}
    (ha : a.IsEquivariant ρF ρH) (ρE : EquivariantStructure G E) :
    (a.tensorLeft E).IsEquivariant (ρE.tensor ρF) (ρE.tensor ρH) := by
  /- Stage 1: tensorLeft retains the original compact control, so use its
  original invariance certificate without saturation or enlargement.
  Stage 2: on a pure tensor u tensor v, the left route through the boundary
  square is g*u tensor alpha(g*v), and the right route is g*u tensor g*alpha(v).
  RelativeTriple.tensorLeft_tmul gives these actual boundary values, while
  the original tensor action uses the two supplied moving-fiber maps. The
  old boundary intertwining equation identifies the second factors.
  Stage 3: both routes are linear maps on the same original tensor fiber.
  Pure tensors span that fiber, so tensor induction proves the full square.
  The restriction comparisons retain the original exterior and total topologies. -/
  refine ⟨ha.invariant_control, ?_⟩
  intro g x w
  change (a.controlᶜ : Set X) at x
  let gx : (a.controlᶜ : Set X) :=
    ⟨g • x.val, fun hx ↦ x.property ((ha.invariant_control g x.val).mp hx)⟩
  -- Compare the two linear maps on pure tensors, retaining the old boundary point values.
  have hmaps : ((a.boundary.tensorLeft E).linearEquiv gx).toLinearMap.comp
        (TensorProduct.map (ρE.linearMap g x) (ρF.linearMap g x)) =
      (TensorProduct.map (ρE.linearMap g x) (ρH.linearMap g x)).comp
        ((a.boundary.tensorLeft E).linearEquiv x).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    have hl := RelativeTriple.tensorLeft_tmul E a.boundary gx
      (ρE.linearMap g x u) (ρF.linearMap g x v)
    have hr := RelativeTriple.tensorLeft_tmul E a.boundary x u v
    exact hl.trans ((congrArg (fun v ↦ (ρE.linearMap g x u) ⊗ₜ[ℂ] v)
      (ha.boundary_intertwines g x v)).trans
        (congrArg (TensorProduct.map (ρE.linearMap g x) (ρH.linearMap g x)) hr).symm)
  exact DFunLike.congr_fun hmaps w

namespace EquivariantSupportBundleTriple

/-- Tensor an arbitrary finite equivariant bundle with the exact original support triple. -/
@[reducible]
def tensorLeft (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber)
    (a : EquivariantSupportBundleTriple G X) : EquivariantSupportBundleTriple G X :=
  ⟨a.1.tensorLeft E,
    { sourceAction := ρE.tensor a.2.sourceAction
      targetAction := ρE.tensor a.2.targetAction
      isEquivariant := a.2.isEquivariant.tensorLeft ρE }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual left tensoring preserves equivariant isomorphism, stabilization, sum and identity. -/
theorem tensorLeft_relations (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber) :
    (∀ a b : EquivariantSupportBundleTriple G X,
      a.IsIsomorphic b → (tensorLeft E ρE a).IsIsomorphic (tensorLeft E ρE b)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      a.IsStablyIsomorphic b →
        (tensorLeft E ρE a).IsStablyIsomorphic (tensorLeft E ρE b)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      (tensorLeft E ρE (a.sum b)).IsIsomorphic
        ((tensorLeft E ρE a).sum (tensorLeft E ρE b))) ∧
    ∀ (F : FiniteBundle X) (ρF : EquivariantStructure G F.Fiber),
      (tensorLeft E ρE (identity F ρF)).IsIsomorphic
        (identity (E.tensor F) (ρE.tensor ρF)) := by
  /- Stage 1: retain the supplied common invariant compact control and its
  two original inclusions. Tensor each original global source/target
  isomorphism with the identity on E. On pure vectors, tensor equivariance
  and the new boundary square are exactly the original equations with the
  same E factor attached. Linearity extends them to all tensor vectors.
  Stage 2: distribute the original tensor fibers over the two direct-sum
  factors by u tensor (v,w) mapped to (u tensor v,u tensor w). The algebraic
  distributivity equivalence and its inverse are continuous in finite tensor
  charts; this compares the original total topologies, not chosen substitutes.
  Both tensor actions and exterior boundaries intertwine componentwise.
  The two controls are the same union. Tensoring an identity has empty
  control and the identity on the actual tensor bundle, giving the fourth clause.
  Stage 3: tensor the original stabilized square from Stage 1 and compose
  the Stage 2 sum and identity comparisons on both sides. Its stabilizers
  are exactly E tensor F and E tensor H with their specified tensor actions,
  where F and H were the original arbitrary finite equivariant stabilizers.
  No product-representation reduction or cancellation of E is required. -/
  let eqv := (isIsomorphic_properties (G := G) (X := X)).1
  have hsumIso := (isIsomorphic_sum_enlarge (G := G) (X := X)).1
  -- Enlargement reads the same original tensor boundary on a smaller exterior.
  have htensor (a : SupportBundleTriple X) (K : Set X) (hK : IsCompact K)
      (ha : a.datum.control ⊆ K) (x : (Kᶜ : Set X))
      (u : E.Fiber x) (v : a.source.Fiber x) :
      (((a.tensorLeft E).datum).enlarge K hK ha).boundary.linearEquiv x (u ⊗ₜ[ℂ] v) =
        u ⊗ₜ[ℂ] (a.datum.enlarge K hK ha).boundary.linearEquiv x v := by
    simp only [SupportBundleTriple.tensorLeft, SupportBundleTriple.ofBoundary,
      CompactSupportTriple.tensorLeft, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.tensorLeft_tmul]
    rfl
  have hiso (a b : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic b) :
      (tensorLeft E ρE a).IsIsomorphic (tensorLeft E ρE b) := by
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsquare⟩ := h
    -- Tensor the same global maps by identity, retaining the supplied invariant control.
    refine ⟨K, hK, hInv, ha, hb, (Iso.refl E.Fiber).tensor u,
      (Iso.refl E.Fiber).tensor v,
      (EquivariantStructure.tensor_maps ρE a.2.sourceAction ρE b.2.sourceAction).2
        (Iso.refl E.Fiber) u (fun _ _ _ ↦ rfl) hu,
      (EquivariantStructure.tensor_maps ρE a.2.targetAction ρE b.2.targetAction).2
        (Iso.refl E.Fiber) v (fun _ _ _ ↦ rfl) hv, ?_⟩
    intro x w
    have hmaps : (((Iso.refl E.Fiber).tensor v).linearEquiv x).toLinearMap.comp
          (((tensorLeft E ρE a).1.datum.enlarge K hK ha).boundary.linearEquiv x).toLinearMap =
        (((tensorLeft E ρE b).1.datum.enlarge K hK hb).boundary.linearEquiv x).toLinearMap.comp
          (((Iso.refl E.Fiber).tensor u).linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro e w
      have htleft := htensor a.1 K hK ha x e w
      have htright := htensor b.1 K hK hb x e (u.linearEquiv x w)
      exact (congrArg (((Iso.refl E.Fiber).tensor v).linearEquiv x) htleft).trans
        ((congrArg (fun w ↦ e ⊗ₜ[ℂ] w) (hsquare x w)).trans htright.symm)
    exact DFunLike.congr_fun hmaps w
  have compare (J K : FiniteBundle X) (ρJ : EquivariantStructure G J.Fiber)
      (ρK : EquivariantStructure G K.Fiber) :
      ∃ e : Iso (E.tensor (J.sum K)).Fiber ((E.tensor J).sum (E.tensor K)).Fiber,
        (∀ x u v, e.linearEquiv x (u ⊗ₜ[ℂ] v) = (u ⊗ₜ[ℂ] v.1, u ⊗ₜ[ℂ] v.2)) ∧
          e.IsEquivariant (ρE.tensor (ρJ.sum ρK))
            ((ρE.tensor ρJ).sum (ρE.tensor ρK)) := by
    -- The actual projections give continuity in the original tensor and sum topologies.
    let p : Hom (E.tensor (J.sum K)).Fiber (E.tensor J).Fiber :=
      (Iso.refl E.Fiber).toHom.tensor (sumFst (E := J.Fiber) (F := K.Fiber))
    let q : Hom (E.tensor (J.sum K)).Fiber (E.tensor K).Fiber :=
      (Iso.refl E.Fiber).toHom.tensor (sumSnd (E := J.Fiber) (F := K.Fiber))
    let d (x : X) := TensorProduct.prodRight ℂ ℂ (E.Fiber x) (J.Fiber x) (K.Fiber x)
    have hvalue (x : X) (w : (E.tensor (J.sum K)).Fiber x) :
        d x w = (p.linearMap x w, q.linearMap x w) := by
      have hm : (d x).toLinearMap = (p.linearMap x).prod (q.linearMap x) := by
        apply TensorProduct.ext'
        intro u v
        rfl
      exact DFunLike.congr_fun hm w
    let D : Hom (E.tensor (J.sum K)).Fiber ((E.tensor J).sum (E.tensor K)).Fiber :=
      { linearMap x := (d x).toLinearMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply (p.continuous_total.prodMk q.continuous_total).congr
          intro z
          exact congrArg (fun w ↦
            ((⟨z.proj, w.1⟩ : TotalSpace Unit (E.tensor J).Fiber),
              (⟨z.proj, w.2⟩ : TotalSpace Unit (E.tensor K).Fiber))) (hvalue z.proj z.snd).symm }
    -- The finite-rank inverse theorem upgrades this very forward map to an isomorphism.
    let e := D.toIso (fun x ↦ (d x).bijective)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_⟩
    intro g x w
    have hm : (e.linearEquiv (g • x)).toLinearMap.comp
          ((ρE.tensor (ρJ.sum ρK)).linearMap g x) =
        (((ρE.tensor ρJ).sum (ρE.tensor ρK)).linearMap g x).comp
          (e.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      rfl
    exact DFunLike.congr_fun hm w
  have hsum (a b : EquivariantSupportBundleTriple G X) :
      (tensorLeft E ρE (a.sum b)).IsIsomorphic
        ((tensorLeft E ρE a).sum (tensorLeft E ρE b)) := by
    obtain ⟨u, hu, hueq⟩ := compare a.1.source b.1.source a.2.sourceAction b.2.sourceAction
    obtain ⟨v, hv, hveq⟩ := compare a.1.target b.1.target a.2.targetAction b.2.targetAction
    let K := a.1.datum.control ∪ b.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control.union b.1.datum.isCompact_control
    refine ⟨K, hK, (fun g x ↦ (a.2.isEquivariant.invariant_control g x).or
      (b.2.isEquivariant.invariant_control g x)), Set.Subset.refl _, Set.Subset.refl _,
      u, v, hueq, hveq, ?_⟩
    intro x w
    -- The distributive map intertwines exactly the two old exterior boundary components.
    have hm : (v.linearEquiv x).toLinearMap.comp
          (((tensorLeft E ρE (a.sum b)).1.datum.enlarge K hK
            (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
        ((((tensorLeft E ρE a).sum (tensorLeft E ρE b)).1.datum.enlarge K hK
          (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap.comp
          (u.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro e w
      have hleft := htensor (a.1.sum b.1) K hK (Set.Subset.refl _) x e w
      have ha := htensor a.1 K hK Set.subset_union_left x e w.1
      have hb := htensor b.1 K hK Set.subset_union_right x e w.2
      have hsumleft := ((a.1.datum.sum b.1.datum).enlarge_apply K hK
        (Set.Subset.refl _) x w).trans
        (RelativeTriple.sum_apply
          (a.1.datum.enlarge K hK Set.subset_union_left).boundary
          (b.1.datum.enlarge K hK Set.subset_union_right).boundary x w)
      have hsumright := (((a.1.tensorLeft E).datum.sum (b.1.tensorLeft E).datum).enlarge_apply
        K hK (Set.Subset.refl _) x (e ⊗ₜ[ℂ] w.1, e ⊗ₜ[ℂ] w.2)).trans
        (RelativeTriple.sum_apply
          ((a.1.tensorLeft E).datum.enlarge K hK Set.subset_union_left).boundary
          ((b.1.tensorLeft E).datum.enlarge K hK Set.subset_union_right).boundary
          x (e ⊗ₜ[ℂ] w.1, e ⊗ₜ[ℂ] w.2))
      have hl := (congrArg (v.linearEquiv x) hleft).trans (hv x e _)
      have hll := congrArg (fun w : (a.1.target.sum b.1.target).Fiber x ↦
        (e ⊗ₜ[ℂ] w.1, e ⊗ₜ[ℂ] w.2)) hsumleft
      have hr := congrArg ((((tensorLeft E ρE a).sum (tensorLeft E ρE b)).1.datum.enlarge
        K hK (Set.Subset.refl _)).boundary.linearEquiv x) (hu x e w)
      exact hl.trans (hll.trans
        ((congrArg₂ Prod.mk ha hb).symm.trans (hsumright.symm.trans hr.symm)))
    exact DFunLike.congr_fun hm w
  have hid (F : FiniteBundle X) (ρF : EquivariantStructure G F.Fiber) :
      (tensorLeft E ρE (identity F ρF)).IsIsomorphic
        (identity (E.tensor F) (ρE.tensor ρF)) := by
    -- Tensoring an identity retains empty control and the original tensor bundle/action.
    refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl), Set.Subset.refl _, Set.Subset.refl _,
      Iso.refl (E.tensor F).Fiber, Iso.refl (E.tensor F).Fiber,
      (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro x w
    have hm : (((tensorLeft E ρE (identity F ρF)).1.datum.enlarge ∅ isCompact_empty
          (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
        (((identity (E.tensor F) (ρE.tensor ρF)).1.datum.enlarge ∅ isCompact_empty
          (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro e w
      have ht := htensor (SupportBundleTriple.identity F) ∅ isCompact_empty
        (Set.Subset.refl _) x e w
      have hs := (SupportBundleTriple.identity F).datum.enlarge_apply ∅ isCompact_empty
        (Set.Subset.refl _) x w
      have hr := (SupportBundleTriple.identity (E.tensor F)).datum.enlarge_apply
        ∅ isCompact_empty (Set.Subset.refl _) x (e ⊗ₜ[ℂ] w)
      exact ht.trans ((congrArg (fun w ↦ e ⊗ₜ[ℂ] w) hs).trans hr.symm)
    exact DFunLike.congr_fun hm w
  refine ⟨hiso, ?_, hsum, hid⟩
  intro a b h
  obtain ⟨F, H, ρF, ρH, h⟩ := h
  -- Keep the arbitrary original stabilizers, tensored with the supplied coefficient action.
  refine ⟨E.tensor F, E.tensor H, ρE.tensor ρF, ρE.tensor ρH, ?_⟩
  have hleft := eqv.trans (hsum a (identity F ρF))
    (hsumIso _ _ _ _ (eqv.refl (tensorLeft E ρE a)) (hid F ρF))
  have hright := eqv.trans (hsum b (identity H ρH))
    (hsumIso _ _ _ _ (eqv.refl (tensorLeft E ρE b)) (hid H ρH))
  exact eqv.trans (eqv.symm hleft) (eqv.trans (hiso _ _ h) hright)

end EquivariantSupportBundleTriple

end AtiyahSinger.ComplexBundle
