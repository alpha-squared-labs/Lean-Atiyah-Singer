/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportIsomorphism

/-!
# Proper pullback of the original equivariant support triples

Public module ID: M1814.

The underlying support triple is exactly its previous proper pullback. Its
control is the inverse image of the original compact control, its boundary is
the original relative-triple pullback, and its two actions are the specified
pulled-back actions. Equivariant isomorphism and arbitrary equivariant identity
stabilization are preserved, as are direct sum and identity up to the same
equivariant isomorphism relation.

Sources: SG I.9.26, p.66, and KA II.2.33 for actual relative-triple pullback;
KA II.4.1--4.2 for proper contravariance with compact supports; ASI I, Section 2,
printed pp.494--495, for the equivariant extension. The direct presentation
certificates on general topological groups and bases are project supplements.
Properness is used only for compact inverse-image controls; no compact group,
Hausdorffness or local compactness is needed for these formulas and relations.
The original pullback equivariance and compatibility certificates are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology isFiniteRank_sum

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The original proper pullback has invariant control and intertwines the actual pulled actions. -/
theorem CompactSupportTriple.IsEquivariant.pullback {a : CompactSupportTriple E F}
    {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}
    (ha : a.IsEquivariant ρE ρF) (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    (a.pullback f hf).IsEquivariant (ρE.pullback f heq) (ρF.pullback f heq) := by
  /- Stage 1: the old proper pullback has precisely the control f inverse K,
  compact by hf. Membership of g*y in this control is membership of f(g*y)
  in K; heq and the old invariance law identify it with membership of f(y).
  Stage 2: outside that inverse image, RelativeTriple.pullback_apply identifies
  the pulled boundary with the original boundary at f(y). Apply the old
  intertwining square there. Transport its target fibers along the same heq
  used by the two pulled actions. The complement witnesses differ only by
  proof irrelevance, so this is the square for the original pulled boundary. -/
  have hInv (g : G) (y : Y) : g • y ∈ (a.pullback f hf).control ↔
      y ∈ (a.pullback f hf).control := by
    change f (g • y) ∈ a.control ↔ f y ∈ a.control
    rw [heq g y]
    exact ha.invariant_control g (f y)
  refine ⟨hInv, ?_⟩
  intro g y v
  -- Read both pulled boundary values on their original fibers at f(y).
  have htransport (x z : X) (hxz : x = z) (hx : x ∈ a.controlᶜ)
      (hz : z ∈ a.controlᶜ) (LE : E (f y) →ₗ[ℂ] E z) (LF : F (f y) →ₗ[ℂ] F z)
      (hsquare : ∀ w, a.boundary.linearEquiv ⟨z, hz⟩ (LE w) =
        LF (a.boundary.linearEquiv ⟨f y, y.property⟩ w)) :
      a.boundary.linearEquiv ⟨x, hx⟩
          ((Eq.mpr (congrArg (fun b ↦ E (f y) →ₗ[ℂ] E b) hxz) LE) v) =
        (Eq.mpr (congrArg (fun b ↦ F (f y) →ₗ[ℂ] F b) hxz) LF)
          (a.boundary.linearEquiv ⟨f y, y.property⟩ v) := by
    subst z
    exact hsquare v
  -- The same supplied base equality transports the two sides of the original square.
  have hsquare := htransport (f (g • y)) (g • f y) (heq g y)
    (fun h ↦ y.property ((hInv g y).mp h))
    (fun h ↦ y.property ((ha.invariant_control g (f y)).mp h))
    (ρE.linearMap g (f y)) (ρF.linearMap g (f y))
    (ha.boundary_intertwines g ⟨f y, y.property⟩)
  have hl := RelativeTriple.pullback_apply a.boundary f
    ⟨g • y.val, fun h ↦ y.property ((hInv g y).mp h)⟩
    ((ρE.pullback f heq).linearMap g y v)
  have hr := RelativeTriple.pullback_apply a.boundary f y v
  exact hl.trans (hsquare.trans
    (congrArg ((ρF.pullback f heq).linearMap g y) hr).symm)

namespace EquivariantSupportBundleTriple

/-- Proper pullback retains exactly the old support triple and equips it with the pulled actions. -/
@[reducible]
def pullback (a : EquivariantSupportBundleTriple G X) (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    EquivariantSupportBundleTriple G Y :=
  ⟨a.1.pullback f hf,
    { sourceAction := a.2.sourceAction.pullback f heq
      targetAction := a.2.targetAction.pullback f heq
      isEquivariant := a.2.isEquivariant.pullback f heq hf }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual proper pullback preserves equivariant isomorphism, stabilization, sum and identity. -/
theorem pullback_relations (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    (∀ a b : EquivariantSupportBundleTriple G X,
      a.IsIsomorphic b → (a.pullback f heq hf).IsIsomorphic (b.pullback f heq hf)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      a.IsStablyIsomorphic b →
        (a.pullback f heq hf).IsStablyIsomorphic (b.pullback f heq hf)) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      ((a.sum b).pullback f heq hf).IsIsomorphic
        ((a.pullback f heq hf).sum (b.pullback f heq hf))) ∧
    ∀ (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber),
      ((identity E ρE).pullback f heq hf).IsIsomorphic
        (identity (E.pullback f) (ρE.pullback f heq)) := by
  /- Stage 1: pull the supplied common invariant compact control K back to
  f inverse K. Properness gives compactness, and heq gives invariance. Use
  exactly the old global isomorphisms u.pullback f and v.pullback f. Their
  equivariance follows from pullback_maps, and the boundary square at y is
  the old square at f(y), by the original relative pullback formula.
  Stage 2: pullback commutes with the original componentwise sum through the
  vector-preserving comparison from E(f(y)) times F(f(y)) to itself. Its
  forward and inverse total maps are continuous in the original induced
  topologies; both actions are the same componentwise original action with
  the same target transport. The controls agree because inverse image
  preserves union, and the boundary maps agree componentwise. Identity
  pullback uses the original pulled bundle, empty control and identity map.
  These comparisons give the third and fourth clauses without choosing new
  bundles, actions or boundary maps.
  Stage 3: for a supplied stable square, pull that square back using Stage 1.
  Apply the Stage 2 sum and identity comparisons on both sides and compose
  equivariant squares. The stabilizers are exactly the original arbitrary
  finite bundles E.pullback f and F.pullback f with their pulled actions.
  No stabilization by product representations or cancellation is assumed. -/
  let eqv := (isIsomorphic_properties (G := G) (X := Y)).1
  have hsumIso := (isIsomorphic_sum_enlarge (G := G) (X := Y)).1
  have hpull (a b : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic b) :
      (a.pullback f heq hf).IsIsomorphic (b.pullback f heq hf) := by
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsquare⟩ := h
    have hInv' (g : G) (y : Y) : g • y ∈ f ⁻¹' K ↔ y ∈ f ⁻¹' K := by
      change f (g • y) ∈ K ↔ f y ∈ K
      rw [heq g y]
      exact hInv g (f y)
    -- Pull the same global maps and the same invariant compact control back.
    refine ⟨f ⁻¹' K, hf.isCompact_preimage hK, hInv', Set.preimage_mono ha,
      Set.preimage_mono hb, u.pullback f, v.pullback f,
      (EquivariantStructure.pullback_maps _ _ f heq).2 u hu,
      (EquivariantStructure.pullback_maps _ _ f heq).2 v hv, ?_⟩
    intro y w
    let x : (Kᶜ : Set X) := ⟨f y, y.property⟩
    have hsquare' := hsquare x w
    have ha₀ := a.1.datum.enlarge_apply K hK ha x w
    have hb₀ := b.1.datum.enlarge_apply K hK hb x (u.linearEquiv (f y) w)
    have hleft := (a.1.datum.pullback f hf).enlarge_apply (f ⁻¹' K)
      (hf.isCompact_preimage hK) (Set.preimage_mono ha) y w
    have hright := (b.1.datum.pullback f hf).enlarge_apply (f ⁻¹' K)
      (hf.isCompact_preimage hK) (Set.preimage_mono hb) y (u.linearEquiv (f y) w)
    have hl := hleft.trans (RelativeTriple.pullback_apply a.1.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (ha hy)⟩ w)
    have hr := hright.trans (RelativeTriple.pullback_apply b.1.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (hb hy)⟩ (u.linearEquiv (f y) w))
    exact (congrArg (v.linearEquiv (f y)) (hl.trans ha₀.symm)).trans
      (hsquare'.trans (hb₀.trans hr.symm))
  have compare (J K : FiniteBundle X) (ρJ : EquivariantStructure G J.Fiber)
      (ρK : EquivariantStructure G K.Fiber) :
      ∃ e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber,
        (∀ y w, e.linearEquiv y w = w) ∧
          e.IsEquivariant ((ρJ.sum ρK).pullback f heq)
            ((ρJ.pullback f heq).sum (ρK.pullback f heq)) := by
    -- This comparison is identity on vectors and continuous in both native sum/pullback topologies.
    let e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber :=
      { linearEquiv y := LinearEquiv.refl ℂ (J.Fiber (f y) × K.Fiber (f y))
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
              (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber f).continuous_iff]
          apply ((Pullback.continuous_proj Unit J.Fiber f).comp continuous_sum_fst).prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit J.Fiber f).comp continuous_sum_fst).prodMk
            ((Pullback.continuous_lift Unit K.Fiber f).comp continuous_sum_snd) }
    refine ⟨e, (fun _ _ ↦ rfl), ?_⟩
    intro g y w
    -- Transport of a product map is the product of the two maps with that same transport.
    have htransport (x z : X) (hxz : x = z)
        (LJ : J.Fiber (f y) →ₗ[ℂ] J.Fiber z)
        (LK : K.Fiber (f y) →ₗ[ℂ] K.Fiber z) :
        (Eq.mpr (congrArg (fun b ↦ (J.Fiber (f y) × K.Fiber (f y)) →ₗ[ℂ]
          (J.Fiber b × K.Fiber b)) hxz) (LJ.prodMap LK)) w =
        ((Eq.mpr (congrArg (fun b ↦ J.Fiber (f y) →ₗ[ℂ] J.Fiber b) hxz) LJ) w.1,
          (Eq.mpr (congrArg (fun b ↦ K.Fiber (f y) →ₗ[ℂ] K.Fiber b) hxz) LK) w.2) := by
      subst z
      rfl
    exact htransport (f (g • y)) (g • f y) (heq g y)
      (ρJ.linearMap g (f y)) (ρK.linearMap g (f y))
  have hsum (a b : EquivariantSupportBundleTriple G X) :
      ((a.sum b).pullback f heq hf).IsIsomorphic
        ((a.pullback f heq hf).sum (b.pullback f heq hf)) := by
    obtain ⟨u, hu, hueq⟩ := compare a.1.source b.1.source a.2.sourceAction b.2.sourceAction
    obtain ⟨v, hv, hveq⟩ := compare a.1.target b.1.target a.2.targetAction b.2.targetAction
    let R := a.1.datum.control ∪ b.1.datum.control
    have hR : IsCompact R := a.1.datum.isCompact_control.union b.1.datum.isCompact_control
    let K := f ⁻¹' R
    have hK : IsCompact K := hf.isCompact_preimage hR
    have hInv (g : G) (y : Y) : g • y ∈ K ↔ y ∈ K := by
      change f (g • y) ∈ R ↔ f y ∈ R
      rw [heq g y]
      exact (a.2.isEquivariant.invariant_control g (f y)).or
        (b.2.isEquivariant.invariant_control g (f y))
    refine ⟨K, hK, hInv, Set.Subset.refl _, Set.Subset.refl _, u, v, hueq, hveq, ?_⟩
    intro y w
    let x : (Rᶜ : Set X) := ⟨f y, y.property⟩
    -- Evaluate both routes using the exact original sum and pullback boundary formulas.
    have hl := ((a.1.datum.sum b.1.datum).pullback f hf).enlarge_apply K hK
      (Set.Subset.refl _) y w
    have hp := RelativeTriple.pullback_apply (a.1.datum.sum b.1.datum).boundary f y w
    have hs := RelativeTriple.sum_apply
      (a.1.datum.enlarge R hR Set.subset_union_left).boundary
      (b.1.datum.enlarge R hR Set.subset_union_right).boundary x w
    have ha := a.1.datum.enlarge_apply R hR Set.subset_union_left x w.1
    have hb := b.1.datum.enlarge_apply R hR Set.subset_union_right x w.2
    have hleft := hl.trans (hp.trans (hs.trans (congrArg₂ Prod.mk ha hb)))
    have hr := ((a.1.datum.pullback f hf).sum (b.1.datum.pullback f hf)).enlarge_apply
      K hK (Set.Subset.refl _) y w
    have ht := RelativeTriple.sum_apply
      ((a.1.datum.pullback f hf).enlarge K hK Set.subset_union_left).boundary
      ((b.1.datum.pullback f hf).enlarge K hK Set.subset_union_right).boundary y w
    have hpa := (a.1.datum.pullback f hf).enlarge_apply K hK Set.subset_union_left y w.1
    have hpb := (b.1.datum.pullback f hf).enlarge_apply K hK Set.subset_union_right y w.2
    have hqa := RelativeTriple.pullback_apply a.1.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (Or.inl hy)⟩ w.1
    have hqb := RelativeTriple.pullback_apply b.1.datum.boundary f
      ⟨y.val, fun hy ↦ y.property (Or.inr hy)⟩ w.2
    have hright := hr.trans (ht.trans (congrArg₂ Prod.mk (hpa.trans hqa) (hpb.trans hqb)))
    exact (hv y _).trans ((hleft.trans hright.symm).trans
      (congrArg ((((a.1.datum.pullback f hf).sum (b.1.datum.pullback f hf)).enlarge
        K hK (Set.Subset.refl _)).boundary.linearEquiv y) (hu y w)).symm)
  have hid (J : FiniteBundle X) (ρJ : EquivariantStructure G J.Fiber) :
      ((identity J ρJ).pullback f heq hf).IsIsomorphic
        (identity (J.pullback f) (ρJ.pullback f heq)) := by
    refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl),
      (fun _ h ↦ h), Set.Subset.refl _, Iso.refl (J.pullback f).Fiber,
      Iso.refl (J.pullback f).Fiber, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro y w
    have hl := ((identity J ρJ).1.datum.pullback f hf).enlarge_apply
      ∅ isCompact_empty (fun _ h ↦ h) y w
    have hp := RelativeTriple.pullback_apply (identity J ρJ).1.datum.boundary f y w
    have hr := (identity (J.pullback f) (ρJ.pullback f heq)).1.datum.enlarge_apply
      ∅ isCompact_empty (Set.Subset.refl _) y w
    exact (hl.trans hp).trans hr.symm
  refine ⟨hpull, ?_, hsum, hid⟩
  intro a b h
  obtain ⟨J, K, ρJ, ρK, h⟩ := h
  refine ⟨J.pullback f, K.pullback f, ρJ.pullback f heq, ρK.pullback f heq, ?_⟩
  -- Stabilizers are the original pulled equivariant bundles, and both comparisons use them.
  have hleft := eqv.trans (hsum a (identity J ρJ))
    (hsumIso _ _ _ _ (eqv.refl (a.pullback f heq hf)) (hid J ρJ))
  have hright := eqv.trans (hsum b (identity K ρK))
    (hsumIso _ _ _ _ (eqv.refl (b.pullback f heq hf)) (hid K ρK))
  exact eqv.trans (eqv.symm hleft) (eqv.trans (hpull _ _ h) hright)

end EquivariantSupportBundleTriple

end AtiyahSinger.ComplexBundle
