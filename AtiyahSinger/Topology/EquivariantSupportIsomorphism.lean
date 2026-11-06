/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportBundleTriple

/-!
# Equivariant isomorphism and stabilization of the original support triples

Public module ID: M1812.

Isomorphism uses two original global bundle isomorphisms, each intertwining the
specified actions, whose boundary square commutes outside one common invariant
compact control. Stabilization adds identity triples on arbitrary finite-rank
equivariant bundles; it is not restricted to product representation bundles.
All objects retain the original support triples and their specified actions.

Sources: SG I.9.23--I.9.26 and ASI I, Section 2, printed pp.489 and 494--495.
The precise equivariant closure certificates are project supplements to the
standard relative-triple stabilization and its G-bundle version. They use only
the original componentwise sum, equivariant associators and permutations, and
unions of invariant controls. No compactness of G, local compactness or
Hausdorffness of X is required for these equivalence and compatibility laws.

Forgetting the actions gives the previously defined ordinary relations in one
direction. No converse, cancellation of unstabilized bundles, comparison with
an equivariant K group, or additive-inverse identity is asserted here.
The original equivalence and compatibility certificates are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology isFiniteRank_sum

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

namespace EquivariantSupportBundleTriple

/-- Original equivariant global isomorphisms commute at infinity on one invariant exterior. -/
def IsIsomorphic (a b : EquivariantSupportBundleTriple G X) : Prop :=
  ∃ K : Set X, ∃ hK : IsCompact K,
    (∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K) ∧
      ∃ ha : a.1.datum.control ⊆ K, ∃ hb : b.1.datum.control ⊆ K,
        ∃ u : Iso a.1.source.Fiber b.1.source.Fiber,
          ∃ v : Iso a.1.target.Fiber b.1.target.Fiber,
            u.IsEquivariant a.2.sourceAction b.2.sourceAction ∧
            v.IsEquivariant a.2.targetAction b.2.targetAction ∧
            ∀ (x : (Kᶜ : Set X)) (w : a.1.source.Fiber x),
              v.linearEquiv x ((a.1.datum.enlarge K hK ha).boundary.linearEquiv x w) =
                (b.1.datum.enlarge K hK hb).boundary.linearEquiv x (u.linearEquiv x w)

/-- Stable isomorphism adds identities of arbitrary finite-rank equivariant bundles. -/
def IsStablyIsomorphic (a b : EquivariantSupportBundleTriple G X) : Prop :=
  ∃ E F : FiniteBundle X,
    ∃ ρE : EquivariantStructure G E.Fiber, ∃ ρF : EquivariantStructure G F.Fiber,
      (a.sum (identity E ρE)).IsIsomorphic (b.sum (identity F ρF))

set_option backward.isDefEq.respectTransparency.types false in
/-- Equivariant isomorphism is an equivalence and forgets to the original ordinary relation. -/
theorem isIsomorphic_properties :
    Equivalence (IsIsomorphic (G := G) (X := X)) ∧
      ∀ a b : EquivariantSupportBundleTriple G X,
        a.IsIsomorphic b → a.1.IsIsomorphic b.1 := by
  /- Stage 1: for reflexivity use the original triple's compact control,
  invariant by its equivariant structure, and the two original identity
  bundle maps. They intertwine the same actions and give the identity square.
  Stage 2: for symmetry retain the same control and invert both original
  global maps. The original intertwining equations and inverse identities
  show that these inverse maps intertwine the swapped actions. Solve the
  original boundary square for the reversed square on the same complement.
  Stage 3: for transitivity use the union of the two supplied compact
  invariant controls. Restrict both squares to its complement and compose
  their original global maps. Their equivariance equations compose, and
  both occurrences of the middle boundary map are the same restriction.
  Stage 4: forget only the two equivariance proofs and control invariance.
  The same compact set, inclusions and original global isomorphisms witness
  the existing ordinary IsIsomorphic relation. No reverse implication is used. -/
  have hinverse (J K : FiniteBundle X) (ρJ : EquivariantStructure G J.Fiber)
      (ρK : EquivariantStructure G K.Fiber) (u : Iso J.Fiber K.Fiber)
      (hu : u.IsEquivariant ρJ ρK) : u.symm.IsEquivariant ρK ρJ := by
    intro g x w
    apply (u.linearEquiv (g • x)).injective
    change (u.linearEquiv (g • x)) ((u.linearEquiv (g • x)).symm
      (ρK.linearMap g x w)) =
      (u.linearEquiv (g • x)) (ρJ.linearMap g x ((u.linearEquiv x).symm w))
    exact ((u.linearEquiv (g • x)).apply_symm_apply _).trans
      ((hu g x ((u.linearEquiv x).symm w)).trans
        (congrArg (ρK.linearMap g x) ((u.linearEquiv x).apply_symm_apply w))).symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Reflexivity uses the original invariant control and original identity maps.
    intro a
    exact ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      Iso.refl a.1.source.Fiber, Iso.refl a.1.target.Fiber,
      (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), (fun _ _ ↦ rfl)⟩
  · intro a b h
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsquare⟩ := h
    refine ⟨K, hK, hInv, hb, ha, u.symm, v.symm,
      hinverse _ _ _ _ u hu, hinverse _ _ _ _ v hv, ?_⟩
    intro x w
    -- Solve this same global square with its actual inverse maps.
    apply (v.linearEquiv x).injective
    change v.linearEquiv x ((v.linearEquiv x).symm
      ((b.1.datum.enlarge K hK hb).boundary.linearEquiv x w)) =
      v.linearEquiv x ((a.1.datum.enlarge K hK ha).boundary.linearEquiv x
        ((u.linearEquiv x).symm w))
    exact ((v.linearEquiv x).apply_symm_apply _).trans
      ((hsquare x ((u.linearEquiv x).symm w)).trans
        (congrArg ((b.1.datum.enlarge K hK hb).boundary.linearEquiv x)
          ((u.linearEquiv x).apply_symm_apply w))).symm
  · intro a b c h k
    obtain ⟨K, hK, hInvK, ha, hb, u, v, hu, hv, huv⟩ := h
    obtain ⟨L, hL, hInvL, hb', hc, w, z, hw, hz, hwz⟩ := k
    refine ⟨K ∪ L, hK.union hL, fun g x ↦ (hInvK g x).or (hInvL g x),
      fun x hx ↦ Or.inl (ha hx), fun x hx ↦ Or.inr (hc hx),
      u.trans w, v.trans z, ?_, ?_, ?_⟩
    · intro g x q
      exact (congrArg (w.linearEquiv (g • x)) (hu g x q)).trans
        (hw g x (u.linearEquiv x q))
    · intro g x q
      exact (congrArg (z.linearEquiv (g • x)) (hv g x q)).trans
        (hz g x (v.linearEquiv x q))
    · intro x q
      let xK : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
      let xL : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
      have hfirst := huv xK q
      have hsecond := hwz xL (u.linearEquiv x q)
      simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] at hfirst hsecond ⊢
      exact (congrArg (z.linearEquiv x) hfirst).trans hsecond
  · -- Forget only the action certificates, retaining the same witnesses.
    intro a b h
    obtain ⟨K, hK, _, ha, hb, u, v, _, _, hsquare⟩ := h
    exact ⟨K, hK, ha, hb, u, v, hsquare⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Direct sum respects equivariant squares, and invariant enlargement keeps the same germ. -/
theorem isIsomorphic_sum_enlarge :
    (∀ a b c d : EquivariantSupportBundleTriple G X,
      a.IsIsomorphic b → c.IsIsomorphic d → (a.sum c).IsIsomorphic (b.sum d)) ∧
      ∀ (a : EquivariantSupportBundleTriple G X) (K : Set X) (hK : IsCompact K)
        (h : a.1.datum.control ⊆ K)
        (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K),
        a.IsIsomorphic (a.enlarge K hK h hInv) := by
  /- Stage 1: for direct sum use the union of the two original common
  controls. The sums of the source and target global isomorphisms act
  componentwise on the original sum fibers. Their two equivariance equations
  and the two boundary squares therefore combine at the same x and g*x.
  The union is compact and invariant, and contains both summed controls.
  Stage 2: for enlargement use exactly the supplied invariant compact K and
  identity global bundle maps, with the unchanged source and target actions.
  Both exterior boundary maps are the same restriction of the original one.
  This concerns the original enlarged triple, not an isomorphic substitute. -/
  constructor
  · intro a b c d h k
    obtain ⟨K, hK, hInvK, ha, hb, u, v, hu, hv, huv⟩ := h
    obtain ⟨L, hL, hInvL, hc, hd, w, z, hw, hz, hwz⟩ := k
    let R := K ∪ L
    have hR : IsCompact R := hK.union hL
    have hac : (a.sum c).1.datum.control ⊆ R := Set.union_subset_union ha hc
    have hbd : (b.sum d).1.datum.control ⊆ R := Set.union_subset_union hb hd
    refine ⟨R, hR, fun g x ↦ (hInvK g x).or (hInvL g x), hac, hbd,
      u.sum w, v.sum z, ?_, ?_, ?_⟩
    · intro g x q
      exact Prod.ext (hu g x q.1) (hw g x q.2)
    · intro g x q
      exact Prod.ext (hv g x q.1) (hz g x q.2)
    · -- Both original squares are read outside one invariant compact union.
      intro x q
      let xK : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
      let xL : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
      have hfirst := huv xK q.1
      have hsecond := hwz xL q.2
      simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] at hfirst hsecond
      simp only [sum, SupportBundleTriple.sum, SupportBundleTriple.ofBoundary,
        CompactSupportTriple.sum, CompactSupportTriple.enlarge,
        Iso.restrictTo_apply, RelativeTriple.sum_apply]
      exact Prod.ext hfirst hsecond
  · intro a K hK h hInv
    refine ⟨K, hK, hInv, h, Set.Subset.refl _, Iso.refl a.1.source.Fiber,
      Iso.refl a.1.target.Fiber, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro x v
    -- Enlargement changes only where the original boundary is read.
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Equivariant identity stabilization is an equivalence compatible with sum and forgetting. -/
theorem isStablyIsomorphic_properties :
    Equivalence (IsStablyIsomorphic (G := G) (X := X)) ∧
      (∀ a b : EquivariantSupportBundleTriple G X,
        a.IsIsomorphic b → a.IsStablyIsomorphic b) ∧
      (∀ a b c d : EquivariantSupportBundleTriple G X,
        a.IsStablyIsomorphic b → c.IsStablyIsomorphic d →
          (a.sum c).IsStablyIsomorphic (b.sum d)) ∧
      ∀ a b : EquivariantSupportBundleTriple G X,
        a.IsStablyIsomorphic b → a.1.IsStablyIsomorphic b.1 := by
  /- Stage 1: an equivariant isomorphism remains one after adding the same
  equivariant identity to both sides. One may use the original source bundle
  of a with its given action; no trivialization or representation embedding
  is needed. Applying this to reflexivity proves stable reflexivity.
  Symmetry exchanges the two supplied stabilizing bundles and reverses the
  actual stabilized square, retaining the same invariant compact control.
  Stage 2: given a plus identity E isomorphic to b plus identity F, and
  b plus identity H isomorphic to c plus identity J, add identity H to the
  first square and identity F to the second. The original componentwise
  actions make the usual associators and swaps equivariant. Reorder the
  middle sum so that it is the same b plus both identities, then compose
  outside the union of the two invariant controls. Stabilizers E plus H
  and J plus F are actual finite-rank equivariant bundles; no stabilization
  by product representations or cancellation of b is assumed.
  Stage 3: for sum compatibility sum the two stabilized squares, then use
  the same equivariant associators and swaps to collect the source-side
  and target-side identities on the right. Their direct sums provide the
  two permitted arbitrary equivariant stabilizing bundles.
  Stage 4: forget equivariance of the actual stabilized square. The original
  finite bundles E and F and their original identity triples then witness
  the existing ordinary stable relation. This gives no converse and proves
  no inverse-cancellation or equivariant K-group comparison theorem. -/
  let eqv := (isIsomorphic_properties (G := G) (X := X)).1
  have hsum := (isIsomorphic_sum_enlarge (G := G) (X := X)).1
  -- These structural squares use the actual coordinate permutations and given sum actions.
  have hcomm (a b : EquivariantSupportBundleTriple G X) :
      (a.sum b).IsIsomorphic (b.sum a) := by
    let K := a.1.datum.control ∪ b.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control.union b.1.datum.isCompact_control
    refine ⟨K, hK, fun g x ↦ (a.2.isEquivariant.invariant_control g x).or
      (b.2.isEquivariant.invariant_control g x), Set.Subset.refl _,
      Set.union_subset Set.subset_union_right Set.subset_union_left,
      sumCommIso, sumCommIso, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro x v
    simp only [sum, SupportBundleTriple.sum, SupportBundleTriple.ofBoundary,
      CompactSupportTriple.sum, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.sum_apply]
    rfl
  have hassoc (a b c : EquivariantSupportBundleTriple G X) :
      ((a.sum b).sum c).IsIsomorphic (a.sum (b.sum c)) := by
    let K := (a.1.datum.control ∪ b.1.datum.control) ∪ c.1.datum.control
    have hK : IsCompact K :=
      (a.1.datum.isCompact_control.union b.1.datum.isCompact_control).union
        c.1.datum.isCompact_control
    refine ⟨K, hK, fun g x ↦
      ((a.2.isEquivariant.invariant_control g x).or
        (b.2.isEquivariant.invariant_control g x)).or
          (c.2.isEquivariant.invariant_control g x), Set.Subset.refl _,
      Set.union_subset (fun _ h ↦ Or.inl (Or.inl h))
        (Set.union_subset (fun _ h ↦ Or.inl (Or.inr h)) Set.subset_union_right),
      a.1.source.sumAssocIso b.1.source c.1.source,
      a.1.target.sumAssocIso b.1.target c.1.target, ?_, ?_, ?_⟩
    · intro g x v
      exact (FiniteBundle.sumAssocIso_apply a.1.source b.1.source c.1.source (g • x)
        (((a.sum b).sum c).2.sourceAction.linearMap g x v)).trans
          (congrArg ((a.sum (b.sum c)).2.sourceAction.linearMap g x)
            (FiniteBundle.sumAssocIso_apply a.1.source b.1.source c.1.source x v)).symm
    · intro g x v
      exact (FiniteBundle.sumAssocIso_apply a.1.target b.1.target c.1.target (g • x)
        (((a.sum b).sum c).2.targetAction.linearMap g x v)).trans
          (congrArg ((a.sum (b.sum c)).2.targetAction.linearMap g x)
            (FiniteBundle.sumAssocIso_apply a.1.target b.1.target c.1.target x v)).symm
    · intro x v
      simp only [sum, SupportBundleTriple.sum, SupportBundleTriple.ofBoundary,
        CompactSupportTriple.sum, CompactSupportTriple.enlarge,
        Iso.restrictTo_apply, RelativeTriple.sum_apply]
      exact (FiniteBundle.sumAssocIso_apply a.1.target b.1.target c.1.target x _).trans
        (congrArg (fun w : (a.1.source.sum (b.1.source.sum c.1.source)).Fiber x ↦
          (a.1.datum.boundary.linearEquiv
            ⟨x, fun h ↦ x.property (Or.inl (Or.inl h))⟩ w.1,
            b.1.datum.boundary.linearEquiv
              ⟨x, fun h ↦ x.property (Or.inl (Or.inr h))⟩ w.2.1,
            c.1.datum.boundary.linearEquiv
              ⟨x, fun h ↦ x.property (Or.inr h)⟩ w.2.2))
          (FiniteBundle.sumAssocIso_apply a.1.source b.1.source c.1.source x v)).symm
  have hidentity (E F : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber)
      (ρF : EquivariantStructure G F.Fiber) :
      ((identity E ρE).sum (identity F ρF)).IsIsomorphic
        (identity (E.sum F) (ρE.sum ρF)) := by
    refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl),
      Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _), Set.Subset.refl _,
      Iso.refl (E.sum F).Fiber, Iso.refl (E.sum F).Fiber,
      (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro x v
    simp only [sum, identity, SupportBundleTriple.sum, SupportBundleTriple.identity,
      SupportBundleTriple.ofBoundary, CompactSupportTriple.sum, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.sum_apply, CompactSupportTriple.ofIso]
    rfl
  have hflatten (a : EquivariantSupportBundleTriple G X) (E F : FiniteBundle X)
      (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber) :
      ((a.sum (identity E ρE)).sum (identity F ρF)).IsIsomorphic
        (a.sum (identity (E.sum F) (ρE.sum ρF))) :=
    eqv.trans (hassoc a (identity E ρE) (identity F ρF))
      (hsum _ _ _ _ (eqv.refl a) (hidentity E F ρE ρF))
  have hshuffle (a b c d : EquivariantSupportBundleTriple G X) :
      ((a.sum b).sum (c.sum d)).IsIsomorphic ((a.sum c).sum (b.sum d)) := by
    -- Reassociate and swap only the middle two original summands.
    apply eqv.trans (hassoc a b (c.sum d))
    apply eqv.trans (hsum _ _ _ _ (eqv.refl a) (eqv.symm (hassoc b c d)))
    apply eqv.trans (hsum _ _ _ _ (eqv.refl a)
      (hsum _ _ _ _ (hcomm b c) (eqv.refl d)))
    apply eqv.trans (hsum _ _ _ _ (eqv.refl a) (hassoc c b d))
    exact eqv.symm (hassoc a c (b.sum d))
  have hstable (a b : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic b) :
      a.IsStablyIsomorphic b := by
    -- The original source of a is an allowed stabilizer with its specified action.
    exact ⟨a.1.source, a.1.source, a.2.sourceAction, a.2.sourceAction,
      hsum _ _ _ _ h (eqv.refl (identity a.1.source a.2.sourceAction))⟩
  refine ⟨⟨?_, ?_, ?_⟩, hstable, ?_, ?_⟩
  · intro a
    exact hstable a a (eqv.refl a)
  · intro a b h
    obtain ⟨E, F, ρE, ρF, h⟩ := h
    exact ⟨F, E, ρF, ρE, eqv.symm h⟩
  · intro a b c h k
    obtain ⟨E, F, ρE, ρF, hab⟩ := h
    obtain ⟨H, J, ρH, ρJ, hbc⟩ := k
    refine ⟨E.sum H, J.sum F, ρE.sum ρH, ρJ.sum ρF, ?_⟩
    -- Add the other identity and align the identical middle triple before composing.
    apply eqv.trans (eqv.symm (hflatten a E H ρE ρH))
    apply eqv.trans (hsum _ _ _ _ hab (eqv.refl (identity H ρH)))
    apply eqv.trans (hassoc b (identity F ρF) (identity H ρH))
    apply eqv.trans (hsum _ _ _ _ (eqv.refl b)
      (hcomm (identity F ρF) (identity H ρH)))
    apply eqv.trans (eqv.symm (hassoc b (identity H ρH) (identity F ρF)))
    apply eqv.trans (hsum _ _ _ _ hbc (eqv.refl (identity F ρF)))
    exact hflatten c J F ρJ ρF
  · intro a b c d h k
    obtain ⟨E, F, ρE, ρF, hab⟩ := h
    obtain ⟨H, J, ρH, ρJ, hcd⟩ := k
    refine ⟨E.sum H, F.sum J, ρE.sum ρH, ρF.sum ρJ, ?_⟩
    -- The same four-summand shuffle collects precisely the original identity stabilizers.
    apply eqv.trans (hsum _ _ _ _ (eqv.refl (a.sum c))
      (eqv.symm (hidentity E H ρE ρH)))
    apply eqv.trans (eqv.symm (hshuffle a (identity E ρE) c (identity H ρH)))
    apply eqv.trans (hsum _ _ _ _ hab hcd)
    apply eqv.trans (hshuffle b (identity F ρF) d (identity J ρJ))
    exact hsum _ _ _ _ (eqv.refl (b.sum d)) (hidentity F J ρF ρJ)
  · intro a b h
    obtain ⟨E, F, ρE, ρF, h⟩ := h
    exact ⟨E, F, (isIsomorphic_properties (G := G) (X := X)).2 _ _ h⟩

end EquivariantSupportBundleTriple

end AtiyahSinger.ComplexBundle
