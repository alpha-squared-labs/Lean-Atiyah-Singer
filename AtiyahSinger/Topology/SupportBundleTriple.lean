/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTriple
public import AtiyahSinger.Topology.CompactSupportTriple
public import AtiyahSinger.Topology.FiniteBundle

/-!
# Bundled triples with an isomorphism at infinity

Public module ID: M2184.

D07/K02. A triple carries two locally finite-rank bundles and one compact control
set. Isomorphism is a commuting global bundle square after enlarging the control;
this is equality of the boundary germ at infinity. Stable equivalence adds only
identity triples. No global rank bound or extension to the compactification is assumed.
Sources: SG I.9.26, p.67; the n=1 relation of I.9.23 and KA II.2.26–2.29.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

attribute [local instance] sumTopology trivialTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two finite-rank bundle objects with a specified isomorphism at infinity. -/
structure SupportBundleTriple (X : Type*) [TopologicalSpace X] where
  /-- The source bundle on the original space. -/
  source : FiniteBundle X
  /-- The target bundle on the original space. -/
  target : FiniteBundle X
  /-- A compact control and the actual isomorphism outside it. -/
  datum : CompactSupportTriple source.Fiber target.Fiber

/-- Package existing compact-support boundary data without changing its action. -/
@[reducible]
def SupportBundleTriple.ofBoundary (E F : FiniteBundle X)
    (a : CompactSupportTriple E.Fiber F.Fiber) : SupportBundleTriple X where
  source := E
  target := F
  datum := a

/-- The global identity, with empty compact control. -/
@[reducible]
def SupportBundleTriple.identity (E : FiniteBundle X) : SupportBundleTriple X :=
  ofBoundary E E (CompactSupportTriple.ofIso (Iso.refl E.Fiber))

/-- Enlarge only the control and restrict the same boundary map. -/
@[reducible]
def SupportBundleTriple.enlarge (a : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (h : a.datum.control ⊆ K) : SupportBundleTriple X :=
  ofBoundary a.source a.target (a.datum.enlarge K hK h)

/-- Reverse the bundles and invert the map at infinity. -/
@[reducible]
def SupportBundleTriple.inverse (a : SupportBundleTriple X) : SupportBundleTriple X :=
  ofBoundary a.target a.source a.datum.inverse

/-- Direct sum uses the union of the two compact controls. -/
@[reducible]
def SupportBundleTriple.sum (a b : SupportBundleTriple X) : SupportBundleTriple X :=
  ofBoundary (a.source.sum b.source) (a.target.sum b.target) (a.datum.sum b.datum)

/-- Proper pullback uses the actual inverse image of the compact control. -/
@[reducible]
def SupportBundleTriple.pullback (a : SupportBundleTriple X) (f : C(Y, X))
    (hf : IsProperMap f) : SupportBundleTriple Y :=
  ofBoundary (a.source.pullback f) (a.target.pullback f) (a.datum.pullback f hf)


/-- A global isomorphism square is required only outside one common compact set. -/
def SupportBundleTriple.IsIsomorphic (a b : SupportBundleTriple X) : Prop :=
  ∃ K : Set X, ∃ hK : IsCompact K, ∃ ha : a.datum.control ⊆ K,
    ∃ hb : b.datum.control ⊆ K,
      RelativeTriple.IsIsomorphic (a.datum.enlarge K hK ha).boundary
        (b.datum.enlarge K hK hb).boundary

/-- Stable equivalence adds independent identity triples to the two sides. -/
def SupportBundleTriple.IsStablyIsomorphic (a b : SupportBundleTriple X) : Prop :=
  ∃ E F : FiniteBundle X,
    (a.sum (SupportBundleTriple.identity E)).IsIsomorphic
      (b.sum (SupportBundleTriple.identity F))

section

set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate a sum after one common enlargement; reused in the stable germ proofs. -/
private theorem SupportBundleTriple.sum_enlarge_apply (a b : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (h : (a.sum b).datum.control ⊆ K)
    (x : (Kᶜ : Set X)) (v : (a.source.sum b.source).Fiber x) :
    ((a.sum b).datum.enlarge K hK h).boundary.linearEquiv x v =
      (a.datum.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (h (Or.inl hx))⟩ v.1,
        b.datum.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (h (Or.inr hx))⟩ v.2) := by
  -- Evaluate each existing chosen restriction without unfolding its total-space comparisons.
  let L := a.datum.control ∪ b.datum.control
  have hL : IsCompact L := a.datum.isCompact_control.union b.datum.isCompact_control
  let y : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property (h hx)⟩
  have ho := CompactSupportTriple.enlarge_apply (a.datum.sum b.datum) K hK h x v
  have hs := RelativeTriple.sum_apply
    (a.datum.enlarge L hL Set.subset_union_left).boundary
    (b.datum.enlarge L hL Set.subset_union_right).boundary y v
  exact ho.trans (hs.trans (Prod.ext
    (a.datum.enlarge_apply L hL Set.subset_union_left y v.1)
    (b.datum.enlarge_apply L hL Set.subset_union_right y v.2)))

/-- Evaluate the corresponding ordinary stabilized boundary on the same exterior region. -/
private theorem SupportBundleTriple.boundary_stabilize_apply (a : SupportBundleTriple X)
    (E : FiniteBundle X) (K : Set X) (hK : IsCompact K) (ha : a.datum.control ⊆ K)
    (x : (Kᶜ : Set X)) (v : a.source.Fiber x × E.Fiber x) :
    ((BundleTriple.ofBoundary a.source a.target (a.datum.enlarge K hK ha).boundary).sum
      (BundleTriple.identity Kᶜ E)).boundary.linearEquiv x v =
      (a.datum.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (ha hx)⟩ v.1, v.2) := by
  -- The original identity summand fixes its vector, while enlargement reads the old germ.
  exact (RelativeTriple.sum_apply (a.datum.enlarge K hK ha).boundary
    (RelativeTriple.identity E.Fiber Kᶜ) x v).trans
      (Prod.ext (a.datum.enlarge_apply K hK ha x v.1) rfl)

/-- Every infinity triple is isomorphic to itself. -/
theorem SupportBundleTriple.isIsomorphic_refl (a : SupportBundleTriple X) : a.IsIsomorphic a := by
  /- Use the original compact control and identity maps on its source and target bundles. Both
  routes through the boundary square are the same original isomorphism. -/

  exact ⟨a.datum.control, a.datum.isCompact_control, Set.Subset.refl _,
    Set.Subset.refl _, RelativeTriple.isIsomorphic_refl _⟩

/-- Invert a global square while retaining its common compact control. -/
theorem SupportBundleTriple.IsIsomorphic.symm {a b : SupportBundleTriple X}
    (h : a.IsIsomorphic b) : b.IsIsomorphic a := by
  /- Exchange the two control inclusions and invert the two global bundle isomorphisms. The
  original commuting square yields the reversed commuting square. -/

  obtain ⟨K, hK, ha, hb, h⟩ := h
  exact ⟨K, hK, hb, ha, RelativeTriple.IsIsomorphic.symm h⟩

/-- Isomorphisms at infinity compose after taking the union of controls. -/
theorem SupportBundleTriple.IsIsomorphic.trans {a b c : SupportBundleTriple X}
    (h : a.IsIsomorphic b) (k : b.IsIsomorphic c) : a.IsIsomorphic c := by
  /- Take the union of the compact controls and restrict both squares to its complement.
  Compose the source and target global isomorphisms. The middle boundary maps agree after
  restriction, so the composite square commutes. -/
  obtain ⟨K, hK, ha, hb, u, v, huv⟩ := h
  obtain ⟨L, hL, hb', hc, w, z, hwz⟩ := k

  refine ⟨K ∪ L, hK.union hL, fun x hx ↦ Or.inl (ha hx),
    fun x hx ↦ Or.inr (hc hx), u.trans w, v.trans z, ?_⟩
  intro x q
  let xK : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
  let xL : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
  have hfirst := huv xK q
  have hsecond := hwz xL (u.linearEquiv x q)
  simp only [Iso.restrictTo_apply] at hfirst hsecond ⊢
  -- Both appearances of the middle map are the same original boundary value.
  exact (congrArg (z.linearEquiv x) hfirst).trans hsecond

/-- Enlarging the control leaves the same triple germ. -/
theorem SupportBundleTriple.isIsomorphic_enlarge (a : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (h : a.datum.control ⊆ K) :
    a.IsIsomorphic (a.enlarge K hK h) := by
  /- Use K as the common control and identity global bundle maps. On its complement both
  boundary maps are the identical restriction of the original isomorphism. -/

  refine ⟨K, hK, h, Set.Subset.refl _, Iso.refl a.source.Fiber,
    Iso.refl a.target.Fiber, ?_⟩
  intro x v
  simp only [Iso.restrictTo_apply]
  rfl

/-- Direct sum preserves isomorphisms at infinity. -/
theorem SupportBundleTriple.IsIsomorphic.sum {a b c d : SupportBundleTriple X}
    (h : a.IsIsomorphic b) (k : c.IsIsomorphic d) : (a.sum c).IsIsomorphic (b.sum d) := by
  obtain ⟨K, hK, ha, hb, u, v, huv⟩ := h
  obtain ⟨L, hL, hc, hd, w, z, hwz⟩ := k
  let R := K ∪ L
  have hR : IsCompact R := hK.union hL
  have hac : (a.sum c).datum.control ⊆ R := Set.union_subset_union ha hc
  have hbd : (b.sum d).datum.control ⊆ R := Set.union_subset_union hb hd
  refine ⟨R, hR, hac, hbd, u.sum w, v.sum z, ?_⟩
  intro x q
  let xK : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inl hx)⟩
  let xL : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property (Or.inr hx)⟩
  have hfirst := huv xK q.1
  have hsecond := hwz xL q.2
  simp only [Iso.restrictTo_apply] at hfirst hsecond
  -- Evaluate the two sum boundaries before applying the two original squares.
  have hl := a.sum_enlarge_apply c R hR hac x q
  have hr := b.sum_enlarge_apply d R hR hbd x ((u.sum w).linearEquiv x q)
  exact (congrArg ((v.sum z).linearEquiv x) hl).trans
    ((Prod.ext hfirst hsecond).trans hr.symm)

/-- Proper pullback preserves isomorphisms at infinity. -/
theorem SupportBundleTriple.IsIsomorphic.pullback {a b : SupportBundleTriple X}
    (h : a.IsIsomorphic b) (f : C(Y, X)) (hf : IsProperMap f) :
    (a.pullback f hf).IsIsomorphic (b.pullback f hf) := by
  /- The inverse image of the common compact control is compact by properness. Pull back both
  global isomorphisms and the commuting boundary equation to its complement. -/
  obtain ⟨K, hK, ha, hb, u, v, huv⟩ := h
  -- Properness supplies compactness of this exact inverse-image control.
  refine ⟨f ⁻¹' K, hf.isCompact_preimage hK, Set.preimage_mono ha,
    Set.preimage_mono hb, Iso.pullback f u, Iso.pullback f v, ?_⟩
  intro y q
  let x : (Kᶜ : Set X) := ⟨f y, y.property⟩
  have hsquare := huv x q
  have ha₀ := a.datum.enlarge_apply K hK ha x q
  have hb₀ := b.datum.enlarge_apply K hK hb x (u.linearEquiv (f y) q)
  have hleft := (a.datum.pullback f hf).enlarge_apply (f ⁻¹' K)
    (hf.isCompact_preimage hK) (Set.preimage_mono ha) y q
  have hright := (b.datum.pullback f hf).enlarge_apply (f ⁻¹' K)
    (hf.isCompact_preimage hK) (Set.preimage_mono hb) y (u.linearEquiv (f y) q)
  have hl := hleft.trans (RelativeTriple.pullback_apply a.datum.boundary f
    ⟨y.val, fun hy ↦ y.property (ha hy)⟩ q)
  have hr := hright.trans (RelativeTriple.pullback_apply b.datum.boundary f
    ⟨y.val, fun hy ↦ y.property (hb hy)⟩ (u.linearEquiv (f y) q))
  exact (congrArg (v.linearEquiv (f y)) (hl.trans ha₀.symm)).trans
    (hsquare.trans (hb₀.trans hr.symm))

/-- Isomorphism implies stable isomorphism by adding zero bundles. -/
theorem SupportBundleTriple.isStablyIsomorphic_of_isIsomorphic (a b : SupportBundleTriple X)
    (h : a.IsIsomorphic b) : a.IsStablyIsomorphic b := by
  /- Add the zero-rank trivial bundle on both sides by summing the given
  square with its identity square over the same exterior region. -/

  let Z := FiniteBundle.trivial X 0
  exact ⟨Z, Z, h.sum (SupportBundleTriple.isIsomorphic_refl
    (SupportBundleTriple.identity Z))⟩

/-- Stable equivalence at infinity is reflexive. -/
theorem SupportBundleTriple.isStablyIsomorphic_refl (a : SupportBundleTriple X) :
    a.IsStablyIsomorphic a := by
  /- Apply the preceding zero-stabilization construction to the identity square of the triple.
  This uses its original compact control and imposes no compactness on X. -/
  exact a.isStablyIsomorphic_of_isIsomorphic a a.isIsomorphic_refl

/-- Stable equivalence at infinity is symmetric. -/
theorem SupportBundleTriple.IsStablyIsomorphic.symm {a b : SupportBundleTriple X}
    (h : a.IsStablyIsomorphic b) : b.IsStablyIsomorphic a := by
  /- Swap the two stabilizing bundles and reverse the isomorphism of the stabilized triples.
  The common compact control is retained. -/
  obtain ⟨E, F, hEF⟩ := h
  exact ⟨F, E, SupportBundleTriple.IsIsomorphic.symm hEF⟩

/-- Stable equivalence at infinity is transitive. -/
theorem SupportBundleTriple.IsStablyIsomorphic.trans {a b c : SupportBundleTriple X}
    (h : a.IsStablyIsomorphic b) (k : b.IsStablyIsomorphic c) : a.IsStablyIsomorphic c := by
  /- Add the other square's identity stabilizers, reassociate and permute direct sums to align
  the middle triples, and work outside the union of the compact controls. Compose the two
  resulting global squares. -/
  obtain ⟨E, F, K, hK, ha, hb, u, v, huv⟩ := h
  obtain ⟨G, H, L, hL, hb', hc, w, z, hwz⟩ := k
  let R := K ∪ L
  have hR : IsCompact R := hK.union hL
  have haR : a.datum.control ⊆ R := fun x hx ↦ Or.inl (ha (Or.inl hx))
  have hbR : b.datum.control ⊆ R := fun x hx ↦ Or.inl (hb (Or.inl hx))
  have hcR : c.datum.control ⊆ R := fun x hx ↦ Or.inr (hc (Or.inl hx))
  -- Read the same three germs as ordinary triples on one common exterior region.
  let aR := BundleTriple.ofBoundary a.source a.target (a.datum.enlarge R hR haR).boundary
  let bR := BundleTriple.ofBoundary b.source b.target (b.datum.enlarge R hR hbR).boundary
  let cR := BundleTriple.ofBoundary c.source c.target (c.datum.enlarge R hR hcR).boundary
  have hab : aR.IsStablyIsomorphic bR := by
    refine ⟨E, F, u, v, ?_⟩
    intro x q
    let y : (Kᶜ : Set X) := ⟨x.val, fun hx ↦ x.property (Or.inl hx)⟩
    have hl := a.sum_enlarge_apply (SupportBundleTriple.identity E) K hK ha y q
    have hr := b.sum_enlarge_apply (SupportBundleTriple.identity F) K hK hb y
      (u.linearEquiv x q)
    have hleft := a.boundary_stabilize_apply E R hR haR x q
    have hright := b.boundary_stabilize_apply F R hR hbR x (u.linearEquiv x q)
    exact (congrArg (v.linearEquiv x) (hleft.trans hl.symm)).trans
      ((huv y q).trans (hr.trans hright.symm))
  have hbc : bR.IsStablyIsomorphic cR := by
    refine ⟨G, H, w, z, ?_⟩
    intro x q
    let y : (Lᶜ : Set X) := ⟨x.val, fun hx ↦ x.property (Or.inr hx)⟩
    have hl := b.sum_enlarge_apply (SupportBundleTriple.identity G) L hL hb' y q
    have hr := c.sum_enlarge_apply (SupportBundleTriple.identity H) L hL hc y
      (w.linearEquiv x q)
    have hleft := b.boundary_stabilize_apply G R hR hbR x q
    have hright := c.boundary_stabilize_apply H R hR hcR x (w.linearEquiv x q)
    exact (congrArg (z.linearEquiv x) (hleft.trans hl.symm)).trans
      ((hwz y q).trans (hr.trans hright.symm))
  -- The already proved stable relation composes these actual global squares.
  obtain ⟨J, M, U, V, hsquare⟩ := BundleTriple.IsStablyIsomorphic.trans hab hbc
  refine ⟨J, M, R, hR, Set.union_subset haR (Set.empty_subset _),
    Set.union_subset hcR (Set.empty_subset _), U, V, ?_⟩
  intro x q
  have hleft := a.sum_enlarge_apply (SupportBundleTriple.identity J) R hR
    (Set.union_subset haR (Set.empty_subset _)) x q
  have hright := c.sum_enlarge_apply (SupportBundleTriple.identity M) R hR
    (Set.union_subset hcR (Set.empty_subset _)) x (U.linearEquiv x q)
  have hA := a.boundary_stabilize_apply J R hR haR x q
  have hC := c.boundary_stabilize_apply M R hR hcR x (U.linearEquiv x q)
  exact (congrArg (V.linearEquiv x) (hleft.trans hA.symm)).trans
    ((hsquare x q).trans (hC.trans hright.symm))

/-- Stable equivalence respects direct sums. -/
theorem SupportBundleTriple.IsStablyIsomorphic.sum {a b c d : SupportBundleTriple X}
    (h : a.IsStablyIsomorphic b) (k : c.IsStablyIsomorphic d) :
    (a.sum c).IsStablyIsomorphic (b.sum d) := by
  /- Sum the stabilized squares and reorder identity summands to the right using vector-
  preserving associators and swaps. The union of the controls works for all factors. -/
  obtain ⟨E, F, K, hK, ha, hb, u, v, huv⟩ := h
  obtain ⟨G, H, L, hL, hc, hd, w, z, hwz⟩ := k
  let R := K ∪ L
  have hR : IsCompact R := hK.union hL
  have haR : a.datum.control ⊆ R := fun x hx ↦ Or.inl (ha (Or.inl hx))
  have hbR : b.datum.control ⊆ R := fun x hx ↦ Or.inl (hb (Or.inl hx))
  have hcR : c.datum.control ⊆ R := fun x hx ↦ Or.inr (hc (Or.inl hx))
  have hdR : d.datum.control ⊆ R := fun x hx ↦ Or.inr (hd (Or.inl hx))
  let aR := BundleTriple.ofBoundary a.source a.target (a.datum.enlarge R hR haR).boundary
  let bR := BundleTriple.ofBoundary b.source b.target (b.datum.enlarge R hR hbR).boundary
  let cR := BundleTriple.ofBoundary c.source c.target (c.datum.enlarge R hR hcR).boundary
  let dR := BundleTriple.ofBoundary d.source d.target (d.datum.enlarge R hR hdR).boundary
  -- Both input squares are read on the same exterior, with unchanged vector maps.
  have hab : aR.IsStablyIsomorphic bR := by
    refine ⟨E, F, u, v, ?_⟩
    intro x q
    let y : (Kᶜ : Set X) := ⟨x.val, fun hx ↦ x.property (Or.inl hx)⟩
    have hl := a.sum_enlarge_apply (SupportBundleTriple.identity E) K hK ha y q
    have hr := b.sum_enlarge_apply (SupportBundleTriple.identity F) K hK hb y
      (u.linearEquiv x q)
    have hleft := a.boundary_stabilize_apply E R hR haR x q
    have hright := b.boundary_stabilize_apply F R hR hbR x (u.linearEquiv x q)
    exact (congrArg (v.linearEquiv x) (hleft.trans hl.symm)).trans
      ((huv y q).trans (hr.trans hright.symm))
  have hcd : cR.IsStablyIsomorphic dR := by
    refine ⟨G, H, w, z, ?_⟩
    intro x q
    let y : (Lᶜ : Set X) := ⟨x.val, fun hx ↦ x.property (Or.inr hx)⟩
    have hl := c.sum_enlarge_apply (SupportBundleTriple.identity G) L hL hc y q
    have hr := d.sum_enlarge_apply (SupportBundleTriple.identity H) L hL hd y
      (w.linearEquiv x q)
    have hleft := c.boundary_stabilize_apply G R hR hcR x q
    have hright := d.boundary_stabilize_apply H R hR hdR x (w.linearEquiv x q)
    exact (congrArg (z.linearEquiv x) (hleft.trans hl.symm)).trans
      ((hwz y q).trans (hr.trans hright.symm))
  -- Ordinary stable addition supplies the actual regrouped stabilizers and maps.
  obtain ⟨J, M, U, V, hsquare⟩ := BundleTriple.IsStablyIsomorphic.sum hab hcd
  refine ⟨J, M, R, hR,
    Set.union_subset (Set.union_subset haR hcR) (Set.empty_subset _),
    Set.union_subset (Set.union_subset hbR hdR) (Set.empty_subset _), U, V, ?_⟩
  intro x q
  -- Compare both resulting boundaries with the same original coordinate values.
  have hac : (a.sum c).datum.control ⊆ R := Set.union_subset haR hcR
  have hbd : (b.sum d).datum.control ⊆ R := Set.union_subset hbR hdR
  have hleft := (a.sum c).sum_enlarge_apply (SupportBundleTriple.identity J) R hR
    (Set.union_subset hac (Set.empty_subset _)) x q
  have hright := (b.sum d).sum_enlarge_apply (SupportBundleTriple.identity M) R hR
    (Set.union_subset hbd (Set.empty_subset _)) x (U.linearEquiv x q)
  have hla := (a.sum c).datum.enlarge_apply R hR hac x q.1
  have hlb := a.sum_enlarge_apply c R hR hac x q.1
  have hra := (b.sum d).datum.enlarge_apply R hR hbd x (U.linearEquiv x q).1
  have hrb := b.sum_enlarge_apply d R hR hbd x (U.linearEquiv x q).1
  have hl₀ := congrArg (fun r : a.target.Fiber x × c.target.Fiber x ↦ (r, q.2))
    (hla.symm.trans hlb)
  have hr₀ := congrArg
    (fun r : b.target.Fiber x × d.target.Fiber x ↦ (r, (U.linearEquiv x q).2))
    (hra.symm.trans hrb)
  have hl := hleft.trans hl₀
  have hr := hright.trans hr₀
  have hvalue := hsquare x q
  simp only [aR, bR, cR, dR, BundleTriple.ofBoundary, BundleTriple.sum,
    BundleTriple.identity, RelativeTriple.sum_apply, CompactSupportTriple.enlarge,
    RelativeTriple.identity, Iso.restrictTo_apply, Iso.refl,
    LinearEquiv.refl_apply] at hvalue
  exact (congrArg (V.linearEquiv x) hl).trans (hvalue.trans hr.symm)

/-- Stable equivalence respects proper pullback. -/
theorem SupportBundleTriple.IsStablyIsomorphic.pullback {a b : SupportBundleTriple X}
    (h : a.IsStablyIsomorphic b) (f : C(Y, X)) (hf : IsProperMap f) :
    (a.pullback f hf).IsStablyIsomorphic (b.pullback f hf) := by
  /- Pull back the stabilizing bundles and the global square. Pullback commutes with direct sum
  and identity by the actual vector maps. Properness supplies the inverse-image compact
  control. -/
  obtain ⟨E, F, K, hK, ha, hb, u, v, huv⟩ := h
  have haK : a.datum.control ⊆ K := fun x hx ↦ ha (Or.inl hx)
  have hbK : b.datum.control ⊆ K := fun x hx ↦ hb (Or.inl hx)
  let aK := BundleTriple.ofBoundary a.source a.target (a.datum.enlarge K hK haK).boundary
  let bK := BundleTriple.ofBoundary b.source b.target (b.datum.enlarge K hK hbK).boundary
  have hab : aK.IsStablyIsomorphic bK := by
    refine ⟨E, F, u, v, ?_⟩
    intro x q
    let y : (Kᶜ : Set X) := x
    have hl := a.sum_enlarge_apply (SupportBundleTriple.identity E) K hK ha y q
    have hr := b.sum_enlarge_apply (SupportBundleTriple.identity F) K hK hb y
      (u.linearEquiv x q)
    have hleft := a.boundary_stabilize_apply E K hK haK x q
    have hright := b.boundary_stabilize_apply F K hK hbK x (u.linearEquiv x q)
    exact (congrArg (v.linearEquiv x) (hleft.trans hl.symm)).trans
      ((huv y q).trans (hr.trans hright.symm))
  -- Pull back the same stabilized square, using the proven sum/pullback comparison.
  obtain ⟨J, M, U, V, hsquare⟩ := BundleTriple.IsStablyIsomorphic.pullback hab f
  refine ⟨J, M, f ⁻¹' K, hf.isCompact_preimage hK,
    Set.union_subset (Set.preimage_mono haK) (Set.empty_subset _),
    Set.union_subset (Set.preimage_mono hbK) (Set.empty_subset _), U, V, ?_⟩
  intro y q
  -- The support pullback and ordinary pullback read exactly the same vector at f(y).
  have ha' : (a.pullback f hf).datum.control ⊆ f ⁻¹' K := Set.preimage_mono haK
  have hb' : (b.pullback f hf).datum.control ⊆ f ⁻¹' K := Set.preimage_mono hbK
  have hleft := (a.pullback f hf).sum_enlarge_apply (SupportBundleTriple.identity J)
    (f ⁻¹' K) (hf.isCompact_preimage hK)
    (Set.union_subset ha' (Set.empty_subset _)) y q
  have hright := (b.pullback f hf).sum_enlarge_apply (SupportBundleTriple.identity M)
    (f ⁻¹' K) (hf.isCompact_preimage hK)
    (Set.union_subset hb' (Set.empty_subset _)) y (U.linearEquiv y q)
  have hla := RelativeTriple.pullback_apply a.datum.boundary f
    ⟨y.val, fun hy ↦ y.property (haK hy)⟩ q.1
  have hra := RelativeTriple.pullback_apply b.datum.boundary f
    ⟨y.val, fun hy ↦ y.property (hbK hy)⟩ (U.linearEquiv y q).1
  have hl₀ := congrArg (fun r : a.target.Fiber (f y) ↦ (r, q.2)) hla
  have hr₀ := congrArg (fun r : b.target.Fiber (f y) ↦ (r, (U.linearEquiv y q).2)) hra
  have hl := hleft.trans hl₀
  have hr := hright.trans hr₀
  have hvalue := hsquare y q
  simp only [aK, bK, BundleTriple.pullback, BundleTriple.ofBoundary, BundleTriple.sum,
    BundleTriple.identity, RelativeTriple.sum_apply, RelativeTriple.pullback_apply,
    CompactSupportTriple.enlarge, RelativeTriple.identity, Iso.restrictTo_apply,
    Iso.refl, LinearEquiv.refl_apply] at hvalue
  exact (congrArg (V.linearEquiv y) hl).trans (hvalue.trans hr.symm)

end

/-- The setoid of the stated identity-stabilization relation at infinity. -/
def SupportBundleTriple.stableSetoid (X : Type*) [TopologicalSpace X] :
    Setoid (SupportBundleTriple X) :=
  { r := SupportBundleTriple.IsStablyIsomorphic
    iseqv := ⟨SupportBundleTriple.isStablyIsomorphic_refl,
      fun h ↦ h.symm, fun h k ↦ h.trans k⟩ }

/-- Actual stable classes of compact-support triples. -/
abbrev StableSupportTripleClass (X : Type*) [TopologicalSpace X] : Type _ :=
  Quotient (SupportBundleTriple.stableSetoid X)

/-- The stable class of a triple with its boundary germ. -/
def SupportBundleTriple.stableClass (a : SupportBundleTriple X) : StableSupportTripleClass X :=
  Quotient.mk _ a

/-- The stable quotient imposes exactly the stated stable germ relation. -/
theorem SupportBundleTriple.stableClass_eq_iff (a b : SupportBundleTriple X) :
    a.stableClass = b.stableClass ↔ a.IsStablyIsomorphic b := by
  /- Apply effectiveness of the setoid quotient. Its relation is the stated existential
  stabilization and exterior commuting square, with no homotopy added by definition. -/

  constructor
  · exact Quotient.exact
  · exact fun h ↦ @Quotient.sound _ (SupportBundleTriple.stableSetoid X) a b h

end AtiyahSinger.ComplexBundle
