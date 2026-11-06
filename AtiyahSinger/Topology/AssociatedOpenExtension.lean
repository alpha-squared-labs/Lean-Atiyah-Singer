/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSupportProduct
public import AtiyahSinger.Topology.EquivariantOpenExtension

/-!
# Open extension through the original associated quotient

Public module ID: M1543.

An equivariant open embedding induces an open embedding of associated spaces.
For a compact principal base, descent of the original equivariant supported
class commutes with extension through this same open map. The comparison uses
the original equivariant extension and both associated pullback bundle maps.
The compact control and its exterior boundary are retained before passing to
the support group. No properness of the open embedding is asserted.

Sources: associated bundle local trivializations and compact-support excision,
as used in SG Appendix C.1 and III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

omit [TopologicalSpace G] [IsTopologicalGroup G] [ContinuousSMul Gᵐᵒᵖ P]
  [ContinuousSMul G X] [ContinuousSMul G Y] in
/-- An equivariant open embedding remains an open embedding on the original associated spaces. -/
theorem isOpenEmbedding_associatedBundleMap
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (associatedBundleMap (P := P) f heq) := by
  let q := associatedBundleMap (P := P) f heq
  have hinj : Function.Injective q := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h a =>
      induction w using Quotient.inductionOn with
      | h b =>
        obtain ⟨g, hg⟩ := Quotient.exact h
        have hp : b.1 = MulOpposite.op g • a.1 := congrArg Prod.fst hg
        have hv : f b.2 = g⁻¹ • f a.2 := congrArg Prod.snd hg
        exact Quotient.sound ⟨g, Prod.ext hp (hf.injective (hv.trans (heq g⁻¹ a.2).symm))⟩
  have hopen : IsOpenMap q := by
    intro U hU
    let jX : P × X → AssociatedBundle G P X := Quotient.mk (associatedBundleSetoid G P X)
    let jY : P × Y → AssociatedBundle G P Y := Quotient.mk (associatedBundleSetoid G P Y)
    have himage : jY ⁻¹' (q '' U) = (Prod.map id f) '' (jX ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨z, hz, he⟩
        induction z using Quotient.inductionOn with
        | h a =>
          obtain ⟨g, hg⟩ := Quotient.exact he
          refine ⟨(MulOpposite.op g • a.1, g⁻¹ • a.2), ?_, ?_⟩
          · have hclass : jX (MulOpposite.op g • a.1, g⁻¹ • a.2) = jX a := by
              apply Eq.symm
              exact Quotient.sound
                (show (associatedBundleSetoid G P X).r a
                  (MulOpposite.op g • a.1, g⁻¹ • a.2) from ⟨g, rfl⟩)
            change jX (MulOpposite.op g • a.1, g⁻¹ • a.2) ∈ U
            rw [hclass]
            exact hz
          · apply Prod.ext
            · exact (congrArg Prod.fst hg).symm
            · exact (heq g⁻¹ a.2).trans (congrArg Prod.snd hg).symm
      · rintro ⟨z, hz, rfl⟩
        exact ⟨jX z, hz, rfl⟩
    change IsOpen (jY ⁻¹' (q '' U))
    rw [himage]
    exact (IsOpenEmbedding.id.prodMap hf).isOpenMap _
      (hU.preimage (show Continuous jX from continuous_quot_mk))
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap q.continuous hinj hopen

variable [CompactSpace G] [T2Space G] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant isFiniteRank_pullback

set_option maxHeartbeats 1000000 in
-- Compare the same two associated parity bundles and their native pulled boundary maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Associated descent commutes with the original equivariant compact-support open extension. -/
theorem associatedSupportKZero_openPushforward (hP : IsPrincipalBundle G projection)
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hf : IsOpenEmbedding f) (a : EquivariantSupportTripleKZero G X) :
    letI := associatedBundle_t2Space (Y := X) hP
    letI := associatedBundle_locallyCompactSpace (Y := X) hP
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    associatedSupportKZero hP (equivariantSupportTripleKZeroOpenPushforward f hf heq a) =
      compactSupportKZeroOpenPushforward (associatedBundleMap (P := P) f heq)
        (isOpenEmbedding_associatedBundleMap f heq hf) (associatedSupportKZero hP a) := by
  classical
  let := associatedBundle_t2Space (Y := X) hP
  let := associatedBundle_locallyCompactSpace (Y := X) hP
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  -- Obtain one actual equivariant extension, then retain it for both associated boundaries.
  obtain ⟨a₀, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨b, hc, hstable⟩ := a₀.exists_openExtension f hf heq
  have ha := EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic _ _ hstable
  rw [← ha, equivariantSupportTripleKZeroOpenPushforward_class,
    associatedSupportKZero_class, associatedSupportKZero_class]
  let c := b.openRestrict f hf heq hc
  let q := associatedBundleMap (P := P) f heq
  have hq : IsOpenEmbedding q := isOpenEmbedding_associatedBundleMap f heq hf
  let D := associatedSupportTriple hP b.1.datum b.2.sourceAction b.2.targetAction b.2.isEquivariant
  let A := associatedSupportTriple hP c.1.datum c.2.sourceAction c.2.targetAction c.2.isEquivariant
  obtain ⟨U, hU⟩ := exists_associatedEquivariantFiber_pullback_iso hP f heq
    b.1.source.Fiber b.2.sourceAction
  obtain ⟨V, hV⟩ := exists_associatedEquivariantFiber_pullback_iso hP f heq
    b.1.target.Fiber b.2.targetAction
  have hcontrol : D.control ⊆ q '' A.control := by
    intro z hz
    induction z using Quotient.inductionOn with
    | h w =>
      have hw : w.2 ∈ b.1.datum.control :=
        (associatedControl_mk_mem_iff b.1.datum.control
          b.2.isEquivariant.invariant_control w.1 w.2).mp hz
      obtain ⟨x, hx⟩ := hc hw
      refine ⟨associatedBundleMk G P X w.1 x, ?_, ?_⟩
      · apply (associatedControl_mk_mem_iff c.1.datum.control
          c.2.isEquivariant.invariant_control w.1 x).mpr
        change f x ∈ b.1.datum.control
        exact hx ▸ hw
      · change associatedBundleMk G P Y w.1 (f x) = associatedBundleMk G P Y w.1 w.2
        rw [hx]
  -- At every original representative, both routes act by the same boundary at f(x).
  have boundaryX (p : P) (x : (c.1.datum.controlᶜ : Set X))
      {z : AssociatedBundle G P X} (hz : associatedBundleMk G P X p x = z)
      (hout : z ∈ A.controlᶜ) (w : c.1.source.Fiber x) :
      A.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP c.2.sourceAction p x hz w) =
        associatedEquivariantFiberMk hP c.2.targetAction p x hz
          (c.1.datum.boundary.linearEquiv x w) := by
    cases hz
    exact associatedSupportBoundary_apply hP c.1.datum c.2.sourceAction
      c.2.targetAction c.2.isEquivariant p x w
  have boundaryY (p : P) (y : (b.1.datum.controlᶜ : Set Y))
      {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z)
      (hout : z ∈ D.controlᶜ) (w : b.1.source.Fiber y) :
      D.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP b.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hP b.2.targetAction p y hz
          (b.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hP b.1.datum b.2.sourceAction
      b.2.targetAction b.2.isEquivariant p y w
  change D.compactSupportClass = compactSupportKZeroOpenPushforward q hq A.compactSupportClass
  apply A.compactSupportClass_eq_openPushforward D q hq hcontrol U V
  intro z hz hqz w
  let p := (Quotient.out z).1
  let x := (Quotient.out z).2
  have hxz : associatedBundleMk G P X p x = z := Quotient.out_eq z
  have hx : x ∈ c.1.datum.controlᶜ := by
    intro hx
    exact hz (hxz ▸ (associatedControl_mk_mem_iff c.1.datum.control
      c.2.isEquivariant.invariant_control p x).mpr hx)
  let xc : (c.1.datum.controlᶜ : Set X) := ⟨x, hx⟩
  let yb : (b.1.datum.controlᶜ : Set Y) := ⟨f x, hx⟩
  obtain ⟨w₀, rfl⟩ :=
    (associatedEquivariantFiberMk_bijective hP c.2.sourceAction p x hxz).2 w
  have hA := boundaryX p xc hxz hz w₀
  have hD := boundaryY p yb (congrArg q hxz) hqz w₀
  have hpull := RelativeTriple.pullback_apply b.1.datum.boundary f xc w₀
  exact (congrArg (V.linearEquiv z) hA).trans
    ((hV p x hxz (c.1.datum.boundary.linearEquiv xc w₀)).trans
      ((congrArg (associatedEquivariantFiberMk hP b.2.targetAction p (f x)
        (congrArg q hxz)) hpull).trans
          (hD.symm.trans (congrArg (D.boundary.linearEquiv ⟨q z, hqz⟩)
            (hU p x hxz w₀).symm))))

end AtiyahSinger
