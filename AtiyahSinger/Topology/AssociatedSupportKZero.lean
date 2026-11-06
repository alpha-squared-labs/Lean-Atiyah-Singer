/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedEquivariantMaps
public import AtiyahSinger.Topology.AssociatedSupportDescent
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Associated descent on the original equivariant support group

Public module ID: M1550.

The generator value is the ordinary compact-support class of the actual
associated triple. The existing arbitrary-universe support-class construction
uses its specified small-model isomorphisms; no replacement boundary or new
small-family functor is introduced. The same value respects the original
equivariant isomorphism, direct-sum and arbitrary-bundle identity relations.
Their existing universal property gives the actual additive descent map.

Sources: SG III.13, pp.251--253, and ASI I Section 2. This is the associated
compact-support operation appearing in that route, with a direct construction
valid for arbitrary topological G. Compact Hausdorff B and LCH Y ensure the
target compactification model exists and its descended controls are compact.
No compactness of G or P, invariant cutoff existence, global constant rank,
free-action equivalence, equivariant analytic index or Bott theorem is claimed.
The proofs below establish these relations and the exact generator equation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [CompactSpace B] [T2Space B] [LocallyCompactSpace Y] [T2Space Y]

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant

/-- The ordinary support class of exactly the descended original equivariant triple. -/
def associatedSupportClass (hP : IsPrincipalBundle G projection)
    (a : EquivariantSupportBundleTriple G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    CompactSupportKZero (AssociatedBundle G P Y) :=
  letI := associatedBundle_t2Space (Y := Y) hP
  letI := associatedBundle_locallyCompactSpace (Y := Y) hP
  (associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant).compactSupportClass

/-- Associated classes respect the three relations of the original equivariant presentation. -/
theorem associatedSupportClass_relations (hP : IsPrincipalBundle G projection) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    (∀ a b : EquivariantSupportBundleTriple G Y,
      a.IsIsomorphic b → associatedSupportClass hP a = associatedSupportClass hP b) ∧
    (∀ a b : EquivariantSupportBundleTriple G Y,
      associatedSupportClass hP (a.sum b) =
        associatedSupportClass hP a + associatedSupportClass hP b) ∧
    ∀ (E : FiniteBundle Y) (σ : EquivariantStructure G E.Fiber),
      associatedSupportClass hP (EquivariantSupportBundleTriple.identity E σ) = 0 := by
  /- Stage 1: take the common invariant compact control and the two actual
  equivariant global isomorphisms in the supplied IsIsomorphic witness.
  Descend those maps using associatedEquivariantIso. The original common
  control descends to a compact set containing both descended controls.
  On its exterior the representative formulas preserve the same commuting
  boundary square. The old support-class enlargement and conjugation laws,
  with the same resizing isomorphisms, give equality of the actual classes.
  Stage 2: the fiber map [p,(y,(v,w))] mapped to
  ([p,(y,v)],[p,(y,w)]) is a linear isomorphism from the descended sum to
  the sum of the descended bundles. Both factors use the same p and y.
  Representative changes act simultaneously, and principal/vector charts
  prove continuity both ways. The control is exactly the union of the two
  associated controls. Its boundary square is the original componentwise
  one; apply compactSupportClass_sum and invariance under these isomorphisms.
  Stage 3: an identity triple on any supplied equivariant finite bundle
  has empty control, whose associated image is empty. Its descended boundary
  is the restriction of the actual identity on the associated bundle.
  The ordinary global-isomorphism class is zero. No trivial representation
  stabilization, compact-group cutoff, or homotopy relation is substituted. -/
  classical
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let Z := AssociatedBundle G P Y
  let descend (a : EquivariantSupportBundleTriple G Y) :=
    associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
      a.2.isEquivariant
  -- A common original exterior square suffices for arbitrary-universe support classes.
  have classEq {E₁ F₁ E₂ F₂ : Z → Type _}
      [∀ z, AddCommGroup (E₁ z)] [∀ z, Module ℂ (E₁ z)]
      [∀ z, AddCommGroup (F₁ z)] [∀ z, Module ℂ (F₁ z)]
      [∀ z, AddCommGroup (E₂ z)] [∀ z, Module ℂ (E₂ z)]
      [∀ z, AddCommGroup (F₂ z)] [∀ z, Module ℂ (F₂ z)]
      [TopologicalSpace (TotalSpace Unit E₁)] [TopologicalSpace (TotalSpace Unit F₁)]
      [TopologicalSpace (TotalSpace Unit E₂)] [TopologicalSpace (TotalSpace Unit F₂)]
      [IsFiniteRank E₁] [IsFiniteRank F₁] [IsFiniteRank E₂] [IsFiniteRank F₂]
      (a : CompactSupportTriple E₁ F₁) (b : CompactSupportTriple E₂ F₂)
      (K : Set Z) (hK : IsCompact K) (ha : a.control ⊆ K) (hb : b.control ⊆ K)
      (u : Iso E₁ E₂) (v : Iso F₁ F₂)
      (hsquare : ∀ (z : (Kᶜ : Set Z)) (w : E₁ z),
        v.linearEquiv z ((a.enlarge K hK ha).boundary.linearEquiv z w) =
          (b.enlarge K hK hb).boundary.linearEquiv z (u.linearEquiv z w)) :
      a.compactSupportClass = b.compactSupportClass := by
    have heq : (a.enlarge K hK ha).congr u v = b.enlarge K hK hb := by
      change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
      congr 1
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro w
      change v.linearEquiv z ((a.enlarge K hK ha).boundary.linearEquiv z
        (u.symm.linearEquiv z w)) = (b.enlarge K hK hb).boundary.linearEquiv z w
      exact (hsquare z (u.symm.linearEquiv z w)).trans
        (congrArg ((b.enlarge K hK hb).boundary.linearEquiv z)
          ((u.linearEquiv z).apply_symm_apply w))
    calc
      a.compactSupportClass = (a.enlarge K hK ha).compactSupportClass :=
        (a.compactSupportClass_enlarge K hK ha).symm
      _ = ((a.enlarge K hK ha).congr u v).compactSupportClass :=
        ((a.enlarge K hK ha).compactSupportClass_congr u v).symm
      _ = (b.enlarge K hK hb).compactSupportClass := congrArg _ heq
      _ = b.compactSupportClass := b.compactSupportClass_enlarge K hK hb
  -- The original selected boundary formula also holds at any equal representative base.
  have boundary (a : EquivariantSupportBundleTriple G Y) (p : P)
      (y : (a.1.datum.controlᶜ : Set Y)) {z : Z}
      (hz : associatedBundleMk G P Y p y = z)
      (hout : z ∈ (descend a).controlᶜ) (w : a.1.source.Fiber y) :
      (descend a).boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP a.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hP a.2.targetAction p y hz
          (a.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction
      a.2.targetAction a.2.isEquivariant p y w
  -- The direct-sum comparison is built from the two original descended projections.
  have sumComparison (E F : Y → Type)
      [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
      [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
      [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
      [IsFiniteRank E] [IsFiniteRank F]
      (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
      let := sumTopology (E := E) (F := F)
      let := isFiniteRank_sum (E := E) (F := F)
      let := sumTopology (E := AssociatedEquivariantFiber hP σ)
        (F := AssociatedEquivariantFiber hP τ)
      let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP σ)
        (F := AssociatedEquivariantFiber hP τ)
      ∃ u : Iso (AssociatedEquivariantFiber hP (σ.sum τ))
          (AssociatedEquivariantFiber hP σ ×ᵇ AssociatedEquivariantFiber hP τ),
        ∀ (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z)
          (w : E y × F y),
          u.linearEquiv z (associatedEquivariantFiberMk hP (σ.sum τ) p y hz w) =
            (associatedEquivariantFiberMk hP σ p y hz w.1,
              associatedEquivariantFiberMk hP τ p y hz w.2) := by
    let := sumTopology (E := E) (F := F)
    let := isFiniteRank_sum (E := E) (F := F)
    let := sumTopology (E := AssociatedEquivariantFiber hP σ)
      (F := AssociatedEquivariantFiber hP τ)
    let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP σ)
      (F := AssociatedEquivariantFiber hP τ)
    let l := associatedEquivariantHom hP (σ.sum τ) σ
      (sumFst (E := E) (F := F)) (fun _ _ _ ↦ rfl)
    let r := associatedEquivariantHom hP (σ.sum τ) τ
      (sumSnd (E := E) (F := F)) (fun _ _ _ ↦ rfl)
    let a : Hom (AssociatedEquivariantFiber hP (σ.sum τ))
        (AssociatedEquivariantFiber hP σ ×ᵇ AssociatedEquivariantFiber hP τ) :=
      { linearMap z := (l.linearMap z).prod (r.linearMap z)
        continuous_total := continuous_induced_rng.mpr
          (l.continuous_total.prodMk r.continuous_total) }
    have hformula (p : P) (y : Y) {z : Z}
        (hz : associatedBundleMk G P Y p y = z) (w : E y × F y) :
        a.linearMap z (associatedEquivariantFiberMk hP (σ.sum τ) p y hz w) =
          (associatedEquivariantFiberMk hP σ p y hz w.1,
            associatedEquivariantFiberMk hP τ p y hz w.2) := by
      exact Prod.ext
        (associatedEquivariantHom_apply hP (σ.sum τ) σ
          (sumFst (E := E) (F := F)) (fun _ _ _ ↦ rfl) p y hz w)
        (associatedEquivariantHom_apply hP (σ.sum τ) τ
          (sumSnd (E := E) (F := F)) (fun _ _ _ ↦ rfl) p y hz w)
    have hbij (z : Z) : Function.Bijective (a.linearMap z) := by
      let p := (Quotient.out z).1
      let y := (Quotient.out z).2
      have hz : associatedBundleMk G P Y p y = z := Quotient.out_eq z
      have hsource := associatedEquivariantFiberMk_bijective hP (σ.sum τ) p y hz
      have hleft := associatedEquivariantFiberMk_bijective hP σ p y hz
      have hright := associatedEquivariantFiberMk_bijective hP τ p y hz
      constructor
      · intro v w hvw
        obtain ⟨v₀, rfl⟩ := hsource.2 v
        obtain ⟨w₀, rfl⟩ := hsource.2 w
        rw [hformula, hformula] at hvw
        exact congrArg (associatedEquivariantFiberMk hP (σ.sum τ) p y hz)
          (Prod.ext (hleft.1 (congrArg Prod.fst hvw))
            (hright.1 (congrArg Prod.snd hvw)))
      · rintro ⟨v, w⟩
        obtain ⟨v₀, rfl⟩ := hleft.2 v
        obtain ⟨w₀, rfl⟩ := hright.2 w
        exact ⟨associatedEquivariantFiberMk hP (σ.sum τ) p y hz (v₀, w₀),
          hformula p y hz (v₀, w₀)⟩
    exact ⟨a.toIso hbij, hformula⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Descend the same equivariant global square outside its original common control.
    intro a b hab
    obtain ⟨K, hK, hInv, ha, hb, u, v, hu, hv, hsquare⟩ := hab
    let da := descend a
    let db := descend b
    let L := associatedControl G P Y K
    have hL : IsCompact L := isCompact_associatedControl hP K hK hInv
    have hleft : da.control ⊆ L := by
      rintro z ⟨⟨p, y⟩, hy, rfl⟩
      exact ⟨(p, y), ⟨Set.mem_univ p, ha hy.2⟩, rfl⟩
    have hright : db.control ⊆ L := by
      rintro z ⟨⟨p, y⟩, hy, rfl⟩
      exact ⟨(p, y), ⟨Set.mem_univ p, hb hy.2⟩, rfl⟩
    let U := associatedEquivariantIso hP a.2.sourceAction b.2.sourceAction u hu
    let V := associatedEquivariantIso hP a.2.targetAction b.2.targetAction v hv
    change da.compactSupportClass = db.compactSupportClass
    refine classEq da db L hL hleft hright U V ?_
    intro z w
    let p := (Quotient.out z.val).1
    let y := (Quotient.out z.val).2
    have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
    have hy : y ∈ Kᶜ := by
      intro hy
      exact z.property (hz ▸ (associatedControl_mk_mem_iff K hInv p y).mpr hy)
    let ya : (a.1.datum.controlᶜ : Set Y) := ⟨y, fun h ↦ hy (ha h)⟩
    let yb : (b.1.datum.controlᶜ : Set Y) := ⟨y, fun h ↦ hy (hb h)⟩
    let za : (da.controlᶜ : Set Z) := ⟨z, fun h ↦ z.property (hleft h)⟩
    let zb : (db.controlᶜ : Set Z) := ⟨z, fun h ↦ z.property (hright h)⟩
    obtain ⟨w₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective hP a.2.sourceAction p y hz).2 w
    have hda := boundary a p ya hz za.property w₀
    have hdb := boundary b p yb hz zb.property (u.linearEquiv y w₀)
    have hU := associatedEquivariantHom_apply hP a.2.sourceAction b.2.sourceAction
      u.toHom hu p y hz w₀
    have hV := associatedEquivariantHom_apply hP a.2.targetAction b.2.targetAction
      v.toHom hv p y hz (a.1.datum.boundary.linearEquiv ya w₀)
    have hs := hsquare ⟨y, hy⟩ w₀
    rw [a.1.datum.enlarge_apply, b.1.datum.enlarge_apply] at hs
    rw [da.enlarge_apply, db.enlarge_apply]
    exact (congrArg (V.linearEquiv z) hda).trans
      (hV.trans ((congrArg (associatedEquivariantFiberMk hP b.2.targetAction p y hz)
        hs).trans (hdb.symm.trans
          (congrArg (db.boundary.linearEquiv zb) hU.symm))))
  · -- Descending a direct sum preserves its two ordered representative coordinates.
    intro a b
    let := sumTopology (E := a.1.source.Fiber) (F := b.1.source.Fiber)
    let := isFiniteRank_sum (E := a.1.source.Fiber) (F := b.1.source.Fiber)
    let := sumTopology (E := a.1.target.Fiber) (F := b.1.target.Fiber)
    let := isFiniteRank_sum (E := a.1.target.Fiber) (F := b.1.target.Fiber)
    let := sumTopology (E := AssociatedEquivariantFiber hP a.2.sourceAction)
      (F := AssociatedEquivariantFiber hP b.2.sourceAction)
    let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP a.2.sourceAction)
      (F := AssociatedEquivariantFiber hP b.2.sourceAction)
    let := sumTopology (E := AssociatedEquivariantFiber hP a.2.targetAction)
      (F := AssociatedEquivariantFiber hP b.2.targetAction)
    let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP a.2.targetAction)
      (F := AssociatedEquivariantFiber hP b.2.targetAction)
    obtain ⟨U, hU⟩ := sumComparison a.1.source.Fiber b.1.source.Fiber
      a.2.sourceAction b.2.sourceAction
    obtain ⟨V, hV⟩ := sumComparison a.1.target.Fiber b.1.target.Fiber
      a.2.targetAction b.2.targetAction
    let da := descend a
    let db := descend b
    let ds := descend (a.sum b)
    let L := ds.control
    have hright : (da.sum db).control ⊆ L := by
      rintro z (hz | hz)
      · obtain ⟨⟨p, y⟩, hy, rfl⟩ := hz
        exact ⟨(p, y), ⟨Set.mem_univ p, Or.inl hy.2⟩, rfl⟩
      · obtain ⟨⟨p, y⟩, hy, rfl⟩ := hz
        exact ⟨(p, y), ⟨Set.mem_univ p, Or.inr hy.2⟩, rfl⟩
    have hclass : ds.compactSupportClass = (da.sum db).compactSupportClass := by
      refine classEq ds (da.sum db) L ds.isCompact_control (fun _ h ↦ h) hright U V ?_
      intro z w
      let p := (Quotient.out z.val).1
      let y := (Quotient.out z.val).2
      have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
      have hy : y ∈ ((a.sum b).1.datum.controlᶜ : Set Y) := by
        intro hy
        exact z.property (hz ▸ (associatedControl_mk_mem_iff
          (a.sum b).1.datum.control (a.sum b).2.isEquivariant.invariant_control p y).mpr hy)
      let ys : ((a.sum b).1.datum.controlᶜ : Set Y) := ⟨y, hy⟩
      let ya : (a.1.datum.controlᶜ : Set Y) := ⟨y, fun h ↦ hy (Or.inl h)⟩
      let yb : (b.1.datum.controlᶜ : Set Y) := ⟨y, fun h ↦ hy (Or.inr h)⟩
      let zt : ((da.sum db).controlᶜ : Set Z) := ⟨z, fun h ↦ z.property (hright h)⟩
      let za : (da.controlᶜ : Set Z) := ⟨z, fun h ↦ zt.property (Or.inl h)⟩
      let zb : (db.controlᶜ : Set Z) := ⟨z, fun h ↦ zt.property (Or.inr h)⟩
      obtain ⟨w₀, rfl⟩ := (associatedEquivariantFiberMk_bijective hP
        (a.sum b).2.sourceAction p y hz).2 w
      have hds := boundary (a.sum b) p ys hz z.property w₀
      have hsum := RelativeTriple.sum_apply
        (a.1.datum.enlarge _ (a.1.datum.isCompact_control.union b.1.datum.isCompact_control)
          Set.subset_union_left).boundary
        (b.1.datum.enlarge _ (a.1.datum.isCompact_control.union b.1.datum.isCompact_control)
          Set.subset_union_right).boundary ys w₀
      have horiginal := hsum.trans (congrArg₂ Prod.mk
        (a.1.datum.enlarge_apply _ _ Set.subset_union_left ys w₀.1)
        (b.1.datum.enlarge_apply _ _ Set.subset_union_right ys w₀.2))
      have htarget := RelativeTriple.sum_apply
        (da.enlarge _ (da.isCompact_control.union db.isCompact_control)
          Set.subset_union_left).boundary
        (db.enlarge _ (da.isCompact_control.union db.isCompact_control)
          Set.subset_union_right).boundary zt
        (associatedEquivariantFiberMk hP a.2.sourceAction p y hz w₀.1,
          associatedEquivariantFiberMk hP b.2.sourceAction p y hz w₀.2)
      have htarget' := htarget.trans (congrArg₂ Prod.mk
        (da.enlarge_apply _ _ Set.subset_union_left zt _)
        (db.enlarge_apply _ _ Set.subset_union_right zt _))
      have hda := boundary a p ya hz za.property w₀.1
      have hdb := boundary b p yb hz zb.property w₀.2
      have ht := htarget'.trans (congrArg₂ Prod.mk hda hdb)
      rw [ds.enlarge_apply L ds.isCompact_control (Set.Subset.refl _) z _,
        (da.sum db).enlarge_apply L ds.isCompact_control hright z _]
      exact (congrArg (V.linearEquiv z) hds).trans
        ((hV p y hz ((a.sum b).1.datum.boundary.linearEquiv ys w₀)).trans
          ((congrArg (fun v ↦
            (associatedEquivariantFiberMk hP a.2.targetAction p y hz v.1,
              associatedEquivariantFiberMk hP b.2.targetAction p y hz v.2)) horiginal).trans
            (ht.symm.trans
            (congrArg ((da.sum db).boundary.linearEquiv zt) (hU p y hz w₀).symm))))
    exact hclass.trans (da.compactSupportClass_sum db)
  · -- The original identity descends to the actual associated identity with empty control.
    intro E σ
    let a := EquivariantSupportBundleTriple.identity E σ
    let d := descend a
    let e := Iso.refl (AssociatedEquivariantFiber hP σ)
    let b := CompactSupportTriple.ofIso e
    have hleft : d.control ⊆ (∅ : Set Z) := by
      rintro z ⟨⟨p, y⟩, hy, rfl⟩
      exact False.elim hy.2
    have hclass : d.compactSupportClass = b.compactSupportClass := by
      refine classEq d b ∅ isCompact_empty hleft (fun _ h ↦ h) e e ?_
      intro z w
      let p := (Quotient.out z.val).1
      let y := (Quotient.out z.val).2
      have hz : associatedBundleMk G P Y p y = z.val := Quotient.out_eq z.val
      let ya : (a.1.datum.controlᶜ : Set Y) := ⟨y, fun h ↦ h⟩
      let zd : (d.controlᶜ : Set Z) := ⟨z, fun h ↦ z.property (hleft h)⟩
      obtain ⟨w₀, rfl⟩ := (associatedEquivariantFiberMk_bijective hP σ p y hz).2 w
      rw [d.enlarge_apply ∅ isCompact_empty hleft,
        b.enlarge_apply ∅ isCompact_empty (Set.Subset.refl _)]
      exact boundary a p ya hz zd.property w₀
    exact hclass.trans (CompactSupportTriple.compactSupportClass_ofIso e)

/-- The actual additive descent map on the existing equivariant support presentation. -/
def associatedSupportKZero (hP : IsPrincipalBundle G projection) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    EquivariantSupportTripleKZero G Y →+
      CompactSupportKZero (AssociatedBundle G P Y) :=
  letI := associatedBundle_t2Space (Y := Y) hP
  letI := associatedBundle_locallyCompactSpace (Y := Y) hP
  (equivariantSupportTripleKZero_universal_property (associatedSupportClass hP)
    (associatedSupportClass_relations hP).1
    (associatedSupportClass_relations hP).2.1
    (associatedSupportClass_relations hP).2.2).choose

/-- The selected homomorphism sends each original generator to its exact associated class. -/
theorem associatedSupportKZero_class (hP : IsPrincipalBundle G projection)
    (a : EquivariantSupportBundleTriple G Y) :
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    associatedSupportKZero hP a.kZeroClass = associatedSupportClass hP a := by
  /- Read the generator clause from the same universal-property witness
  used to define associatedSupportKZero. The value is the specified original
  quotient triple's class, including its boundary and its original action.
  This does not identify an abstract free-action K group by a separate choice. -/
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  exact (equivariantSupportTripleKZero_universal_property (associatedSupportClass hP)
    (associatedSupportClass_relations hP).1
    (associatedSupportClass_relations hP).2.1
    (associatedSupportClass_relations hP).2.2).choose_spec.1 a

end AtiyahSinger
