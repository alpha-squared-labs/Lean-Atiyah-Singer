/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleHomotopy

/-!
# The group presented by triples invertible at infinity

Public module ID: M2195.

D07/K02. The actual free abelian quotient uses isomorphism of boundary germs,
direct sum and identity relations. Locally compact Hausdorff hypotheses enter
the inverse and stable-class comparison through the spatial cutoff lemma.
Sources: SG I.9.23–9.26; KA II.2.14–2.29, with the stated cutoff supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X]

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial


/-- The explicit isomorphism, sum and identity relations at infinity. -/
def supportTripleKZeroRelations (X : Type*) [TopologicalSpace X] :
    AddSubgroup (FreeAbelianGroup (SupportBundleTriple X)) :=
  AddSubgroup.closure
    ({z | ∃ a b : SupportBundleTriple X, a.IsIsomorphic b ∧
      z = FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ a b : SupportBundleTriple X,
      z = FreeAbelianGroup.of (a.sum b) - FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ E : FiniteBundle X, z = FreeAbelianGroup.of (SupportBundleTriple.identity E)})

/-- The abelian group with the three explicit geometric relations. -/
abbrev SupportTripleKZero (X : Type*) [TopologicalSpace X] : Type _ :=
  FreeAbelianGroup (SupportBundleTriple X) ⧸ supportTripleKZeroRelations X

/-- The quotient image of the actual triple generator. -/
def SupportBundleTriple.kZeroClass (a : SupportBundleTriple X) : SupportTripleKZero X :=
  QuotientAddGroup.mk' (supportTripleKZeroRelations X) (FreeAbelianGroup.of a)

/-- Isomorphism at infinity preserves the group class. -/
theorem SupportBundleTriple.kZeroClass_eq_of_isIsomorphic (a b : SupportBundleTriple X)
    (h : a.IsIsomorphic b) : a.kZeroClass = b.kZeroClass := by
  /- The difference of these generators is an explicit isomorphism relation. Its quotient image
  is zero. -/

  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inl ⟨a, b, h, rfl⟩)

/-- Direct sum is addition in the presented group. -/
theorem SupportBundleTriple.kZeroClass_sum (a b : SupportBundleTriple X) :
    (a.sum b).kZeroClass = a.kZeroClass + b.kZeroClass := by
  /- The sum relation identifies the generator of the actual fiber sum with the sum of the two
  generators. -/

  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) _ -
    ((QuotientAddGroup.mk' (supportTripleKZeroRelations X)) _ +
      (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) _) = 0
  rw [← map_add, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inr ⟨a, b, by abel⟩)

/-- Every identity triple represents zero. -/
theorem SupportBundleTriple.kZeroClass_identity (E : FiniteBundle X) :
    (SupportBundleTriple.identity E).kZeroClass = 0 := by
  /- The generator of each identity triple belongs to the defining relation subgroup. -/
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inr ⟨E, rfl⟩

/-- Identity stabilization does not alter the class. -/
theorem SupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic (a b : SupportBundleTriple X)
    (h : a.IsStablyIsomorphic b) : a.kZeroClass = b.kZeroClass := by
  /- Apply isomorphism invariance to the stabilized triples, expand their direct sums, and
  remove the identity classes. -/
  obtain ⟨E, F, hEF⟩ := h
  -- Both specified identity stabilizers have zero class.
  have heq := SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _ hEF
  simpa only [SupportBundleTriple.kZeroClass_sum, SupportBundleTriple.kZeroClass_identity,
    add_zero] using heq

/-- Enlarging compact control preserves the same boundary germ class. -/
theorem SupportBundleTriple.kZeroClass_enlarge (a : SupportBundleTriple X)
    (K : Set X) (hK : IsCompact K) (h : a.datum.control ⊆ K) :
    (a.enlarge K hK h).kZeroClass = a.kZeroClass := by
  /- The enlarged and original triples are isomorphic using identity global maps and the
  enlarged control. Apply isomorphism invariance. -/
  exact ((a.kZeroClass_eq_of_isIsomorphic (a.enlarge K hK h))
    (a.isIsomorphic_enlarge K hK h)).symm

/-- An additive map is determined by values respecting the three geometric relations. -/
theorem supportTripleKZero_universal_property (X : Type*) [TopologicalSpace X]
    {G : Type*} [AddCommGroup G] (v : SupportBundleTriple X → G)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (hz : ∀ E, v (SupportBundleTriple.identity E) = 0) :
    ∃! f : SupportTripleKZero X →+ G, ∀ a, f a.kZeroClass = v a := by
  /- Extend v to the free abelian group. The assumptions annihilate all three sets of relation
  generators, hence their subgroup. Descend to the quotient; uniqueness follows because its
  generators span. -/

  let f : FreeAbelianGroup (SupportBundleTriple X) →+ G := FreeAbelianGroup.lift v
  have hrelations : supportTripleKZeroRelations X ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ((⟨a, b, hab, rfl⟩ | ⟨a, b, rfl⟩) | ⟨E, rfl⟩)
    · change f (_ - _) = 0
      simp [f, hi a b hab]
    · change f (_ - _ - _) = 0
      simp [f, hs a b]
    · change f (FreeAbelianGroup.of (SupportBundleTriple.identity E)) = 0
      exact (FreeAbelianGroup.lift_apply_of v _).trans (hz E)
  let φ : SupportTripleKZero X →+ G :=
    QuotientAddGroup.lift (supportTripleKZeroRelations X) f hrelations
  have hφ (a : SupportBundleTriple X) : φ a.kZeroClass = v a :=
    FreeAbelianGroup.lift_apply_of v a
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  -- Equality on the same generators determines the descended homomorphism.
  have hcomp : ψ.comp (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) =
      φ.comp (QuotientAddGroup.mk' (supportTripleKZeroRelations X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    exact (hψ a).trans (hφ a).symm
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (supportTripleKZeroRelations X) z
  exact DFunLike.congr_fun hcomp w

/-- Stable classes map to the actual quotient generators. -/
def stableSupportTripleClassToKZero (X : Type*) [TopologicalSpace X] :
    StableSupportTripleClass X → SupportTripleKZero X :=
  Quotient.lift SupportBundleTriple.kZeroClass
    (fun a b h ↦ SupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic a b h)

variable [hL : LocallyCompactSpace X] [hT : T2Space X]
include hL hT

/-- Reversing a triple represents its additive inverse. -/
theorem SupportBundleTriple.kZeroClass_inverse (a : SupportBundleTriple X) :
    a.inverse.kZeroClass = -a.kZeroClass := by
  /- The sum with its inverse is isomorphic at infinity to an identity triple by the elementary
  matrix path and spatial cutoff. Its class is zero, so the two classes are additive
  inverses. -/
  have heq := SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _
    a.isIsomorphic_sum_inverse
  rw [SupportBundleTriple.kZeroClass_sum, SupportBundleTriple.kZeroClass_identity] at heq
  exact eq_neg_of_add_eq_zero_right heq

/-- Every class is represented by a single support triple. -/
theorem supportBundleTriple_kZeroClass_surjective :
    Function.Surjective (SupportBundleTriple.kZeroClass (X := X)) := by
  /- Write a representative as a finite signed sum. Replace negative terms by inverse triples
  and combine terms by direct sum. The empty sum is the identity on the zero-rank bundle. -/
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (supportTripleKZeroRelations X) z
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
      refine ⟨SupportBundleTriple.identity (FiniteBundle.trivial X 0), ?_⟩
      exact (SupportBundleTriple.kZeroClass_identity _).trans (map_zero _).symm
  | of a => exact ⟨a, rfl⟩
  | neg a _ =>
      exact ⟨a.inverse, a.kZeroClass_inverse.trans (map_neg _ _).symm⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a.sum b, ?_⟩
      rw [SupportBundleTriple.kZeroClass_sum, ha, hb, map_add]

/-- The group presentation makes exactly the stable identifications. -/
theorem SupportBundleTriple.kZeroClass_eq_iff_stable (a b : SupportBundleTriple X) :
    a.kZeroClass = b.kZeroClass ↔ a.IsStablyIsomorphic b := by
  /- Stable classes form a commutative monoid by direct sum. The cutoff inverse lemma makes it
  an abelian group. Its universal property agrees with the three defining relations, so
  passage to the group adds no further identifications. -/
  classical
  -- Read each direct sum on the same chosen exterior, with its original boundary values.
  have hsum (a b : SupportBundleTriple X) (K : Set X) (hK : IsCompact K)
      (ha : a.datum.control ⊆ K) (hb : b.datum.control ⊆ K)
      (x : (Kᶜ : Set X)) (v : (a.source.sum b.source).Fiber x) :
      ((a.sum b).datum.enlarge K hK (Set.union_subset ha hb)).boundary.linearEquiv x v =
        ((a.datum.enlarge K hK ha).boundary.linearEquiv x v.1,
          (b.datum.enlarge K hK hb).boundary.linearEquiv x v.2) := by
    let L := a.datum.control ∪ b.datum.control
    have hL : IsCompact L := a.datum.isCompact_control.union b.datum.isCompact_control
    let y : (Lᶜ : Set X) := ⟨x, fun hx ↦ x.property ((Set.union_subset ha hb) hx)⟩
    have ho := (a.datum.sum b.datum).enlarge_apply K hK (Set.union_subset ha hb) x v
    have hs := RelativeTriple.sum_apply
      (a.datum.enlarge L hL Set.subset_union_left).boundary
      (b.datum.enlarge L hL Set.subset_union_right).boundary y v
    have hA := (a.datum.enlarge_apply L hL Set.subset_union_left y v.1).trans
      (a.datum.enlarge_apply K hK ha x v.1).symm
    have hB := (b.datum.enlarge_apply L hL Set.subset_union_right y v.2).trans
      (b.datum.enlarge_apply K hK hb x v.2).symm
    exact ho.trans (hs.trans (Prod.ext hA hB))
  let Q := StableSupportTripleClass X
  let Z := FiniteBundle.trivial X 0
  let : Zero Q := ⟨(SupportBundleTriple.identity Z).stableClass⟩
  let : Add Q := ⟨fun x y ↦ Quotient.liftOn₂ x y
    (fun a b ↦ (a.sum b).stableClass)
    (fun a b c d hac hbd ↦ ((a.sum b).stableClass_eq_iff (c.sum d)).mpr (hac.sum hbd))⟩
  have hadd (a b : SupportBundleTriple X) :
      (a.stableClass : Q) + b.stableClass = (a.sum b).stableClass := rfl
  have hiso (a b : SupportBundleTriple X) (h : a.IsIsomorphic b) :
      a.stableClass = b.stableClass :=
    (a.stableClass_eq_iff b).mpr (a.isStablyIsomorphic_of_isIsomorphic b h)
  -- Identity triples agree after swapping the two identity stabilizers.
  have hzero (E : FiniteBundle X) : (SupportBundleTriple.identity E).stableClass = (0 : Q) := by
    apply ((SupportBundleTriple.identity E).stableClass_eq_iff
      (SupportBundleTriple.identity Z)).mpr
    refine ⟨Z, E, ∅, isCompact_empty,
      Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _),
      Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _), sumCommIso, sumCommIso, ?_⟩
    intro x v
    have hl := hsum (SupportBundleTriple.identity E) (SupportBundleTriple.identity Z)
      ∅ isCompact_empty (Set.Subset.refl _) (Set.Subset.refl _) x v
    have hr := hsum (SupportBundleTriple.identity Z) (SupportBundleTriple.identity E)
      ∅ isCompact_empty (Set.Subset.refl _) (Set.Subset.refl _) x
      ((sumCommIso (E := E.Fiber) (F := Z.Fiber)).linearEquiv x v)
    exact (congrArg ((sumCommIso (E := E.Fiber) (F := Z.Fiber)).linearEquiv x) hl).trans hr.symm
  have hcomm (x y : Q) : x + y = y + x := by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        apply hiso
        let K := a.datum.control ∪ b.datum.control
        have hK : IsCompact K := a.datum.isCompact_control.union b.datum.isCompact_control
        let u : Iso (a.source.sum b.source).Fiber (b.source.sum a.source).Fiber := sumCommIso
        let v : Iso (a.target.sum b.target).Fiber (b.target.sum a.target).Fiber := sumCommIso
        refine ⟨K, hK, Set.union_subset Set.subset_union_left Set.subset_union_right,
          Set.union_subset Set.subset_union_right Set.subset_union_left, u, v, ?_⟩
        intro x q
        have hl := hsum a b K hK Set.subset_union_left Set.subset_union_right x q
        have hr := hsum b a K hK Set.subset_union_right Set.subset_union_left x
          (u.linearEquiv x q)
        exact (congrArg (v.linearEquiv x) hl).trans hr.symm
  have hassoc (x y z : Q) : x + y + z = x + (y + z) := by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        induction z using Quotient.inductionOn with
        | _ c =>
          apply hiso
          let K := (a.datum.control ∪ b.datum.control) ∪ c.datum.control
          have hK : IsCompact K :=
            (a.datum.isCompact_control.union b.datum.isCompact_control).union
              c.datum.isCompact_control
          have ha : a.datum.control ⊆ K := fun x hx ↦ Or.inl (Or.inl hx)
          have hb : b.datum.control ⊆ K := fun x hx ↦ Or.inl (Or.inr hx)
          have hc : c.datum.control ⊆ K := fun x hx ↦ Or.inr hx
          have hab : (a.sum b).datum.control ⊆ K := Set.union_subset ha hb
          have hbc : (b.sum c).datum.control ⊆ K := Set.union_subset hb hc
          let u := FiniteBundle.sumAssocIso a.source b.source c.source
          let v := FiniteBundle.sumAssocIso a.target b.target c.target
          refine ⟨K, hK, Set.union_subset hab hc, Set.union_subset ha hbc, u, v, ?_⟩
          intro x q
          let α := (a.datum.enlarge K hK ha).boundary.linearEquiv x
          let β := (b.datum.enlarge K hK hb).boundary.linearEquiv x
          let γ := (c.datum.enlarge K hK hc).boundary.linearEquiv x
          have hl := hsum (a.sum b) c K hK hab hc x q
          have hlab := hsum a b K hK ha hb x q.1
          have hleft := hl.trans
            (congrArg (fun w : (a.target.sum b.target).Fiber x ↦ (w, γ q.2)) hlab)
          have hu := FiniteBundle.sumAssocIso_apply a.source b.source c.source x q
          have hr := hsum a (b.sum c) K hK ha hbc x (q.1.1, q.1.2, q.2)
          have hrbc := hsum b c K hK hb hc x (q.1.2, q.2)
          have hright := (congrArg (fun w ↦
            ((a.sum (b.sum c)).datum.enlarge K hK (Set.union_subset ha hbc)).boundary.linearEquiv
              x w) hu).trans (hr.trans (congrArg
                (fun w : (b.target.sum c.target).Fiber x ↦ (α q.1.1, w)) hrbc))
          have hv := FiniteBundle.sumAssocIso_apply a.target b.target c.target x
            ((α q.1.1, β q.1.2), γ q.2)
          exact (congrArg (v.linearEquiv x) hleft).trans (hv.trans hright.symm)
  have hright (x : Q) : x + 0 = x := by
    induction x using Quotient.inductionOn with
    | _ a =>
      apply hiso
      obtain ⟨u, hu⟩ := FiniteBundle.exists_sum_zero_iso a.source
      obtain ⟨v, hv⟩ := FiniteBundle.exists_sum_zero_iso a.target
      let K := a.datum.control
      have hK : IsCompact K := a.datum.isCompact_control
      have ha : a.datum.control ⊆ K := Set.Subset.refl _
      have hZ : (SupportBundleTriple.identity Z).datum.control ⊆ K := Set.empty_subset _
      refine ⟨K, hK, Set.union_subset ha hZ, ha, u, v, ?_⟩
      intro x q
      let α := (a.datum.enlarge K hK ha).boundary.linearEquiv x
      have hl := hsum a (SupportBundleTriple.identity Z) K hK ha hZ x q
      exact (congrArg (v.linearEquiv x) hl).trans
        ((hv x _).trans (congrArg α (hu x q)).symm)
  -- These actual squares give the monoid laws on the original stable quotient.
  let : AddCommMonoid Q :=
    { add_assoc := hassoc
      zero_add := fun x ↦ (hcomm 0 x).trans (hright x)
      add_zero := hright
      add_comm := hcomm
      nsmul := nsmulRec }
  have hinverse (x : Q) : ∃ y : Q, y + x = 0 := by
    induction x using Quotient.inductionOn with
    | _ a =>
      refine ⟨a.inverse.stableClass, ?_⟩
      change a.inverse.stableClass + a.stableClass = (0 : Q)
      rw [hcomm, hadd]
      exact (hiso _ _ a.isIsomorphic_sum_inverse).trans (hzero _)
  -- Choose inverses only after proving their existence in this same stable quotient.
  let : Neg Q := ⟨fun x ↦ (hinverse x).choose⟩
  let : AddCommGroup Q :=
    { ‹AddCommMonoid Q›, ‹Neg Q› with
      neg_add_cancel := fun x ↦ (hinverse x).choose_spec
      zsmul := zsmulRec }
  obtain ⟨φ, hφ, _⟩ := supportTripleKZero_universal_property X
    (fun a ↦ (a.stableClass : Q)) hiso (fun a b ↦ (hadd a b).symm) hzero
  constructor
  · intro h
    apply (a.stableClass_eq_iff b).mp
    exact (hφ a).symm.trans ((congrArg φ h).trans (hφ b))
  · exact a.kZeroClass_eq_of_isStablyIsomorphic b

/-- Vanishing means that a stabilized germ extends to a global isomorphism. -/
theorem SupportBundleTriple.kZeroClass_eq_zero_iff (a : SupportBundleTriple X) :
    a.kZeroClass = 0 ↔ ∃ G : FiniteBundle X,
      ∃ L : Set X, ∃ hL : IsCompact L, ∃ h : a.datum.control ⊆ L,
        ∃ e : Iso (a.source.sum G).Fiber (a.target.sum G).Fiber,
          e.restrict Lᶜ = (a.datum.enlarge L hL h).boundary.stabilize G.Fiber := by
  /- A stable isomorphism to an identity triple supplies two global isomorphisms whose
  composite extends the stabilized boundary on the common exterior. Conversely an extension
  identifies the stabilized triple with an identity triple outside that compact set. No
  global complement is needed. -/
  -- Compare stabilization before and after enlargement on the same chosen exterior.
  have hboundary (a : SupportBundleTriple X) (G : FiniteBundle X)
      (L : Set X) (hL : IsCompact L) (h : a.datum.control ⊆ L)
      (x : (Lᶜ : Set X)) (w : (a.source.sum G).Fiber x) :
      ((a.sum (SupportBundleTriple.identity G)).datum.enlarge L hL
        (Set.union_subset h (Set.empty_subset _))).boundary.linearEquiv x w =
        ((a.datum.enlarge L hL h).boundary.stabilize G.Fiber).linearEquiv x w := by
    let i := SupportBundleTriple.identity G
    let K := a.datum.control ∪ i.datum.control
    have hK : IsCompact K := a.datum.isCompact_control.union i.datum.isCompact_control
    have hKL : K ⊆ L := Set.union_subset h (Set.empty_subset _)
    let y : (Kᶜ : Set X) := ⟨x, fun hx ↦ x.property (hKL hx)⟩
    have ho := (a.datum.sum i.datum).enlarge_apply L hL hKL x w
    have hs := RelativeTriple.sum_apply
      (a.datum.enlarge K hK Set.subset_union_left).boundary
      (i.datum.enlarge K hK Set.subset_union_right).boundary y w
    have hA := (a.datum.enlarge_apply K hK Set.subset_union_left y w.1).trans
      (a.datum.enlarge_apply L hL h x w.1).symm
    have hG := i.datum.enlarge_apply K hK Set.subset_union_right y w.2
    have ht := RelativeTriple.sum_apply (a.datum.enlarge L hL h).boundary
      (RelativeTriple.identity G.Fiber Lᶜ) x w
    exact ho.trans ((hs.trans (Prod.ext hA hG)).trans ht.symm)
  constructor
  · intro ha
    let Z := FiniteBundle.trivial X 0
    have haz : a.kZeroClass = (SupportBundleTriple.identity Z).kZeroClass :=
      ha.trans (SupportBundleTriple.kZeroClass_identity Z).symm
    obtain ⟨G, H, L, hL, haL, hZL, u, v, huv⟩ :=
      (a.kZeroClass_eq_iff_stable (SupportBundleTriple.identity Z)).mp haz
    have h : a.datum.control ⊆ L := fun x hx ↦ haL (Or.inl hx)
    -- Compose the two original global comparisons, retaining exactly their stabilizer G.
    refine ⟨G, L, hL, h, u.trans v.symm, ?_⟩
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro w
    apply (v.linearEquiv x).injective
    change v.linearEquiv x ((v.linearEquiv x).symm (u.linearEquiv x w)) =
      v.linearEquiv x (((a.datum.enlarge L hL h).boundary.stabilize G.Fiber).linearEquiv x w)
    have hA := hboundary a G L hL h x w
    have hI := hboundary (SupportBundleTriple.identity Z) H L hL (Set.empty_subset _) x
      (u.linearEquiv x w)
    have ht := RelativeTriple.sum_apply
      ((SupportBundleTriple.identity Z).datum.enlarge L hL (Set.empty_subset _)).boundary
      (RelativeTriple.identity H.Fiber Lᶜ) x (u.linearEquiv x w)
    have hz := (SupportBundleTriple.identity Z).datum.enlarge_apply L hL (Set.empty_subset _)
      x (u.linearEquiv x w).1
    have hidentity := hI.trans (ht.trans (Prod.ext hz rfl))
    have hsquare := (congrArg (v.linearEquiv x) hA.symm).trans
      ((huv x w).trans hidentity)
    exact ((v.linearEquiv x).apply_symm_apply _).trans hsquare.symm
  · rintro ⟨G, L, hL, h, e, he⟩
    -- The given extension supplies the actual square to an identity germ outside L.
    have hi : (a.sum (SupportBundleTriple.identity G)).IsIsomorphic
        (SupportBundleTriple.identity (a.source.sum G)) := by
      refine ⟨L, hL, Set.union_subset h (Set.empty_subset _), Set.empty_subset _,
        Iso.refl (a.source.sum G).Fiber, e.symm, ?_⟩
      intro x w
      have hA := hboundary a G L hL h x w
      have hw := congrArg (fun q : RelativeTriple (a.source.sum G).Fiber
        (a.target.sum G).Fiber Lᶜ ↦ q.linearEquiv x w) he
      have hI := (SupportBundleTriple.identity (a.source.sum G)).datum.enlarge_apply L hL
        (Set.empty_subset _) x w
      exact (congrArg (e.linearEquiv x).symm (hA.trans hw.symm)).trans
        (((e.linearEquiv x).symm_apply_apply w).trans hI.symm)
    have hh := SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _ hi
    simpa only [SupportBundleTriple.kZeroClass_sum, SupportBundleTriple.kZeroClass_identity,
      add_zero] using hh

/-- Uniformly controlled boundary homotopy preserves the class. -/
theorem supportBundleTriple_kZeroClass_eq_of_homotopic (E F : FiniteBundle X)
    (a b : CompactSupportTriple E.Fiber F.Fiber) (H : a.Homotopic b) :
    (SupportBundleTriple.ofBoundary E F a).kZeroClass =
      (SupportBundleTriple.ofBoundary E F b).kZeroClass := by
  /- Spatial cutoff converts the given homotopy, with its single common compact control, into
  an isomorphism at infinity. Apply the defining isomorphism relation. -/

  exact SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _
    (supportBundleTriple_isIsomorphic_of_homotopic E F a b H)

/-- Composition of the boundary maps adds the two support classes. -/
theorem supportBundleTriple_kZeroClass_compose (E F G : FiniteBundle X)
    (a : CompactSupportTriple E.Fiber F.Fiber) (b : CompactSupportTriple F.Fiber G.Fiber) :
    (SupportBundleTriple.ofBoundary E G (a.compose b)).kZeroClass =
      (SupportBundleTriple.ofBoundary E F a).kZeroClass +
        (SupportBundleTriple.ofBoundary F G b).kZeroClass := by
  /- Use the isomorphism at infinity between the sum and the composite plus an identity triple.
  Apply sum additivity and remove the identity class. -/
  have heq := SupportBundleTriple.kZeroClass_eq_of_isIsomorphic _ _
    (supportBundleTriple_isIsomorphic_sum_compose E F G a b)
  rw [SupportBundleTriple.kZeroClass_sum, SupportBundleTriple.kZeroClass_sum,
    SupportBundleTriple.kZeroClass_identity, add_zero] at heq
  exact heq.symm

/-- The stable quotient maps bijectively to the presented group. -/
theorem stableSupportTripleClassToKZero_bijective :
    Function.Bijective (stableSupportTripleClassToKZero X) := by
  /- Equality of generators is exactly stable isomorphism, giving injectivity of the quotient
  map. Single-triple representation gives surjectivity. -/
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact (a.stableClass_eq_iff b).mpr ((a.kZeroClass_eq_iff_stable b).mp hxy)
  · intro z
    obtain ⟨a, ha⟩ := supportBundleTriple_kZeroClass_surjective z
    exact ⟨a.stableClass, ha⟩

/-- Identify the stable quotient through the actual generator map. -/
def stableSupportTripleClassKZeroEquiv : StableSupportTripleClass X ≃ SupportTripleKZero X :=
  Equiv.ofBijective _ stableSupportTripleClassToKZero_bijective

end AtiyahSinger.ComplexBundle
