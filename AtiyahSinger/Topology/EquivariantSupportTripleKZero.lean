/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportCutoff
public import AtiyahSinger.Topology.SupportTripleKZero

/-!
# The group presented by actual equivariant support triples

Public module ID: M1818.

The generators retain the original support triples and specified actions.
Relations use actual equivariant global squares, the original direct sum and
identity triples of arbitrary equivariant finite-rank bundles. Forgetting actions
descends to the already defined ordinary support group on the same generators.

For a compact acting group and a locally compact Hausdorff base, invariant spatial
cutoff and the equivariant block path provide additive inverses of stable classes.
Only with these hypotheses do we identify the group presentation with the actual
identity-stable quotient. Fixed-bundle equivariant homotopy then preserves its
class through the same invariant-cutoff construction.

Sources: SG I.9.23--9.26 and ASI I §2 for the equivariant triple presentation;
KA II.2.14--2.15 for the block path. The invariant spatial cutoff and comparison
are explicit supplementary arguments. No one-point compactification comparison,
equivariant product/Bott theorem or analytic index realization is asserted.
The presentation and forgetful map are proved without compactness assumptions.
The original compact-group cutoff theorems prove the stable classification and
fixed-action homotopy invariance under the stated compact-group and LCH hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable (G X : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- Actual equivariant isomorphism, direct-sum and identity relations on the original triples. -/
def equivariantSupportTripleKZeroRelations :
    AddSubgroup (FreeAbelianGroup (EquivariantSupportBundleTriple G X)) :=
  AddSubgroup.closure
    ({z | ∃ a b : EquivariantSupportBundleTriple G X, a.IsIsomorphic b ∧
      z = FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ a b : EquivariantSupportBundleTriple G X,
      z = FreeAbelianGroup.of (a.sum b) - FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ E : FiniteBundle X, ∃ ρE : EquivariantStructure G E.Fiber,
      z = FreeAbelianGroup.of (EquivariantSupportBundleTriple.identity E ρE)})

/-- The actual abelian group presented by the three equivariant geometric relations. -/
abbrev EquivariantSupportTripleKZero : Type _ :=
  FreeAbelianGroup (EquivariantSupportBundleTriple G X) ⧸
    equivariantSupportTripleKZeroRelations G X

variable {G X}

/-- The quotient image of the same triple with its original specified equivariant structure. -/
def EquivariantSupportBundleTriple.kZeroClass (a : EquivariantSupportBundleTriple G X) :
    EquivariantSupportTripleKZero G X :=
  QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X) (FreeAbelianGroup.of a)

/-- The quotient generators satisfy exactly the three stated geometric relations. -/
theorem equivariantSupportTripleKZero_generator_relations :
    (∀ a b : EquivariantSupportBundleTriple G X,
      a.IsIsomorphic b → a.kZeroClass = b.kZeroClass) ∧
    (∀ a b : EquivariantSupportBundleTriple G X,
      (a.sum b).kZeroClass = a.kZeroClass + b.kZeroClass) ∧
    ∀ (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber),
      (EquivariantSupportBundleTriple.identity E ρE).kZeroClass = 0 := by
  /- Each displayed difference is one of the three explicit sets of relation
  generators. It belongs to their subgroup closure and maps to zero under the
  quotient homomorphism. The isomorphism relation contains equivariance of both
  global maps; the identity relation permits every supplied equivariant bundle.
  These are the defining relations; no completeness statement for stable
  classes is used. -/
  constructor
  · intro a b h
    -- The original equivariant square is an explicit relation generator.
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply AddSubgroup.subset_closure
    exact Or.inl (Or.inl ⟨a, b, h, rfl⟩)
  constructor
  · intro a b
    apply sub_eq_zero.mp
    change (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) _ -
      ((QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) _ +
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) _) = 0
    rw [← map_add, ← map_sub]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    apply AddSubgroup.subset_closure
    exact Or.inl (Or.inr ⟨a, b, by abel⟩)
  · intro E ρE
    -- The same specified equivariant bundle supplies the identity relation.
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    apply AddSubgroup.subset_closure
    exact Or.inr ⟨E, ρE, rfl⟩

/-- Additive maps out of the presentation are uniquely determined by compatible generator values. -/
theorem equivariantSupportTripleKZero_universal_property
    {A : Type*} [AddCommGroup A] (v : EquivariantSupportBundleTriple G X → A)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (hz : ∀ (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber),
      v (EquivariantSupportBundleTriple.identity E ρE) = 0) :
    ∃! f : EquivariantSupportTripleKZero G X →+ A, ∀ a, f a.kZeroClass = v a := by
  /- Stage 1: extend v uniquely to the free abelian group on the actual equivariant
  triples. Each assumption annihilates one of the three relation families, so
  the entire subgroup they generate lies in the kernel.
  Stage 2: descend through this specified quotient. The generator equation is
  inherited from the free extension. Any competing homomorphism agrees on all
  generators and therefore on their integer linear combinations and quotient.
  No compactness, stabilization theorem or choice of invariant metric is used. -/
  -- Extend the given values and annihilate exactly the original three relation families.
  let f : FreeAbelianGroup (EquivariantSupportBundleTriple G X) →+ A :=
    FreeAbelianGroup.lift v
  have hrelations : equivariantSupportTripleKZeroRelations G X ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ((⟨a, b, hab, rfl⟩ | ⟨a, b, rfl⟩) | ⟨E, ρE, rfl⟩)
    · change f (_ - _) = 0
      simp [f, hi a b hab]
    · change f (_ - _ - _) = 0
      simp [f, hs a b]
    · change f (FreeAbelianGroup.of (EquivariantSupportBundleTriple.identity E ρE)) = 0
      exact (FreeAbelianGroup.lift_apply_of v _).trans (hz E ρE)
  let φ : EquivariantSupportTripleKZero G X →+ A :=
    QuotientAddGroup.lift (equivariantSupportTripleKZeroRelations G X) f hrelations
  have hφ (a : EquivariantSupportBundleTriple G X) : φ a.kZeroClass = v a :=
    FreeAbelianGroup.lift_apply_of v a
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  -- Equality on these same generators determines the quotient homomorphism.
  have hcomp : ψ.comp (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      φ.comp (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    exact (hψ a).trans (hφ a).symm
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  exact DFunLike.congr_fun hcomp w

/-- Identity stabilization by actual equivariant bundles preserves the group class. -/
theorem EquivariantSupportBundleTriple.kZeroClass_eq_of_isStablyIsomorphic
    (a b : EquivariantSupportBundleTriple G X) (h : a.IsStablyIsomorphic b) :
    a.kZeroClass = b.kZeroClass := by
  /- Read the two specified equivariant stabilizing bundles and the actual
  equivariant global square. Apply the isomorphism generator relation, expand
  the two direct-sum generator values, and remove their identity generators.
  This only proves that stable equivalence descends; the reverse implication
  below needs compact-group invariant cutoff and a locally compact base. -/
  obtain ⟨E, F, ρE, ρF, hEF⟩ := h
  obtain ⟨hi, hs, hz⟩ := equivariantSupportTripleKZero_generator_relations (G := G) (X := X)
  -- Both actual stabilizers are identity generators for their own specified actions.
  have heq := hi _ _ hEF
  rw [hs, hs, hz, hz, add_zero, add_zero] at heq
  exact heq

/-- The setoid of the existing equivariant identity-stabilization relation. -/
def EquivariantSupportBundleTriple.stableSetoid :
    Setoid (EquivariantSupportBundleTriple G X) where
  r := EquivariantSupportBundleTriple.IsStablyIsomorphic
  iseqv := (EquivariantSupportBundleTriple.isStablyIsomorphic_properties
    (G := G) (X := X)).1

/-- Actual stable classes of the original equivariant compact-support triples. -/
abbrev StableEquivariantSupportTripleClass (G X : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] :
    Type _ :=
  Quotient (EquivariantSupportBundleTriple.stableSetoid (G := G) (X := X))

/-- The stable class retains the original equivariant triple as its representative. -/
def EquivariantSupportBundleTriple.stableClass (a : EquivariantSupportBundleTriple G X) :
    StableEquivariantSupportTripleClass G X :=
  Quotient.mk _ a

/-- The stable-to-group comparison is induced by the same original triple generator. -/
def stableEquivariantSupportTripleClassToKZero :
    StableEquivariantSupportTripleClass G X → EquivariantSupportTripleKZero G X :=
  Quotient.lift EquivariantSupportBundleTriple.kZeroClass
    (fun a b h ↦ a.kZeroClass_eq_of_isStablyIsomorphic b h)

/-- Forget the specified actions by descending the original ordinary triple classes. -/
def equivariantSupportTripleKZeroForget :
    EquivariantSupportTripleKZero G X →+ SupportTripleKZero X :=
  (equivariantSupportTripleKZero_universal_property (fun a ↦ a.1.kZeroClass)
    (fun a b h ↦ a.1.kZeroClass_eq_of_isIsomorphic b.1
      ((EquivariantSupportBundleTriple.isIsomorphic_properties
        (G := G) (X := X)).2 a b h))
    (fun a b ↦ a.1.kZeroClass_sum b.1)
    (fun E _ ↦ SupportBundleTriple.kZeroClass_identity E)).choose

/-- Forgetting acts on each generator by retaining precisely its original nonequivariant triple. -/
theorem equivariantSupportTripleKZeroForget_apply (a : EquivariantSupportBundleTriple G X) :
    equivariantSupportTripleKZeroForget a.kZeroClass = a.1.kZeroClass := by
  /- The homomorphism was chosen from the universal property with value
  a ↦ a.1.kZeroClass. Read the generator equation from that same witness.
  No dimension map, ordinary replacement triple or unverified surjectivity of
  forgetting is involved. -/
  -- Read the equation from the very witness defining the original forgetful map.
  exact (equivariantSupportTripleKZero_universal_property (fun a ↦ a.1.kZeroClass)
    (fun a b h ↦ a.1.kZeroClass_eq_of_isIsomorphic b.1
      ((EquivariantSupportBundleTriple.isIsomorphic_properties
        (G := G) (X := X)).2 a b h))
    (fun a b ↦ a.1.kZeroClass_sum b.1)
    (fun E _ ↦ SupportBundleTriple.kZeroClass_identity E)).choose_spec.1 a

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

variable [hG : CompactSpace G] [hL : LocallyCompactSpace X] [hT : T2Space X]
include hG hL hT

/-- Reversing the original equivariant triple gives its additive inverse. -/
theorem EquivariantSupportBundleTriple.kZeroClass_inverse
    (a : EquivariantSupportBundleTriple G X) : a.inverse.kZeroClass = -a.kZeroClass := by
  /- The equivariant block path and invariant cutoff give an actual equivariant
  isomorphism from a plus its inverse to the identity on the source-target sum.
  Apply the three generator relations. The sum of the two classes is zero,
  giving the displayed inverse formula. The actual swapped actions are retained. -/
  obtain ⟨hi, hs, hz⟩ := equivariantSupportTripleKZero_generator_relations (G := G) (X := X)
  have h := hi _ _ a.isIsomorphic_sum_inverse
  rw [hs, hz] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Every group class is represented by one original equivariant support triple. -/
theorem equivariantSupportBundleTriple_kZeroClass_surjective :
    Function.Surjective (EquivariantSupportBundleTriple.kZeroClass (G := G) (X := X)) := by
  /- Write a representative as a finite integer combination of actual generators.
  Replace each negative generator by its actual inverse triple using the preceding
  theorem, then combine all terms by direct sum. The empty sum is the identity
  triple of a zero-dimensional product representation bundle. This permits
  locally varying unbounded ranks and does not assert a finite trivial complement. -/
  -- A zero-dimensional product bundle carries the original product topology and identity action.
  let Z := FiniteBundle.trivial X 0
  let ρZ : EquivariantStructure G Z.Fiber :=
    { linearMap := fun _ _ ↦ LinearMap.id
      one_map := fun x v ↦ congrArg (fun y ↦ (⟨y, v⟩ : TotalSpace Unit Z.Fiber))
        (one_smul G x)
      mul_map := fun g h x v ↦ congrArg (fun y ↦ (⟨y, v⟩ : TotalSpace Unit Z.Fiber))
        (mul_smul g h x)
      continuous_action := by
        have hc : Continuous (fun z : TotalSpace Unit Z.Fiber ↦ (z.proj, z.snd)) :=
          continuous_induced_dom
        exact continuous_induced_rng.mpr
          ((continuous_fst.smul (hc.fst.comp continuous_snd)).prodMk
            (hc.snd.comp continuous_snd)) }
  obtain ⟨_, hs, hz⟩ := equivariantSupportTripleKZero_generator_relations (G := G) (X := X)
  -- Descend a free-group representative; inverse triples handle the negative generators.
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
      refine ⟨EquivariantSupportBundleTriple.identity Z ρZ, ?_⟩
      exact (hz Z ρZ).trans (map_zero _).symm
  | of a => exact ⟨a, rfl⟩
  | neg a _ =>
      exact ⟨a.inverse, a.kZeroClass_inverse.trans (map_neg _ _).symm⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a.sum b, ?_⟩
      rw [hs, ha, hb, map_add]

open EquivariantSupportBundleTriple in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a compact-group LCH base, the group adds exactly the equivariant stable identifications. -/
theorem EquivariantSupportBundleTriple.kZeroClass_eq_iff_stable
    (a b : EquivariantSupportBundleTriple G X) :
    a.kZeroClass = b.kZeroClass ↔ a.IsStablyIsomorphic b := by
  /- Stage 1: on the actual identity-stable quotient, direct sum is well defined
  by stable sum compatibility. Coordinate associators and swaps are equivariant
  for the same componentwise actions, and identity triples represent zero.
  Stage 2: the actual equivariant sum-inverse isomorphism gives additive inverses
  in this quotient. This is where compact G and the LCH base enter through
  invariant cutoff; general group completion alone would not prove this claim.
  Stage 3: the resulting abelian group satisfies exactly the same generator
  relations and universal property as the presented group. Their generator maps
  are mutual inverses. Effectiveness of the stable setoid quotient identifies
  equality precisely with the stated equivariant stabilization relation. -/
  classical
  let eqv := (EquivariantSupportBundleTriple.isIsomorphic_properties (G := G) (X := X)).1
  have hsum := (EquivariantSupportBundleTriple.isIsomorphic_sum_enlarge
    (G := G) (X := X)).1
  -- Coordinate permutations retain the original sum actions and invariant union controls.
  have hcomm (a b : EquivariantSupportBundleTriple G X) :
      (a.sum b).IsIsomorphic (b.sum a) := by
    let K := a.1.datum.control ∪ b.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control.union b.1.datum.isCompact_control
    refine ⟨K, hK, fun g x ↦ (a.2.isEquivariant.invariant_control g x).or
      (b.2.isEquivariant.invariant_control g x), Set.Subset.refl _,
      Set.union_subset Set.subset_union_right Set.subset_union_left,
      sumCommIso, sumCommIso, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
    intro x v
    simp only [EquivariantSupportBundleTriple.sum, SupportBundleTriple.sum,
      SupportBundleTriple.ofBoundary,
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
      simp only [EquivariantSupportBundleTriple.sum, SupportBundleTriple.sum,
        SupportBundleTriple.ofBoundary,
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
    simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.identity,
      SupportBundleTriple.sum, SupportBundleTriple.identity,
      SupportBundleTriple.ofBoundary, CompactSupportTriple.sum, CompactSupportTriple.enlarge,
      Iso.restrictTo_apply, RelativeTriple.sum_apply, CompactSupportTriple.ofIso]
    rfl
  have hflatten (a : EquivariantSupportBundleTriple G X) (E F : FiniteBundle X)
      (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber) :
      ((a.sum (identity E ρE)).sum (identity F ρF)).IsIsomorphic
        (a.sum (identity (E.sum F) (ρE.sum ρF))) :=
    eqv.trans (hassoc a (identity E ρE) (identity F ρF))
      (hsum _ _ _ _ (eqv.refl a) (hidentity E F ρE ρF))
  let Q := StableEquivariantSupportTripleClass G X
  let Z := a.1.source
  let ρZ := a.2.sourceAction
  -- Any identity triple is zero in this same quotient; use an already supplied bundle/action.
  let : Zero Q := ⟨(EquivariantSupportBundleTriple.identity Z ρZ).stableClass⟩
  let : Add Q := ⟨fun x y ↦ Quotient.liftOn₂ x y
    (fun c d ↦ (c.sum d).stableClass)
    (fun c d e f hce hdf ↦ Quotient.sound
      ((EquivariantSupportBundleTriple.isStablyIsomorphic_properties
        (G := G) (X := X)).2.2.1 c e d f hce hdf))⟩
  have hadd (c d : EquivariantSupportBundleTriple G X) :
      (c.stableClass : Q) + d.stableClass = (c.sum d).stableClass := rfl
  have hiso (c d : EquivariantSupportBundleTriple G X) (h : c.IsIsomorphic d) :
      c.stableClass = d.stableClass :=
    Quotient.sound ((EquivariantSupportBundleTriple.isStablyIsomorphic_properties
      (G := G) (X := X)).2.1 c d h)
  have hzero (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber) :
      (EquivariantSupportBundleTriple.identity E ρE).stableClass = (0 : Q) := by
    apply Quotient.sound
    exact ⟨Z, E, ρZ, ρE, hcomm (EquivariantSupportBundleTriple.identity E ρE)
      (EquivariantSupportBundleTriple.identity Z ρZ)⟩
  have hadd_comm (x y : Q) : x + y = y + x := by
    induction x using Quotient.inductionOn with
    | _ c =>
      induction y using Quotient.inductionOn with
      | _ d => exact hiso _ _ (hcomm c d)
  have hadd_assoc (x y z : Q) : x + y + z = x + (y + z) := by
    induction x using Quotient.inductionOn with
    | _ c =>
      induction y using Quotient.inductionOn with
      | _ d =>
        induction z using Quotient.inductionOn with
        | _ e => exact hiso _ _ (hassoc c d e)
  have hright (x : Q) : x + 0 = x := by
    induction x using Quotient.inductionOn with
    | _ c =>
      -- Stabilize by Z on the left and Z plus Z on the right, using the actual associator.
      apply Quotient.sound
      exact ⟨Z, Z.sum Z, ρZ, ρZ.sum ρZ, hflatten c Z Z ρZ ρZ⟩
  let : AddCommMonoid Q :=
    { add_assoc := hadd_assoc
      zero_add := fun x ↦ (hadd_comm 0 x).trans (hright x)
      add_zero := hright
      add_comm := hadd_comm
      nsmul := nsmulRec }
  -- The original equivariant inverse square supplies an inverse in this same stable quotient.
  have hinverse (x : Q) : ∃ y : Q, y + x = 0 := by
    induction x using Quotient.inductionOn with
    | _ c =>
      refine ⟨c.inverse.stableClass, ?_⟩
      change c.inverse.stableClass + c.stableClass = (0 : Q)
      rw [hadd_comm, hadd]
      exact (hiso _ _ c.isIsomorphic_sum_inverse).trans (hzero _ _)
  let : Neg Q := ⟨fun x ↦ (hinverse x).choose⟩
  let : AddCommGroup Q :=
    { ‹AddCommMonoid Q›, ‹Neg Q› with
      neg_add_cancel := fun x ↦ (hinverse x).choose_spec
      zsmul := zsmulRec }
  -- The original universal property detects precisely equality of these stable classes.
  obtain ⟨φ, hφ, _⟩ := equivariantSupportTripleKZero_universal_property
    (fun c ↦ (c.stableClass : Q)) hiso (fun c d ↦ (hadd c d).symm) hzero
  constructor
  · intro h
    exact Quotient.exact ((hφ a).symm.trans ((congrArg φ h).trans (hφ b)))
  · exact a.kZeroClass_eq_of_isStablyIsomorphic b

/-- The specified stable-to-group generator map is bijective under the cutoff hypotheses. -/
theorem stableEquivariantSupportTripleClassToKZero_bijective :
    Function.Bijective (stableEquivariantSupportTripleClassToKZero (G := G) (X := X)) := by
  /- Equality of two generator images is exactly stable equivalence by the
  preceding theorem, proving injectivity on the actual stable quotient.
  Single-triple representation proves surjectivity of this same forward map.
  No separate isomorphism between unrelated K-theory models is chosen. -/
  constructor
  · -- Effectiveness of the original quotient turns the group equality into its stable relation.
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b => exact Quotient.sound ((a.kZeroClass_eq_iff_stable b).mp hxy)
  · -- Represent the same presented group class by one original equivariant triple.
    intro z
    obtain ⟨a, ha⟩ := equivariantSupportBundleTriple_kZeroClass_surjective z
    exact ⟨a.stableClass, ha⟩

/-- The comparison equivalence retains the specified original generator map as its forward map. -/
def stableEquivariantSupportTripleClassKZeroEquiv :
    StableEquivariantSupportTripleClass G X ≃ EquivariantSupportTripleKZero G X :=
  Equiv.ofBijective _ stableEquivariantSupportTripleClassToKZero_bijective

/-- The given fixed-action homotopy preserves the classes of its exact endpoint triples. -/
theorem equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (E F : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber)
    (ρF : EquivariantStructure G F.Fiber)
    (a b : CompactSupportTriple E.Fiber F.Fiber)
    (ha : a.IsEquivariant ρE ρF) (hb : b.IsEquivariant ρE ρF)
    (H : a.EquivariantlyHomotopic b ρE ρF) :
    (EquivariantSupportBundleTriple.ofBoundary E F a ρE ρF ha).kZeroClass =
      (EquivariantSupportBundleTriple.ofBoundary E F b ρE ρF hb).kZeroClass := by
  /- Use invariant cutoff on this actual uniformly controlled equivariant
  homotopy. It produces a global equivariant isomorphism square for the same
  endpoint bundles and boundary germs. The isomorphism relation in the stated
  presentation identifies their exact generators; no homotopy relation is
  silently added to the subgroup definition. -/
  -- Apply the actual equivariant global square obtained from this same fixed-action homotopy.
  exact equivariantSupportTripleKZero_generator_relations.1 _ _
    (equivariantSupportBundleTriple_isIsomorphic_of_homotopic E F ρE ρF a b ha hb H)

end AtiyahSinger.ComplexBundle
