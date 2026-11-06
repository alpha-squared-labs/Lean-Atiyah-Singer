/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BanachUnitLifting
public import AtiyahSinger.Topology.BundleIsoHomotopyRotation
public import AtiyahSinger.Topology.BundleTriple

/-!
# The abelian group presented by relative bundle triples

Public module ID: M2258.

D07/K02. Take the free abelian group modulo isomorphism, direct-sum and identity
relations. The comparison with stable-isomorphism classes is a separate theorem
for compact Hausdorff closed pairs. Sources: SG I.9.23–9.25; KA II.2.14–2.29.
No quotient-space K group, difference bundle or index identity enters the definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

variable {X : Type*} [TopologicalSpace X]


/-- The explicit defining relations of the geometric triple group. -/
def tripleKZeroRelations (A : Set X) : AddSubgroup (FreeAbelianGroup (BundleTriple A)) :=
  AddSubgroup.closure
    ({z | ∃ a b : BundleTriple A, a.IsIsomorphic b ∧
      z = FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ a b : BundleTriple A,
      z = FreeAbelianGroup.of (a.sum b) - FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ E : FiniteBundle X, z = FreeAbelianGroup.of (BundleTriple.identity A E)})

/-- The group given by the ordinary isomorphism, sum and identity triple relations. -/
abbrev TripleKZero (A : Set X) : Type _ :=
  FreeAbelianGroup (BundleTriple A) ⧸ tripleKZeroRelations A

/-- The actual quotient class of a triple generator. -/
def BundleTriple.kZeroClass {A : Set X} (a : BundleTriple A) : TripleKZero A :=
  QuotientAddGroup.mk' (tripleKZeroRelations A) (FreeAbelianGroup.of a)

/-- Isomorphic triples represent the same class. -/
theorem BundleTriple.kZeroClass_eq_of_isIsomorphic {A : Set X} (a b : BundleTriple A)
    (h : a.IsIsomorphic b) : a.kZeroClass = b.kZeroClass := by
  /- The difference of these two generators is among the explicit isomorphism
  relations. Its image in the quotient group is zero, giving equality of the classes. -/
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inl ⟨a, b, h, rfl⟩)

/-- Direct sum represents addition. -/
theorem BundleTriple.kZeroClass_sum {A : Set X} (a b : BundleTriple A) :
    (a.sum b).kZeroClass = a.kZeroClass + b.kZeroClass := by
  /- The difference between the left side and the two terms on the right is
  a defining sum relation. It vanishes under the quotient homomorphism. -/
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (tripleKZeroRelations A)) _ -
    ((QuotientAddGroup.mk' (tripleKZeroRelations A)) _ +
      (QuotientAddGroup.mk' (tripleKZeroRelations A)) _) = 0
  rw [← map_add, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inr ⟨a, b, by abel⟩)

/-- The identity triple is zero. -/
theorem BundleTriple.kZeroClass_identity (A : Set X) (E : FiniteBundle X) :
    (BundleTriple.identity A E).kZeroClass = 0 := by
  /- Its free generator is included among the identity relations. The quotient
  homomorphism therefore sends this generator to zero, independently of compactness. -/
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inr ⟨E, rfl⟩

/-- Stable isomorphism preserves the presented group class. -/
theorem BundleTriple.kZeroClass_eq_of_isStablyIsomorphic {A : Set X}
    (a b : BundleTriple A) (h : a.IsStablyIsomorphic b) : a.kZeroClass = b.kZeroClass := by
  /- The stabilized triples are isomorphic, so their classes agree. Expand the
  sum classes and remove the two identity classes, which are zero by the defining relations. -/
  obtain ⟨E, F, hEF⟩ := h
  have heq := BundleTriple.kZeroClass_eq_of_isIsomorphic _ _ hEF
  simpa only [BundleTriple.kZeroClass_sum, BundleTriple.kZeroClass_identity,
    add_zero] using heq

/-- Functions respecting the three relations descend uniquely to an additive map. -/
theorem tripleKZero_universal_property (A : Set X) {G : Type*} [AddCommGroup G]
    (v : BundleTriple A → G)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (hz : ∀ E, v (BundleTriple.identity A E) = 0) :
    ∃! f : TripleKZero A →+ G, ∀ a, f a.kZeroClass = v a := by
  /- Extend v to the free abelian group. Each of the three assumptions kills
  the corresponding relation generators, hence their generated subgroup. Descend
  through the quotient; uniqueness holds because the triple classes generate it. -/

  let f : FreeAbelianGroup (BundleTriple A) →+ G := FreeAbelianGroup.lift v
  have hrelations : tripleKZeroRelations A ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ((⟨a, b, hab, rfl⟩ | ⟨a, b, rfl⟩) | ⟨E, rfl⟩)
    · change f (_ - _) = 0
      simp [f, hi a b hab]
    · change f (_ - _ - _) = 0
      simp [f, hs a b]
    · change f (FreeAbelianGroup.of (BundleTriple.identity A E)) = 0
      exact (FreeAbelianGroup.lift_apply_of v _).trans (hz E)
  let φ : TripleKZero A →+ G := QuotientAddGroup.lift (tripleKZeroRelations A) f hrelations
  have hφ (a : BundleTriple A) : φ a.kZeroClass = v a :=
    FreeAbelianGroup.lift_apply_of v a
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  -- Equality on the original generators determines the map out of the same quotient.
  have hcomp : ψ.comp (QuotientAddGroup.mk' (tripleKZeroRelations A)) =
      φ.comp (QuotientAddGroup.mk' (tripleKZeroRelations A)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    exact (hψ a).trans (hφ a).symm
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (tripleKZeroRelations A) z
  exact DFunLike.congr_fun hcomp w

variable [hX : CompactSpace X] [hT : T2Space X]
include hX hT

/-- A triple and its reverse sum to a triple isomorphic to an actual identity triple. -/
theorem BundleTriple.isIsomorphic_sum_inverse (A : Set X) (hA : IsClosed A)
    (a : BundleTriple A) :
    (a.sum a.inverse).IsIsomorphic
      (BundleTriple.identity A (a.source.sum a.target)) := by
  /- Karoubi II.2.14 and II.2.25. The signed permutation takes the boundary
  direct sum to a rotation. Extend that rotation from the closed subspace,
  then use the extension and the same global permutation as the two maps. -/
  let E := a.source.Fiber
  let F := a.target.Fiber
  let S := E ×ᵇ F
  let : IsFiniteRank (Restrict E A) := isFiniteRank_restrict A
  let : IsFiniteRank (Restrict F A) := isFiniteRank_restrict A
  obtain ⟨b, hb, ⟨H⟩⟩ := a.boundary.exists_signed_swap_homotopy
  let c : Iso (Restrict S A) (Restrict E A ×ᵇ Restrict F A) := restrictSumIso A
  let d : RelativeTriple S S A := (c.trans b).trans c.symm
  let πA : C(I × A, A) := ⟨Prod.snd, continuous_snd⟩
  -- Conjugate the entire path by the vector-preserving restriction comparison.
  let K : IsoHomotopy (RelativeTriple.identity S A) d :=
    { iso := ((c.pullback πA).trans H.iso).trans (c.symm.pullback πA)
      map_zero := by
        intro x v
        change (c.linearEquiv x).symm
          (H.iso.linearEquiv (0, x) (c.linearEquiv x v)) = v
        exact (congrArg (c.linearEquiv x).symm (H.map_zero x _)).trans
          ((c.linearEquiv x).symm_apply_apply v)
      map_one := by
        intro x v
        exact congrArg (c.linearEquiv x).symm (H.map_one x _) }
  have hd (x : A) (v : S x) : d.linearEquiv x v =
      (-(a.boundary.linearEquiv x).symm v.2, a.boundary.linearEquiv x v.1) := by
    apply (c.linearEquiv x).injective
    change (c.linearEquiv x) ((c.linearEquiv x).symm
      (b.linearEquiv x (c.linearEquiv x v))) = _
    rw [LinearEquiv.apply_symm_apply]
    erw [restrictSumIso_apply, hb, restrictSumIso_apply]
  obtain ⟨e, he⟩ := d.exists_extension_of_isElementary A hA ⟨K⟩
  -- Negation on the original E is continuous by pullback-section scalar multiplication.
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E → X) *ᵖ E) := isFiniteRank_pullback p
  have hi : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hn : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, -z.snd⟩ : TotalSpace Unit E)) := by
    have hs := continuous_smul_section ((p : TotalSpace Unit E → X) *ᵖ E)
      (ContinuousMap.const _ (-1 : ℂ)) _ hi
    have hc := (Pullback.continuous_lift Unit E p).comp hs
    change Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, (-1 : ℂ) • z.snd⟩ : TotalSpace Unit E)) at hc
    simpa only [neg_one_smul] using hc
  let n : Iso E E :=
    { linearEquiv := fun _ ↦ LinearEquiv.neg ℂ
      continuous_total := hn
      continuous_symm := hn }
  let swap : Iso (F ×ᵇ E) S := sumCommIso.trans (n.sum (Iso.refl F))
  refine ⟨e, swap, ?_⟩
  intro x v
  have hex := congrArg (fun q : RelativeTriple S S A ↦ q.linearEquiv x v) he
  change swap.linearEquiv x
    ((RelativeTriple.sum a.boundary a.boundary.symm).linearEquiv x v) = e.linearEquiv x v
  rw [RelativeTriple.sum_apply]
  exact (hd x v).symm.trans hex.symm

/-- Reversing the boundary isomorphism represents the additive inverse. -/
theorem BundleTriple.kZeroClass_inverse (A : Set X) (hA : IsClosed A) (a : BundleTriple A) :
    a.inverse.kZeroClass = -a.kZeroClass := by
  /- Apply the preceding rotation-and-extension comparison to identify the
  sum of a and its reverse with an identity triple. Its class is zero;
  direct-sum additivity then identifies the reversed class with the inverse. -/
  have heq := BundleTriple.kZeroClass_eq_of_isIsomorphic _ _
    (a.isIsomorphic_sum_inverse A hA)
  rw [BundleTriple.kZeroClass_sum, BundleTriple.kZeroClass_identity] at heq
  exact eq_neg_of_add_eq_zero_right heq

/-- Every class is represented by a single geometric triple. -/
theorem bundleTriple_kZeroClass_surjective (A : Set X) (hA : IsClosed A) :
    Function.Surjective (BundleTriple.kZeroClass (A := A)) := by
  /- A free abelian expression is a finite signed sum of generators. Replace
  each negative generator by the reversed triple and combine the result by direct
  sums. The empty expression is represented by the zero-rank identity triple. -/
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (tripleKZeroRelations A) z
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
      refine ⟨BundleTriple.identity A (FiniteBundle.trivial X 0), ?_⟩
      exact (BundleTriple.kZeroClass_identity _ _).trans (map_zero _).symm
  | of a => exact ⟨a, rfl⟩
  | neg a _ =>
      exact ⟨a.inverse, (a.kZeroClass_inverse A hA).trans (map_neg _ _).symm⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a.sum b, ?_⟩
      rw [BundleTriple.kZeroClass_sum, ha, hb, map_add]

/-- On a closed compact pair, the presentation has exactly the stable relation. -/
theorem BundleTriple.kZeroClass_eq_iff_stable (A : Set X) (hA : IsClosed A)
    (a b : BundleTriple A) : a.kZeroClass = b.kZeroClass ↔ a.IsStablyIsomorphic b := by
  /- The stable quotient is a commutative monoid under direct sum. The rotation
  path and closed-subspace lifting give inverses, so it is already an abelian group.
  Its universal property is precisely the three relations used here. Thus group
  completion introduces no further identifications beyond stable isomorphism. -/
  classical
  let Q := StableTripleClass A
  let Z := FiniteBundle.trivial X 0
  let : Zero Q := ⟨(BundleTriple.identity A Z).stableClass⟩
  let : Add Q := ⟨fun x y ↦ Quotient.liftOn₂ x y
    (fun a b ↦ (a.sum b).stableClass)
    (fun a b c d hac hbd ↦ ((a.sum b).stableClass_eq_iff (c.sum d)).mpr (hac.sum hbd))⟩
  have hadd (a b : BundleTriple A) :
      (a.stableClass : Q) + b.stableClass = (a.sum b).stableClass := rfl
  have hiso (a b : BundleTriple A) (h : a.IsIsomorphic b) :
      a.stableClass = b.stableClass :=
    (a.stableClass_eq_iff b).mpr (a.isStablyIsomorphic_of_isIsomorphic b h)
  -- Every identity triple is the same zero class, by the actual summand interchange.
  have hzero (E : FiniteBundle X) : (BundleTriple.identity A E).stableClass = (0 : Q) := by
    apply ((BundleTriple.identity A E).stableClass_eq_iff (BundleTriple.identity A Z)).mpr
    refine ⟨Z, E, sumCommIso, sumCommIso, ?_⟩
    intro x v
    change (sumCommIso (E := E.Fiber) (F := Z.Fiber)).linearEquiv x
      ((RelativeTriple.sum (RelativeTriple.identity E.Fiber A)
        (RelativeTriple.identity Z.Fiber A)).linearEquiv x v) =
      (RelativeTriple.sum (RelativeTriple.identity Z.Fiber A)
        (RelativeTriple.identity E.Fiber A)).linearEquiv x
        ((sumCommIso (E := E.Fiber) (F := Z.Fiber)).linearEquiv x v)
    rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply]
    rfl
  have hcomm (x y : Q) : x + y = y + x := by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        apply hiso
        refine ⟨sumCommIso, sumCommIso, ?_⟩
        intro x v
        change (sumCommIso (E := a.target.Fiber) (F := b.target.Fiber)).linearEquiv x
          ((RelativeTriple.sum a.boundary b.boundary).linearEquiv x v) =
          (RelativeTriple.sum b.boundary a.boundary).linearEquiv x
            ((sumCommIso (E := a.source.Fiber) (F := b.source.Fiber)).linearEquiv x v)
        rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply]
        rfl
  have hassoc (x y z : Q) : x + y + z = x + (y + z) := by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        induction z using Quotient.inductionOn with
        | _ c =>
          apply hiso
          refine ⟨FiniteBundle.sumAssocIso a.source b.source c.source,
            FiniteBundle.sumAssocIso a.target b.target c.target, ?_⟩
          intro x v
          change (FiniteBundle.sumAssocIso a.target b.target c.target).linearEquiv x
            ((RelativeTriple.sum (RelativeTriple.sum a.boundary b.boundary) c.boundary).linearEquiv
              x v) = (RelativeTriple.sum a.boundary
                (RelativeTriple.sum b.boundary c.boundary)).linearEquiv x
              ((FiniteBundle.sumAssocIso a.source b.source c.source).linearEquiv x v)
          erw [RelativeTriple.sum_apply, RelativeTriple.sum_apply,
            FiniteBundle.sumAssocIso_apply, FiniteBundle.sumAssocIso_apply,
            RelativeTriple.sum_apply, RelativeTriple.sum_apply]
          rfl
  have hright (x : Q) : x + 0 = x := by
    induction x using Quotient.inductionOn with
    | _ a =>
      apply hiso
      obtain ⟨u, hu⟩ := FiniteBundle.exists_sum_zero_iso a.source
      obtain ⟨v, hv⟩ := FiniteBundle.exists_sum_zero_iso a.target
      refine ⟨u, v, ?_⟩
      intro x w
      change v.linearEquiv x
        ((RelativeTriple.sum a.boundary (RelativeTriple.identity Z.Fiber A)).linearEquiv x w) =
        a.boundary.linearEquiv x (u.linearEquiv x w)
      erw [RelativeTriple.sum_apply, hu, hv]
  -- The original stable quotient is already a commutative monoid under direct sum.
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
      exact (hiso _ _ (a.isIsomorphic_sum_inverse A hA)).trans (hzero _)
  -- Choose an inverse only after its existence is proved in this same quotient.
  let : Neg Q := ⟨fun x ↦ (hinverse x).choose⟩
  let : AddCommGroup Q :=
    { ‹AddCommMonoid Q›, ‹Neg Q› with
      neg_add_cancel := fun x ↦ (hinverse x).choose_spec
      zsmul := zsmulRec }
  obtain ⟨φ, hφ, _⟩ := tripleKZero_universal_property A
    (fun a ↦ (a.stableClass : Q)) hiso (fun a b ↦ (hadd a b).symm) hzero
  constructor
  · intro h
    apply (a.stableClass_eq_iff b).mp
    exact (hφ a).symm.trans ((congrArg φ h).trans (hφ b))
  · exact a.kZeroClass_eq_of_isStablyIsomorphic b

/-- The zero criterion is extension after identity stabilization. -/
theorem BundleTriple.kZeroClass_eq_zero_iff (A : Set X) (hA : IsClosed A) (a : BundleTriple A) :
    a.kZeroClass = 0 ↔ ∃ G : FiniteBundle X,
      ∃ e : Iso (a.source.sum G).Fiber (a.target.sum G).Fiber,
        e.restrict A = a.boundary.stabilize G.Fiber := by
  /- This is Karoubi II.2.28–2.29. A stable isomorphism to an identity triple
  yields an extension by composing the two global comparison isomorphisms.
  Conversely such an extension identifies the stabilized triple with an identity triple. -/
  constructor
  · intro ha
    let Z := FiniteBundle.trivial X 0
    have haz : a.kZeroClass = (BundleTriple.identity A Z).kZeroClass :=
      ha.trans (BundleTriple.kZeroClass_identity A Z).symm
    obtain ⟨G, H, u, v, huv⟩ :=
      (a.kZeroClass_eq_iff_stable A hA (BundleTriple.identity A Z)).mp haz
    -- The two actual comparison maps identify the same stabilized target bundle.
    refine ⟨G, u.trans v.symm, ?_⟩
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro w
    apply (v.linearEquiv x).injective
    change v.linearEquiv x ((v.linearEquiv x).symm (u.linearEquiv x w)) =
      v.linearEquiv x ((a.boundary.stabilize G.Fiber).linearEquiv x w)
    have hw := huv x w
    change v.linearEquiv x ((a.boundary.stabilize G.Fiber).linearEquiv x w) =
      (RelativeTriple.sum (RelativeTriple.identity Z.Fiber A)
        (RelativeTriple.identity H.Fiber A)).linearEquiv x (u.linearEquiv x w) at hw
    rw [RelativeTriple.sum_apply] at hw
    exact ((v.linearEquiv x).apply_symm_apply _).trans hw.symm
  · rintro ⟨G, e, he⟩
    -- The supplied global extension is an isomorphism to an identity triple.
    have hi : (a.sum (BundleTriple.identity A G)).IsIsomorphic
        (BundleTriple.identity A (a.source.sum G)) := by
      refine ⟨Iso.refl (a.source.sum G).Fiber, e.symm, ?_⟩
      intro x w
      have hw := congrArg (fun q : RelativeTriple (a.source.sum G).Fiber
        (a.target.sum G).Fiber A ↦ q.linearEquiv x w) he
      change (e.linearEquiv x).symm ((a.boundary.stabilize G.Fiber).linearEquiv x w) = w
      exact (congrArg (e.linearEquiv x).symm hw.symm).trans
        ((e.linearEquiv x).symm_apply_apply w)
    have hh := BundleTriple.kZeroClass_eq_of_isIsomorphic _ _ hi
    simpa only [BundleTriple.kZeroClass_sum, BundleTriple.kZeroClass_identity, add_zero] using hh

/-- Homotopies through boundary isomorphisms preserve the group class. -/
theorem bundleTriple_kZeroClass_eq_of_homotopy (A : Set X) (hA : IsClosed A)
    (E F : FiniteBundle X) (a b : RelativeTriple E.Fiber F.Fiber A) (H : IsoHomotopy a b) :
    (BundleTriple.ofBoundary E F a).kZeroClass = (BundleTriple.ofBoundary E F b).kZeroClass := by
  /- Use the homotopy from identity to b composed with the inverse of a as
  an automorphism homotopy on the restricted target bundle. Lift it globally
  with identity start; its endpoint supplies an isomorphism of the two triples. -/
  let d : RelativeTriple F.Fiber F.Fiber A := a.symm.trans b
  let πA : C(I × A, A) := ⟨Prod.snd, continuous_snd⟩

  let K : IsoHomotopy (RelativeTriple.identity F.Fiber A) d :=
    { iso := (a.symm.pullback πA).trans H.iso
      map_zero := by
        intro x v
        change H.iso.linearEquiv (0, x) ((a.linearEquiv x).symm v) = v
        exact (H.map_zero x ((a.linearEquiv x).symm v)).trans
          ((a.linearEquiv x).apply_symm_apply v)
      map_one := by
        intro x v
        exact H.map_one x ((a.linearEquiv x).symm v) }
  have hd : d.IsElementary := ⟨K⟩
  obtain ⟨e, he⟩ := d.exists_extension_of_isElementary A hA hd
  -- This same global extension supplies the target map of the original boundary square.
  apply BundleTriple.kZeroClass_eq_of_isIsomorphic
  refine ⟨Iso.refl E.Fiber, e, ?_⟩
  intro x v
  have h := congrArg (fun q : RelativeTriple F.Fiber F.Fiber A ↦
    q.linearEquiv x (a.linearEquiv x v)) he
  exact h.trans (congrArg (b.linearEquiv x) ((a.linearEquiv x).symm_apply_apply v))

/-- Map stable classes to the group using the original generators. -/
def stableTripleClassToKZero (A : Set X) : StableTripleClass A → TripleKZero A :=
  Quotient.lift BundleTriple.kZeroClass
    (fun a b h ↦ BundleTriple.kZeroClass_eq_of_isStablyIsomorphic a b h)

/-- The stable quotient and the presented group have the same elements. -/
theorem stableTripleClassToKZero_bijective (A : Set X) (hA : IsClosed A) :
    Function.Bijective (stableTripleClassToKZero A) := by
  /- Injectivity is the exact stable-equivalence criterion for equal group
  classes. Surjectivity follows from representation of every group class by a single triple. -/
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        exact (a.stableClass_eq_iff b).mpr
          ((a.kZeroClass_eq_iff_stable A hA b).mp hxy)
  · intro z
    obtain ⟨a, ha⟩ := bundleTriple_kZeroClass_surjective A hA z
    exact ⟨a.stableClass, ha⟩

/-- Identify stable classes with the group through their actual generator map. -/
def stableTripleClassKZeroEquiv (A : Set X) (hA : IsClosed A) :
    StableTripleClass A ≃ TripleKZero A :=
  Equiv.ofBijective _ (stableTripleClassToKZero_bijective A hA)

end AtiyahSinger.ComplexBundle
