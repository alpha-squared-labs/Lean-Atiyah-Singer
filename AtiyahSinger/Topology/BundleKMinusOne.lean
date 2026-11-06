/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.BundleIsoHomotopyRotation
public import AtiyahSinger.Topology.FiniteBundle
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# K^{-1} presented by actual bundle automorphisms

Public module ID: M1583.

Karoubi II.3 defines negative K-theory from pairs (E,α), where α is an actual
automorphism of E. An elementary pair has an automorphism homotopic to identity
through bundle isomorphisms. This module takes the free abelian group on these
pairs modulo isomorphism, direct-sum and elementary relations.

Both maps and homotopies use the original bundle total topologies. Isomorphism
means a commuting square, not equality of underlying bundle classes. The general
zero criterion permits stabilization by an arbitrary finite bundle; trivial
stabilization is not inserted without a complement theorem. Compact Hausdorff
hypotheses occur only in the final existence of a trivial-bundle representative.

The quotient lift uses the actual FreeAbelianGroup and QuotientAddGroup lifts,
with specified generator values. No additive map is selected from an existence
theorem. The presentation does not identify this group with a suspension group,
construct a pair boundary, or assume a Puppe exact sequence.
Sources: Karoubi, K-Theory, II.3.3--3.7. The arbitrary-base statements extend
the same block-matrix and stabilization proofs to jointly continuous bundle
homotopies; they do not require the compact-base Banach-category framework.
The trivial representative is the surjectivity step of II.3.16--3.17, using
the finite-complement theorem of SG I.9.9 / Karoubi I.6.
The defining relations, block-rotation laws, arbitrary-base stable-zero criterion
and compact trivial representatives are proved using actual bundle homotopies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A finite complex vector bundle equipped with an actual continuous automorphism. -/
structure BundleAutomorphism (X : Type*) [TopologicalSpace X] where
  /-- The original locally finite-rank bundle. -/
  bundle : FiniteBundle X
  /-- Its actual automorphism, including forward and inverse total-space continuity. -/
  automorphism : Iso bundle.Fiber bundle.Fiber

/-- The identity automorphism of the specified bundle. -/
@[reducible]
def BundleAutomorphism.identity (E : FiniteBundle X) : BundleAutomorphism X where
  bundle := E
  automorphism := Iso.refl E.Fiber

/-- Direct sum retains the two actual bundle automorphisms on their respective summands. -/
@[reducible]
def BundleAutomorphism.sum (a b : BundleAutomorphism X) : BundleAutomorphism X where
  bundle := a.bundle.sum b.bundle
  automorphism := a.automorphism.sum b.automorphism

/-- Reverse the same automorphism, leaving its bundle unchanged. -/
@[reducible]
def BundleAutomorphism.inverse (a : BundleAutomorphism X) : BundleAutomorphism X where
  bundle := a.bundle
  automorphism := a.automorphism.symm

/-- Pullback applies the original automorphism at f(y) on the original pulled-back fiber. -/
@[reducible]
def BundleAutomorphism.pullback (a : BundleAutomorphism X) (f : C(Y, X)) :
    BundleAutomorphism Y where
  bundle := a.bundle.pullback f
  automorphism := a.automorphism.pullback f

/-- Isomorphism of automorphism pairs is a specified commuting conjugacy square. -/
def BundleAutomorphism.IsIsomorphic (a b : BundleAutomorphism X) : Prop :=
  ∃ e : Iso a.bundle.Fiber b.bundle.Fiber,
    ∀ (x : X) (v : a.bundle.Fiber x),
      e.linearEquiv x (a.automorphism.linearEquiv x v) =
        b.automorphism.linearEquiv x (e.linearEquiv x v)

/-- An elementary pair has a jointly continuous path from identity to its automorphism. -/
def BundleAutomorphism.IsElementary (a : BundleAutomorphism X) : Prop :=
  Nonempty (IsoHomotopy (Iso.refl a.bundle.Fiber) a.automorphism)

/-- The isomorphism, direct-sum and elementary relations of the automorphism presentation. -/
def bundleKMinusOneRelations (X : Type*) [TopologicalSpace X] :
    AddSubgroup (FreeAbelianGroup (BundleAutomorphism X)) :=
  AddSubgroup.closure
    ({z | ∃ a b : BundleAutomorphism X, a.IsIsomorphic b ∧
      z = FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ a b : BundleAutomorphism X,
      z = FreeAbelianGroup.of (a.sum b) - FreeAbelianGroup.of a - FreeAbelianGroup.of b} ∪
    {z | ∃ a : BundleAutomorphism X, a.IsElementary ∧ z = FreeAbelianGroup.of a})

/-- The abelian group presented by finite bundle automorphisms and elementary homotopy. -/
abbrev BundleKMinusOne (X : Type*) [TopologicalSpace X] : Type _ :=
  FreeAbelianGroup (BundleAutomorphism X) ⧸ bundleKMinusOneRelations X

/-- The actual quotient image of an automorphism-pair generator. -/
def BundleAutomorphism.kMinusOneClass (a : BundleAutomorphism X) : BundleKMinusOne X :=
  QuotientAddGroup.mk' (bundleKMinusOneRelations X) (FreeAbelianGroup.of a)

/-- Isomorphic automorphism pairs have equal classes. -/
theorem BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic (a b : BundleAutomorphism X)
    (h : a.IsIsomorphic b) : a.kMinusOneClass = b.kMinusOneClass := by
  /- The difference of the two generators is one of the explicit isomorphism
  relations. Its image under the quotient homomorphism vanishes. The conjugating
  map commutes with the original automorphisms on every original fiber. -/
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inl ⟨a, b, h, rfl⟩)

/-- Direct sum of automorphism pairs represents addition. -/
theorem BundleAutomorphism.kMinusOneClass_sum (a b : BundleAutomorphism X) :
    (a.sum b).kMinusOneClass = a.kMinusOneClass + b.kMinusOneClass := by
  /- The displayed difference is exactly a defining direct-sum relation. The
  quotient map is additive and kills that relation generator. -/
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' (bundleKMinusOneRelations X)) _ -
    ((QuotientAddGroup.mk' (bundleKMinusOneRelations X)) _ +
      (QuotientAddGroup.mk' (bundleKMinusOneRelations X)) _) = 0
  rw [← map_add, ← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inl (Or.inr ⟨a, b, by abel⟩)

/-- Every elementary automorphism pair represents zero. -/
theorem BundleAutomorphism.kMinusOneClass_eq_zero_of_isElementary (a : BundleAutomorphism X)
    (h : a.IsElementary) : a.kMinusOneClass = 0 := by
  /- The actual generator of a belongs to the elementary part of the relation
  set. Its image in the quotient is therefore zero. In particular, an identity
  automorphism is elementary by the constant original-bundle homotopy. -/
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply AddSubgroup.subset_closure
  exact Or.inr ⟨a, h, rfl⟩

/-- The original inverse pair contracts by signed bundle interchanges (KA II.3.4). -/
theorem BundleAutomorphism.isElementary_sum_inverse (a : BundleAutomorphism X) :
    (a.sum a.inverse).IsElementary := by
  let := sumTopology (E := a.bundle.Fiber) (F := a.bundle.Fiber)
  -- Each signed interchange is connected to the identity by the explicit shear path.
  obtain ⟨s, hs, ⟨H⟩⟩ := a.automorphism.exists_signed_swap_homotopy
  obtain ⟨r, hr, ⟨K⟩⟩ := (Iso.refl a.bundle.Fiber).exists_signed_swap_homotopy
  obtain ⟨L⟩ := H.nonempty_comp K.nonempty_inverse.some
  -- Compose with the inverse signed interchange for identity to obtain the diagonal pair.
  have hstart : (Iso.refl (a.bundle.sum a.bundle).Fiber).trans
      (Iso.refl (a.bundle.sum a.bundle).Fiber).symm =
      Iso.refl (a.bundle.sum a.bundle).Fiber := by
    apply Iso.ext
    intro x
    rfl
  have hend : s.trans r.symm = (a.sum a.inverse).automorphism := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    apply (r.linearEquiv x).injective
    change r.linearEquiv x ((r.linearEquiv x).symm (s.linearEquiv x v)) = _
    rw [LinearEquiv.apply_symm_apply, hs, hr]
    rfl
  exact ⟨hstart ▸ hend ▸ L⟩

/-- KA II.3.4: inverting an automorphism represents additive negation. -/
theorem BundleAutomorphism.kMinusOneClass_inverse (a : BundleAutomorphism X) :
    a.inverse.kMinusOneClass = -a.kMinusOneClass := by
  /- Compose the signed-swap homotopy of α with the inverse of the
  signed-swap homotopy of identity on E⊕E. Their elementary shear paths use
  only the original automorphism and its continuous inverse. The composite
  starts at identity and ends at diag(α,α⁻¹), so a.sum a.inverse is elementary.
  Its zero class and direct-sum additivity identify the inverse-pair class
  with -[a]. No compactness, metric or trivial complement is required. -/
  have hzero := (a.sum a.inverse).kMinusOneClass_eq_zero_of_isElementary
    a.isElementary_sum_inverse
  rw [BundleAutomorphism.kMinusOneClass_sum] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

/-- KA II.3.5: homotopies through automorphisms of one bundle preserve the class. -/
theorem BundleAutomorphism.kMinusOneClass_eq_of_homotopy (E : FiniteBundle X)
    (a b : Iso E.Fiber E.Fiber) (H : IsoHomotopy a b) :
    (⟨E, a⟩ : BundleAutomorphism X).kMinusOneClass =
      (⟨E, b⟩ : BundleAutomorphism X).kMinusOneClass := by
  /- Stage 1: add the constant inverse b⁻¹ as a second summand to H. This gives
  a path from diag(a,b⁻¹) to diag(b,b⁻¹). Concatenate with the block-rotation
  contraction of the latter to identity, and reverse the path. Thus the actual
  pair (E⊕E,diag(a,b⁻¹)) is elementary.
  Stage 2: direct-sum additivity and the preceding inverse formula identify its
  zero class with [a]-[b]. This argument does not use the later composition
  formula, avoiding a circular proof of the two standard K^{-1} laws. -/
  let := sumTopology (E := E.Fiber) (F := E.Fiber)
  let A : BundleAutomorphism X := ⟨E, a⟩
  let B : BundleAutomorphism X := ⟨E, b⟩
  -- Add the fixed inverse of the terminal endpoint, retaining the original bundle.
  obtain ⟨K⟩ := H.nonempty_sum_refl b.symm
  obtain ⟨L⟩ := B.isElementary_sum_inverse
  have he : (A.sum B.inverse).IsElementary :=
    L.nonempty_trans K.symm
  have hzero := (A.sum B.inverse).kMinusOneClass_eq_zero_of_isElementary he
  -- The diagonal contraction and direct-sum relation turn this into equality of classes.
  rw [BundleAutomorphism.kMinusOneClass_sum,
    BundleAutomorphism.kMinusOneClass_inverse] at hzero
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hzero)

/-- KA II.3.6: composition on one bundle adds the two automorphism classes. -/
theorem BundleAutomorphism.kMinusOneClass_trans (E : FiniteBundle X)
    (a b : Iso E.Fiber E.Fiber) :
    (⟨E, a.trans b⟩ : BundleAutomorphism X).kMinusOneClass =
      (⟨E, a⟩ : BundleAutomorphism X).kMinusOneClass +
        (⟨E, b⟩ : BundleAutomorphism X).kMinusOneClass := by
  /- Stage 1: the standard block rotation compares diag(a,b) with diag(b∘a,id)
  on the same E⊕E. Here a.trans b means first a and then b, so its fiber action
  is b∘a. The path and its inverse consist of the same continuous bundle maps
  and elementary shears for the signed interchange.
  Stage 2: apply the preceding, independently established homotopy invariance.
  Direct-sum additivity and elementary vanishing of the identity summand give
  the formula. No boundary exactness or suspension comparison enters this law. -/
  let := sumTopology (E := E.Fiber) (F := E.Fiber)
  let D := a.sum (Iso.refl E.Fiber)
  let C := (Iso.refl E.Fiber).sum b
  -- Rotate the second automorphism into the first summand, preserving invertibility.
  obtain ⟨r, hr, ⟨K⟩⟩ := (Iso.refl E.Fiber).exists_signed_swap_homotopy
  obtain ⟨L⟩ := K.nonempty_comp (IsoHomotopy.refl C)
  obtain ⟨M⟩ := L.nonempty_comp K.nonempty_inverse.some
  obtain ⟨N⟩ := (IsoHomotopy.refl D).nonempty_comp M
  have hstart : D.trans (((Iso.refl (E.sum E).Fiber).trans C).trans
      (Iso.refl (E.sum E).Fiber).symm) = a.sum b := by
    apply Iso.ext
    intro x
    rfl
  have hend : D.trans ((r.trans C).trans r.symm) =
      (a.trans b).sum (Iso.refl E.Fiber) := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    apply (r.linearEquiv x).injective
    change r.linearEquiv x ((r.linearEquiv x).symm
      (C.linearEquiv x (r.linearEquiv x (D.linearEquiv x v)))) = _
    rw [LinearEquiv.apply_symm_apply, hr, hr]
    rfl
  have H : IsoHomotopy (a.sum b) ((a.trans b).sum (Iso.refl E.Fiber)) :=
    hstart ▸ hend ▸ N
  -- Apply homotopy invariance, then remove the constant identity summand.
  have heq := BundleAutomorphism.kMinusOneClass_eq_of_homotopy (E.sum E)
    (a.sum b) ((a.trans b).sum (Iso.refl E.Fiber)) H
  change ((⟨E, a⟩ : BundleAutomorphism X).sum ⟨E, b⟩).kMinusOneClass =
    ((⟨E, a.trans b⟩ : BundleAutomorphism X).sum
      (BundleAutomorphism.identity E)).kMinusOneClass at heq
  have hi := (BundleAutomorphism.identity E).kMinusOneClass_eq_zero_of_isElementary
    (IsoHomotopy.nonempty_refl (Iso.refl E.Fiber))
  simpa only [BundleAutomorphism.kMinusOneClass_sum, hi, add_zero] using heq.symm

/-- Every element of the automorphism presentation has a single-pair representative. -/
theorem bundleAutomorphism_kMinusOneClass_surjective :
    Function.Surjective (BundleAutomorphism.kMinusOneClass (X := X)) := by
  /- Represent a quotient element by a finite integral combination of free
  generators. Replace each negative generator by the inverse automorphism pair,
  and combine all remaining terms by direct sum. For an empty expression use
  the identity on the zero-rank trivial bundle, which is elementary. -/
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (bundleKMinusOneRelations X) z
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
      let E : FiniteBundle X := FiniteBundle.trivial X 0
      let := E.totalTopology
      refine ⟨BundleAutomorphism.identity E, ?_⟩
      have hi := (BundleAutomorphism.identity E).kMinusOneClass_eq_zero_of_isElementary
        (IsoHomotopy.nonempty_refl (Iso.refl E.Fiber))
      exact hi.trans (map_zero _).symm
  | of a => exact ⟨a, rfl⟩
  | neg a _ =>
      exact ⟨a.inverse, a.kMinusOneClass_inverse.trans (map_neg _ _).symm⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a.sum b, ?_⟩
      rw [BundleAutomorphism.kMinusOneClass_sum, ha, hb, map_add]

/-- A generator assignment respecting all defining relations kills the relation subgroup. -/
theorem bundleKMinusOneRelations_le_ker (X : Type*) [TopologicalSpace X]
    {G : Type*} [AddCommGroup G] (v : BundleAutomorphism X → G)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (he : ∀ a, a.IsElementary → v a = 0) :
    bundleKMinusOneRelations X ≤ (FreeAbelianGroup.lift v).ker := by
  /- Extend v by the standard free abelian group lift. The three assumptions
  annihilate respectively the isomorphism differences, direct-sum differences
  and elementary generators. Its kernel is an additive subgroup, hence contains
  the subgroup generated by their union. This verifies the actual quotient-lift
  side condition, without selecting an unspecified additive homomorphism. -/
  apply (AddSubgroup.closure_le _).mpr
  rintro x ((⟨a, b, hab, rfl⟩ | ⟨a, b, rfl⟩) | ⟨a, ha, rfl⟩)
  · change (FreeAbelianGroup.lift v) (_ - _) = 0
    simp [hi a b hab]
  · change (FreeAbelianGroup.lift v) (_ - _ - _) = 0
    simp [hs a b]
  · change (FreeAbelianGroup.lift v) (FreeAbelianGroup.of a) = 0
    simpa only [FreeAbelianGroup.lift_apply_of] using he a ha

/-- The actual quotient lift with specified values on all automorphism generators. -/
def bundleKMinusOneLift (X : Type*) [TopologicalSpace X]
    {G : Type*} [AddCommGroup G] (v : BundleAutomorphism X → G)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (he : ∀ a, a.IsElementary → v a = 0) : BundleKMinusOne X →+ G :=
  QuotientAddGroup.lift (bundleKMinusOneRelations X) (FreeAbelianGroup.lift v)
    (fun _ hx ↦ bundleKMinusOneRelations_le_ker X v hi hs he hx)

/-- Evaluating the actual quotient lift on a generator returns its prescribed value. -/
theorem bundleKMinusOneLift_apply (X : Type*) [TopologicalSpace X]
    {G : Type*} [AddCommGroup G] (v : BundleAutomorphism X → G)
    (hi : ∀ a b, a.IsIsomorphic b → v a = v b)
    (hs : ∀ a b, v (a.sum b) = v a + v b)
    (he : ∀ a, a.IsElementary → v a = 0) (a : BundleAutomorphism X) :
    bundleKMinusOneLift X v hi hs he a.kMinusOneClass = v a := by
  /- Evaluate QuotientAddGroup.lift on the quotient of FreeAbelianGroup.of a,
  then evaluate FreeAbelianGroup.lift on that same generator. Both are the
  defining evaluation formulas of the specified constructors. -/
  simp [bundleKMinusOneLift, BundleAutomorphism.kMinusOneClass]

section StableZeroCriterion

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology

/-- KA II.3.7: vanishing means elementary homotopy after finite-bundle stabilization. -/
theorem BundleAutomorphism.kMinusOneClass_eq_zero_iff (a : BundleAutomorphism X) :
    a.kMinusOneClass = 0 ↔ ∃ F : FiniteBundle X,
      (a.sum (BundleAutomorphism.identity F)).IsElementary := by
  classical
  /- Karoubi's elementary-stable quotient makes this criterion immediate from its
  definition. For the original free-abelian presentation, compare with the group
  completion of homotopy-conjugacy classes and then remove one common summand
  using its actual inverse automorphism. No trivial complement is required. -/
  -- First retain the original bundle topologies through conjugation and direct sum.
  have hconj (E F : FiniteBundle X) (e : Iso E.Fiber F.Fiber)
      (a b : Iso E.Fiber E.Fiber) (H : IsoHomotopy a b) :
      Nonempty (IsoHomotopy ((e.symm.trans a).trans e) ((e.symm.trans b).trans e)) := by
    obtain ⟨K⟩ := (IsoHomotopy.refl e.symm).nonempty_comp H
    exact K.nonempty_comp (IsoHomotopy.refl e)
  have hsum (E F : FiniteBundle X) (a₀ a₁ : Iso E.Fiber E.Fiber)
      (b₀ b₁ : Iso F.Fiber F.Fiber) (H : IsoHomotopy a₀ a₁) (K : IsoHomotopy b₀ b₁) :
      Nonempty (IsoHomotopy (a₀.sum b₀) (a₁.sum b₁)) := by
    obtain ⟨L⟩ := H.nonempty_sum_refl b₀
    obtain ⟨M⟩ := K.nonempty_sum_refl a₁
    obtain ⟨N⟩ := hconj (F.sum E) (E.sum F) sumCommIso _ _ M
    have h₀ : ((sumCommIso (E := F.Fiber) (F := E.Fiber)).symm.trans
        (b₀.sum a₁)).trans sumCommIso = a₁.sum b₀ := by
      apply Iso.ext
      intro x
      rfl
    have h₁ : ((sumCommIso (E := F.Fiber) (F := E.Fiber)).symm.trans
        (b₁.sum a₁)).trans sumCommIso = a₁.sum b₁ := by
      apply Iso.ext
      intro x
      rfl
    exact L.nonempty_trans (h₀ ▸ h₁ ▸ N)
  let R (a b : BundleAutomorphism X) : Prop :=
    ∃ e : Iso a.bundle.Fiber b.bundle.Fiber,
      Nonempty (IsoHomotopy a.automorphism ((e.trans b.automorphism).trans e.symm))
  have hiso (a b : BundleAutomorphism X) (h : a.IsIsomorphic b) : R a b := by
    obtain ⟨e, he⟩ := h
    refine ⟨e, ?_⟩
    have hendpoint : (e.trans b.automorphism).trans e.symm = a.automorphism := by
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro v
      apply (e.linearEquiv x).injective
      change e.linearEquiv x ((e.linearEquiv x).symm
        (b.automorphism.linearEquiv x (e.linearEquiv x v))) = _
      rw [LinearEquiv.apply_symm_apply]
      exact (he x v).symm
    rw [hendpoint]
    exact IsoHomotopy.nonempty_refl _
  have hrefl (a : BundleAutomorphism X) : R a a := by
    apply hiso
    exact ⟨Iso.refl a.bundle.Fiber, fun _ _ ↦ rfl⟩
  have hsymm (a b : BundleAutomorphism X) (hab : R a b) : R b a := by
    obtain ⟨e, ⟨H⟩⟩ := hab
    refine ⟨e.symm, ?_⟩
    obtain ⟨K⟩ := hconj a.bundle b.bundle e _ _ H.symm
    have hstart : (e.symm.trans ((e.trans b.automorphism).trans e.symm)).trans e =
        b.automorphism := by
      apply Iso.ext
      intro x
      ext v
      simp [Iso.trans, Iso.symm]
    exact ⟨hstart ▸ K⟩
  have htrans (a b c : BundleAutomorphism X) (hab : R a b) (hbc : R b c) : R a c := by
    obtain ⟨e, ⟨H⟩⟩ := hab
    obtain ⟨f, ⟨K⟩⟩ := hbc
    refine ⟨e.trans f, ?_⟩
    obtain ⟨L⟩ := hconj b.bundle a.bundle e.symm _ _ K
    have hstart : (e.symm.symm.trans b.automorphism).trans e.symm =
        (e.trans b.automorphism).trans e.symm := by
      apply Iso.ext
      intro x
      rfl
    obtain ⟨M⟩ := H.nonempty_trans (hstart ▸ L)
    convert! (show Nonempty (IsoHomotopy _ _) from ⟨M⟩) using 1
  have hsumR (a a' b b' : BundleAutomorphism X)
      (haa' : R a a') (hbb' : R b b') : R (a.sum b) (a'.sum b') := by
    obtain ⟨e, ⟨H⟩⟩ := haa'
    obtain ⟨f, ⟨K⟩⟩ := hbb'
    refine ⟨e.sum f, ?_⟩
    obtain ⟨L⟩ := hsum a.bundle b.bundle _ _ _ _ H K
    convert! (show Nonempty (IsoHomotopy _ _) from ⟨L⟩) using 1
  let s : Setoid (BundleAutomorphism X) :=
    ⟨R, ⟨hrefl, fun h ↦ hsymm _ _ h, fun h k ↦ htrans _ _ _ h k⟩⟩
  let M := Quotient s
  let cls : BundleAutomorphism X → M := Quotient.mk s
  let Z := BundleAutomorphism.identity (FiniteBundle.trivial X 0)
  let add : M → M → M := Quotient.map₂ BundleAutomorphism.sum (by
    intro a a' ha b b' hb
    exact hsumR a a' b b' ha hb)
  -- The standard coordinate comparisons give a commutative monoid, without cancellation.
  have hcomm (a b : BundleAutomorphism X) : R (a.sum b) (b.sum a) := by
    apply hiso
    exact ⟨sumCommIso, fun _ _ ↦ rfl⟩
  have hassoc (a b c : BundleAutomorphism X) :
      R ((a.sum b).sum c) (a.sum (b.sum c)) := by
    apply hiso
    refine ⟨FiniteBundle.sumAssocIso _ _ _, ?_⟩
    intro x v
    rw [FiniteBundle.sumAssocIso_apply, FiniteBundle.sumAssocIso_apply]
    rfl
  have hzero (a : BundleAutomorphism X) : R (a.sum Z) a := by
    apply hiso
    obtain ⟨e, he⟩ := a.bundle.exists_sum_zero_iso
    refine ⟨e, ?_⟩
    intro x v
    change e.linearEquiv x ((a.automorphism.linearEquiv x v.1), v.2) =
      a.automorphism.linearEquiv x (e.linearEquiv x v)
    rw [he, he]
  let : AddCommMonoid M := {
    add := add
    zero := cls Z
    add_assoc := fun x y z ↦ Quotient.inductionOn₃ x y z
      (fun a b c ↦ Quotient.sound (hassoc a b c))
    zero_add := fun x ↦ Quotient.inductionOn x
      (fun a ↦ Quotient.sound (htrans _ _ _ (hcomm Z a) (hzero a)))
    add_zero := fun x ↦ Quotient.inductionOn x (fun a ↦ Quotient.sound (hzero a))
    add_comm := fun x y ↦ Quotient.inductionOn₂ x y
      (fun a b ↦ Quotient.sound (hcomm a b))
    nsmul := @nsmulRec M ⟨cls Z⟩ ⟨add⟩
    nsmul_zero := fun _ ↦ rfl
    nsmul_succ := fun _ _ ↦ rfl }
  let v (a : BundleAutomorphism X) : Algebra.GrothendieckAddGroup M :=
    Algebra.GrothendieckAddGroup.of (cls a) -
      Algebra.GrothendieckAddGroup.of (cls (BundleAutomorphism.identity a.bundle))
  -- Subtract the identity on the same bundle to kill the original presentation relations.
  have hvIso (a b : BundleAutomorphism X) (hab : a.IsIsomorphic b) : v a = v b := by
    have h₁ : cls a = cls b := Quotient.sound (hiso a b hab)
    have h₂ : cls (BundleAutomorphism.identity a.bundle) =
        cls (BundleAutomorphism.identity b.bundle) := by
      apply Quotient.sound
      apply hiso
      obtain ⟨e, _⟩ := hab
      exact ⟨e, fun _ _ ↦ rfl⟩
    dsimp only [v]
    rw [h₁, h₂]
  have hvSum (a b : BundleAutomorphism X) : v (a.sum b) = v a + v b := by
    have h₁ : cls (a.sum b) = cls a + cls b := rfl
    have h₂ : cls (BundleAutomorphism.identity (a.sum b).bundle) =
        cls (BundleAutomorphism.identity a.bundle) +
          cls (BundleAutomorphism.identity b.bundle) := by
      apply Quotient.sound
      apply hiso
      exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
    dsimp only [v]
    rw [h₁, h₂, map_add, map_add]
    abel
  have hvElementary (a : BundleAutomorphism X) (ha : a.IsElementary) : v a = 0 := by
    have h : cls a = cls (BundleAutomorphism.identity a.bundle) := by
      apply Quotient.sound
      refine ⟨Iso.refl _, ?_⟩
      obtain ⟨H⟩ := ha
      exact ⟨H.symm⟩
    dsimp only [v]
    rw [h, sub_self]
  constructor
  · intro ha
    -- Effective equality in the group completion gives one actual common automorphism.
    have hv : v a = 0 := by
      rw [← bundleKMinusOneLift_apply X v hvIso hvSum hvElementary a, ha, map_zero]
    have heq : Algebra.GrothendieckAddGroup.of (cls a) =
        Algebra.GrothendieckAddGroup.of (cls (BundleAutomorphism.identity a.bundle)) :=
      sub_eq_zero.mp hv
    obtain ⟨c, hc⟩ :=
      (AddSubmonoid.LocalizationMap.eq_iff_exists (AddLocalization.addMonoidOf
        (⊤ : AddSubmonoid M))).mp heq
    obtain ⟨b, hb⟩ := Quotient.exists_rep (c : M)
    rw [← hb] at hc
    have hab : R (b.sum a) (b.sum (BundleAutomorphism.identity a.bundle)) :=
      Quotient.exact hc
    -- Add the inverse of the unwanted automorphism, then move a to the first block.
    let d := b.sum b.inverse
    let F := b.bundle.sum b.bundle
    let iE := BundleAutomorphism.identity a.bundle
    let iF := BundleAutomorphism.identity F
    have hswitch (p q r : BundleAutomorphism X) :
        R ((p.sum q).sum r) (q.sum (p.sum r)) :=
      htrans _ _ _ (hsumR _ _ _ _ (hcomm p q) (hrefl r)) (hassoc q p r)
    have hadded : R ((b.sum a).sum b.inverse) ((b.sum iE).sum b.inverse) :=
      hsumR _ _ _ _ hab (hrefl b.inverse)
    have hshifted : R (a.sum d) (iE.sum d) :=
      htrans _ _ _ (hsymm _ _ (hswitch b a b.inverse))
        (htrans _ _ _ hadded (hswitch b iE b.inverse))
    -- The same inverse-pair rotation contracts d on its actual bundle F.
    have hd : R d iF := by
      refine ⟨Iso.refl F.Fiber, ?_⟩
      obtain ⟨H⟩ := b.isElementary_sum_inverse
      exact ⟨H.symm⟩
    have hstart : R (a.sum iF) (a.sum d) :=
      hsumR _ _ _ _ (hrefl a) (hsymm _ _ hd)
    have hend : R (iE.sum d) (iE.sum iF) :=
      hsumR _ _ _ _ (hrefl iE) hd
    have hfinal : R (a.sum iF) (iE.sum iF) :=
      htrans _ _ _ hstart (htrans _ _ _ hshifted hend)
    -- Conjugation of this same identity is identity, leaving a genuine elementary stabilization.
    obtain ⟨e, ⟨H⟩⟩ := hfinal
    have hidentity : (e.trans (iE.sum iF).automorphism).trans e.symm =
        Iso.refl (a.sum iF).bundle.Fiber := by
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro v
      change (e.linearEquiv x).symm (e.linearEquiv x v) = v
      exact (e.linearEquiv x).symm_apply_apply v
    refine ⟨F, ?_⟩
    exact ⟨(hidentity ▸ H).symm⟩
  · rintro ⟨F, hF⟩
    have h := (a.sum (BundleAutomorphism.identity F)).kMinusOneClass_eq_zero_of_isElementary hF
    have hi := (BundleAutomorphism.identity F).kMinusOneClass_eq_zero_of_isElementary
      (IsoHomotopy.nonempty_refl (Iso.refl F.Fiber))
    simpa only [BundleAutomorphism.kMinusOneClass_sum, hi, add_zero] using h

end StableZeroCriterion

attribute [local instance] trivialTopology

/-- On a compact Hausdorff base every pair class has a finite trivial-bundle representative. -/
theorem BundleAutomorphism.exists_trivial_representative [CompactSpace X] [T2Space X]
    (a : BundleAutomorphism X) :
    ∃ n : ℕ, ∃ b : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber,
      (⟨FiniteBundle.trivial X n, b⟩ : BundleAutomorphism X).kMinusOneClass =
        a.kMinusOneClass := by
  /- Stage 1: the specified idempotent presentation supplies its complementary
  image F and an isomorphism E⊕F ≃ X×ℂ^p.size. Stabilize a by identity
  on this same F; the added elementary class is zero.
  Stage 2: conjugate the original block automorphism along that isomorphism.
  The resulting automorphism is on the stated trivial bundle and its conjugacy
  square preserves the stabilized pair class. This provides the claimed n and b.
  Compactness is used only for the global finite trivial complement; it is not
  inserted into the preceding arbitrary-bundle stabilization criterion. -/
  obtain ⟨p, ⟨e⟩⟩ := exists_complement_bundle (E := a.bundle.Fiber)
  let := p.complement.fiberTotalSpaceTopology
  let := p.complement.isFiniteRank_fiber
  let := sumTopology (E := a.bundle.Fiber) (F := fun x ↦ p.complement.fiber x)
  let F : FiniteBundle X := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let A := a.sum (BundleAutomorphism.identity F)
  let b : Iso (FiniteBundle.trivial X p.size).Fiber (FiniteBundle.trivial X p.size).Fiber :=
    (e.symm.trans A.automorphism).trans e
  -- Transport the same stabilized automorphism along the specified complement isomorphism.
  have hi : A.IsIsomorphic ⟨FiniteBundle.trivial X p.size, b⟩ := by
    refine ⟨e, ?_⟩
    intro x v
    change e.linearEquiv x (A.automorphism.linearEquiv x v) =
      e.linearEquiv x (A.automorphism.linearEquiv x
        ((e.linearEquiv x).symm (e.linearEquiv x v)))
    rw [LinearEquiv.symm_apply_apply]
  have heq := A.kMinusOneClass_eq_of_isIsomorphic _ hi
  have hzero := (BundleAutomorphism.identity F).kMinusOneClass_eq_zero_of_isElementary
    (IsoHomotopy.nonempty_refl (Iso.refl F.Fiber))
  -- Stabilization adds an elementary identity pair, hence leaves the class unchanged.
  refine ⟨p.size, b, ?_⟩
  simpa only [A, BundleAutomorphism.kMinusOneClass_sum, hzero, add_zero] using heq.symm

end AtiyahSinger.ComplexBundle
