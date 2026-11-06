/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneFunctor
public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# The compactified automorphism model of K^{-1}

Public module ID: M1650.

Karoubi II.4.1 defines compactly supported K^{-1} as the evaluation kernel on
one-point compactification, starting from the ordinary bundle-automorphism group.
This standard automorphism presentation is identified with the real-suspension
group CompactSupportK 1 in BundleKMinusOneSuspension. Its proper pullbacks use the
same one-point maps as compactly supported K-zero.

The reduced kernel and its pointed pullback make sense for the existing ordinary
automorphism presentation on arbitrary topological spaces. Compactness is only
used below for the compact-base comparison and the later homotopy arguments.
The point used for evaluation is PUnit in Type 0, with no auxiliary universe.
The reduced and proper functor laws and compact-base comparison are proved below.
The comparison uses clopen automorphism cutoffs on the same original quotient;
no vanishing theorem for the group of a point is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle OnePoint
open scoped unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Reduced automorphism K^{-1} is the kernel of restriction to the specified point. -/
def reducedBundleKMinusOne (x₀ : X) : AddSubgroup (BundleKMinusOne X) :=
  (bundleKMinusOnePullback (ContinuousMap.const PUnit.{1} x₀)).ker

/-- The actual pullback of a reduced automorphism class remains reduced for a pointed map. -/
theorem bundleKMinusOnePullback_mem_reduced (x₀ : X) (y₀ : Y)
    (f : C(X, Y)) (hf₀ : f x₀ = y₀) (a : BundleKMinusOne Y)
    (ha : a ∈ reducedBundleKMinusOne y₀) :
    bundleKMinusOnePullback f a ∈ reducedBundleKMinusOne x₀ := by
  /- Evaluate after the actual pullback. Contravariant composition identifies
  this with pullback along the constant map at f(x₀), which equals the constant
  map at y₀ by the pointed hypothesis. The original evaluation of a is zero.
  This only uses the quotient functor laws, so no compactness is needed. -/
  -- Evaluate the original composite pullback at the specified base point.
  change bundleKMinusOnePullback (ContinuousMap.const PUnit.{1} x₀)
    (bundleKMinusOnePullback f a) = 0
  change bundleKMinusOnePullback (ContinuousMap.const PUnit.{1} y₀) a = 0 at ha
  have hcomp : f.comp (ContinuousMap.const PUnit.{1} x₀) =
      ContinuousMap.const PUnit.{1} y₀ := by
    ext x
    exact hf₀
  rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hcomp]
  exact ha

/-- Pointed pullback restricted to the original evaluation kernels. -/
def reducedBundleKMinusOnePullback (x₀ : X) (y₀ : Y)
    (f : C(X, Y)) (hf₀ : f x₀ = y₀) :
    reducedBundleKMinusOne y₀ →+ reducedBundleKMinusOne x₀ where
  toFun a := ⟨bundleKMinusOnePullback f a.val,
    bundleKMinusOnePullback_mem_reduced x₀ y₀ f hf₀ a.val a.property⟩
  map_zero' := Subtype.ext (map_zero (bundleKMinusOnePullback f))
  map_add' a b := Subtype.ext (map_add (bundleKMinusOnePullback f) a.val b.val)

/-- KA II.4.1: compactly supported automorphism K^{-1} uses the actual infinity kernel. -/
abbrev CompactSupportBundleKMinusOne (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : Type _ :=
  reducedBundleKMinusOne (∞ : OnePoint X)

variable [LocallyCompactSpace X] [T2Space X]
  [LocallyCompactSpace Y] [T2Space Y] [LocallyCompactSpace Z] [T2Space Z]

/-- Proper pullback in the compactified automorphism model. -/
def compactSupportBundleKMinusOnePullback (f : C(X, Y)) (hf : IsProperMap f) :
    CompactSupportBundleKMinusOne Y →+ CompactSupportBundleKMinusOne X :=
  reducedBundleKMinusOnePullback ∞ ∞ (properOnePointMap f hf) rfl

/-- The identity acts as identity on the actual compactified automorphism kernel. -/
theorem compactSupportBundleKMinusOnePullback_id :
    compactSupportBundleKMinusOnePullback (ContinuousMap.id X) isProperMap_id =
      AddMonoidHom.id (CompactSupportBundleKMinusOne X) := by
  /- The extension of identity fixes every finite point and infinity. The
  ordinary automorphism pullback is therefore identity by its existing functor
  law. Restricting that equality to the same evaluation kernel gives the result. -/
  have hmap : properOnePointMap (ContinuousMap.id X) isProperMap_id =
      ContinuousMap.id (OnePoint X) := by
    ext x
    cases x using OnePoint.rec <;> rfl
  -- Compare the underlying elements of the original evaluation kernel.
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change bundleKMinusOnePullback (properOnePointMap (ContinuousMap.id X) isProperMap_id)
    a.val = a.val
  rw [hmap, bundleKMinusOnePullback_id]
  rfl

/-- Proper pullbacks compose using the same one-point extensions and evaluation kernels. -/
theorem compactSupportBundleKMinusOnePullback_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsProperMap f) (hg : IsProperMap g) :
    compactSupportBundleKMinusOnePullback (g.comp f) (hg.comp hf) =
      (compactSupportBundleKMinusOnePullback f hf).comp
        (compactSupportBundleKMinusOnePullback g hg) := by
  /- The one-point extension of g composed with f agrees pointwise with the
  composite of the two extensions, including infinity. Apply the ordinary
  automorphism pullback composition law and compare underlying kernel elements.
  No statement about arbitrary homotopies on a noncompact base is used. -/
  have hmap : properOnePointMap (g.comp f) (hg.comp hf) =
      (properOnePointMap g hg).comp (properOnePointMap f hf) := by
    ext x
    cases x using OnePoint.rec <;> rfl
  -- The same extension maps compose on finite points and fix infinity.
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change bundleKMinusOnePullback (properOnePointMap (g.comp f) (hg.comp hf)) a.val =
    bundleKMinusOnePullback (properOnePointMap f hf)
      (bundleKMinusOnePullback (properOnePointMap g hg) a.val)
  rw [hmap, bundleKMinusOnePullback_comp]
  rfl

/-- Pullback by an actual homeomorphism is bijective on the compactified kernel. -/
theorem compactSupportBundleKMinusOnePullback_bijective (e : X ≃ₜ Y) :
    Function.Bijective
      (compactSupportBundleKMinusOnePullback ⟨e, e.continuous⟩ e.isProperMap) := by
  /- The inverse homeomorphism is proper. The two proper pullbacks compose to
  identity by the preceding laws and the actual inverse formulas for e. Thus
  the inverse pullback gives an inverse on precisely these infinity kernels. -/
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hfg : g.comp f = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hgf : f.comp g = ContinuousMap.id Y := by
    ext y
    exact e.apply_symm_apply y
  -- The actual inverse homeomorphism gives both inverse pullback identities.
  let u := compactSupportBundleKMinusOnePullback f e.isProperMap
  let v := compactSupportBundleKMinusOnePullback g e.symm.isProperMap
  have hleft : v.comp u = AddMonoidHom.id (CompactSupportBundleKMinusOne Y) := by
    dsimp [u, v]
    rw [← compactSupportBundleKMinusOnePullback_comp]
    simpa only [hgf] using (compactSupportBundleKMinusOnePullback_id (X := Y))
  have hright : u.comp v = AddMonoidHom.id (CompactSupportBundleKMinusOne X) := by
    dsimp [u, v]
    rw [← compactSupportBundleKMinusOnePullback_comp]
    simpa only [hfg] using (compactSupportBundleKMinusOnePullback_id (X := X))
  exact ⟨(show Function.LeftInverse v u from
      fun a ↦ DFunLike.congr_fun hleft a).injective,
    (show Function.RightInverse v u from
      fun a ↦ DFunLike.congr_fun hright a).surjective⟩

/-- Covariant transport by a homeomorphism is the specified inverse proper pullback. -/
def compactSupportBundleKMinusOneHomeomorphEquiv (e : X ≃ₜ Y) :
    CompactSupportBundleKMinusOne X ≃+ CompactSupportBundleKMinusOne Y :=
  AddEquiv.ofBijective
    (compactSupportBundleKMinusOnePullback ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap)
    (compactSupportBundleKMinusOnePullback_bijective e.symm)

/-- On a compact base, the comparison is actual restriction from its compactification. -/
def compactSupportBundleKMinusOneToAbsolute [CompactSpace X] :
    CompactSupportBundleKMinusOne X →+ BundleKMinusOne X :=
  (bundleKMinusOnePullback ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩).comp
    (reducedBundleKMinusOne (∞ : OnePoint X)).subtype

/-- KA II.4.1: the compactified automorphism presentation recovers the compact-base group. -/
theorem compactSupportBundleKMinusOneToAbsolute_bijective [CompactSpace X] :
    Function.Bijective (compactSupportBundleKMinusOneToAbsolute (X := X)) := by
  /- On the two clopen components of the compactification, cut an actual
  automorphism to identity on the other component. The original conjugacy,
  addition and elementary-homotopy relations make these cutoffs additive.
  Their sum recovers the original class by the composition law. Finite trivial
  representatives then identify each summand using its actual component
  restriction. Evaluation at infinity kills precisely the second summand,
  and a finite-side cutoff extends every class on X. The empty case is handled
  separately. This is the disjoint-union argument behind KA II.4.1, without
  point-group vanishing, a suspension comparison or compact-support exactness. -/
  classical
  -- On the empty base the ordinary group and the infinity evaluation kernel are both zero.
  rcases isEmpty_or_nonempty X with hX | hX
  · let := hX
    have hz (a : BundleKMinusOne X) : a = 0 := by
      obtain ⟨b, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective a
      apply b.kMinusOneClass_eq_zero_of_isElementary
      have hb : b.automorphism = Iso.refl b.bundle.Fiber := by
        apply Iso.ext
        intro x
        exact isEmptyElim x
      rw [BundleAutomorphism.IsElementary, hb]
      exact IsoHomotopy.nonempty_refl _
    have hk (a : CompactSupportBundleKMinusOne X) : a = 0 := by
      let i := ContinuousMap.const PUnit.{1} (∞ : OnePoint X)
      let p := ContinuousMap.const (OnePoint X) PUnit.unit
      have hip : i.comp p = ContinuousMap.id (OnePoint X) := by
        ext x
        cases x using OnePoint.rec with
        | infty => rfl
        | coe x => exact isEmptyElim x
      have ha : bundleKMinusOnePullback i a.val = 0 := a.property
      have h := congrArg (bundleKMinusOnePullback p) ha
      rw [← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hip,
        bundleKMinusOnePullback_id, map_zero] at h
      exact Subtype.ext h
    exact ⟨fun a b _ ↦ (hk a).trans (hk b).symm,
      fun a ↦ ⟨0, (map_zero _).trans (hz a).symm⟩⟩
  · let := hX
    -- A clopen cutoff keeps the original bundle and replaces only its automorphism by identity.
    let cut {Y : Type _} [TopologicalSpace Y] (S : Set Y) (hS : IsClopen S)
        (E : FiniteBundle Y) (α : Iso E.Fiber E.Fiber) : Iso E.Fiber E.Fiber :=
      { linearEquiv := fun y ↦ if y ∈ S then α.linearEquiv y else LinearEquiv.refl ℂ _
        continuous_total := by
          have hcl : IsClopen {z : TotalSpace Unit E.Fiber | z.proj ∈ S} :=
            hS.preimage continuous_proj
          have hc := Continuous.if (p := fun z : TotalSpace Unit E.Fiber ↦ z.proj ∈ S)
            (fun z hz ↦ (show False from by
              simp only [hcl.frontier_eq, Set.mem_empty_iff_false] at hz).elim)
            α.continuous_total continuous_id
          exact hc.congr (fun z ↦ by split_ifs <;> rfl)
        continuous_symm := by
          have hcl : IsClopen {z : TotalSpace Unit E.Fiber | z.proj ∈ S} :=
            hS.preimage continuous_proj
          have hc := Continuous.if (p := fun z : TotalSpace Unit E.Fiber ↦ z.proj ∈ S)
            (fun z hz ↦ (show False from by
              simp only [hcl.frontier_eq, Set.mem_empty_iff_false] at hz).elim)
            α.continuous_symm continuous_id
          exact hc.congr (fun z ↦ by split_ifs <;> rfl) }
    let cutPair (S : Set (OnePoint X)) (hS : IsClopen S)
        (a : BundleAutomorphism (OnePoint X)) : BundleAutomorphism (OnePoint X) :=
      ⟨a.bundle, cut S hS a.bundle a.automorphism⟩
    -- The same clopen cutoff respects conjugacy, block addition and actual cylinder homotopies.
    have hi (S : Set (OnePoint X)) (hS : IsClopen S)
        (a b : BundleAutomorphism (OnePoint X)) (hab : a.IsIsomorphic b) :
        (cutPair S hS a).kMinusOneClass = (cutPair S hS b).kMinusOneClass := by
      obtain ⟨e, he⟩ := hab
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨e, ?_⟩
      intro x v
      by_cases hx : x ∈ S
      · simpa [cutPair, cut, hx] using he x v
      · simp [cutPair, cut, hx]
    have hs (S : Set (OnePoint X)) (hS : IsClopen S)
        (a b : BundleAutomorphism (OnePoint X)) :
        (cutPair S hS (a.sum b)).kMinusOneClass =
          (cutPair S hS a).kMinusOneClass + (cutPair S hS b).kMinusOneClass := by
      let := sumTopology (E := a.bundle.Fiber) (F := b.bundle.Fiber)
      rw [← BundleAutomorphism.kMinusOneClass_sum]
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨Iso.refl (a.bundle.sum b.bundle).Fiber, ?_⟩
      intro x v
      by_cases hx : x ∈ S <;> simp [cutPair, cut, hx, BundleAutomorphism.sum, Iso.sum, Iso.refl]
    have he (S : Set (OnePoint X)) (hS : IsClopen S)
        (a : BundleAutomorphism (OnePoint X)) (ha : a.IsElementary) :
        (cutPair S hS a).kMinusOneClass = 0 := by
      obtain ⟨H⟩ := ha
      let p : C(I × OnePoint X, OnePoint X) := ⟨Prod.snd, continuous_snd⟩
      let W := cut (Prod.snd ⁻¹' S) (hS.preimage continuous_snd)
        (a.bundle.pullback p) H.iso
      apply BundleAutomorphism.kMinusOneClass_eq_zero_of_isElementary
      refine ⟨{ iso := W, map_zero := ?_, map_one := ?_ }⟩
      · intro x v
        by_cases hx : x ∈ S
        · simpa [W, cut, hx, p] using H.map_zero x v
        · simp [W, cut, hx, Iso.refl, cutPair, p]
          rfl
      · intro x v
        by_cases hx : x ∈ S
        · simpa [W, cut, cutPair, hx, p] using H.map_one x v
        · simp [W, cut, cutPair, hx, p]
          rfl
    let Q (S : Set (OnePoint X)) (hS : IsClopen S) :
        BundleKMinusOne (OnePoint X) →+ BundleKMinusOne (OnePoint X) :=
      bundleKMinusOneLift (OnePoint X) (fun a ↦ (cutPair S hS a).kMinusOneClass)
        (hi S hS) (hs S hS) (he S hS)
    have hQ (S : Set (OnePoint X)) (hS : IsClopen S)
        (a : BundleAutomorphism (OnePoint X)) :
        Q S hS a.kMinusOneClass = (cutPair S hS a).kMinusOneClass :=
      bundleKMinusOneLift_apply _ _ _ _ _ a
    -- The two cutoff automorphisms compose to precisely the original automorphism.
    have hsplit (S : Set (OnePoint X)) (hS : IsClopen S)
        (a : BundleKMinusOne (OnePoint X)) : a = Q S hS a + Q Sᶜ hS.compl a := by
      obtain ⟨b, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective a
      rw [hQ S hS b, hQ Sᶜ hS.compl b]
      change b.kMinusOneClass =
        (⟨b.bundle, cut S hS b.bundle b.automorphism⟩ : BundleAutomorphism _).kMinusOneClass +
        (⟨b.bundle, cut Sᶜ hS.compl b.bundle b.automorphism⟩ : BundleAutomorphism _).kMinusOneClass
      rw [← BundleAutomorphism.kMinusOneClass_trans]
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨Iso.refl b.bundle.Fiber, ?_⟩
      intro x v
      by_cases hx : x ∈ S <;> simp [cut, Iso.trans, Iso.refl, hx]
    -- On a compact base, finite trivial representatives compare the same cutoff under a map.
    have hfixed (S : Set (OnePoint X)) (hS : IsClopen S) (f : C(OnePoint X, OnePoint X))
        (hf : ∀ x ∈ S, f x = x) (a : BundleKMinusOne (OnePoint X)) :
        Q S hS (bundleKMinusOnePullback f a) = Q S hS a := by
      obtain ⟨b, hb⟩ := bundleAutomorphism_kMinusOneClass_surjective a
      obtain ⟨n, α, hα⟩ := b.exists_trivial_representative
      let := trivialTopology (X := OnePoint X) n
      rw [← hb, ← hα, bundleKMinusOnePullback_class, hQ S hS _, hQ S hS _]
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨pullbackTrivialIso f n, ?_⟩
      intro x v
      change Fin n → ℂ at v
      by_cases hx : x ∈ S
      · dsimp only [cutPair, cut]
        simp only [ite_eq_left hx]
        change (pullbackTrivialIso f n).linearEquiv x (α.linearEquiv (f x) v) =
          α.linearEquiv x ((pullbackTrivialIso f n).linearEquiv x v)
        rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply, hf x hx]
      · dsimp only [cutPair, cut]
        simp only [ite_eq_right hx]
        rfl
    -- Compactness makes infinity isolated. The finite inclusion then has an actual retraction.
    have hinfty : IsClopen ({∞} : Set (OnePoint X)) := by
      refine ⟨OnePoint.isClosed_infty, ?_⟩
      apply (OnePoint.isOpen_iff_of_mem (Set.mem_singleton (∞ : OnePoint X))).mpr
      simp only [Set.preimage_singleton, OnePoint.coe_ne_infty, Set.ofPred_false,
        Set.compl_empty]
      exact ⟨isClosed_univ, isCompact_univ⟩
    let S : Set (OnePoint X) := ({∞} : Set (OnePoint X))ᶜ
    have hS : IsClopen S := hinfty.compl
    let i : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
    let j : C(PUnit.{1}, OnePoint X) := ContinuousMap.const _ ∞
    let p : C(OnePoint X, PUnit.{1}) := ContinuousMap.const _ PUnit.unit
    let x₀ : X := Classical.choice hX
    let r : C(OnePoint X, X) :=
      ⟨fun z ↦ z.elim x₀ id, by
        apply (OnePoint.continuous_iff _).mpr
        constructor
        · simp only [Filter.coclosedCompact_eq_cocompact, Filter.cocompact_eq_bot]
          exact Filter.tendsto_bot
        · exact continuous_id⟩
    have hri : r.comp i = ContinuousMap.id X := by
      ext x
      rfl
    have hfinite (a : BundleKMinusOne (OnePoint X)) :
        Q S hS (bundleKMinusOnePullback r (bundleKMinusOnePullback i a)) = Q S hS a := by
      rw [← AddMonoidHom.comp_apply (bundleKMinusOnePullback r)
        (bundleKMinusOnePullback i), ← bundleKMinusOnePullback_comp]
      apply hfixed S hS (i.comp r)
      intro z hz
      cases z using OnePoint.rec with
      | infty => exact (hz (Set.mem_singleton ∞)).elim
      | coe x => rfl
    have hinfinite (a : BundleKMinusOne (OnePoint X)) :
        Q Sᶜ hS.compl (bundleKMinusOnePullback p (bundleKMinusOnePullback j a)) =
          Q Sᶜ hS.compl a := by
      rw [← AddMonoidHom.comp_apply (bundleKMinusOnePullback p)
        (bundleKMinusOnePullback j), ← bundleKMinusOnePullback_comp]
      apply hfixed Sᶜ hS.compl (j.comp p)
      intro z hz
      have hz' : z = ∞ := by simpa [S] using hz
      subst z
      rfl
    -- Restriction preserves the finite cutoff, while its value at infinity is elementary.
    have hrestrict (a : BundleKMinusOne (OnePoint X)) :
        bundleKMinusOnePullback i (Q S hS a) = bundleKMinusOnePullback i a := by
      obtain ⟨b, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective a
      rw [hQ S hS b, bundleKMinusOnePullback_class, bundleKMinusOnePullback_class]
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨Iso.refl (b.bundle.pullback i).Fiber, ?_⟩
      intro x v
      simp only [cutPair, BundleAutomorphism.pullback, Iso.pullback, Iso.refl, cut]
      simp only [i, ContinuousMap.coe_mk, S, Set.mem_compl_iff, Set.mem_singleton_iff,
        OnePoint.coe_ne_infty, not_false_eq_true, ite_eq_left]
      rfl
    have hevaluate (a : BundleKMinusOne (OnePoint X)) :
        bundleKMinusOnePullback j (Q S hS a) = 0 := by
      obtain ⟨b, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective a
      rw [hQ S hS b, bundleKMinusOnePullback_class]
      apply BundleAutomorphism.kMinusOneClass_eq_zero_of_isElementary
      have hid : ((cutPair S hS b).pullback j).automorphism =
          Iso.refl ((cutPair S hS b).bundle.pullback j).Fiber := by
        apply Iso.ext
        intro x
        apply LinearEquiv.ext
        intro v
        simp only [cutPair, BundleAutomorphism.pullback, Iso.pullback, Iso.refl, cut]
        simp only [j, ContinuousMap.const_apply, S, Set.mem_compl_iff,
          Set.mem_singleton_iff, not_true_eq_false]
        rfl
      rw [BundleAutomorphism.IsElementary, hid]
      exact IsoHomotopy.nonempty_refl _
    constructor
    · -- Vanishing of both original restrictions kills the two actual cutoff summands.
      apply (injective_iff_map_eq_zero _).mpr
      intro a ha
      have hai : bundleKMinusOnePullback i a.val = 0 := ha
      have haj : bundleKMinusOnePullback j a.val = 0 := a.property
      have hfin : Q S hS a.val = 0 := by
        rw [← hfinite a.val, hai, map_zero, map_zero]
      have hinf : Q Sᶜ hS.compl a.val = 0 := by
        rw [← hinfinite a.val, haj, map_zero, map_zero]
      apply Subtype.ext
      change a.val = 0
      rw [hsplit S hS a.val, hfin, hinf, add_zero]
    · -- Extend via r, then cut off infinity; the forward map is still the original restriction.
      intro a
      let b := Q S hS (bundleKMinusOnePullback r a)
      have hb : b ∈ reducedBundleKMinusOne (∞ : OnePoint X) := hevaluate _
      refine ⟨⟨b, hb⟩, ?_⟩
      change bundleKMinusOnePullback i b = a
      rw [hrestrict, ← AddMonoidHom.comp_apply, ← bundleKMinusOnePullback_comp, hri,
        bundleKMinusOnePullback_id]
      rfl


/-- The compact-base equivalence retains actual restriction as its forward function. -/
def compactSupportBundleKMinusOneCompactEquiv (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    CompactSupportBundleKMinusOne X ≃+ BundleKMinusOne X :=
  AddEquiv.ofBijective (compactSupportBundleKMinusOneToAbsolute (X := X))
    compactSupportBundleKMinusOneToAbsolute_bijective

end AtiyahSinger.ComplexBundle
