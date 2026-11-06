/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopyPullback
public import AtiyahSinger.Topology.BundleKMinusOne
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Pullback and homotopy invariance of the automorphism K^{-1} model

Public module ID: M1586.

Pullback is the actual quotient lift of the pulled-back bundle automorphism.
Its functor laws use the original fiberwise identity comparison maps, not an
arbitrary isomorphism of the underlying bundle classes. Homotopy invariance is
stated on compact Hausdorff bases, following Karoubi II.3.17: finite complements
reduce generators to maps into finite general linear groups. Thus the homotopy
tracks the automorphism as well as the bundle. An isomorphism of endpoint bundles
alone would not supply that argument.

This is ordinary automorphism K^{-1}. No comparison with CompactSupportK 1 or
clutching over a suspension is assumed. The actual pullback relations, functor
laws and compact-base homotopy invariance are proved using the same automorphisms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Actual pullback respects all three presentation relations. -/
theorem bundleKMinusOnePullback_relations (f : C(X, Y)) :
    (∀ a b : BundleAutomorphism Y, a.IsIsomorphic b →
      (a.pullback f).kMinusOneClass = (b.pullback f).kMinusOneClass) ∧
    (∀ a b : BundleAutomorphism Y,
      ((a.sum b).pullback f).kMinusOneClass =
        (a.pullback f).kMinusOneClass + (b.pullback f).kMinusOneClass) ∧
    (∀ a : BundleAutomorphism Y, a.IsElementary →
      (a.pullback f).kMinusOneClass = 0) := by
  /- Pull back the specified conjugating isomorphism for the first relation.
  For direct sums use the vector-preserving pullback/sum comparison, which
  intertwines the two block automorphisms. For an elementary pair pull back its
  actual homotopy along (t,x) ↦ (t,f(x)); the same endpoint equations hold.
  Apply the three class relations to supply the quotient lift below. -/
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    -- The original commuting square pulls back on each fiber at f(x).
    apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
    obtain ⟨e, he⟩ := hab
    exact ⟨e.pullback f, fun x v ↦ he (f x) v⟩
  · intro a b
    let J := a.bundle
    let K := b.bundle
    let := sumTopology (E := J.Fiber) (F := K.Fiber)
    let := sumTopology (E := (J.pullback f).Fiber) (F := (K.pullback f).Fiber)
    -- The canonical comparison is identity on vectors in the two induced topologies.
    let e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber :=
      { linearEquiv x := LinearEquiv.refl ℂ (J.Fiber (f x) × K.Fiber (f x))
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
    have heq := BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      ((a.sum b).pullback f) ((a.pullback f).sum (b.pullback f))
      ⟨e, fun _ _ ↦ rfl⟩
    exact heq.trans (BundleAutomorphism.kMinusOneClass_sum _ _)
  · intro a ha
    -- Pull back the entire cylinder homotopy, including its fixed endpoints.
    apply BundleAutomorphism.kMinusOneClass_eq_zero_of_isElementary
    obtain ⟨H⟩ := ha
    obtain ⟨K, _⟩ := H.exists_pullback f
    exact ⟨K⟩

/-- Contravariant K^{-1} pullback with its actual values on bundle automorphisms. -/
def bundleKMinusOnePullback (f : C(X, Y)) : BundleKMinusOne Y →+ BundleKMinusOne X :=
  bundleKMinusOneLift Y (fun a ↦ (a.pullback f).kMinusOneClass)
    (bundleKMinusOnePullback_relations f).1
    (bundleKMinusOnePullback_relations f).2.1
    (bundleKMinusOnePullback_relations f).2.2

/-- The induced pullback takes the class of the original pulled-back automorphism. -/
theorem bundleKMinusOnePullback_class (f : C(X, Y)) (a : BundleAutomorphism Y) :
    bundleKMinusOnePullback f a.kMinusOneClass = (a.pullback f).kMinusOneClass := by
  /- Evaluate the actual quotient lift on this generator. Its prescribed
  value is the class of a.pullback f, with the original pulled-back topology. -/
  exact bundleKMinusOneLift_apply Y _ _ _ _ a

/-- Identity pullback induces the identity homomorphism. -/
theorem bundleKMinusOnePullback_id :
    bundleKMinusOnePullback (ContinuousMap.id X) = AddMonoidHom.id (BundleKMinusOne X) := by
  /- Every class has a pair representative. On that pair the canonical
  identity-pullback isomorphism is the identity on each original vector and
  intertwines its automorphism. Apply the generator formula and conjugacy relation. -/
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective z
  rw [bundleKMinusOnePullback_class]
  apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
  refine ⟨pullbackIdIso (E := a.bundle.Fiber), ?_⟩
  intro x v
  change a.bundle.Fiber x at v
  change (pullbackIdIso (E := a.bundle.Fiber)).linearEquiv x
    (a.automorphism.linearEquiv x v) =
      a.automorphism.linearEquiv x ((pullbackIdIso (E := a.bundle.Fiber)).linearEquiv x v)
  rw [pullbackIdIso_apply, pullbackIdIso_apply]

/-- Pullback along a composite is the composite of the same actual pullbacks. -/
theorem bundleKMinusOnePullback_comp (f : C(X, Y)) (g : C(Y, Z)) :
    bundleKMinusOnePullback (g.comp f) =
      (bundleKMinusOnePullback f).comp (bundleKMinusOnePullback g) := by
  /- On a pair generator use the canonical pullback-composition isomorphism.
  Its fiber map preserves the original vector, so it conjugates the composite
  pullback automorphism to the iterated one. Extend the equality to all classes. -/
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective z
  simp only [bundleKMinusOnePullback_class, AddMonoidHom.comp_apply]
  symm
  apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
  refine ⟨pullbackCompIso (E := a.bundle.Fiber) g f, ?_⟩
  intro x v
  change a.bundle.Fiber (g (f x)) at v
  change (pullbackCompIso (E := a.bundle.Fiber) g f).linearEquiv x
    (a.automorphism.linearEquiv (g (f x)) v) =
      a.automorphism.linearEquiv (g (f x))
        ((pullbackCompIso (E := a.bundle.Fiber) g f).linearEquiv x v)
  rw [pullbackCompIso_apply, pullbackCompIso_apply]

/-- Restriction is pullback along the actual subtype inclusion. -/
def bundleKMinusOneRestriction (A : Set X) : BundleKMinusOne X →+ BundleKMinusOne A :=
  bundleKMinusOnePullback ⟨Subtype.val, continuous_subtype_val⟩

/-- KA II.3.17: homotopic maps of compact Hausdorff spaces induce equal K^{-1} maps. -/
theorem bundleKMinusOnePullback_eq_of_homotopic [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (f g : C(X, Y)) (hfg : f.Homotopic g) :
    bundleKMinusOnePullback f = bundleKMinusOnePullback g := by
  /- Stage 1: represent a target class by an actual automorphism pair and
  stabilize it using a finite complement on Y. Conjugation gives an automorphism
  of one finite trivial bundle without changing its K^{-1} class.
  Stage 2: pull its finite matrix function back along the given homotopy. In the
  canonical trivial coordinates this is a jointly continuous path of invertible
  matrices on X, with exactly the f and g pullback automorphisms at its ends.
  Stage 3: apply same-bundle homotopy invariance of the pair class, then undo
  the complement and the canonical pullback-trivial comparisons. This tracks
  the automorphisms; an arbitrary isomorphism of endpoint bundles is insufficient. -/
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective z
  obtain ⟨n, B, hB⟩ := a.exists_trivial_representative
  -- Use one finite trivial representative on Y before pulling back either endpoint.
  rw [← hB, bundleKMinusOnePullback_class, bundleKMinusOnePullback_class]
  let := trivialTopology (X := X) n
  let := trivialTopology (X := Y) n
  let := trivialTopology (X := I × X) n
  let EX := FiniteBundle.trivial X n
  let A : BundleAutomorphism Y := ⟨FiniteBundle.trivial Y n, B⟩
  let T (k : C(X, Y)) := pullbackTrivialIso k n
  let D (k : C(X, Y)) : Iso EX.Fiber EX.Fiber :=
    ((T k).symm.trans (B.pullback k)).trans (T k)
  have ht (k : C(X, Y)) (x : X) (v : Fin n → ℂ) :
      (T k).linearEquiv x v = v := pullbackTrivialIso_apply k n x v
  have hti (k : C(X, Y)) (x : X) (v : Fin n → ℂ) :
      ((T k).linearEquiv x).symm v = v := by
    have hi := ((T k).linearEquiv x).symm_apply_apply v
    rw [ht] at hi
    exact hi
  have hd (k : C(X, Y)) (x : X) (v : Fin n → ℂ) :
      (D k).linearEquiv x v = B.linearEquiv (k x) v := by
    change (T k).linearEquiv x
      (B.linearEquiv (k x) (((T k).linearEquiv x).symm v)) = _
    rw [hti, ht]
  have hi (k : C(X, Y)) : (A.pullback k).IsIsomorphic ⟨EX, D k⟩ := by
    refine ⟨T k, ?_⟩
    intro x v
    change Fin n → ℂ at v
    change (T k).linearEquiv x (B.linearEquiv (k x) v) =
      (D k).linearEquiv x ((T k).linearEquiv x v)
    rw [ht, hd, ht]
  -- Pull that same automorphism along the given cylinder map, in both directions.
  obtain ⟨H⟩ := hfg
  let p : C(I × X, X) := ⟨Prod.snd, continuous_snd⟩
  let U := pullbackTrivialIso p n
  let V := pullbackTrivialIso H.toContinuousMap n
  let W : Iso ((p : I × X → X) *ᵖ EX.Fiber) ((p : I × X → X) *ᵖ EX.Fiber) :=
    ((((U.trans V.symm).trans (B.pullback H.toContinuousMap)).trans V).trans U.symm)
  have hu (x : I × X) (v : Fin n → ℂ) :
      U.linearEquiv x v = v := pullbackTrivialIso_apply p n x v
  have hui (x : I × X) (v : Fin n → ℂ) : (U.linearEquiv x).symm v = v := by
    have hi := (U.linearEquiv x).symm_apply_apply v
    rw [hu] at hi
    exact hi
  have hv (x : I × X) (v : Fin n → ℂ) :
      V.linearEquiv x v = v := pullbackTrivialIso_apply H.toContinuousMap n x v
  have hvi (x : I × X) (v : Fin n → ℂ) : (V.linearEquiv x).symm v = v := by
    have hi := (V.linearEquiv x).symm_apply_apply v
    rw [hv] at hi
    exact hi
  have hw (x : I × X) (v : Fin n → ℂ) :
      W.linearEquiv x v = B.linearEquiv (H x) v := by
    change (U.linearEquiv x).symm
      (V.linearEquiv x (B.linearEquiv (H x)
        ((V.linearEquiv x).symm (U.linearEquiv x v)))) = _
    rw [hu, hvi, hv, hui]
  -- The coordinate identities determine precisely the two specified endpoint automorphisms.
  let K : IsoHomotopy (D f) (D g) :=
    { iso := W
      map_zero := by
        intro x v
        change Fin n → ℂ at v
        rw [hw, H.apply_zero, hd]
      map_one := by
        intro x v
        change Fin n → ℂ at v
        rw [hw, H.apply_one, hd] }
  calc
    (A.pullback f).kMinusOneClass =
        (⟨EX, D f⟩ : BundleAutomorphism X).kMinusOneClass :=
      BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ (hi f)
    _ = (⟨EX, D g⟩ : BundleAutomorphism X).kMinusOneClass :=
      BundleAutomorphism.kMinusOneClass_eq_of_homotopy EX (D f) (D g) K
    _ = (A.pullback g).kMinusOneClass :=
      (BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ (hi g)).symm

/-- A specified homotopy equivalence induces a bijection on ordinary K^{-1}. -/
theorem bundleKMinusOnePullback_bijective_of_homotopyEquiv
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    Function.Bijective (bundleKMinusOnePullback e.toFun) := by
  /- Pull back along e.invFun. Contravariant composition and the two specified
  homotopies identify both composites with identity. Thus this actual pullback
  supplies a two-sided inverse to pullback along e.toFun. -/
  let u := bundleKMinusOnePullback e.toFun
  let v := bundleKMinusOnePullback e.invFun
  -- Contravariance reverses the two composites of the supplied homotopy equivalence.
  have hleft : v.comp u = AddMonoidHom.id (BundleKMinusOne Y) := by
    rw [← bundleKMinusOnePullback_comp]
    exact (bundleKMinusOnePullback_eq_of_homotopic _ _ e.right_inv).trans
      bundleKMinusOnePullback_id
  have hright : u.comp v = AddMonoidHom.id (BundleKMinusOne X) := by
    rw [← bundleKMinusOnePullback_comp]
    exact (bundleKMinusOnePullback_eq_of_homotopic _ _ e.left_inv).trans
      bundleKMinusOnePullback_id
  -- These are actual inverse maps on the original quotient groups.
  exact ⟨(show Function.LeftInverse v u from
      fun z ↦ DFunLike.congr_fun hleft z).injective,
    (show Function.RightInverse v u from
      fun z ↦ DFunLike.congr_fun hright z).surjective⟩

end AtiyahSinger.ComplexBundle
