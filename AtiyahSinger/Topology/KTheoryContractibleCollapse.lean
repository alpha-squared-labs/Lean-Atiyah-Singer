/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneExactness
public import AtiyahSinger.Topology.RelativePointKZero
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Reduced K-theory after collapsing a contractible closed subspace

Public module ID: M1916.

The map is pullback along the actual pointed quotient map. Its bijectivity is
the compact-pair consequence of Karoubi II.3.27 used in II.3.29. Apply that
proposition to the identity map from (X,{x₀}) to (X,A), using contractibility of A
to show that the singleton inclusion is a homotopy equivalence. The inverse of
that subspace map need not extend to a homotopy inverse of pairs.

This does not assert that X → X/A is a homotopy equivalence of spaces. No
cofibration assumption is needed for this compact Hausdorff K-theory statement.
The comparison uses the identity on X and the singleton inclusion into A,
which are separately homotopy equivalences.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

attribute [local instance] PointedQuotient.compactSpace

/-- Pullback along the actual collapse, with the source base point inside the collapsed set. -/
def reducedComplexKZeroCollapse (A : Set X) (hA : IsClosed A) (x₀ : X) (hx₀ : x₀ ∈ A) :
    letI := PointedQuotient.t2Space A hA
    reducedComplexKZero (PointedQuotient.basepoint A) →+ reducedComplexKZero x₀ :=
  letI := PointedQuotient.t2Space A hA
  reducedComplexKZeroPullback x₀ (PointedQuotient.basepoint A)
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
    ((PointedQuotient.of_eq_basepoint_iff A x₀).2 hx₀)

/-- KA II.3.27 consequence: collapsing a contractible closed subspace preserves reduced K⁰. -/
theorem reducedComplexKZeroCollapse_bijective (A : Set X) (hA : IsClosed A)
    (x₀ : X) (hx₀ : x₀ ∈ A) [ContractibleSpace A] :
    Function.Bijective (reducedComplexKZeroCollapse A hA x₀ hx₀) := by
  /- Stage 1: the singleton inclusion {x₀} → A is a homotopy equivalence.
  Contractibility supplies a contraction to some point; a path to x₀ changes
  it to a contraction to the specified point. The singleton has its unique
  topology, and its inverse is the constant map. No relative contraction is
  required. The ambient map of (X,{x₀}) → (X,A) is the actual identity on X.
  Stage 2: apply II.3.27 to this map of pairs, obtaining an isomorphism from
  RelativeKZero A to RelativeKZero {x₀}. The existing singleton equivalence
  then maps to the reduced subgroup at x₀ by the actual relative forgetting map.
  Stage 3: both composites pull back the same pointed quotient class along
  X → PointedQuotient A. On underlying absolute classes their values agree,
  and reduced-subgroup extensionality identifies the maps. Thus bijectivity
  applies to precisely reducedComplexKZeroCollapse, not an unrelated map. -/
  classical
  let S : Set X := {x₀}
  let hS : IsClosed S := isClosed_singleton
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let := hS.isClosedEmbedding_subtypeVal.compactSpace
  let a₀ : A := ⟨x₀, hx₀⟩
  have hj (x : S) : x.val ∈ A := by
    simpa only [S, Set.mem_singleton_iff.mp x.property] using hx₀
  let j : C(S, A) := ⟨fun x ↦ ⟨x.val, hj x⟩, continuous_subtype_val.subtype_mk hj⟩
  let r : C(A, S) := ContinuousMap.const A ⟨x₀, Set.mem_singleton x₀⟩
  -- Contract to the specified point, using the original contraction's own pointwise path.
  obtain ⟨a, ⟨H⟩⟩ := id_nullhomotopic A
  have hpoint : (ContinuousMap.id A).Homotopic (ContinuousMap.const A a₀) :=
    ⟨H.trans (H.evalAt a₀).symm.toHomotopyConst⟩
  have hleft : r.comp j = ContinuousMap.id S := by
    ext x
    exact (Set.mem_singleton_iff.mp x.property).symm
  have hright : j.comp r = ContinuousMap.const A a₀ := by
    ext x
    rfl
  let e : ContinuousMap.HomotopyEquiv S A :=
    { toFun := j
      invFun := r
      left_inv := by rw [hleft]
      right_inv := by rw [hright]; exact hpoint.symm }
  -- The ambient map is identity and the subspace map is exactly this singleton inclusion.
  have hf : Set.MapsTo (ContinuousMap.id X) S A := by
    intro x hx
    change x ∈ A
    simpa only [S, Set.mem_singleton_iff.mp hx] using hx₀
  have hrelative : Function.Bijective
      (relativeKZeroPullback S hS A hA (ContinuousMap.id X) hf) :=
    ComplexBundle.relativeKZeroPullback_bijective_of_homotopyEquiv S hS A hA
      (ContinuousMap.id X) hf ⟨ContinuousMap.HomotopyEquiv.refl X, rfl⟩
      ⟨e, fun _ ↦ rfl⟩
  have hmap : reducedComplexKZeroCollapse A hA x₀ hx₀ =
      (relativeKZeroPointToReduced x₀).comp
        (relativeKZeroPullback S hS A hA (ContinuousMap.id X) hf) := by
    apply AddMonoidHom.ext
    intro b
    apply Subtype.ext
    have hn := DFunLike.congr_fun
      (relativeKZeroForget_natural S hS A hA (ContinuousMap.id X) hf) b
    change relativeKZeroForget A hA b =
      relativeKZeroForget S hS
        (relativeKZeroPullback S hS A hA (ContinuousMap.id X) hf b)
    change _ = kZeroMap (RingHom.id _) (relativeKZeroForget A hA b) at hn
    simpa only [kZeroMap_id, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using hn.symm
  -- Both factors keep their actual forward maps, hence their composite is the stated collapse.
  rw [hmap]
  exact (relativeKZeroPointToReduced_bijective x₀).comp hrelative

/-- The additive equivalence whose forward map is the specified quotient pullback. -/
def reducedComplexKZeroCollapseEquiv (A : Set X) (hA : IsClosed A)
    (x₀ : X) (hx₀ : x₀ ∈ A) [ContractibleSpace A] :
    letI := PointedQuotient.t2Space A hA
    reducedComplexKZero (PointedQuotient.basepoint A) ≃+ reducedComplexKZero x₀ :=
  letI := PointedQuotient.t2Space A hA
  AddEquiv.ofBijective (reducedComplexKZeroCollapse A hA x₀ hx₀)
    (reducedComplexKZeroCollapse_bijective A hA x₀ hx₀)

end AtiyahSinger
