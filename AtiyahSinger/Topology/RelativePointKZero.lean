/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeKZeroExcision

/-!
# Relative K at a point and the reduced group

Public module ID: M2084.

Forgetting for the singleton pair gives the actual comparison with the
kernel of basepoint evaluation. The actual singleton quotient map is a homeomorphism,
so inverse pullback proves bijectivity without general-pair exactness.
This prepares the finite-neighborhood form of Karoubi II.4.22 without identifying
the relative group of a general pair with an absolute restriction kernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint
open scoped unitInterval Topology

variable {X : Type*} [TopologicalSpace X]


/-- The explicit constant retraction to a singleton subspace. -/
def singletonRetraction (x : X) : C(X, ({x} : Set X)) :=
  ContinuousMap.const X ⟨x, Set.mem_singleton x⟩

/-- The singleton retraction fixes its only point. -/
theorem singletonRetraction_apply (x : X) (a : ({x} : Set X)) : singletonRetraction x a = a := by
  /- The membership proof of a says its underlying point is x. Substitute that equality; both
  sides are the unique element of the singleton subtype. -/
  apply Subtype.ext
  exact (Set.mem_singleton_iff.mp a.property).symm

variable [hX : CompactSpace X] [hT : T2Space X]
include hX hT

/-- A relative singleton class has zero evaluation at its base point. -/
theorem relativeKZeroForget_singleton_mem_reduced (x : X)
    (a : RelativeKZero ({x} : Set X) isClosed_singleton) :
    relativeKZeroForget ({x} : Set X) isClosed_singleton a ∈ reducedComplexKZero x := by
  /- Restricting a forgotten relative class to the singleton is zero. Evaluation at its only
  point identifies that restriction with the original evaluation homomorphism, so the
  forgotten absolute class lies in the reduced kernel. -/
  let := PointedQuotient.compactSpace ({x} : Set X)
  let := PointedQuotient.t2Space ({x} : Set X) isClosed_singleton
  -- The original quotient map sends this exact base point to the distinguished quotient point.
  let q : C(X, PointedQuotient ({x} : Set X)) :=
    ⟨PointedQuotient.of {x}, PointedQuotient.continuous_of {x}⟩
  have hpoint : q x = PointedQuotient.basepoint ({x} : Set X) :=
    (PointedQuotient.of_eq_basepoint_iff {x} x).mpr (Set.mem_singleton x)
  exact complexKZeroPullback_mem_reduced x _ q hpoint a.val a.property

/-- Restrict singleton-pair forgetting to the actual reduced subgroup. -/
def relativeKZeroPointToReduced (x : X) :
    RelativeKZero ({x} : Set X) isClosed_singleton →+ reducedComplexKZero x :=
  { toFun := fun a ↦ ⟨relativeKZeroForget ({x} : Set X) isClosed_singleton a,
      relativeKZeroForget_singleton_mem_reduced x a⟩
    map_zero' := Subtype.ext (map_zero (relativeKZeroForget ({x} : Set X) isClosed_singleton))
    map_add' := fun a b ↦
      Subtype.ext (map_add (relativeKZeroForget ({x} : Set X) isClosed_singleton) a b) }

/-- The reduced comparison retains the original forgotten class. -/
theorem relativeKZeroPointToReduced_val (x : X)
    (a : RelativeKZero ({x} : Set X) isClosed_singleton) :
    (relativeKZeroPointToReduced x a).val =
      relativeKZeroForget ({x} : Set X) isClosed_singleton a := by
  /- The reduced map is defined by pairing the original forgotten value with its kernel-
  membership certificate. Taking the underlying value discards only that proof. -/
  rfl

/-- The singleton comparison is injective. -/
theorem relativeKZeroPointToReduced_injective (x : X) :
    Function.Injective (relativeKZeroPointToReduced x) := by
  /- For a singleton the actual quotient map from X is a continuous bijection, hence a
  homeomorphism by compactness and Hausdorffness. Pulling back along its inverse recovers
  every quotient class from its forgotten class. This direct argument avoids needing the
  general relative-forgetting theorem for arbitrary retract pairs. -/
  let := PointedQuotient.compactSpace ({x} : Set X)
  let := PointedQuotient.t2Space ({x} : Set X) isClosed_singleton
  let q : C(X, PointedQuotient ({x} : Set X)) :=
    ⟨PointedQuotient.of {x}, PointedQuotient.continuous_of {x}⟩
  have hpoint : q x = PointedQuotient.basepoint ({x} : Set X) :=
    (PointedQuotient.of_eq_basepoint_iff {x} x).mpr (Set.mem_singleton x)
  -- Collapsing this single point together with the added point identifies no distinct X-points.
  have hinj : Function.Injective q := by
    intro y z h
    rcases (PointedQuotient.of_eq_of_iff {x} y z).mp h with h | ⟨hy, hz⟩
    · exact h
    · exact (Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hz).symm
  have hsurj : Function.Surjective q := by
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists ({x} : Set X) z with hz | ⟨y, hy⟩
    · exact ⟨x, hpoint.trans hz.symm⟩
    · exact ⟨y, hy.symm⟩
  let e : X ≃ₜ PointedQuotient ({x} : Set X) :=
    (Equiv.ofBijective q ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
      q.continuous q.continuous.isClosedMap
  let r : C(PointedQuotient ({x} : Set X), X) := ⟨e.symm, e.symm.continuous⟩
  have hleft (a : ComplexKZero (PointedQuotient ({x} : Set X))) :
      complexKZeroPullback r (complexKZeroPullback q a) = a := by
    have hid : q.comp r = ContinuousMap.id _ := by
      ext z
      exact e.apply_symm_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a = a
    rw [kZeroMap_id]
    rfl
  -- Apply the inverse pullback to equality of the original forgotten absolute classes.
  intro a b h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change complexKZeroPullback q a.val = complexKZeroPullback q b.val at hval
  exact (hleft a.val).symm.trans ((congrArg (complexKZeroPullback r) hval).trans (hleft b.val))

/-- Every reduced class lifts to the singleton relative group. -/
theorem relativeKZeroPointToReduced_surjective (x : X) :
    Function.Surjective (relativeKZeroPointToReduced x) := by
  /- Use the actual homeomorphism between X and its singleton pointed quotient. Its inverse
  preserves the specified base points, so pullback takes a reduced class on X into the
  original relative group. Pulling this class back along the quotient map gives the initial
  class exactly, without invoking general-pair exactness. -/
  let := PointedQuotient.compactSpace ({x} : Set X)
  let := PointedQuotient.t2Space ({x} : Set X) isClosed_singleton
  let q : C(X, PointedQuotient ({x} : Set X)) :=
    ⟨PointedQuotient.of {x}, PointedQuotient.continuous_of {x}⟩
  have hpoint : q x = PointedQuotient.basepoint ({x} : Set X) :=
    (PointedQuotient.of_eq_basepoint_iff {x} x).mpr (Set.mem_singleton x)
  -- Collapsing this single point together with the added point identifies no distinct X-points.
  have hinj : Function.Injective q := by
    intro y z h
    rcases (PointedQuotient.of_eq_of_iff {x} y z).mp h with h | ⟨hy, hz⟩
    · exact h
    · exact (Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hz).symm
  have hsurj : Function.Surjective q := by
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists ({x} : Set X) z with hz | ⟨y, hy⟩
    · exact ⟨x, hpoint.trans hz.symm⟩
    · exact ⟨y, hy.symm⟩
  let e : X ≃ₜ PointedQuotient ({x} : Set X) :=
    (Equiv.ofBijective q ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
      q.continuous q.continuous.isClosedMap
  let r : C(PointedQuotient ({x} : Set X), X) := ⟨e.symm, e.symm.continuous⟩
  have hrpoint : r (PointedQuotient.basepoint ({x} : Set X)) = x := by
    calc
      r (PointedQuotient.basepoint ({x} : Set X)) = r (q x) := congrArg r hpoint.symm
      _ = x := e.symm_apply_apply x
  -- The actual inverse homeomorphism sends the original reduced class to the relative kernel.
  let inv := reducedComplexKZeroPullback (PointedQuotient.basepoint ({x} : Set X)) x r
    hrpoint
  intro a
  refine ⟨inv a, ?_⟩
  apply Subtype.ext
  change complexKZeroPullback q (complexKZeroPullback r a.val) = a.val
  have hid : r.comp q = ContinuousMap.id _ := by
    ext y
    exact e.symm_apply_apply y
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
  change kZeroMap (RingHom.id _) a.val = a.val
  rw [kZeroMap_id]
  rfl

/-- The actual singleton comparison is bijective. -/
theorem relativeKZeroPointToReduced_bijective (x : X) :
    Function.Bijective (relativeKZeroPointToReduced x) := by
  /- Combine injectivity and surjectivity from the actual singleton quotient homeomorphism.
  Both concern the same original restricted forgetful homomorphism. -/
  exact ⟨relativeKZeroPointToReduced_injective x, relativeKZeroPointToReduced_surjective x⟩

/-- Identify relative K at a point with reduced K using actual forgetting. -/
def relativeKZeroPointReducedEquiv (x : X) :
    RelativeKZero ({x} : Set X) isClosed_singleton ≃+ reducedComplexKZero x :=
  AddEquiv.ofBijective _ (relativeKZeroPointToReduced_bijective x)

end AtiyahSinger
