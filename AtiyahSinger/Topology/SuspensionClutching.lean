/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOne
public import AtiyahSinger.Topology.ClutchingBundle
public import AtiyahSinger.Topology.Suspension

/-!
# The specified clutching bundle on an ordinary suspension

Public module ID: M2224.

Karoubi I.3.14 glues trivial bundles on the two closed cones. The transition
from the upper cone to the lower cone is the original automorphism alpha.
We keep the actual closed hemispheres in the existing quotient suspension,
and characterize the glued bundle by its two charts and that exact transition.
The choice is therefore constrained by geometric descent data, not by a desired
K class. The ordinary suspension always has two poles in this project; no
classification statement for its exceptional empty-base convention is made here.

The closed-cover geometry supports the bundle descent, its two-chart
uniqueness and the reduced class at the original south pole.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped unitInterval

namespace UnreducedSuspension

variable (X : Type*) [TopologicalSpace X]

/-- The lower closed hemisphere, including the south pole in the empty-base convention. -/
def lowerHemisphere : Set (UnreducedSuspension X) :=
  {south} ∪ {z | ∃ x : X, ∃ t : I, (t : ℝ) ≤ 1 / 2 ∧ z = of x t}

/-- The upper closed hemisphere, including the north pole in the empty-base convention. -/
def upperHemisphere : Set (UnreducedSuspension X) :=
  {north} ∪ {z | ∃ x : X, ∃ t : I, 1 / 2 ≤ (t : ℝ) ∧ z = of x t}

/-- The actual equator at height one half in the original cylinder quotient. -/
def equator : C(X, UnreducedSuspension X) :=
  ofMap.comp ⟨fun x ↦ (x, (⟨1 / 2, by norm_num, by norm_num⟩ : I)), by fun_prop⟩

attribute [local instance] compactSpace t2Space

/-- The closed hemispheres cover the suspension and meet in its embedded equator. -/
theorem hemisphere_geometry [CompactSpace X] [T2Space X] :
    IsClosed (upperHemisphere X) ∧ IsClosed (lowerHemisphere X) ∧
      upperHemisphere X ∪ lowerHemisphere X = Set.univ ∧
      upperHemisphere X ∩ lowerHemisphere X = Set.range (equator X) ∧
      Topology.IsClosedEmbedding (equator X) := by
  -- In the first quotient, only height one belongs to the upper collapsed end.
  have hupper (x : X) (t : I)
      (ht : PointedQuotient.of (lowerEnd X) (x, t) ∈ upperEnd X) : t = 1 := by
    obtain ⟨y, hy⟩ := ht
    rcases (PointedQuotient.of_eq_of_iff (lowerEnd X) (y, 1) (x, t)).1 hy with
      heq | ⟨hzero, _⟩
    · exact (congrArg Prod.snd heq).symm
    · exact (one_ne_zero hzero).elim
  have hnorth (x : X) (t : I) (h : of x t = north) : t = 1 :=
    hupper x t ((PointedQuotient.of_eq_basepoint_iff (upperEnd X) _).1 h)
  have hsouth (x : X) (t : I) (h : of x t = south) : t = 0 := by
    rcases (PointedQuotient.of_eq_of_iff (upperEnd X) _ _).1 h with h | ⟨_, hb⟩
    · exact (PointedQuotient.of_eq_basepoint_iff (lowerEnd X) (x, t)).1 h
    · obtain ⟨y, hy⟩ := hb
      exact (one_ne_zero
        ((PointedQuotient.of_eq_basepoint_iff (lowerEnd X) (y, 1)).1 hy)).elim
  -- Both quotient relations preserve height, and preserve the point at interior heights.
  have hheight (x y : X) (s t : I) (h : of x s = of y t) : s = t := by
    rcases (PointedQuotient.of_eq_of_iff (upperEnd X) _ _).1 h with h | ⟨hs, ht⟩
    · rcases (PointedQuotient.of_eq_of_iff (lowerEnd X) (x, s) (y, t)).1 h with
        h | ⟨hs, ht⟩
      · exact congrArg Prod.snd h
      · exact hs.trans ht.symm
    · exact (hupper x s hs).trans (hupper y t ht).symm
  have heqinj : Function.Injective (equator X) := by
    intro x y h
    rcases (PointedQuotient.of_eq_of_iff (upperEnd X) _ _).1 h with h | ⟨hx, _⟩
    · rcases (PointedQuotient.of_eq_of_iff (lowerEnd X) _ _).1 h with h | ⟨hx, _⟩
      · exact congrArg Prod.fst h
      · have : (1 / 2 : ℝ) = 0 := congrArg Subtype.val hx
        norm_num at this
    · have : (1 / 2 : ℝ) = 1 := congrArg Subtype.val (hupper x _ hx)
      norm_num at this
  have heqclosed := (equator X).continuous.isClosedEmbedding heqinj
  -- Each half is the union of its pole and the compact image of a closed half-cylinder.
  have hU : upperHemisphere X = {north} ∪
      ofMap '' {p : X × I | 1 / 2 ≤ (p.2 : ℝ)} := by
    ext z
    simp only [upperHemisphere, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro (h | ⟨x, t, ht, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(x, t), ht, h.symm⟩
    · rintro (h | ⟨⟨x, t⟩, ht, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, t, ht, h.symm⟩
  have hL : lowerHemisphere X = {south} ∪
      ofMap '' {p : X × I | (p.2 : ℝ) ≤ 1 / 2} := by
    ext z
    simp only [lowerHemisphere, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro (h | ⟨x, t, ht, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(x, t), ht, h.symm⟩
    · rintro (h | ⟨⟨x, t⟩, ht, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, t, ht, h.symm⟩
  have hcU : IsClosed (upperHemisphere X) := by
    rw [hU]
    have hcompact : IsCompact {p : X × I | 1 / 2 ≤ (p.2 : ℝ)} :=
      (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).isCompact
    exact isClosed_singleton.union (hcompact.image ofMap.continuous).isClosed
  have hcL : IsClosed (lowerHemisphere X) := by
    rw [hL]
    have hcompact : IsCompact {p : X × I | (p.2 : ℝ) ≤ 1 / 2} :=
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact
    exact isClosed_singleton.union (hcompact.image ofMap.continuous).isClosed
  refine ⟨hcU, hcL, ?_, ?_, heqclosed⟩
  · -- Every point is a pole or a cylinder point, whose height belongs to a half.
    apply Set.eq_univ_of_forall
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists (upperEnd X) z with hz | ⟨q, rfl⟩
    · exact Or.inl (Or.inl hz)
    · rcases PointedQuotient.eq_basepoint_or_exists (lowerEnd X) q with hq | ⟨p, rfl⟩
      · exact Or.inr (Or.inl (congrArg (PointedQuotient.of (upperEnd X)) hq))
      · rcases le_total (1 / 2 : ℝ) p.2 with hp | hp
        · exact Or.inl (Or.inr ⟨p.1, p.2, hp, rfl⟩)
        · exact Or.inr (Or.inr ⟨p.1, p.2, hp, rfl⟩)
  · -- The poles are disjoint from the opposite half, and the overlap has height one half.
    ext z
    constructor
    · rintro ⟨hU, hL⟩
      rcases hU with hz | ⟨x, s, hs, hz⟩
      · rcases hL with hz' | ⟨y, t, ht, hz'⟩
        · exact (south_ne_north (hz'.symm.trans hz)).elim
        · have ht1 := congrArg Subtype.val (hnorth y t (hz'.symm.trans hz))
          have htval : (t : ℝ) = 1 := ht1
          linarith
      · rcases hL with hz' | ⟨y, t, ht, hz'⟩
        · have hs0 := congrArg Subtype.val (hsouth x s (hz.symm.trans hz'))
          have hsval : (s : ℝ) = 0 := hs0
          linarith
        · have hst := congrArg Subtype.val (hheight x y s t (hz.symm.trans hz'))
          have hsval : (s : ℝ) = 1 / 2 := by linarith
          have hs' : s = (⟨1 / 2, by norm_num, by norm_num⟩ : I) :=
            Subtype.ext hsval
          exact ⟨x, (congrArg (of x) hs').symm.trans hz.symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Or.inr ⟨x, _, le_rfl, rfl⟩, Or.inr ⟨x, _, le_rfl, rfl⟩⟩

end UnreducedSuspension

namespace ComplexBundle

variable {X : Type*} [TopologicalSpace X]

attribute [local instance] UnreducedSuspension.compactSpace UnreducedSuspension.t2Space
  trivialTopology isFiniteRank_trivial

/-- Descent data with the original automorphism as the upper-to-lower transition. -/
def SuspensionClutchingCompatible (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber)
    (W : FiniteBundle (UnreducedSuspension X))
    (eU : Iso (W.restrict (UnreducedSuspension.upperHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.upperHemisphere X) n).Fiber)
    (eL : Iso (W.restrict (UnreducedSuspension.lowerHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.lowerHemisphere X) n).Fiber) : Prop :=
  ∀ x : X, ∀ v : Fin n → ℂ,
    eL.linearEquiv
        ⟨UnreducedSuspension.equator X x, Or.inr ⟨x, _, le_rfl, rfl⟩⟩
        ((eU.linearEquiv
          ⟨UnreducedSuspension.equator X x, Or.inr ⟨x, _, le_rfl, rfl⟩⟩).symm v) =
      α.linearEquiv x v

variable [CompactSpace X] [T2Space X]

set_option backward.isDefEq.respectTransparency false in
/-- KA I.3.14: the specified equatorial transition admits a finite-rank glued bundle. -/
theorem exists_suspensionClutchingBundle (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    ∃ W : FiniteBundle (UnreducedSuspension X),
      ∃ eU : Iso (W.restrict (UnreducedSuspension.upperHemisphere X)).Fiber
        (FiniteBundle.trivial (UnreducedSuspension.upperHemisphere X) n).Fiber,
        ∃ eL : Iso (W.restrict (UnreducedSuspension.lowerHemisphere X)).Fiber
          (FiniteBundle.trivial (UnreducedSuspension.lowerHemisphere X) n).Fiber,
          SuspensionClutchingCompatible n α W eU eL := by
  /- Pull the already constructed double-clutching bundle back along the map
  that uses the left copy on the upper hemisphere and the right copy on the lower.
  These maps agree exactly on the equator; the pulled-back charts retain alpha. -/
  classical
  -- Identify the original equator with its actual closed image and transport alpha.
  let S := UnreducedSuspension X
  let U := UnreducedSuspension.upperHemisphere X
  let L := UnreducedSuspension.lowerHemisphere X
  let A : Set S := Set.range (UnreducedSuspension.equator X)
  obtain ⟨hU, hL, hcover, hUL, heq⟩ := UnreducedSuspension.hemisphere_geometry X
  have hA : IsClosed A := heq.isClosed_range
  let e : X ≃ₜ A := heq.isEmbedding.toHomeomorph
  let j : C(A, X) := ⟨e.symm, e.symm.continuous⟩
  let iA : C(A, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let T := FiniteBundle.trivial S n
  let b : Iso (Restrict T.Fiber A) (Restrict T.Fiber A) :=
    (pullbackTrivialIso iA n).trans ((pullbackTrivialIso j n).symm.trans
      ((α.pullback j).trans ((pullbackTrivialIso j n).trans (pullbackTrivialIso iA n).symm)))
  have hb (x : X) (v : Fin n → ℂ) : b.linearEquiv (e x) v = α.linearEquiv x v := by
    have hinvA (y : A) (w : Fin n → ℂ) :
        ((pullbackTrivialIso iA n).linearEquiv y).symm w = w := by
      have hh := pullbackTrivialIso_apply iA n y
        (((pullbackTrivialIso iA n).linearEquiv y).symm w)
      exact hh.symm.trans (LinearEquiv.apply_symm_apply _ _)
    have hinvJ (y : A) (w : Fin n → ℂ) :
        ((pullbackTrivialIso j n).linearEquiv y).symm w = w := by
      have hh := pullbackTrivialIso_apply j n y
        (((pullbackTrivialIso j n).linearEquiv y).symm w)
      exact hh.symm.trans (LinearEquiv.apply_symm_apply _ _)
    change ((pullbackTrivialIso iA n).linearEquiv (e x)).symm
      ((pullbackTrivialIso j n).linearEquiv (e x)
        (α.linearEquiv (j (e x))
          (((pullbackTrivialIso j n).linearEquiv (e x)).symm
            ((pullbackTrivialIso iA n).linearEquiv (e x) v)))) = _
    rw [hinvA, pullbackTrivialIso_apply, hinvJ, pullbackTrivialIso_apply]
    change α.linearEquiv (e.symm (e x)) v = _
    rw [e.symm_apply_apply]
  -- The existing double construction uses this same boundary action.
  let a : BundleTriple A := BundleTriple.ofBoundary T T b
  let V := clutchingBundle hA a
  let cU := clutchingLeftIso hA a
  let cL := clutchingRightIso hA a
  -- Paste the two copies along the original finite closed cover.
  let d (z : S) : DoubleSpace A := if z ∈ U then DoubleSpace.left A z
    else DoubleSpace.right A z
  have hdU (z : S) (hz : z ∈ U) : d z = DoubleSpace.left A z := by
    simp only [d, hz, ite_true]
  have hdL (z : S) (hz : z ∈ L) : d z = DoubleSpace.right A z := by
    dsimp only [d]
    split_ifs with hu
    · have ha : z ∈ A := by
        change z ∈ Set.range (UnreducedSuspension.equator X)
        rw [← hUL]
        exact ⟨hu, hz⟩
      exact DoubleSpace.left_eq_right A ⟨z, ha⟩
    · rfl
  have hd : Continuous d := by
    rw [← continuousOn_univ, ← hcover]
    apply ContinuousOn.union_of_isClosed _ _ hU hL
    · exact (DoubleSpace.continuous_left A).continuousOn.congr (fun z hz ↦ hdU z hz)
    · exact (DoubleSpace.continuous_right A).continuousOn.congr (fun z hz ↦ hdL z hz)
  -- Pull back one witness, then compare the two hemisphere restrictions.
  let f : C(S, DoubleSpace A) := ⟨d, hd⟩
  let W := V.pullback f
  let iU : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let iL : C(L, S) := ⟨Subtype.val, continuous_subtype_val⟩
  have hfU : f.comp iU = (DoubleSpace.leftMap A).comp iU := by
    ext z
    exact hdU z z.property
  have hfL : f.comp iL = (DoubleSpace.rightMap A).comp iL := by
    ext z
    exact hdL z z.property
  have isoEq (Y : Set S) (g k : C(Y, DoubleSpace A)) (h : g = k) :
      ∃ q : Iso ((g : Y → DoubleSpace A) *ᵖ V.Fiber)
        ((k : Y → DoubleSpace A) *ᵖ V.Fiber),
        ∀ y v, q.linearEquiv y v = cast (congrArg V.Fiber (DFunLike.congr_fun h y)) v := by
    subst k
    exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
  obtain ⟨qU, hqU⟩ := isoEq U (f.comp iU) ((DoubleSpace.leftMap A).comp iU) hfU
  obtain ⟨qL, hqL⟩ := isoEq L (f.comp iL) ((DoubleSpace.rightMap A).comp iL) hfL
  let eU : Iso (W.restrict U).Fiber (FiniteBundle.trivial U n).Fiber :=
    (pullbackCompIso (E := V.Fiber) f iU).trans (qU.trans
      ((pullbackCompIso (E := V.Fiber) (DoubleSpace.leftMap A) iU).symm.trans
        ((cU.pullback iU).trans (pullbackTrivialIso iU n))))
  let eL : Iso (W.restrict L).Fiber (FiniteBundle.trivial L n).Fiber :=
    (pullbackCompIso (E := V.Fiber) f iL).trans (qL.trans
      ((pullbackCompIso (E := V.Fiber) (DoubleSpace.rightMap A) iL).symm.trans
        ((cL.pullback iL).trans (pullbackTrivialIso iL n))))
  have hinvComp (Z : Set S) (g : C(S, DoubleSpace A)) (k : C(Z, S))
      (z : Z) (v : V.Fiber (g (k z))) :
      ((pullbackCompIso (E := V.Fiber) g k).linearEquiv z).symm v = v := by
    have hh := pullbackCompIso_apply (E := V.Fiber) g k z
      (((pullbackCompIso (E := V.Fiber) g k).linearEquiv z).symm v)
    exact hh.symm.trans (LinearEquiv.apply_symm_apply _ _)
  -- Express both hemisphere charts on the original fibers to compare their equatorial seam.
  have heU (z : U) (v : W.Fiber z) : eU.linearEquiv z v =
      cU.linearEquiv z (cast (congrArg V.Fiber (DFunLike.congr_fun hfU z)) v) := by
    change (pullbackTrivialIso iU n).linearEquiv z
      (cU.linearEquiv z
        (((pullbackCompIso (E := V.Fiber) (DoubleSpace.leftMap A) iU).linearEquiv z).symm
          (qU.linearEquiv z ((pullbackCompIso (E := V.Fiber) f iU).linearEquiv z v)))) = _
    rw [pullbackTrivialIso_apply, hinvComp, hqU, pullbackCompIso_apply]
  have heL (z : L) (v : W.Fiber z) : eL.linearEquiv z v =
      cL.linearEquiv z (cast (congrArg V.Fiber (DFunLike.congr_fun hfL z)) v) := by
    change (pullbackTrivialIso iL n).linearEquiv z
      (cL.linearEquiv z
        (((pullbackCompIso (E := V.Fiber) (DoubleSpace.rightMap A) iL).linearEquiv z).symm
          (qL.linearEquiv z ((pullbackCompIso (E := V.Fiber) f iL).linearEquiv z v)))) = _
    rw [pullbackTrivialIso_apply, hinvComp, hqL, pullbackCompIso_apply]
  -- At the equator the two transports compose to the original double seam equality.
  refine ⟨W, eU, eL, ?_⟩
  intro x v
  let zU : U := ⟨UnreducedSuspension.equator X x, Or.inr ⟨x, _, le_rfl, rfl⟩⟩
  let zL : L := ⟨UnreducedSuspension.equator X x, Or.inr ⟨x, _, le_rfl, rfl⟩⟩
  let w : W.Fiber (UnreducedSuspension.equator X x) := (eU.linearEquiv zU).symm v
  have hu : cU.linearEquiv zU
      (cast (congrArg V.Fiber (DFunLike.congr_fun hfU zU)) w) = v :=
    (heU zU w).symm.trans (LinearEquiv.apply_symm_apply _ _)
  have hc := clutching_compatible hA a (e x)
    (cU.linearEquiv zU (cast (congrArg V.Fiber (DFunLike.congr_fun hfU zU)) w))
  change cL.linearEquiv zL
    (cast (congrArg V.Fiber (DoubleSpace.left_eq_right A (e x)))
      ((cU.linearEquiv zU).symm
        (cU.linearEquiv zU (cast (congrArg V.Fiber (DFunLike.congr_fun hfU zU)) w)))) =
    b.linearEquiv (e x)
      (cU.linearEquiv zU (cast (congrArg V.Fiber (DFunLike.congr_fun hfU zU)) w)) at hc
  rw [LinearEquiv.symm_apply_apply, hu, hb] at hc
  change eL.linearEquiv zL w = _
  rw [heL]
  convert hc using 1
  exact congrArg (cL.linearEquiv zL) (by simp only [cast_cast])

/-- The clutching bundle selected from its fully specified two-chart descent data. -/
def suspensionClutchingBundle (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    FiniteBundle (UnreducedSuspension X) :=
  (exists_suspensionClutchingBundle n α).choose

/-- The upper chart belonging to the same gluing witness. -/
def suspensionClutchingUpperIso (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    Iso ((suspensionClutchingBundle n α).restrict
      (UnreducedSuspension.upperHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.upperHemisphere X) n).Fiber :=
  (exists_suspensionClutchingBundle n α).choose_spec.choose

/-- The lower chart belonging to the same gluing witness. -/
def suspensionClutchingLowerIso (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    Iso ((suspensionClutchingBundle n α).restrict
      (UnreducedSuspension.lowerHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.lowerHemisphere X) n).Fiber :=
  (exists_suspensionClutchingBundle n α).choose_spec.choose_spec.choose

/-- The chosen charts satisfy the original upper-to-lower transition equation. -/
theorem suspensionClutching_compatible (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    SuspensionClutchingCompatible n α (suspensionClutchingBundle n α)
      (suspensionClutchingUpperIso n α) (suspensionClutchingLowerIso n α) := by
  -- The bundle and both charts are projections of one chosen descent witness.
  exact (exists_suspensionClutchingBundle n α).choose_spec.choose_spec.choose_spec

set_option backward.isDefEq.respectTransparency false in
/-- Two-chart descent determines the glued bundle up to an actual bundle isomorphism. -/
theorem nonempty_suspensionClutching_iso (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber)
    (W : FiniteBundle (UnreducedSuspension X))
    (eU : Iso (W.restrict (UnreducedSuspension.upperHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.upperHemisphere X) n).Fiber)
    (eL : Iso (W.restrict (UnreducedSuspension.lowerHemisphere X)).Fiber
      (FiniteBundle.trivial (UnreducedSuspension.lowerHemisphere X) n).Fiber)
    (h : SuspensionClutchingCompatible n α W eU eL) :
    Nonempty (Iso W.Fiber (suspensionClutchingBundle n α).Fiber) := by
  -- Compare the given and selected charts on each original hemisphere.
  classical
  let S := UnreducedSuspension X
  let U := UnreducedSuspension.upperHemisphere X
  let L := UnreducedSuspension.lowerHemisphere X
  obtain ⟨hU, hL, hcover, hUL, _⟩ := UnreducedSuspension.hemisphere_geometry X
  let V := suspensionClutchingBundle n α
  let dU := suspensionClutchingUpperIso n α
  let dL := suspensionClutchingLowerIso n α
  let cU := eU.trans dU.symm
  let cL := eL.trans dL.symm
  -- Their common transition alpha makes the two comparisons agree on the equator.
  have hseam (z : S) (hu : z ∈ U) (hl : z ∈ L) :
      cU.linearEquiv ⟨z, hu⟩ = cL.linearEquiv ⟨z, hl⟩ := by
    have hz : z ∈ Set.range (UnreducedSuspension.equator X) := by
      rw [← hUL]
      exact ⟨hu, hl⟩
    obtain ⟨x, rfl⟩ := hz
    apply LinearEquiv.ext
    intro v
    apply (dL.linearEquiv ⟨UnreducedSuspension.equator X x, hl⟩).injective
    change (dL.linearEquiv ⟨_, hl⟩)
      (((dU.linearEquiv ⟨_, hu⟩).symm) (eU.linearEquiv ⟨_, hu⟩ v)) =
      (dL.linearEquiv ⟨_, hl⟩)
        (((dL.linearEquiv ⟨_, hl⟩).symm) (eL.linearEquiv ⟨_, hl⟩ v))
    rw [LinearEquiv.apply_symm_apply]
    have hchosen := suspensionClutching_compatible n α x
      (eU.linearEquiv ⟨UnreducedSuspension.equator X x, hu⟩ v)
    have horiginal := h x (eU.linearEquiv ⟨UnreducedSuspension.equator X x, hu⟩ v)
    change (eL.linearEquiv ⟨_, hl⟩)
      (((eU.linearEquiv ⟨_, hu⟩).symm) (eU.linearEquiv ⟨_, hu⟩ v)) = _ at horiginal
    rw [LinearEquiv.symm_apply_apply] at horiginal
    exact hchosen.trans horiginal.symm
  -- Define the fiber equivalence by either side; compatibility removes the choice.
  have hmem (z : S) (hz : z ∉ U) : z ∈ L := by
    have hall : z ∈ U ∪ L := hcover ▸ Set.mem_univ z
    exact hall.resolve_left hz
  let e (z : S) : W.Fiber z ≃ₗ[ℂ] V.Fiber z :=
    if hz : z ∈ U then cU.linearEquiv ⟨z, hz⟩ else cL.linearEquiv ⟨z, hmem z hz⟩
  have heU (z : U) : e z = cU.linearEquiv z := by
    simp only [e, z.property, dite_true]
    rfl
  have heL (z : L) : e z = cL.linearEquiv z := by
    dsimp only [e]
    split_ifs with hu
    · exact hseam z hu z.property
    · rfl
  -- Closed hemisphere inclusions remain closed embeddings on actual total spaces.
  have hlift (K : FiniteBundle S) (Y : Set S)
      (f : C(Y, S)) (hf : Topology.IsClosedEmbedding f) :
      Topology.IsClosedEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) f) := by
    let j : TotalSpace Unit ((f : Y → S) *ᵖ K.Fiber) →
        Y × TotalSpace Unit K.Fiber := pullbackTotalSpaceEmbedding f
    have hj : Topology.IsEmbedding j := by
      refine ⟨inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f, ?_⟩
      rintro ⟨x, v⟩ ⟨y, w⟩ h
      have hxy : x = y := congrArg Prod.fst h
      subst y
      have hvw : v = w := TotalSpace.mk_injective (f x) (congrArg Prod.snd h)
      subst w
      rfl
    let graph : TotalSpace Unit K.Fiber → S × TotalSpace Unit K.Fiber :=
      fun z ↦ (z.proj, z)
    have hgraph : Continuous graph := (continuous_proj (E := K.Fiber)).prodMk continuous_id
    have hcomp : Topology.IsEmbedding (graph ∘ Pullback.lift (F := Unit) (E := K.Fiber) f) :=
      (hf.isEmbedding.prodMap Topology.IsEmbedding.id).comp hj
    have hemb : Topology.IsEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) f) :=
      Topology.IsEmbedding.of_comp (Pullback.continuous_lift Unit K.Fiber f) hgraph hcomp
    have hrange : Set.range (Pullback.lift (F := Unit) (E := K.Fiber) f) =
        (π Unit K.Fiber) ⁻¹' Set.range f := by
      ext ⟨y, v⟩
      constructor
      · rintro ⟨⟨x, w⟩, h⟩
        exact ⟨x, congrArg (π Unit K.Fiber) h⟩
      · rintro ⟨x, h⟩
        change f x = y at h
        subst y
        exact ⟨⟨x, v⟩, rfl⟩
    exact ⟨hemb, hrange ▸ hf.isClosed_range.preimage (continuous_proj (E := K.Fiber))⟩
  let iU : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let iL : C(L, S) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Continuity of either direction follows from this finite closed total-space cover.
  have hcontinuous (K H : FiniteBundle S) (f : ∀ z, K.Fiber z → H.Fiber z)
      (hupper : Continuous (fun z : TotalSpace Unit (K.restrict U).Fiber ↦
        (⟨z.proj.val, f z.proj.val z.snd⟩ : TotalSpace Unit H.Fiber)))
      (hlower : Continuous (fun z : TotalSpace Unit (K.restrict L).Fiber ↦
        (⟨z.proj.val, f z.proj.val z.snd⟩ : TotalSpace Unit H.Fiber))) :
      Continuous (fun z : TotalSpace Unit K.Fiber ↦
        (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) := by
    let l := Pullback.lift (F := Unit) (E := K.Fiber) iU
    let r := Pullback.lift (F := Unit) (E := K.Fiber) iL
    have hl := hlift K U iU hU.isClosedEmbedding_subtypeVal
    have hr := hlift K L iL hL.isClosedEmbedding_subtypeVal
    have hleft : ContinuousOn (fun z : TotalSpace Unit K.Fiber ↦
        (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) (Set.range l) := by
      rw [← Set.image_univ]
      exact hl.isEmbedding.isInducing.continuousOn_image_iff.mpr hupper.continuousOn
    have hright : ContinuousOn (fun z : TotalSpace Unit K.Fiber ↦
        (⟨z.proj, f z.proj z.snd⟩ : TotalSpace Unit H.Fiber)) (Set.range r) := by
      rw [← Set.image_univ]
      exact hr.isEmbedding.isInducing.continuousOn_image_iff.mpr hlower.continuousOn
    have hcoverTotal : Set.range l ∪ Set.range r = Set.univ := by
      apply Set.eq_univ_of_forall
      rintro ⟨z, v⟩
      have hz : z ∈ U ∪ L := hcover ▸ Set.mem_univ z
      rcases hz with hz | hz
      · exact Or.inl ⟨⟨⟨z, hz⟩, v⟩, rfl⟩
      · exact Or.inr ⟨⟨⟨z, hz⟩, v⟩, rfl⟩
    rw [← continuousOn_univ, ← hcoverTotal]
    exact hleft.union_of_isClosed hright hl.isClosed_range hr.isClosed_range
  -- Glue both directions of these same comparisons, not merely their K classes.
  refine ⟨{ linearEquiv := e, continuous_total := ?_, continuous_symm := ?_ }⟩
  · apply hcontinuous W V (fun z ↦ e z)
    · convert (Pullback.continuous_lift Unit V.Fiber iU).comp cU.continuous_total using 1
      funext z
      change (⟨z.proj.val, e z.proj.val z.snd⟩ : TotalSpace Unit V.Fiber) =
        ⟨_, cU.linearEquiv z.proj z.snd⟩
      rw [heU]
      rfl
    · convert (Pullback.continuous_lift Unit V.Fiber iL).comp cL.continuous_total using 1
      funext z
      change (⟨z.proj.val, e z.proj.val z.snd⟩ : TotalSpace Unit V.Fiber) =
        ⟨_, cL.linearEquiv z.proj z.snd⟩
      rw [heL]
      rfl
  · apply hcontinuous V W (fun z ↦ (e z).symm)
    · convert (Pullback.continuous_lift Unit W.Fiber iU).comp cU.continuous_symm using 1
      funext z
      change (⟨z.proj.val, (e z.proj.val).symm z.snd⟩ : TotalSpace Unit W.Fiber) =
        ⟨_, (cU.linearEquiv z.proj).symm z.snd⟩
      rw [heU]
      rfl
    · convert (Pullback.continuous_lift Unit W.Fiber iL).comp cL.continuous_symm using 1
      funext z
      change (⟨z.proj.val, (e z.proj.val).symm z.snd⟩ : TotalSpace Unit W.Fiber) =
        ⟨_, (cL.linearEquiv z.proj).symm z.snd⟩
      rw [heL]
      rfl

/-- Subtracting the same rank at the south pole gives the reduced clutching class. -/
theorem suspensionClutchingClass_mem_reduced (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    (suspensionClutchingBundle n α).kZeroClass -
        (FiniteBundle.trivial (UnreducedSuspension X) n).kZeroClass ∈
      reducedComplexKZero (UnreducedSuspension.south (X := X)) := by
  -- Evaluation lands in K-zero of the field, where rank detects equality.
  let s := UnreducedSuspension.south (X := X)
  let W := suspensionClutchingBundle n α
  change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ s).toRingHom
    (W.kZeroClass - (FiniteBundle.trivial (UnreducedSuspension X) n).kZeroClass) = 0
  apply (kZeroRank_bijective ℂ).1
  rw [map_zero]
  change complexKZeroRankAt s
    (kZeroClass W.Fiber - kZeroClass (Bundle.Trivial (UnreducedSuspension X) (Fin n → ℂ))) = 0
  rw [map_sub, rankAt_kZeroClass, rankAt_kZeroClass]
  -- The selected lower chart identifies the actual south fiber with the same rank.
  have hdim := ((suspensionClutchingLowerIso n α).linearEquiv
    ⟨s, Or.inl rfl⟩).finrank_eq
  exact sub_eq_zero.mpr (congrArg (fun k : ℕ ↦ (k : ℤ)) hdim)

/-- The actual reduced class [E_alpha] minus the trivial rank-n bundle. -/
def suspensionClutchingClass (n : ℕ)
    (α : Iso (FiniteBundle.trivial X n).Fiber (FiniteBundle.trivial X n).Fiber) :
    reducedComplexKZero (UnreducedSuspension.south (X := X)) :=
  ⟨(suspensionClutchingBundle n α).kZeroClass -
    (FiniteBundle.trivial (UnreducedSuspension X) n).kZeroClass,
    suspensionClutchingClass_mem_reduced n α⟩

end ComplexBundle

end AtiyahSinger
