/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.Suspension
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The reduced suspension of a compactification as the compactified real product

Public module ID: M2225.

For a locally compact Hausdorff X, the reduced suspension of X⁺ at its original
infinity is the one-point compactification of X × ℝ. We retain the existing
ordinary suspension and its meridian quotient, without introducing another
suspension carrier. Its complement of the collapsed meridian is parametrized by
the actual finite point x and the increasing height `unitInterval.sigmoid r`.
The inverse real coordinate at an interior height t is `log (t / (1-t))`.

The homeomorphism is assembled from this particular embedding using mathlib's
uniqueness theorem for one-point compactification. Thus its inverse on finite
points is the specified cylinder class, and the original infinity corresponds
to the existing reduced-suspension base point. Both poles and the whole infinity
meridian are collapsed. This also handles empty X without retaining an extra
pole or a spurious reduced K class.

This geometric comparison supports Karoubi II.3.30 and II.4.8--4.12. It does not
identify any clutching class, connecting homomorphism, or choice of its sign.
The proper-map naturality below uses the same product map and the same increasing
real coordinate. All comparisons below retain those original quotient and product maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology
open scoped unitInterval

universe u v

variable (X : Type u) [TopologicalSpace X]

/-- The actual finite-cylinder parametrization at increasing sigmoid height. -/
def reducedSuspensionCompactificationInclusion :
    C(X × ℝ, ReducedSuspension (∞ : OnePoint X)) :=
  (ReducedSuspension.quotientMap (∞ : OnePoint X)).comp
    (UnreducedSuspension.ofMap.comp
      ((⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ : C(X, OnePoint X)).prodMap
        ⟨unitInterval.sigmoid, unitInterval.continuous_sigmoid⟩))

/-- The specified parametrization embeds onto the complement of the collapsed meridian. -/
theorem reducedSuspensionCompactificationInclusion_geometry
    [LocallyCompactSpace X] [T2Space X] :
    IsEmbedding (reducedSuspensionCompactificationInclusion X) ∧
      Set.range (reducedSuspensionCompactificationInclusion X) =
        ({ReducedSuspension.basepoint (∞ : OnePoint X)}ᶜ :
          Set (ReducedSuspension (∞ : OnePoint X))) := by
  /- Stage 1: in X⁺ × I, the finite spatial points and strictly interior heights
  form the open set X × (0,1). It avoids the two endpoint sets and the infinity
  meridian. Each of the three existing pointed quotients is an embedding on
  the complement of its collapsed closed subset, with the subspace topology.
  Stage 2: the finite inclusion into X⁺ and the strictly increasing sigmoid
  are embeddings. Compose their product with those same quotient restrictions;
  this gives the displayed embedding, without choosing an inverse arbitrarily.
  Stage 3: a reduced-suspension class outside the collapsed meridian has a
  finite spatial representative and an interior height. The sigmoid range is
  exactly (0,1), so it has a representative in the displayed image. Conversely
  none of those representatives is collapsed. Empty X gives an empty complement
  and a singleton reduced suspension, so the same statement still holds. -/
  classical
  -- Each original pointed quotient embeds its unchanged closed-set complement.
  have hcomplement (Z : Type u) [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) :
      IsEmbedding (fun z : (Aᶜ : Set Z) ↦ PointedQuotient.of.{u, 0} A z) := by
    let e := PointedQuotient.onePointHomeomorph.{u, 0} A hA
    have heq : (fun z : (Aᶜ : Set Z) ↦ PointedQuotient.of.{u, 0} A z) =
        e.symm ∘ OnePoint.some := by
      funext z
      apply e.injective
      change e (PointedQuotient.of A z) = e (e.symm (z : OnePoint (Aᶜ : Set Z)))
      rw [e.apply_symm_apply]
      exact PointedQuotient.onePointHomeomorph_of A hA z
    rw [heq]
    exact e.symm.isEmbedding.comp OnePoint.isOpenEmbedding_coe.isEmbedding
  let A₀ := UnreducedSuspension.lowerEnd (OnePoint X)
  let A₁ := UnreducedSuspension.upperEnd (OnePoint X)
  let A₂ := Set.range (UnreducedSuspension.meridian (∞ : OnePoint X))
  have hA₀ : IsClosed A₀ := isClosed_singleton.preimage continuous_snd
  let : CompactSpace (UnreducedSuspension.LowerCone (OnePoint X)) :=
    PointedQuotient.compactSpace A₀
  let : T2Space (UnreducedSuspension.LowerCone (OnePoint X)) :=
    PointedQuotient.t2Space A₀ hA₀
  have hA₁ : IsClosed A₁ :=
    (isCompact_range ((PointedQuotient.continuous_of A₀).comp
      (continuous_id.prodMk continuous_const))).isClosed
  let : CompactSpace (UnreducedSuspension (OnePoint X)) := UnreducedSuspension.compactSpace
  let : T2Space (UnreducedSuspension (OnePoint X)) := UnreducedSuspension.t2Space
  have hA₂ : IsClosed A₂ := UnreducedSuspension.isClosed_range_meridian ∞
  -- An interior finite representative avoids both poles and the infinity meridian.
  have hupper (z : OnePoint X) (t : I) (ht : t ≠ 1) :
      PointedQuotient.of A₀ (z, t) ∉ A₁ := by
    rintro ⟨w, hw⟩
    rcases (PointedQuotient.of_eq_of_iff A₀ (w, 1) (z, t)).1 hw with
      heq | ⟨hzero, _⟩
    · exact ht (congrArg Prod.snd heq).symm
    · exact one_ne_zero hzero
  have hmeridian (x : X) (t : I) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
      UnreducedSuspension.of (x : OnePoint X) t ∉ A₂ := by
    rintro ⟨s, hs⟩
    rcases (PointedQuotient.of_eq_of_iff A₁
      (PointedQuotient.of A₀ (∞, s)) (PointedQuotient.of A₀ ((x : OnePoint X), t))).1 hs with
      hlower | ⟨_, htop⟩
    · rcases (PointedQuotient.of_eq_of_iff A₀ (∞, s) ((x : OnePoint X), t)).1 hlower with
        heq | ⟨_, hzero⟩
      · exact OnePoint.coe_ne_infty x (congrArg Prod.fst heq).symm
      · exact ht₀ hzero
    · exact hupper (x : OnePoint X) t ht₁ htop
  -- Compose the actual finite/sigmoid embedding with the three complement restrictions.
  let k₀ (p : X × ℝ) : OnePoint X × I := (p.1, unitInterval.sigmoid p.2)
  have hk₀ : IsEmbedding k₀ :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.prodMap Topology.isEmbedding_sigmoid
  have havoid₀ (p : X × ℝ) : k₀ p ∈ (A₀ᶜ : Set (OnePoint X × I)) :=
    ne_of_gt (unitInterval.sigmoid_pos p.2)
  let k₁ (p : X × ℝ) : UnreducedSuspension.LowerCone (OnePoint X) :=
    PointedQuotient.of A₀ (k₀ p)
  have hk₁ : IsEmbedding k₁ :=
    (hcomplement _ A₀ hA₀).comp (hk₀.codRestrict A₀ᶜ havoid₀)
  have havoid₁ (p : X × ℝ) : k₁ p ∈ (A₁ᶜ : Set _) :=
    hupper p.1 (unitInterval.sigmoid p.2) (ne_of_lt (unitInterval.sigmoid_lt_one p.2))
  let k₂ (p : X × ℝ) : UnreducedSuspension (OnePoint X) := PointedQuotient.of A₁ (k₁ p)
  have hk₂ : IsEmbedding k₂ :=
    (hcomplement _ A₁ hA₁).comp (hk₁.codRestrict A₁ᶜ havoid₁)
  have havoid₂ (p : X × ℝ) : k₂ p ∈ (A₂ᶜ : Set _) :=
    hmeridian p.1 (unitInterval.sigmoid p.2) (ne_of_gt (unitInterval.sigmoid_pos p.2))
      (ne_of_lt (unitInterval.sigmoid_lt_one p.2))
  have hk₃ : IsEmbedding (reducedSuspensionCompactificationInclusion X) :=
    (hcomplement _ A₂ hA₂).comp (hk₂.codRestrict A₂ᶜ havoid₂)
  refine ⟨hk₃, ?_⟩
  -- Every nonbase class has a finite representative at a strictly interior height.
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    change reducedSuspensionCompactificationInclusion X p ≠
      ReducedSuspension.basepoint (∞ : OnePoint X)
    intro h
    exact havoid₂ p ((PointedQuotient.of_eq_basepoint_iff A₂ (k₂ p)).1 h)
  · intro hz
    change z ≠ ReducedSuspension.basepoint (∞ : OnePoint X) at hz
    rcases PointedQuotient.eq_basepoint_or_exists A₂ z with hbase | ⟨w, rfl⟩
    · exact (hz hbase).elim
    have hw : w ∉ A₂ := by
      intro hw
      exact hz ((PointedQuotient.of_eq_basepoint_iff A₂ w).2 hw)
    rcases PointedQuotient.eq_basepoint_or_exists A₁ w with hnorth | ⟨l, rfl⟩
    · apply (hw ?_).elim
      refine ⟨1, ?_⟩
      change UnreducedSuspension.of (∞ : OnePoint X) 1 = w
      exact (UnreducedSuspension.of_one ∞).trans hnorth.symm
    rcases PointedQuotient.eq_basepoint_or_exists A₀ l with hsouth | ⟨⟨xp, t⟩, rfl⟩
    · apply (hw ?_).elim
      refine ⟨0, ?_⟩
      change UnreducedSuspension.of (∞ : OnePoint X) 0 = PointedQuotient.of A₁ l
      exact (UnreducedSuspension.of_zero ∞).trans
        (congrArg (PointedQuotient.of A₁) hsouth.symm)
    have ht₀ : t ≠ 0 := by
      intro ht
      subst t
      apply hw
      exact ⟨0, (UnreducedSuspension.of_zero ∞).trans
        (UnreducedSuspension.of_zero xp).symm⟩
    have ht₁ : t ≠ 1 := by
      intro ht
      subst t
      apply hw
      exact ⟨1, (UnreducedSuspension.of_one ∞).trans
        (UnreducedSuspension.of_one xp).symm⟩
    cases xp using OnePoint.rec with
    | infty => exact (hw ⟨t, rfl⟩).elim
    | coe x =>
      have ht : t ∈ Set.range unitInterval.sigmoid := by
        rw [unitInterval.range_sigmoid]
        exact ⟨lt_of_le_of_ne t.property.1 ht₀.symm, lt_of_le_of_ne t.property.2 ht₁⟩
      obtain ⟨r, hr⟩ := ht
      refine ⟨(x, r), ?_⟩
      change ReducedSuspension.quotientMap ∞
        (UnreducedSuspension.of (x : OnePoint X) (unitInterval.sigmoid r)) =
          ReducedSuspension.quotientMap ∞ (UnreducedSuspension.of (x : OnePoint X) t)
      rw [hr]

attribute [local instance] ReducedSuspension.compactSpace ReducedSuspension.t2Space

/-- The compactification homeomorphism determined by the actual finite-cylinder map. -/
def reducedSuspensionOnePointHomeomorph [LocallyCompactSpace X] [T2Space X] :
    ReducedSuspension (∞ : OnePoint X) ≃ₜ OnePoint (X × ℝ) :=
  (OnePoint.equivOfIsEmbeddingOfRangeEq
    (ReducedSuspension.basepoint (∞ : OnePoint X))
    (reducedSuspensionCompactificationInclusion X)
    (reducedSuspensionCompactificationInclusion_geometry X).1
    (reducedSuspensionCompactificationInclusion_geometry X).2).symm

/-- The existing collapsed-meridian base point maps to the original infinity. -/
theorem reducedSuspensionOnePointHomeomorph_basepoint [LocallyCompactSpace X] [T2Space X] :
    reducedSuspensionOnePointHomeomorph X
      (ReducedSuspension.basepoint (∞ : OnePoint X)) = ∞ := by
  /- The forward map of the underlying OnePoint comparison sends infinity to
  the specified reduced base point by its infinity branch. Apply the inverse
  law for that same homeomorphism; no pole is selected instead of the meridian. -/
  apply (reducedSuspensionOnePointHomeomorph X).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The inverse comparison inserts the original finite point at its sigmoid height. -/
theorem reducedSuspensionOnePointHomeomorph_symm_coe [LocallyCompactSpace X] [T2Space X]
    (x : X) (r : ℝ) :
    (reducedSuspensionOnePointHomeomorph X).symm ((x, r) : X × ℝ) =
      ReducedSuspension.quotientMap (∞ : OnePoint X)
        (UnreducedSuspension.of (x : OnePoint X) (unitInterval.sigmoid r)) := by
  /- Evaluate the finite branch of OnePoint.equivOfIsEmbeddingOfRangeEq. Its
  prescribed value is precisely reducedSuspensionCompactificationInclusion,
  whose continuous-map composites retain x and the existing sigmoid function. -/
  rfl

/-- At an interior height the forward comparison has the increasing logit coordinate. -/
theorem reducedSuspensionOnePointHomeomorph_of [LocallyCompactSpace X] [T2Space X]
    (x : X) (t : I) (ht₀ : 0 < t) (ht₁ : t < 1) :
    reducedSuspensionOnePointHomeomorph X
        (ReducedSuspension.quotientMap (∞ : OnePoint X)
          (UnreducedSuspension.of (x : OnePoint X) t)) =
      (((x, Real.log ((t : ℝ) / (1 - (t : ℝ)))) : X × ℝ) : OnePoint (X × ℝ)) := by
  /- The strict height inequalities make t/(1-t) positive. The exp/log inverse
  identities give sigmoid(log(t/(1-t)))=t. Substitute this same real parameter
  into the preceding finite-branch formula and apply the inverse homeomorphism
  law. The coordinate increases from minus infinity to plus infinity; neither
  reflection nor a change in the order of the two original poles is introduced. -/
  have hpos : 0 < (t : ℝ) / (1 - (t : ℝ)) :=
    div_pos ht₀ (sub_pos.mpr ht₁)
  -- The chosen inverse coordinate is exactly logit, with its increasing orientation.
  have hs : unitInterval.sigmoid (Real.log ((t : ℝ) / (1 - (t : ℝ)))) = t := by
    apply Subtype.ext
    change Real.sigmoid (Real.log ((t : ℝ) / (1 - (t : ℝ)))) = (t : ℝ)
    rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log hpos]
    field_simp [ne_of_gt (show (0 : ℝ) < t from ht₀),
      sub_ne_zero.mpr (ne_of_gt (show (t : ℝ) < 1 from ht₁))]
    ring
  apply (reducedSuspensionOnePointHomeomorph X).symm.injective
  rw [Homeomorph.symm_apply_apply, reducedSuspensionOnePointHomeomorph_symm_coe, hs]

variable {X} {Y : Type v} [TopologicalSpace Y]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- Proper base maps commute with the same compactification and suspension coordinates. -/
theorem reducedSuspensionOnePointHomeomorph_natural (f : C(X, Y)) (hf : IsProperMap f) :
    (⟨reducedSuspensionOnePointHomeomorph Y,
      (reducedSuspensionOnePointHomeomorph Y).continuous⟩ :
        C(ReducedSuspension (∞ : OnePoint Y), OnePoint (Y × ℝ))).comp
      (ReducedSuspension.map (properOnePointMap f hf) ∞ ∞ rfl) =
    (properOnePointMap (f.prodMap (ContinuousMap.id ℝ))
      (hf.prodMap isProperMap_id)).comp
        ⟨reducedSuspensionOnePointHomeomorph X,
          (reducedSuspensionOnePointHomeomorph X).continuous⟩ := by
  /- Stage 1: precompose with the inverse of the specified source homeomorphism,
  so it suffices to check original finite points and infinity of (X × ℝ)⁺.
  On infinity every map preserves the same collapsed meridian or infinity.
  Stage 2: on (x,r), the inverse comparison inserts x at sigmoid(r). Suspending
  the actual one-point extension of f sends this to f(x) at the identical height.
  The target comparison returns (f(x),r), exactly the finite branch of the
  proper extension of f × id. Extensionality proves the stated continuous-map
  equality. Properness is used for those extensions, not for the quotient map. -/
  have hbase : (reducedSuspensionOnePointHomeomorph X).symm ∞ =
      ReducedSuspension.basepoint (∞ : OnePoint X) :=
    (reducedSuspensionOnePointHomeomorph X).symm_apply_eq.mpr
      (reducedSuspensionOnePointHomeomorph_basepoint X).symm
  let P := properOnePointMap (f.prodMap (ContinuousMap.id ℝ)) (hf.prodMap isProperMap_id)
  let S := ReducedSuspension.map (properOnePointMap f hf) ∞ ∞ rfl
  -- Check the maps after the specified inverse comparison, on both sorts of point.
  ext z
  obtain ⟨w, rfl⟩ := (reducedSuspensionOnePointHomeomorph X).symm.surjective z
  change reducedSuspensionOnePointHomeomorph Y
    (S ((reducedSuspensionOnePointHomeomorph X).symm w)) =
      P (reducedSuspensionOnePointHomeomorph X
        ((reducedSuspensionOnePointHomeomorph X).symm w))
  suffices h : reducedSuspensionOnePointHomeomorph Y
      (S ((reducedSuspensionOnePointHomeomorph X).symm w)) = P w by
    exact h.trans (congrArg P
      ((reducedSuspensionOnePointHomeomorph X).apply_symm_apply w)).symm
  cases w using OnePoint.rec with
  | infty =>
    calc
      reducedSuspensionOnePointHomeomorph Y
          (S ((reducedSuspensionOnePointHomeomorph X).symm ∞)) =
          reducedSuspensionOnePointHomeomorph Y
            (S (ReducedSuspension.basepoint (∞ : OnePoint X))) :=
        congrArg (fun z ↦ reducedSuspensionOnePointHomeomorph Y (S z)) hbase
      _ = ∞ := reducedSuspensionOnePointHomeomorph_basepoint Y
      _ = P ∞ := rfl
  | coe p =>
    rcases p with ⟨x, r⟩
    calc
      reducedSuspensionOnePointHomeomorph Y
          (S ((reducedSuspensionOnePointHomeomorph X).symm ((x, r) : X × ℝ))) =
          reducedSuspensionOnePointHomeomorph Y
            (S (ReducedSuspension.quotientMap ∞
              (UnreducedSuspension.of (x : OnePoint X) (unitInterval.sigmoid r)))) :=
        congrArg (fun z ↦ reducedSuspensionOnePointHomeomorph Y (S z))
          (reducedSuspensionOnePointHomeomorph_symm_coe X x r)
      _ = reducedSuspensionOnePointHomeomorph Y
          (ReducedSuspension.quotientMap ∞
            (UnreducedSuspension.of (f x : OnePoint Y) (unitInterval.sigmoid r))) := rfl
      _ = (((f x, r) : Y × ℝ) : OnePoint (Y × ℝ)) := by
        apply (reducedSuspensionOnePointHomeomorph Y).symm.injective
        rw [Homeomorph.symm_apply_apply, reducedSuspensionOnePointHomeomorph_symm_coe]
      _ = P ((x, r) : X × ℝ) := rfl

end AtiyahSinger
