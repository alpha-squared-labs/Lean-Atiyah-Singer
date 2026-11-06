/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyPowerNaturality
public import AtiyahSinger.Topology.ProjectiveTautologicalChart
public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients
public import AtiyahSinger.Topology.SingularCohomologyLerayHirschDescent
public import AtiyahSinger.Topology.SingularCohomologyLerayHirschTransport

/-!
# Descent from the standard projective model to the original bundle

Public module ID: M1896.

The original orthonormal projective charts retain the supplied metric, native
fiber norms and total topology. Over any subset of one chart, their actual
product homeomorphism identifies the original normalized tautological class
with the standard one. The corresponding cup powers therefore give precisely
the same finite Leray--Hirsch comparison on every finite cover intersection.
Open-cover cochain descent proves the global comparison.

The standard projective product theorem, for every parameter space and
cohomological degree, is an explicit premise here.
`HermitianProjectiveBundleCohomology` supplies it from the original
projective-product calculation to obtain the bundle theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory HomologicalComplex
open HermitianProjectiveSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

set_option maxHeartbeats 800000 in
-- The model hypothesis retains the full dependent projective cohomology and cocycle families.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The standard projective product comparison descends to the original Hermitian bundle. -/
theorem homologyMap_hermitianProjectiveLerayHirsch_bijective_of_model
    (hmodel :
      let W := ULift.{u} (EuclideanSpace ℂ (Fin r))
      let P := HermitianProjectiveSpace W InnerProductSpace.toCore
      ∀ (Z : Type u) [TopologicalSpace Z]
        (c₀ : ∀ i : ULift.{u} (Fin r), singularCocycles R (Z × P) (2 * i.down.val)),
        (∀ i : ULift.{u} (Fin r), singularCocycleClass R (Z × P) (2 * i.down.val) (c₀ i) =
          singularCohomologyPullback R ContinuousMap.snd (2 * i.down.val)
            (singularCohomologyDegreeTwoPow R P
              (singularCohomologyChangeCoefficients R P 2 (tautologicalChernRoot W)) i.down.val)) →
        ∀ n : ℕ, Function.Bijective (homologyMap
          (singularCohomologyLerayHirschMap R ContinuousMap.fst
            (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c₀) n))
    (c : ∀ i : ULift.{u} (Fin r),
      singularCocycles R (HermitianProjectiveBundle r E h) (2 * i.down.val))
    (hc : ∀ i : ULift.{u} (Fin r), singularCocycleClass R (HermitianProjectiveBundle r E h)
        (2 * i.down.val) (c i) =
      singularCohomologyDegreeTwoPow R (HermitianProjectiveBundle r E h)
        (singularCohomologyChangeCoefficients R (HermitianProjectiveBundle r E h) 2
          (hermitianProjectiveChernRoot r E h)) i.down.val) (n : ℕ) :
    Function.Bijective (homologyMap
      (singularCohomologyLerayHirschMap R (hermitianProjectiveProjection r E h)
        (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c) n) := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let W := ULift.{u} V
  let P := HermitianProjectiveSpace W InnerProductSpace.toCore
  let Q := HermitianProjectiveBundle r E h
  let p := hermitianProjectiveProjection r E h
  let d (i : ULift.{u} (Fin r)) := 2 * i.down.val
  let root := hermitianProjectiveChernRoot r E h
  let root₀ := tautologicalChernRoot W
  let rootR := singularCohomologyChangeCoefficients R Q 2 root
  let root₀R := singularCohomologyChangeCoefficients R P 2 root₀
  let := modelTopology V E
  -- Choose the original charts together with their same continuous orthonormal frames.
  choose t ht s hs hsection hconj using (exists_hermitianProjectiveTrivialization r E h)
  let U (x : X) := (t x).baseSet
  have hOpen (x : X) : IsOpen (U x) := (t x).open_baseSet
  have hCover : (⋃ x, U x) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, ht x⟩
  -- The actual pullback functor composes without changing any coefficient, point or degree.
  have hcomp (S : Type) [CommRing S] {A B C : Type u}
      [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
      (f : C(A, B)) (g : C(B, C)) (k : ℕ) (a : singularCohomology S C k) :
      singularCohomologyPullback S f k (singularCohomologyPullback S g k a) =
        singularCohomologyPullback S (g.comp f) k a :=
    congrArg (fun F ↦ F a)
      ((singularCohomologyFunctor S k).map_comp (TopCat.ofHom g).op (TopCat.ofHom f).op).symm
  apply homologyMap_singularCohomologyLerayHirschMap_bijective_of_openCover R p U
    hOpen hCover d c ?_ n
  intro m a k
  let S := singularCechIntersection U a
  have hS : S ⊆ (t (a 0)).baseSet := fun _ hx ↦ hx 0
  let J : C(p ⁻¹' S, Q) := ContinuousMap.subtypeVal (p ⁻¹' S)
  let J₀ : C(p ⁻¹' (t (a 0)).baseSet, Q) :=
    ContinuousMap.subtypeVal (p ⁻¹' (t (a 0)).baseSet)
  let l : C(p ⁻¹' S, p ⁻¹' (t (a 0)).baseSet) :=
    ⟨fun q ↦ ⟨q.val, hS q.property⟩, continuous_subtype_val.subtype_mk _⟩
  let fiber := hermitianProjectiveChartFiber r E h (t (a 0))
  let lift := mapLinearIsometryEquiv (LinearIsometryEquiv.ulift ℂ V).symm
  let H : (p ⁻¹' S) ≃ₜ S × P := ((t (a 0)).preimageHomeomorph hS).trans
    ((Homeomorph.refl S).prodCongr lift)
  let f : C(S × P, p ⁻¹' S) := H.symm
  let g : C(S × P, Q) := J.comp f
  -- Both coordinates of the chart use the same original point and projector.
  have hbase (q : p ⁻¹' S) : (H q).1 = (p.restrictPreimage S) q := by
    change (((t (a 0)).preimageHomeomorph hS) q).1 = _
    rw [Trivialization.preimageHomeomorph_apply]
    rfl
  have hfiber (q : p ⁻¹' S) : (H q).2 = fiber (l q) := by
    change lift (((t (a 0)).preimageHomeomorph hS) q).2 = _
    rw [Trivialization.preimageHomeomorph_apply]
    rfl
  have hp : (p.restrictPreimage S).comp f = ContinuousMap.fst := by
    apply ContinuousMap.ext
    intro z
    exact (hbase (H.symm z)).symm.trans (congrArg Prod.fst (H.apply_symm_apply z))
  have hproj : fiber.comp (l.comp f) = ContinuousMap.snd := by
    apply ContinuousMap.ext
    intro z
    exact (hfiber (H.symm z)).symm.trans (congrArg Prod.snd (H.apply_symm_apply z))
  have hchart := hermitianProjectiveChernRoot_restrict_chart r E h (t (a 0))
    (s (a 0)) (hs (a 0)) (hsection (a 0)) (hconj (a 0))
  have hroot : singularCohomologyPullback ℤ g 2 root =
      singularCohomologyPullback ℤ ContinuousMap.snd 2 root₀ := by
    have ht := congrArg (singularCohomologyPullback ℤ (l.comp f) 2) hchart
    rw [hcomp, hcomp, hproj] at ht
    exact ht
  have hrootR : singularCohomologyPullback R g 2 rootR =
      singularCohomologyPullback R ContinuousMap.snd 2 root₀R := by
    calc
      _ = singularCohomologyChangeCoefficients R (S × P) 2
          (singularCohomologyPullback ℤ g 2 root) :=
        (singularCohomologyChangeCoefficients_naturality R g 2 root).symm
      _ = singularCohomologyChangeCoefficients R (S × P) 2
          (singularCohomologyPullback ℤ ContinuousMap.snd 2 root₀) := congrArg _ hroot
      _ = singularCohomologyPullback R ContinuousMap.snd 2 root₀R :=
        singularCohomologyChangeCoefficients_naturality R
          (ContinuousMap.snd : C(S × P, P)) 2 root₀
  let cS (i : ULift.{u} (Fin r)) := singularCocyclePullback R J (d i) (c i)
  let c₀ (i : ULift.{u} (Fin r)) := singularCocyclePullback R f (d i) (cS i)
  have hc₀ (i : ULift.{u} (Fin r)) : singularCocycleClass R (S × P) (d i) (c₀ i) =
      singularCohomologyPullback R ContinuousMap.snd (d i)
        (singularCohomologyDegreeTwoPow R P root₀R i.down.val) := by
    -- Cup powers are transported only after identifying the same normalized root over R.
    rw [singularCocycleClass_pullback, singularCocycleClass_pullback, hc, hcomp]
    change singularCohomologyPullback R g (2 * i.down.val)
      (singularCohomologyDegreeTwoPow R Q rootR i.down.val) = _
    rw [singularCohomologyPullback_degreeTwoPow, hrootR]
    exact (singularCohomologyPullback_degreeTwoPow R ContinuousMap.snd root₀R i.down.val).symm
  have hmodelS := hmodel S c₀ hc₀ k
  have htransport := homologyMap_singularCohomologyLerayHirschMap_comp_pullback R
    (p.restrictPreimage S) ContinuousMap.fst f hp d cS c₀
    (fun i ↦ (singularCocycleClass_pullback R f (d i) (cS i)).symm) k
  -- The actual inverse chart is a homeomorphism, so its original cohomology pullback is bijective.
  have hmap : Function.Bijective (singularCohomologyPullback R f k) := by
    let eH : TopCat.of (S × P) ≅ TopCat.of (p ⁻¹' S) := TopCat.isoOfHomeo H.symm
    let : IsIso (TopCat.ofHom f) := by
      change IsIso eH.hom
      infer_instance
    change Function.Bijective ((singularCohomologyFunctor R k).map (TopCat.ofHom f).op)
    exact ConcreteCategory.bijective_of_isIso _
  apply (hmap.of_comp_iff' _).mp
  change Function.Bijective (homologyMap
    (singularCohomologyLerayHirschMap R (p.restrictPreimage S) d cS) k ≫
      singularCohomologyPullback R f k)
  rw [htransport]
  exact hmodelS

end AtiyahSinger.ComplexBundle
