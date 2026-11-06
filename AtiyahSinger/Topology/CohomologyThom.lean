/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyOrientation
public import AtiyahSinger.Topology.LocalCohomologyThom
public import AtiyahSinger.Topology.LocalCohomologyThomCup
public import AtiyahSinger.Topology.RealBundleSupport
public import AtiyahSinger.Topology.RelativeCohomologyCup
public import AtiyahSinger.Topology.SingularCohomologyCupDescent
public import AtiyahSinger.Topology.SingularCohomologyDescent

/-!
# The actual relative cohomological Thom class and isomorphism

Public module ID: M1629.

C03. A locally compatible family of fiber generators first gives a unique
global class on the original pair (E,E minus the zero section). This is a
theorem, not a field of the orientation. The chosen class is then multiplied
on the right of the actual pullback from the base. A separate theorem asserts
bijectivity of that particular linear map, giving the Thom equivalence.

Sources: Milnor--Stasheff, Characteristic Classes, Theorem 9.1 and Section 10;
Hatcher, Algebraic Topology, Theorems 4D.8--4D.10; and the relative version
underlying SG III.12.1--12.2. Hatcher 4D.8--4D.9 supplies relative Leray--Hirsch
and the Thom isomorphism given a global Thom class. Theorem 4D.10 proves
existence for integral orientations and for mod-two coefficients, using CW
approximation and relative Mayer--Vietoris. The arbitrary commutative R and
local-unit orientation statement here is a project supplementary formulation
of that R-module argument, not the literal scope of Theorem 4D.10.

MS Theorem 10.4 obtains arbitrary coefficients from an integrally normalized
geometric orientation by coefficient change. That route does not supply an
arbitrary chosen R-orientation. We neither tensor a bare integral cohomology
isomorphism nor use compact-subset inverse limits over a general ring: MS
p.109 explicitly warns that the latter comparison can fail for integers.
The arbitrary-base existence argument below uses the actual small-chain Čech
resolution and finite cohomological descent. The local calculations follow the
original pair connecting maps and retain all base coordinates. Compactness and
paracompactness are not hypotheses on the original base.

Rank zero is included as an explicit supplementary case: the fiber pair is
(point,empty), and a local R-orientation is a locally compatible choice of
units. The Thom map then multiplies by that degree-zero unit class and need
not be the identity unless the orientation is canonically normalized.

This module does not identify the inverse with integration of differential
forms, or replace relative support by ordinary total-space compact support.
GeometricCohomologyOrientation separately constructs the integral orientation
from compatible real frames; support and Gysin comparisons have their own hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Opposite

universe u

variable (R : Type) [CommRing R]
  (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [hV : VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hV in
/-- A local R-orientation extends uniquely to a class on the original total-space pair. -/
theorem existsUnique_cohomologyThomClass :
    ∃! U : relativeSingularCohomology R (bundleNonzero r E) r,
      ∀ x : X,
        relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
          (A := {v : E x | v ≠ 0}) (B := bundleNonzero r E)
          (fun _ hv ↦ hv) r U = o.fiberClass x := by
  /- Refine the given local extensions by the original linear trivializations.
  On every intersection the product calculation gives vanishing below the rank,
  and the original fiber restrictions determine the rank-degree class. Thus the
  local classes agree on overlaps. The actual small-chain Čech resolution glues
  them uniquely; its comparison map returns a class on the original total-space
  pair. Finally, the same fiber detection proves global uniqueness. This finite
  cochain descent includes rank zero and the zero coefficient ring. -/
  choose O hO hx c hc using o.locally_compatible
  let V (x : X) := O x ∩ (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).baseSet
  let U (x : X) := (bundleProjection r E) ⁻¹' V x
  let S (n : ℕ) (a : Fin (n + 1) → X) : Set X := {x | ∀ i, x ∈ V (a i)}
  let res (B D : Set X) (hBD : B ⊆ D) :
      C(BundleTotalOver r E B, BundleTotalOver r E D) :=
    ⟨fun z ↦ ⟨z.val, hBD z.property⟩, continuous_subtype_val.subtype_mk _⟩
  let l (n : ℕ) (a : Fin (n + 1) → X) :
      relativeSingularCohomology R (bundleNonzeroOver r E (S n a)) r :=
    relativeSingularCohomologyPullback R
      (res (S n a) (O (a 0)) (fun _ hy ↦ (hy 0).1))
      (A := bundleNonzeroOver r E (S n a)) (B := bundleNonzeroOver r E (O (a 0)))
      (fun _ hv ↦ hv) r (c (a 0))
  have hOpen (x : X) : IsOpen (U x) :=
    ((hO x).inter (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).open_baseSet).preimage
      (bundleProjection r E).continuous
  have hCover : ⋃ x, U x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    apply Set.mem_iUnion.mpr
    exact ⟨z.proj, hx z.proj, FiberBundle.mem_baseSet_trivializationAt'
      (F := EuclideanSpace ℝ (Fin r)) z.proj⟩
  -- Each chosen class restricts to the prescribed original fiber class.
  have hlocal (n : ℕ) (a : Fin (n + 1) → X) (y : X) (hy : y ∈ S n a) :
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E (S n a) y hy)
        (A := {v : E y | v ≠ 0}) (B := bundleNonzeroOver r E (S n a))
        (fun _ hv ↦ hv) r (l n a) = o.fiberClass y := by
    change relativeSingularCohomologyPullback R _ _ r
      (relativeSingularCohomologyPullback R _ _ r (c (a 0))) = _
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact hc (a 0) y (hy 0).1
  have hrestrict (n m : ℕ) (a : Fin (n + 1) → X) (b : Fin (m + 1) → X)
      (hab : S m b ⊆ S n a) :
      relativeSingularCohomologyPullback R (res (S m b) (S n a) hab)
        (A := bundleNonzeroOver r E (S m b)) (B := bundleNonzeroOver r E (S n a))
        (fun _ hv ↦ hv) r (l n a) = l m b := by
    apply relativeSingularCohomology_bundleTotalOver_ext R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (b 0))
      (S m b) (fun _ hy ↦ (hy 0).2)
    intro y hy
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact (hlocal n a y (hab hy)).trans (hlocal m b y hy).symm
  have hvan (m : ℕ) (a : Fin (m + 2) → X) (q : ℕ) (hq : q < r) :
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U a → _ ) ⁻¹' bundleNonzero r E) q) := by
    change Subsingleton (relativeSingularCohomology R (bundleNonzeroOver r E (S (m + 1) a)) q)
    exact subsingleton_relativeSingularCohomology_bundleTotalOver_below_rank R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S (m + 1) a) (fun _ hy ↦ (hy 0).2) q hq
  let C := singularCechCochains R U (bundleNonzero r E)
  let δ := singularCechDifferential R U (bundleNonzero r E)
  let family (n : ℕ) (a : Fin (n + 1) → X) :=
    (relativeSingularCochainsPresheaf R (bundleNonzero r E)).obj
      (op (singularCechIntersection U a))
  let pr (n : ℕ) (a : Fin (n + 1) → X) : C (n + 1) ⟶ family n a :=
    cochainFamilyProductProjection R (family n) a
  have hbij (n : ℕ) : Function.Bijective (fun z : (C (n + 1)).homology r ↦
      fun a ↦ HomologicalComplex.homologyMap (pr n a) r z) := by
    exact bijective_homologyMap_cochainFamilyProductProjection R (family n) r
  obtain ⟨b, hb⟩ := (hbij 0).surjective (l 0)
  have hb' (a : Fin 1 → X) :
      HomologicalComplex.homologyMap (pr 0 a) r b = l 0 a := congrFun hb a
  let face (a : Fin 2 → X) (j : Fin 2) : Fin 1 → X :=
    a ∘ (SimplexCategory.δ j).toOrderHom
  let restrict (a : Fin 2 → X) (j : Fin 2) : family 0 (face a j) ⟶ family 1 a :=
    (singularCochainDualFunctor R).map (relativeSingularChainsMap R
      (res (S 1 a) (S 0 (face a j)) (fun _ hy i ↦ hy _))
      (A := bundleNonzeroOver r E (S 1 a))
      (B := bundleNonzeroOver r E (S 0 (face a j))) (fun _ hv ↦ hv)).op
  let d : C 1 ⟶ C 2 := δ 1
  have hδ (a : Fin 2 → X) : d ≫ pr 1 a =
      pr 0 (face a 0) ≫ restrict a 0 -
        pr 0 (face a 1) ≫ restrict a 1 := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change (singularCechDifferential R U (bundleNonzero r E) 1).f q v a = _
    rw [singularCechDifferential_succ_apply R U (bundleNonzero r E) 0 q v a,
      Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
      neg_one_zsmul, ← sub_eq_add_neg]
    rfl
  have hclosed : HomologicalComplex.homologyMap d r b = 0 := by
    apply (hbij 1).injective
    funext a
    change HomologicalComplex.homologyMap (pr 1 a) r
      (HomologicalComplex.homologyMap d r b) =
      HomologicalComplex.homologyMap (pr 1 a) r 0
    rw [map_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
      hδ, HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap (restrict a 0) r
        (HomologicalComplex.homologyMap
          (pr 0 (face a 0)) r b) -
      HomologicalComplex.homologyMap (restrict a 1) r
        (HomologicalComplex.homologyMap
          (pr 0 (face a 1)) r b) = 0
    rw [hb', hb']
    apply sub_eq_zero.mpr
    exact (hrestrict 0 1 (face a 0) a (fun _ hy i ↦ hy _)).trans
      (hrestrict 0 1 (face a 1) a (fun _ hy i ↦ hy _)).symm
  -- Čech descent now gives a unique original global class with this local family.
  let G : relativeSingularCochains R (bundleNonzero r E) ⟶
      C 1 := smallRelativeSingularCochainsRestriction R (Set.range U) (bundleNonzero r E) ≫ δ 0
  obtain ⟨z, hz, huniq⟩ := existsUnique_relativeSingularCohomology_of_cech R U
    (bundleNonzero r E) hOpen hCover r hvan b hclosed
  let inc (a : Fin 1 → X) : C(BundleTotalOver r E (S 0 a),
      TotalSpace (EuclideanSpace ℝ (Fin r)) E) := ⟨Subtype.val, continuous_subtype_val⟩
  have hprojection (w : relativeSingularCohomology R (bundleNonzero r E) r)
      (a : Fin 1 → X) :
      HomologicalComplex.homologyMap (pr 0 a) r
        (HomologicalComplex.homologyMap G r w) =
      relativeSingularCohomologyPullback R (inc a)
        (A := bundleNonzeroOver r E (S 0 a)) (B := bundleNonzero r E)
        (fun _ hv ↦ hv) r w := by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp]
    have heq := smallRelativeSingularCochainsRestriction_cechAugmentation_projection R U
      (bundleNonzero r E) a
    change HomologicalComplex.homologyMap ((smallRelativeSingularCochainsRestriction R
      (Set.range U) (bundleNonzero r E) ≫ singularCechAugmentation R U (bundleNonzero r E)) ≫
        pr 0 a) r w = _
    rw [Category.assoc, heq]
    rfl
  have hzlocal (a : Fin 1 → X) :
      relativeSingularCohomologyPullback R (inc a)
        (A := bundleNonzeroOver r E (S 0 a)) (B := bundleNonzero r E)
        (fun _ hv ↦ hv) r z = l 0 a := by
    rw [← hprojection, hz]
    exact hb' a
  refine ⟨z, ?_, ?_⟩
  · intro x
    let a : Fin 1 → X := fun _ ↦ x
    have hxa : x ∈ S 0 a := fun _ ↦ ⟨hx x,
      FiberBundle.mem_baseSet_trivializationAt' (F := EuclideanSpace ℝ (Fin r)) x⟩
    have h := hlocal 0 a x hxa
    rw [← hzlocal a] at h
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp] at h
    exact h
  · intro w hw
    apply huniq
    apply (hbij 0).injective
    funext a
    change HomologicalComplex.homologyMap (pr 0 a) r
      (HomologicalComplex.homologyMap G r w) = HomologicalComplex.homologyMap (pr 0 a) r b
    rw [hb', hprojection]
    apply relativeSingularCohomology_bundleTotalOver_ext R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S 0 a) (fun _ hy ↦ (hy 0).2)
    intro x hxa
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact (hw x).trans (hlocal 0 a x hxa).symm

/-- The unique global class determined by the specified local fiber orientation. -/
def cohomologyThomClass : relativeSingularCohomology R (bundleNonzero r E) r :=
  (existsUnique_cohomologyThomClass R r E o).exists.choose

/-- The actual Thom map sends a to pi-star a cup U, in that order. -/
def cohomologyThomMap (p : ℕ) :
    singularCohomology R X p →ₗ[R]
      relativeSingularCohomology R (bundleNonzero r E) (p + r) :=
  ((relativeSingularCohomologyAction R (bundleNonzero r E) p r).flip
    (cohomologyThomClass R r E o)).comp
      (singularCohomologyPullback R (bundleProjection r E) p).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Multiplication by the specified Thom class is bijective in every nonnegative degree. -/
theorem cohomologyThomMap_bijective (p : ℕ) :
    Function.Bijective (cohomologyThomMap R r E o p) := by
  /- The local product theorem applies to the same restricted global Thom class.
  Exact augmented Čech rows compare its actual right-cup cochain map globally.
  Finally compose with the original projection pullback, whose inverse is supplied
  by the original zero section and fiberwise scaling. The argument retains arbitrary
  base spaces, coefficient rings, empty intersections and rank zero; no inverse
  limit, CW hypothesis or compact-support comparison is inserted. -/
  classical
  -- Keep the original linear charts, total-space pair and chosen Thom class.
  let V (x : X) := (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).baseSet
  let U (x : X) := (bundleProjection r E) ⁻¹' V x
  let S (m : ℕ) (a : Fin (m + 1) → X) : Set X := {x | ∀ i, x ∈ V (a i)}
  let A := bundleNonzero r E
  let t := cohomologyThomClass R r E o
  let I := ((relativeSingularCochains R A).sc r).moduleCatHomologyIso
  obtain ⟨c, hc⟩ := (relativeSingularCoboundaries R A r).mkQ_surjective (I.hom t)
  have hct : relativeSingularCocycleClass R A r c = t := by
    change I.inv ((relativeSingularCoboundaries R A r).mkQ c) = t
    rw [hc]
    exact CategoryTheory.Iso.hom_inv_id_apply I t
  have ht (x : X) : relativeSingularCohomologyPullback R
      (bundleFiberInclusion r E x) (A := {v : E x | v ≠ 0})
      (B := A) (fun _ hv ↦ hv) r t = o.fiberClass x :=
    (existsUnique_cohomologyThomClass R r E o).exists.choose_spec x
  have hOpen (x : X) : IsOpen (U x) :=
    (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).open_baseSet.preimage
      (bundleProjection r E).continuous
  have hCover : ⋃ x, U x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Set.mem_iUnion.mpr ⟨z.proj,
      FiberBundle.mem_baseSet_trivializationAt' (F := EuclideanSpace ℝ (Fin r)) z.proj⟩
  -- On every tuple intersection the same chart gives low-degree vanishing.
  have hvan (m : ℕ) (a : Fin (m + 1) → X) (q : ℕ) (hq : q < r) :
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U a → _) ⁻¹' A) q) := by
    change Subsingleton (relativeSingularCohomology R
      (bundleNonzeroOver r E (S m a)) q)
    exact subsingleton_relativeSingularCohomology_bundleTotalOver_below_rank R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S m a) (fun _ hy ↦ hy 0) q hq
  -- Its restricted Thom class has the prescribed generator on each original fiber.
  have hlocal (m : ℕ) (a : Fin (m + 1) → X) (q : ℕ) :
      Function.Bijective (fun z : singularCohomology R (singularCechIntersection U a) q ↦
        relativeSingularCohomologyAction R
          ((Subtype.val : singularCechIntersection U a → _) ⁻¹' A) q r z
          (relativeSingularCohomologyPullback R
            (⟨Subtype.val, continuous_subtype_val⟩ : C(singularCechIntersection U a, _))
            (fun _ hx ↦ hx) r (relativeSingularCocycleClass R A r c))) := by
    rw [hct]
    let inc : C(BundleTotalOver r E (S m a), TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    change Function.Bijective (fun z : singularCohomology R (BundleTotalOver r E (S m a)) q ↦
      relativeSingularCohomologyAction R (bundleNonzeroOver r E (S m a)) q r z
        (relativeSingularCohomologyPullback R inc
          (A := bundleNonzeroOver r E (S m a)) (B := A) (fun _ hv ↦ hv) r t))
    apply relativeSingularCohomologyAction_bundleTotalOver_bijective R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S m a) (fun _ hy ↦ hy 0)
    intro x hx
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    change Function.Bijective (fun b : R ↦ b • relativeSingularCohomologyPullback R
      (bundleFiberInclusion r E x) (A := {v : E x | v ≠ 0}) (B := A)
      (fun _ hv ↦ hv) r t)
    rw [ht]
    exact o.is_generator x
  -- Actual small-cochain comparison descends this right-cup map to the whole bundle.
  have hcup := relativeSingularCohomologyAction_bijective_of_openCover R
    U A hOpen hCover r c hvan hlocal p
  rw [hct] at hcup
  -- The original projection is a homotopy equivalence, by fiberwise scaling.
  let := RealBundle.isFiniteRank_of_vectorBundle (EuclideanSpace ℝ (Fin r)) E
  have htotal : ((bundleZeroSection r E).comp (bundleProjection r E)).Homotopic
      (ContinuousMap.id (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) :=
    ⟨RealBundle.scalingHomotopy (EuclideanSpace ℝ (Fin r)) E⟩
  have hbase : ((bundleProjection r E).comp (bundleZeroSection r E)).Homotopic
      (ContinuousMap.id X) := ⟨ContinuousMap.Homotopy.refl _⟩
  let := isIso_singularCohomologyPullback_of_homotopyInverse R
    (bundleProjection r E) (bundleZeroSection r E) htotal hbase p
  have hprojection := ConcreteCategory.bijective_of_isIso
    (singularCohomologyPullback R (bundleProjection r E) p)
  -- Their composite is precisely the original pullback-then-right-cup Thom map.
  exact hcup.comp hprojection

/-- The Thom equivalence of the actual base and total-space-pair cohomology modules. -/
def cohomologyThomEquiv (p : ℕ) :
    singularCohomology R X p ≃ₗ[R]
      relativeSingularCohomology R (bundleNonzero r E) (p + r) :=
  LinearEquiv.ofBijective (cohomologyThomMap R r E o p)
    (cohomologyThomMap_bijective R r E o p)

end AtiyahSinger
