/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactConvexLocalHomology
public import AtiyahSinger.Topology.CompactPoincareDualityBasic
public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeEvaluationRationalization

/-!
# The original compact-support cap duality on Euclidean space

Public module ID: M1824.

Compact convex controls have the same relative homology as a point. Their
specified rational fundamental class is a generator because its integral
normalization survives the original coefficient maps. The original Kronecker
pairing identifies cap with this generator in top degree, while complementary
groups vanish in the other degrees. Cofinality of compact convex controls then
gives duality for the original compact-support colimit.

The continuous linear coordinate equivalence is explicit and the ambient space
may lie in an arbitrary universe. No new cap convention or normalization is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace

universe u

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Over a compact convex control containing zero, the specified rational fundamental
class freely generates the original top relative homology. -/
theorem rationalCompactRelativeFundamentalClass_is_generator_of_convex
    (e : E ≃L[ℝ] (Fin n → ℝ)) (O : HomologicalOrientation n E)
    (K : Compacts E) (hK : Convex ℝ (K : Set E)) (hzero : (0 : E) ∈ K) :
    Function.Bijective (fun a : ℚ ↦ a • rationalCompactRelativeFundamentalClass O K) := by
  let A : Set E := {x | x ≠ 0}
  let b : Module.Basis (Fin n) ℝ E := Module.Basis.ofEquivFun e.toLinearEquiv
  let G : ℤ ≃ₗ[ℤ] relativeSingularHomology ℤ A n := O.localGenerator 0
  let z : relativeSingularHomology ℚ A n := relativeSingularHomologyRationalization A n (G 1)
  -- Integral evaluation one survives coefficient change. Since the given integral
  -- local generator spans that cycle, its own rational image cannot vanish.
  have hz : z ≠ 0 := by
    let a₀ : relativeSingularCohomology ℤ A n := realOrientationClass b b.orientation
    let z₀ : relativeSingularHomology ℤ A n := realOrientationCycle b b.orientation
    have hnorm : (singularCochainHomologyEvaluation ℤ (relativeSingularChains ℤ A) n
        a₀ z₀).down = 1 := by
      rw [← relativeSingularCapProduct_augmentation]
      exact realOrientationClass_evaluation b b.orientation
    have hz₀ : relativeSingularHomologyRationalization A n z₀ ≠ 0 := by
      intro h
      have hp := singularCochainHomologyEvaluation_rationalization A n a₀ z₀
      rw [h, map_zero, hnorm] at hp
      norm_num at hp
    intro h
    obtain ⟨k, hk⟩ := G.surjective z₀
    have hk' : k • G 1 = z₀ := by
      rw [← map_zsmul, zsmul_eq_mul, mul_one]
      exact hk
    apply hz₀
    rw [← hk', map_zsmul]
    change k • z = 0
    rw [h, zsmul_zero]
  -- The actual pointed coordinate map gives a rational basis of the same local group.
  let f : C(E, ULift.{u} (Fin n → ℝ)) :=
    ⟨fun x ↦ ULift.up (e x), continuous_uliftUp.comp e.continuous⟩
  let g : C(ULift.{u} (Fin n → ℝ), E) :=
    ⟨fun x ↦ e.symm x.down, e.symm.continuous.comp continuous_uliftDown⟩
  have hf : Set.MapsTo f A {x | x ≠ 0} := by
    intro x hx h
    apply hx
    apply e.injective
    simpa [f] using congrArg ULift.down h
  have hg : Set.MapsTo g {x | x ≠ 0} A := by
    intro x hx h
    apply hx
    apply ULift.ext
    simpa [g] using congrArg e h
  have : IsIso (relativeSingularHomologyMap ℚ f hf n) :=
    isIso_relativeSingularHomologyMap_of_inverse ℚ f g hf hg
      (by apply ContinuousMap.ext; intro x; exact e.symm_apply_apply x)
      (by apply ContinuousMap.ext; intro x; exact congrArg ULift.up (e.apply_symm_apply x.down)) n
  let H : ℚ ≃ₗ[ℚ] relativeSingularHomology ℚ A n :=
    (euclideanLocalHomologyEquiv.{u} ℚ n).trans
      (asIso (relativeSingularHomologyMap ℚ f hf n)).symm.toLinearEquiv
  have hzH : H.symm z ≠ 0 := fun h ↦ hz (H.symm.injective (h.trans (map_zero H.symm).symm))
  have hlocal : Function.Bijective (fun a : ℚ ↦ a • z) := by
    constructor
    · intro a b hab
      have h := congrArg H.symm hab
      simp only [map_smul, smul_eq_mul] at h
      exact mul_right_cancel₀ hzH h
    · intro x
      refine ⟨H.symm x / H.symm z, H.symm.injective ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hzH]
  -- Convex restriction is an isomorphism and carries this very compact class to z.
  let F := relativeSingularHomologyInclusion ℚ ((K : Set E)ᶜ) A
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hzero)) n
  have hF : Function.Bijective F :=
    relativeSingularHomologyInclusion_compactConvex_bijective ℚ (K : Set E)
      K.isCompact hK 0 hzero n
  have hvalue : F (rationalCompactRelativeFundamentalClass O K) = z :=
    rationalCompactRelativeFundamentalClass_restriction O K 0 hzero
  have hcomp : F ∘ (fun a : ℚ ↦ a • rationalCompactRelativeFundamentalClass O K) =
      (fun a : ℚ ↦ a • z) := by
    funext a
    change F (a • _) = _
    rw [map_smul, hvalue]
  apply (hF.of_comp_iff' _).mp
  rw [hcomp]
  exact hlocal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original cap-duality map is bijective on a compact convex Euclidean control.
The specified fundamental class is retained in every complementary degree. -/
theorem compactRelativeDuality_bijective_of_convex
    (e : E ≃L[ℝ] (Fin n → ℝ)) (O : HomologicalOrientation n E)
    (K : Compacts E) (hK : Convex ℝ (K : Set E)) (hzero : (0 : E) ∈ K)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactRelativeDuality O K p q h) := by
  subst n
  cases q with
  | zero =>
    -- Top cap is the actual perfect evaluation on the same normalized generator.
    let z := rationalCompactRelativeFundamentalClass O K
    have hz := rationalCompactRelativeFundamentalClass_is_generator_of_convex e O K hK hzero
    let H : ℚ ≃ₗ[ℚ] relativeSingularHomology ℚ ((K : Set E)ᶜ) p :=
      LinearEquiv.ofBijective ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).smulRight z) hz
    have hH : H 1 = z := one_smul ℚ z
    have hbij := relativeSingularCapProduct_generator_bijective ℚ ((K : Set E)ᶜ) p H
    change Function.Bijective (fun a ↦ relativeSingularCapProduct ℚ ((K : Set E)ᶜ) p 0 a z)
    simpa only [hH] using hbij
  | succ q =>
    -- Below the dimension, convex restriction reduces relative homology to the
    -- punctured local pair. Its vanishing passes to the actual algebraic dual.
    have : Subsingleton (relativeSingularHomology ℚ ({0}ᶜ : Set E) p) :=
      subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
        ℚ e p (by omega)
    have hF := relativeSingularHomologyInclusion_compactConvex_bijective
      ℚ (K : Set E) K.isCompact hK 0 hzero p
    have : Subsingleton (relativeSingularHomology ℚ ((K : Set E)ᶜ) p) :=
      hF.injective.subsingleton
    have := subsingleton_relativeSingularCohomology_of_subsingleton_homology
      ℚ ((K : Set E)ᶜ) p
    -- The complementary positive homology group of the vector space is also zero.
    have := subsingleton_singularHomology_of_contractible ℚ E (q + 1) (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Compact-support Poincare duality holds on an explicitly coordinatized Euclidean space,
for its given homological orientation and its original compact-support cap map. -/
theorem compactPoincareDuality_bijective_of_continuousLinearEquiv
    (e : E ≃L[ℝ] (Fin n → ℝ)) (O : HomologicalOrientation n E)
    (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  let b : Module.Basis (Fin n) ℝ E := Module.Basis.ofEquivFun e.toLinearEquiv
  let : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hzero (a : compactSupportCohomology ℚ E p)
      (ha : compactPoincareDuality O p q h a = 0) : a = 0 := by
    -- Every compact representative fits in one closed ball containing zero.
    obtain ⟨K, c, hc⟩ := compactSupportCohomology_exists_representative ℚ E p a
    obtain ⟨ρ, hρ, hbound⟩ := K.isCompact.isBounded.exists_pos_norm_le
    let L : Compacts E := ⟨Metric.closedBall 0 ρ, isCompact_closedBall 0 ρ⟩
    have hKL : K ≤ L := fun x hx ↦ by
      change dist x 0 ≤ ρ
      simpa only [dist_zero_right] using hbound x hx
    have hzL : (0 : E) ∈ L := Metric.mem_closedBall_self hρ.le
    let cL := (compactSupportCohomologyFunctor ℚ E p).map (homOfLE hKL) c
    have hrep : compactSupportCohomologyClass ℚ E L p cL = a := by
      have hw := congrArg (fun f ↦ f c)
        (colimit.w (compactSupportCohomologyFunctor ℚ E p) (homOfLE hKL))
      exact hw.trans hc
    -- The same compact-relative cap is injective on that convex control.
    have hcap : compactRelativeDuality O L p q h cL = 0 := by
      rw [← compactPoincareDuality_representative O L p q h cL, hrep]
      exact ha
    have hcL : cL = 0 := (compactRelativeDuality_bijective_of_convex e O L
      (convex_closedBall 0 ρ) hzL p q h).injective (hcap.trans (map_zero _).symm)
    rw [hcL, map_zero] at hrep
    exact hrep.symm
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  · -- A fixed singleton control already realizes every ordinary homology class.
    intro z
    let K : Compacts E := ⟨{0}, isCompact_singleton⟩
    obtain ⟨c, hc⟩ := (compactRelativeDuality_bijective_of_convex e O K
      (convex_singleton 0) (Set.mem_singleton 0) p q h).surjective z
    refine ⟨compactSupportCohomologyClass ℚ E K p c, ?_⟩
    rw [compactPoincareDuality_representative]
    exact hc

end AtiyahSinger
