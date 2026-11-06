/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityBasic
public import AtiyahSinger.Topology.LocallyFiniteFundamentalClass
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Compact-support evaluation on actual locally finite homology

Public module ID: M1678.

D11. A compactly supported cohomology representative is paired with the
restriction of a locally finite homology class to the very same compact
control. The original relative cap product followed by the degree-zero
augmentation gives its value. Support compatibility descends this bilinear
pairing through the original compact-support colimit.

For an oriented manifold, evaluating on its normalized rational LF
fundamental class defines top-degree integration. Its equality with the
augmentation of the existing compact Poincare-duality map is stated using
the identical homological orientation, not a newly chosen fundamental class.
This is Atiyah--Singer III p.552's u[X] = epsilon(Du), on the original
singular models. Hatcher section 3.3 supplies the cap and relative-support
construction. No ordinary global fundamental cycle of a noncompact manifold
or unrestricted properness claim is used. ThomGysinComparison separately proves
the signed rational Thom-Gysin comparison under its manifold hypotheses. The
general-space pairing, support formulas and manifold normalization are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Evaluate a relative class against the same compact restriction of an actual LF class. -/
def compactRelativeLocallyFinitePairing (K : Compacts X) (n : ℕ) :
    relativeSingularCohomology R ((K : Set X)ᶜ) n →ₗ[R]
      locallyFiniteSingularHomology R X n →ₗ[R] R := by
  -- The original H_0 augmentation sends each point generator to its coefficient.
  let augmentation : singularHomology R X 0 →ₗ[R] R :=
    (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.comp
      ((TopCat.of X).singularHomology₀ε (singularCoefficient R)).hom
  -- Both relative inputs concern the identical complement of K.
  exact ((relativeSingularCapProduct R ((K : Set X)ᶜ) n 0).compr₂ augmentation).compl₂
    (locallyFiniteSingularHomologyRestriction R K n).hom

/-- Enlarging the cochain support preserves evaluation on the same locally finite class. -/
theorem compactRelativeLocallyFinitePairing_support {K L : Compacts X}
    (h : K ≤ L) (n : ℕ) (a : relativeSingularCohomology R ((K : Set X)ᶜ) n)
    (z : locallyFiniteSingularHomology R X n) :
    compactRelativeLocallyFinitePairing R X L n
        ((compactSupportCohomologyFunctor R X n).map (homOfLE h) a) z =
      compactRelativeLocallyFinitePairing R X K n a z := by
  /- Stage 1: the actual cap-inclusion identity moves the original relative
  cohomology transition past the cap product to the relative homology input.
  Stage 2: the LF restriction over L followed by the original quotient to
  the complement of K is exactly the LF restriction over K. The same H_0
  augmentation on X then gives the displayed equality. Neither a chain
  representative nor a homology class is reselected during this comparison. -/
  -- Move support enlargement to the homology input of the same cap product.
  let augmentation : singularHomology R X 0 →ₗ[R] R :=
    (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.comp
      ((TopCat.of X).singularHomology₀ε (singularCoefficient R)).hom
  change augmentation (relativeSingularCapProduct R ((L : Set X)ᶜ) n 0
    (relativeSingularCohomologyRestriction R ((L : Set X)ᶜ) ((K : Set X)ᶜ)
      (Set.compl_subset_compl.mpr h) n a) (locallyFiniteSingularHomologyRestriction R L n z)) =
    augmentation (relativeSingularCapProduct R ((K : Set X)ᶜ) n 0 a
      (locallyFiniteSingularHomologyRestriction R K n z))
  rw [relativeSingularCapProduct_inclusion]
  -- The original LF restriction is compatible with that same quotient map.
  have hrestriction := congrArg (fun f ↦ f z)
    (locallyFiniteSingularHomologyRestriction_inclusion R h n)
  change relativeSingularHomologyInclusion R ((L : Set X)ᶜ) ((K : Set X)ᶜ)
    (Set.compl_subset_compl.mpr h) n (locallyFiniteSingularHomologyRestriction R L n z) =
      locallyFiniteSingularHomologyRestriction R K n z at hrestriction
  exact congrArg (fun c ↦ augmentation (relativeSingularCapProduct R ((K : Set X)ᶜ) n 0 a c))
    hrestriction

/-- The standard bilinear pairing of compact-support cohomology with actual LF homology. -/
def compactSupportLocallyFinitePairing (n : ℕ) :
    compactSupportCohomology R X n →ₗ[R]
      locallyFiniteSingularHomology R X n →ₗ[R] R :=
  (colimit.desc (compactSupportCohomologyFunctor R X n)
    { pt := ModuleCat.of R (locallyFiniteSingularHomology R X n →ₗ[R] R)
      ι :=
        { app := fun K ↦ ModuleCat.ofHom (compactRelativeLocallyFinitePairing R X K n)
          naturality := by
            intro K L f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            apply LinearMap.ext
            intro z
            exact compactRelativeLocallyFinitePairing_support R X (leOfHom f) n a z } }).hom

/-- Evaluation of a compact representative uses precisely its original relative cap pairing. -/
theorem compactSupportLocallyFinitePairing_representative (K : Compacts X) (n : ℕ)
    (a : relativeSingularCohomology R ((K : Set X)ᶜ) n)
    (z : locallyFiniteSingularHomology R X n) :
    compactSupportLocallyFinitePairing R X n (compactSupportCohomologyClass R X K n a) z =
      compactRelativeLocallyFinitePairing R X K n a z := by
  /- Evaluate the defining colimit descent at its K-th original injection.
  That cocone leg is the displayed relative cap and augmentation evaluated
  on the original restriction of z. This formula does not choose a support
  representative for an arbitrary class or replace the LF homology model. -/
  -- Reuse the very cocone used to define the compact-support pairing.
  let cocone : Cocone (compactSupportCohomologyFunctor R X n) :=
    { pt := ModuleCat.of R (locallyFiniteSingularHomology R X n →ₗ[R] R)
      ι :=
        { app := fun K ↦ ModuleCat.ofHom (compactRelativeLocallyFinitePairing R X K n)
          naturality := by
            intro K L f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro a
            apply LinearMap.ext
            intro z
            exact compactRelativeLocallyFinitePairing_support R X (leOfHom f) n a z } }
  -- Its colimit factorization equation evaluates on the specified representative.
  have h := colimit.ι_desc cocone K
  exact congrArg (fun f : relativeSingularCohomology R ((K : Set X)ᶜ) n ⟶
    ModuleCat.of R (locallyFiniteSingularHomology R X n →ₗ[R] R) ↦ f a z) h

section Manifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]

/-- Top-degree integration is evaluation on the normalized rational LF fundamental class. -/
def compactSupportCohomologyIntegral (O : HomologicalOrientation n M) :
    compactSupportCohomology ℚ M n →ₗ[ℚ] ℚ :=
  (compactSupportLocallyFinitePairing ℚ M n).flip (rationalLocallyFiniteFundamentalClass O)

/-- Atiyah--Singer III's normalization: fundamental-class evaluation is augmentation of duality. -/
theorem compactSupportCohomologyIntegral_eq_duality_augmentation
    (O : HomologicalOrientation n M) (a : compactSupportCohomology ℚ M n) :
    compactSupportCohomologyIntegral O a =
      (((TopCat.of M).singularHomology₀ε (singularCoefficient ℚ))
        (compactPoincareDuality O n 0 (Nat.add_zero n) a)).down := by
  -- Both constructions descend from the same compact-support representatives.
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative ℚ M n a
  change compactSupportLocallyFinitePairing ℚ M n
    (compactSupportCohomologyClass ℚ M K n b)
    (rationalLocallyFiniteFundamentalClass O) = _
  rw [compactSupportLocallyFinitePairing_representative,
    compactPoincareDuality_representative]
  -- Restriction identifies the chosen LF class with the specified relative fundamental class.
  change (((TopCat.of M).singularHomology₀ε (singularCoefficient ℚ))
    (relativeSingularCapProduct ℚ ((K : Set M)ᶜ) n 0 b
      (locallyFiniteSingularHomologyRestriction ℚ K n
        (rationalLocallyFiniteFundamentalClass O)))).down = _
  rw [rationalLocallyFiniteFundamentalClass_restriction]
  rfl

end Manifold

end AtiyahSinger
