/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactDualityNaturality
public import AtiyahSinger.Topology.CompactPoincareDuality
public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing
public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.OpenHomologicalOrientation
public import AtiyahSinger.Topology.SingularHomologyAugmentation

/-!
# Gysin maps defined by the original compact-support Poincare duality

Public module ID: M1988.

Lawson--Michelsohn, Spin Geometry, III.12, (12.2), pp.238--239.
For a continuous map between oriented manifolds, the Gysin map is the
actual composite D_target inverse, ordinary homology pushforward, D_source.
No properness condition is needed on that ordinary homology map.

The degree equation retains the same complementary homology degree.
Above the source dimension the source and target groups both vanish and
the map is zero. Thus natural subtraction is only used when nonnegative.
Negative target degrees are not represented by degree zero. In particular,
bundle input degrees below the fiber rank are handled by vanishing separately.

Both dualities use the original front-face cap convention. This convention
must be compared explicitly with the order of an independently defined Thom
map; it is not silently replaced by a different cap convention. Top-degree
integration uses the original locally finite fundamental-class pairing.
Composition, integral compatibility and open-extension identification follow from
these specified dualities. The open-extension integral formula also follows directly
from cap naturality. Independent Thom and differential-form comparisons are separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Topology

universe u

variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) Y]
  [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]

/-- The original PD-defined Gysin map in every compatible pair of nonnegative degrees. -/
def compactSupportGysin (OX : HomologicalOrientation n X) (OY : HomologicalOrientation m Y)
    (f : C(Y, X)) (p q : ℕ) (h : p + n = q + m) :
    compactSupportCohomology ℚ Y p →ₗ[ℚ] compactSupportCohomology ℚ X q :=
  if hp : p ≤ m then
    (compactPoincareDualityEquiv OX q (m - p) (by omega)).symm.toLinearMap.comp
      ((singularHomologyMap ℚ f (m - p)).hom.comp
        (compactPoincareDualityEquiv OY p (m - p) (Nat.add_sub_of_le hp)).toLinearMap)
  else 0

/-- Successive Gysin maps are the Gysin map of the actual composite continuous map. -/
theorem compactSupportGysin_comp {l : ℕ} {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin l)) Z]
    [T2Space Z] [SecondCountableTopology Z]
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation m Y)
    (OZ : HomologicalOrientation l Z) (f : C(Y, X)) (g : C(Z, Y))
    (p q s : ℕ) (hg : p + m = q + l) (hf : q + n = s + m) :
    (compactSupportGysin OX OY f q s hf).comp
        (compactSupportGysin OY OZ g p q hg) =
      compactSupportGysin OX OZ (f.comp g) p s (by omega) := by
  by_cases hp : p ≤ l
  · have hq : q ≤ m := by omega
    have hdegree : m - q = l - p := by omega
    -- All three dualities use the same nonnegative complementary homology degree.
    simp only [compactSupportGysin, dite_eq_left hp, dite_eq_left hq]
    generalize_proofs at *
    generalize hk : m - q = k at *
    clear hk
    subst k
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    -- The specified middle duality cancels; the remaining maps are functorial pushforwards.
    apply congrArg (compactPoincareDualityEquiv OX s (l - p) (by omega)).symm
    have hcomp : singularHomologyMap ℚ (f.comp g) (l - p) =
        singularHomologyMap ℚ g (l - p) ≫ singularHomologyMap ℚ f (l - p) := by
      change HomologicalComplex.homologyMap
        ((singularChainsFunctor ℚ).map (TopCat.ofHom g ≫ TopCat.ofHom f)) (l - p) = _
      rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
      rfl
    exact congrArg (fun k ↦ k (compactPoincareDualityEquiv OZ p (l - p)
      (Nat.add_sub_of_le hp) a)) hcomp.symm
  · -- Above the source dimension both expressions use the original zero branch.
    simp only [compactSupportGysin, dite_eq_right hp, LinearMap.comp_zero]

/-- Continuous Gysin pushforward preserves the original top-degree integral. -/
theorem compactSupportCohomologyIntegral_gysin
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation m Y)
    (f : C(Y, X)) (a : compactSupportCohomology ℚ Y m) :
    compactSupportCohomologyIntegral OX
        (compactSupportGysin OX OY f m n (by omega) a) =
      compactSupportCohomologyIntegral OY a := by
  -- The original locally finite pairing is augmentation after the same cap-duality map.
  rw [compactSupportCohomologyIntegral_eq_duality_augmentation,
    compactSupportCohomologyIntegral_eq_duality_augmentation]
  simp only [compactSupportGysin, dite_eq_left (Nat.le_refl m),
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize_proofs at *
  generalize hk : m - m = k at *
  have hk0 : k = 0 := by omega
  clear hk
  subst k
  change (((TopCat.of X).singularHomology₀ε (C := ModuleCat.{u} ℚ) (singularCoefficient ℚ))
    (compactPoincareDualityEquiv OX n 0 (Nat.add_zero n)
      ((compactPoincareDualityEquiv OX n 0 (Nat.add_zero n)).symm
        (singularHomologyMap ℚ f 0
          (compactPoincareDuality OY m 0 (Nat.add_zero m) a))))).down = _
  rw [LinearEquiv.apply_symm_apply]
  -- Ordinary zero-homology augmentation is natural for every continuous map.
  exact congrArg (fun k ↦ (k (compactPoincareDuality OY m 0 (Nat.add_zero m) a)).down)
    (singularHomologyMap_augmentation ℚ f)

section OpenEmbedding

variable {U : Type u} [TopologicalSpace U]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) U]
  [T2Space U] [SecondCountableTopology U]

/-- For an orientation-preserving open embedding, Gysin is the actual excision extension. -/
theorem compactSupportGysin_eq_openExtension (OX : HomologicalOrientation n X)
    (OU : HomologicalOrientation n U) (f : C(U, X)) (hf : IsOpenEmbedding f)
    (ho : IsOrientationPreservingOpenEmbedding OU OX f hf) (p : ℕ) :
    compactSupportGysin OX OU f p p (by omega) =
      (compactSupportCohomologyOpenExtension ℚ f hf p).hom := by
  apply LinearMap.ext
  intro a
  by_cases hp : p ≤ n
  · -- Apply the very target duality used in the definition of Gysin.
    let D := compactPoincareDualityEquiv OX p (n - p) (Nat.add_sub_of_le hp)
    apply D.injective
    simp only [compactSupportGysin, dite_eq_left hp, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    change D (D.symm (singularHomologyMap ℚ f (n - p)
      (compactPoincareDuality OU p (n - p) (Nat.add_sub_of_le hp) a))) = _
    rw [LinearEquiv.apply_symm_apply]
    -- Excision extension and this cap map use the same prescribed compact-image class.
    exact (compactPoincareDuality_openExtension OU OX f hf ho p (n - p)
      (Nat.add_sub_of_le hp) a).symm
  · -- Cohomology above dimension vanishes, including the codomain of extension.
    let := compactSupportCohomology_subsingleton_above_dim OX p (by omega)
    exact Subsingleton.elim _ _

/-- Extension by zero preserves integration for the induced original orientation. -/
theorem compactSupportCohomologyIntegral_openExtension
    (OX : HomologicalOrientation n X) (f : C(U, X)) (hf : IsOpenEmbedding f)
    (a : compactSupportCohomology ℚ U n) :
    letI : LocallyCompactSpace X :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) X
    compactSupportCohomologyIntegral OX
        (compactSupportCohomologyOpenExtension ℚ f hf n a) =
      compactSupportCohomologyIntegral (homologicalOrientationOpenPullback OX f hf) a := by
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) X
  let OU := homologicalOrientationOpenPullback OX f hf
  -- Integral evaluation uses the same fundamental class as this cap-duality map.
  rw [compactSupportCohomologyIntegral_eq_duality_augmentation,
    compactSupportCohomologyIntegral_eq_duality_augmentation]
  rw [compactPoincareDuality_openExtension OU OX f hf
    (homologicalOrientationOpenPullback_orientationPreserving OX f hf)]
  -- Ordinary zero-homology admits pushforward along every continuous map.
  exact congrArg (fun h ↦ (h (compactPoincareDuality OU n 0 (Nat.add_zero n) a)).down)
    (singularHomologyMap_augmentation ℚ f)

end OpenEmbedding

end AtiyahSinger
