/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentGysinOrientation
public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing

/-!
# The tangent orientation sign on compact supports

Public module ID: M1480.

The actual grouped and interleaved local generators determine the corresponding
compact-relative fundamental classes uniquely. Their comparison therefore retains
the same permutation sign on every compact support, including signed zero-dimensional
orientations. Evaluation uses the original locally finite class and rationalization.

Sources: the local normalization in TangentGysinOrientation and compact-relative
point detection, Hatcher, Algebraic Topology, Section 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same tangent permutation sign compares the original classes over every compact set. -/
theorem bundleHomologicalOrientation_tangent_compactRelativeFundamentalClass
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M)
    (K : Compacts TM) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    letI : T2Space TM := (tangentBundle_topology V M).1
    letI : SecondCountableTopology TM := (tangentBundle_topology V M).2.1
    (eqToIso (congrArg (relativeSingularHomology ℤ ((K : Set TM)ᶜ))
        (by omega : n + n = 2 * n))).hom
      (@compactRelativeFundamentalClass (n + n) TM _
        (bundleTotalEuclideanChartedSpace n n T) _ _
        (bundleHomologicalOrientation n T O (tangentCohomologyOrientation g O)) K) =
      (-1 : ℤ) ^ (n * (n - 1) / 2) •
        @compactRelativeFundamentalClass (2 * n) TM _
          (tangentBundleEuclideanChartedSpace (n := n) (M := M)) _ _
          (tangentHomologicalOrientation (n := n) (M := M)) K := by
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  let : T2Space TM := (tangentBundle_topology V M).1
  let : SecondCountableTopology TM := (tangentBundle_topology V M).2.1
  -- Degree transport also permits different Euclidean chart structures on the same space.
  have hcompare (i j : ℕ) (hij : i = j)
      (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) TM)
      (D : ChartedSpace (EuclideanSpace ℝ (Fin j)) TM)
      (P : HomologicalOrientation i TM) (Q : HomologicalOrientation j TM) (s : ℤ)
      (hlocal : ∀ z : TM,
        (eqToIso (congrArg (relativeSingularHomology ℤ ({z}ᶜ : Set TM)) hij)).hom
          (P.localGenerator z 1) = s • Q.localGenerator z 1) :
      (eqToIso (congrArg (relativeSingularHomology ℤ ((K : Set TM)ᶜ)) hij)).hom
          (@compactRelativeFundamentalClass i TM _ C _ _ P K) =
        s • @compactRelativeFundamentalClass j TM _ D _ _ Q K := by
    subst j
    simp only [eqToIso_refl, Iso.refl_hom, ModuleCat.id_apply] at hlocal ⊢
    -- Every local restriction of the difference vanishes, so the compact-relative class does.
    apply sub_eq_zero.mp
    apply @relativeSingularHomology_eq_zero_of_point_restrictions ℤ _ TM _ _ i D
      ((K : Set TM)ᶜ) (by simpa using K.isCompact)
    intro z hz
    have hzK : z ∈ K := not_not.mp hz
    rw [map_sub, map_zsmul]
    rw [@compactRelativeFundamentalClass_restriction i TM _ C _ _ P K z hzK,
      @compactRelativeFundamentalClass_restriction i TM _ D _ _ Q K z hzK]
    exact sub_eq_zero.mpr (hlocal z)
  exact hcompare (n + n) (2 * n) (by omega)
    (bundleTotalEuclideanChartedSpace n n T)
    (tangentBundleEuclideanChartedSpace (n := n) (M := M))
    (bundleHomologicalOrientation n T O (tangentCohomologyOrientation g O))
    (tangentHomologicalOrientation (n := n) (M := M))
    ((-1 : ℤ) ^ (n * (n - 1) / 2))
    (bundleHomologicalOrientation_tangent_localGenerator g O)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation on the canonical tangent class is the signed integral for the grouped orientation. -/
theorem tangent_pairing_eq_grouped_integral
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M)
    (a : compactSupportCohomology ℚ TM (2 * n)) :
    letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
    letI : T2Space TM := (tangentBundle_topology V M).1
    letI : SecondCountableTopology TM := (tangentBundle_topology V M).2.1
    compactSupportLocallyFinitePairing ℚ TM (2 * n) a
        (rationalTangentFundamentalClass (n := n) (M := M)) =
      (-1 : ℚ) ^ (n * (n - 1) / 2) *
        @compactSupportCohomologyIntegral (n + n) TM _
          (bundleTotalEuclideanChartedSpace n n T) _ _
          (bundleHomologicalOrientation n T O (tangentCohomologyOrientation g O))
          ((eqToIso (congrArg (compactSupportCohomology ℚ TM)
            (by omega : 2 * n = n + n))).hom a) := by
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  let : T2Space TM := (tangentBundle_topology V M).1
  let : SecondCountableTopology TM := (tangentBundle_topology V M).2.1
  -- Orientation change commutes with degree transport and with the same support injections.
  have hIntegralChange (i j : ℕ) (hij : i = j)
      (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) TM)
      (D : ChartedSpace (EuclideanSpace ℝ (Fin j)) TM)
      (P : HomologicalOrientation i TM) (Q : HomologicalOrientation j TM) (s : ℤ)
      (hs : (s : ℚ) * s = 1)
      (hc : ∀ K : Compacts TM,
        (eqToIso (congrArg (relativeSingularHomology ℤ ((K : Set TM)ᶜ)) hij)).hom
          (@compactRelativeFundamentalClass i TM _ C _ _ P K) =
        s • @compactRelativeFundamentalClass j TM _ D _ _ Q K)
      (b : compactSupportCohomology ℚ TM j) :
      @compactSupportCohomologyIntegral j TM _ D _ _ Q b =
        (s : ℚ) * @compactSupportCohomologyIntegral i TM _ C _ _ P
          ((eqToIso (congrArg (compactSupportCohomology ℚ TM) hij.symm)).hom b) := by
    subst j
    simp only [eqToIso_refl, Iso.refl_hom, ModuleCat.id_apply] at hc ⊢
    have hPQ : @compactSupportCohomologyIntegral i TM _ C _ _ P b =
        (s : ℚ) * @compactSupportCohomologyIntegral i TM _ D _ _ Q b := by
      obtain ⟨K, c, rfl⟩ := compactSupportCohomology_exists_representative ℚ TM i b
      change compactSupportLocallyFinitePairing ℚ TM i
        (compactSupportCohomologyClass ℚ TM K i c)
        (@rationalLocallyFiniteFundamentalClass i TM _ C _ _ P) =
        (s : ℚ) * compactSupportLocallyFinitePairing ℚ TM i
          (compactSupportCohomologyClass ℚ TM K i c)
          (@rationalLocallyFiniteFundamentalClass i TM _ D _ _ Q)
      rw [compactSupportLocallyFinitePairing_representative,
        compactSupportLocallyFinitePairing_representative]
      change (((TopCat.of TM).singularHomology₀ε (singularCoefficient ℚ))
        (relativeSingularCapProduct ℚ ((K : Set TM)ᶜ) i 0 c
          (locallyFiniteSingularHomologyRestriction ℚ K i
            (@rationalLocallyFiniteFundamentalClass i TM _ C _ _ P)))).down =
        (s : ℚ) * (((TopCat.of TM).singularHomology₀ε (singularCoefficient ℚ))
          (relativeSingularCapProduct ℚ ((K : Set TM)ᶜ) i 0 c
            (locallyFiniteSingularHomologyRestriction ℚ K i
              (@rationalLocallyFiniteFundamentalClass i TM _ D _ _ Q)))).down
      rw [@rationalLocallyFiniteFundamentalClass_restriction i TM _ C _ _ P K,
        @rationalLocallyFiniteFundamentalClass_restriction i TM _ D _ _ Q K]
      have hrat : @rationalCompactRelativeFundamentalClass i TM _ C _ _ P K =
          s • @rationalCompactRelativeFundamentalClass i TM _ D _ _ Q K := by
        change relativeSingularHomologyRationalization ((K : Set TM)ᶜ) i
          (@compactRelativeFundamentalClass i TM _ C _ _ P K) = _
        rw [hc K, map_zsmul]
        rfl
      -- Rationalizing the same integral class preserves its sign in the actual cap pairing.
      rw [hrat, map_zsmul, map_zsmul]
      rfl
    rw [hPQ, ← mul_assoc, hs, one_mul]
  have hs : (((-1 : ℤ) ^ (n * (n - 1) / 2) : ℤ) : ℚ) *
      (((-1 : ℤ) ^ (n * (n - 1) / 2) : ℤ) : ℚ) = 1 := by
    push_cast
    rw [← mul_pow]
    simp
  have h := hIntegralChange (n + n) (2 * n) (by omega)
    (bundleTotalEuclideanChartedSpace n n T)
    (tangentBundleEuclideanChartedSpace (n := n) (M := M))
    (bundleHomologicalOrientation n T O (tangentCohomologyOrientation g O))
    (tangentHomologicalOrientation (n := n) (M := M))
    ((-1 : ℤ) ^ (n * (n - 1) / 2)) hs
    (bundleHomologicalOrientation_tangent_compactRelativeFundamentalClass g O) a
  simpa only [compactSupportCohomologyIntegral, rationalTangentFundamentalClass,
    tangentFundamentalClass, rationalLocallyFiniteFundamentalClass, LinearMap.flip_apply,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using h

end AtiyahSinger
