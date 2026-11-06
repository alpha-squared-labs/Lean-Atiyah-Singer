/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleHomologicalOrientation
public import AtiyahSinger.Topology.CompactSupportCohomologyPointGeneration
public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing
public import AtiyahSinger.Topology.HomologicalOrientationChartSign
public import AtiyahSinger.Topology.LocalCohomologyChart
public import AtiyahSinger.Topology.LocalRelativeCupNormalizationNative
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.ThomLocalProduct
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality
public import AtiyahSinger.Topology.SupportedThomOpenExtension

/-!
# Local evaluation for the original Thom integral

Public module ID: M2248.

Top-degree compact-support integration at a singleton is evaluation on the
specified integral local generator after rationalization. These local formulas
retain the given homological orientation, including its sign in dimension zero.

Point-supported classes determine top-degree integration. In the base-first
bundle charts, the fiber orientation sign occurs twice and cancels. The ordered
Thom map therefore preserves top-degree integration for these orientations,
without assuming that the base is compact.

Source: local orientations, relative Kronecker evaluation, and compact-support
integration; Hatcher, Algebraic Topology, Section 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Integration of a point-supported class evaluates on the same chosen local generator. -/
theorem compactSupportCohomologyIntegral_singleton
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] (O : HomologicalOrientation n M)
    (x : M) (a : relativeSingularCohomology ℚ ({x}ᶜ : Set M) n) :
    compactSupportCohomologyIntegral O
        (compactSupportCohomologyClass ℚ M ⟨{x}, isCompact_singleton⟩ n a) =
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({x}ᶜ : Set M)) n a
        (relativeSingularHomologyRationalization ({x}ᶜ : Set M) n
          (O.localGenerator x 1))).down := by
  -- The original compact-support integral is the augmentation of this same relative cap.
  rw [compactSupportCohomologyIntegral_eq_duality_augmentation,
    compactPoincareDuality_representative]
  change (((TopCat.of M).singularHomology₀ε (singularCoefficient.{u} ℚ))
    (relativeSingularCapProduct ℚ ({x}ᶜ : Set M) n 0 a
      (rationalCompactRelativeFundamentalClass O ⟨{x}, isCompact_singleton⟩))).down = _
  rw [relativeSingularCapProduct_augmentation]
  -- At the singleton support the defining point restriction is the identity map.
  have h := rationalCompactRelativeFundamentalClass_restriction O
    ⟨{x}, isCompact_singleton⟩ x (Set.mem_singleton x)
  have hid : relativeSingularHomologyInclusion ℚ ({x}ᶜ : Set M) ({x}ᶜ : Set M)
      Set.Subset.rfl n = 𝟙 _ := by
    simp [relativeSingularHomologyInclusion, relativeSingularHomologyMap,
      relativeSingularChainsMap, Limits.cokernel.map]
  change relativeSingularHomologyInclusion ℚ ({x}ᶜ : Set M) ({x}ᶜ : Set M)
    Set.Subset.rfl n (rationalCompactRelativeFundamentalClass O
      ⟨{x}, isCompact_singleton⟩) = _ at h
  rw [hid, ModuleCat.id_apply] at h
  exact congrArg
    (fun z ↦ (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ ({x}ᶜ : Set M)) n a z).down) h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In any original Euclidean chart, point-supported integration retains its actual sign. -/
theorem compactSupportCohomologyIntegral_singleton_chart
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] (O : HomologicalOrientation n M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (x : M) (hx : x ∈ e.source)
    (a : relativeSingularCohomology ℚ ({x}ᶜ : Set M) n) :
    compactSupportCohomologyIntegral O
        (compactSupportCohomologyClass ℚ M ⟨{x}, isCompact_singleton⟩ n a) =
      (homologicalOrientationChartSign O e x hx : ℚ) *
        (singularCochainHomologyEvaluation ℚ
          (relativeSingularChains ℚ ({e x}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) n
          ((localCohomologyChartIso ℚ e x hx n).hom a)
          (relativeSingularHomologyRationalization
            ({e x}ᶜ : Set (EuclideanSpace ℝ (Fin n))) n
            (euclideanLocalOrientationCycle n (e x)))).down := by
  -- Transport the same integral local generator before changing coefficients.
  rw [compactSupportCohomologyIntegral_singleton,
    ← localCohomologyChartIso_evaluation e x hx n a (O.localGenerator x 1),
    localHomologyChartEquiv_localGenerator O e x hx]
  -- Both rationalization and evaluation preserve the original integer sign.
  rw [map_zsmul, map_zsmul]
  rfl

section Thom

variable {n : ℕ} (r : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M]
  (E : M → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℝ (Fin (n + r))
local notation "TE" => TotalSpace F E

attribute [local instance] t2Space_fiberBundleTotal secondCountable_fiberBundleTotal
  bundleTotalEuclideanChartedSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordered Thom map preserves top-degree integration for the specified orientations. -/
theorem compactSupportCohomologyIntegral_thomMap (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) (a : compactSupportCohomology ℚ M n) :
    compactSupportCohomologyIntegral (bundleHomologicalOrientation r E O o)
      (compactSupportCohomologyThomMap ℚ r E o.rationalization n a) =
        compactSupportCohomologyIntegral O a := by
  classical
  let OT := bundleHomologicalOrientation r E O o
  -- Point-supported classes detect top-degree functionals on the original compact-support group.
  have hmaps : (compactSupportCohomologyIntegral OT).comp
      (compactSupportCohomologyThomMap ℚ r E o.rationalization n) =
        compactSupportCohomologyIntegral O := by
    apply compactSupportCohomology_top_ext_of_singletons O
    intro x α
    let K : Compacts M := ⟨{x}, isCompact_singleton⟩
    let z := zeroSection F E x
    let c := chartAt V x
    let t := chartAt W z
    let L := VectorBundle.continuousLinearEquivAt ℝ F E x
    let b := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
    let f : C(F, E x) := ⟨L.symm, L.symm.continuous⟩
    have hf : Set.MapsTo f {v : F | v ≠ 0} {v : E x | v ≠ 0} :=
      fun _ hv ↦ L.symm.map_ne_zero_iff.mpr hv
    let aChart := (localCohomologyChartIso ℚ c x (mem_chart_source V x) n).hom α
    let bFiber := relativeSingularCohomologyPullback ℚ f hf r (o.rationalization.fiberClass x)
    let fs := realOrientationEvaluation (b.map L.symm.toLinearEquiv)
      (b.map L.symm.toLinearEquiv).orientation (o.fiberClass x)
    let baseEval := (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ ({c x}ᶜ : Set V)) n aChart
      (relativeSingularHomologyRationalization ({c x}ᶜ : Set V) n
        (euclideanLocalOrientationCycle n (c x)))).down
    -- The compact support of the singleton Thom class is exactly the original zero point.
    let Z : Compacts TE := ⟨{z}, isCompact_singleton⟩
    have hZ : supportedCohomologyThomSupport r E K = Z := by
      apply Compacts.ext
      change (bundleZeroSection r E) '' {x} = {z}
      rw [Set.image_singleton]
      rfl
    have hK : ((supportedCohomologyThomSupport r E K : Set TE)ᶜ) = ({z}ᶜ : Set TE) :=
      congrArg (fun S : Compacts TE ↦ (S : Set TE)ᶜ) hZ
    let u := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology ℚ S (n + r)) hK)).hom
      (supportedCohomologyThomMap ℚ r E o.rationalization K n α)
    have castClass (K₁ K₂ : Compacts TE) (h : K₁ = K₂)
        (β : relativeSingularCohomology ℚ ((K₁ : Set TE)ᶜ) (n + r)) :
        compactSupportCohomologyClass ℚ TE K₁ (n + r) β =
          compactSupportCohomologyClass ℚ TE K₂ (n + r)
            ((eqToIso (congrArg (fun S : Compacts TE ↦
              relativeSingularCohomology ℚ ((S : Set TE)ᶜ) (n + r)) h)).hom β) := by
      subst K₂
      rfl
    have hclass : compactSupportCohomologyClass ℚ TE
        (supportedCohomologyThomSupport r E K) (n + r)
          (supportedCohomologyThomMap ℚ r E o.rationalization K n α) =
        compactSupportCohomologyClass ℚ TE Z (n + r) u :=
      castClass _ _ hZ _
    -- The specified integral fiber sign survives the same coefficient and coordinate maps.
    have hfiber : (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : F | v ≠ 0}) r bFiber
        (relativeSingularHomologyRationalization {v : F | v ≠ 0} r
          (realOrientationCycle b b.orientation))).down = (fs : ℚ) := by
      change (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ {v : F | v ≠ 0}) r
        (relativeSingularCohomologyPullback ℚ f hf r
          (relativeSingularCohomologyRationalization {v : E x | v ≠ 0} r (o.fiberClass x)))
        (relativeSingularHomologyRationalization {v : F | v ≠ 0} r
          (realOrientationCycle b b.orientation))).down = _
      rw [← relativeSingularCohomologyRationalization_naturality f hf r (o.fiberClass x),
        singularCochainHomologyEvaluation_rationalization]
      have h := realOrientationEvaluation_pullback b L.symm (o.fiberClass x)
      unfold realOrientationEvaluation at h
      rw [relativeSingularCapProduct_augmentation,
        relativeSingularCapProduct_augmentation] at h
      change _ = (realOrientationEvaluation (b.map L.symm.toLinearEquiv)
        (b.map L.symm.toLinearEquiv).orientation (o.fiberClass x) : ℚ)
      unfold realOrientationEvaluation
      rw [relativeSingularCapProduct_augmentation]
      exact congrArg (fun z : ℤ ↦ (z : ℚ)) h
    have hfs : IsUnit fs := by
      exact isUnit_bundleFiberChartSign r E o (trivializationAt F E x) x
        (mem_baseSet_trivializationAt F E x)
    -- The actual total-space chart class is the same base-first relative cup.
    have hlocal := supportedCohomologyThomMap_localChart ℚ (n := n) r E
      o.rationalization x n α
    have heval := relativeSingularCohomologyUnionCup_local_evaluation_at n r (c x) (t z)
      aChart bFiber (bundleTotalEuclideanChart_support r E x)
    have hvalue : (singularCochainHomologyEvaluation ℚ
        (relativeSingularChains ℚ ({t z}ᶜ : Set W)) (n + r)
        ((localCohomologyChartIso ℚ t z (mem_chart_source W z) (n + r)).hom u)
        (relativeSingularHomologyRationalization ({t z}ᶜ : Set W) (n + r)
          (euclideanLocalOrientationCycle (n + r) (t z)))).down = baseEval * (fs : ℚ) := by
      rw [hlocal]
      exact heval.trans (congrArg (fun q : ℚ ↦ baseEval * q) hfiber)
    -- The total orientation uses the same two signs. The fiber sign appears twice and cancels.
    have hsign : homologicalOrientationChartSign OT t z (mem_chart_source W z) =
        homologicalOrientationChartSign O c x (mem_chart_source V x) * fs := by
      have h := (localHomologyChartEquiv_localGenerator OT t z (mem_chart_source W z)).symm.trans
        (bundleHomologicalOrientation_chart r E O o z)
      exact (euclideanLocalOrientationCycle_is_generator (n + r) (t z)).injective h
    have htotal := compactSupportCohomologyIntegral_singleton_chart OT t z
      (mem_chart_source W z) u
    have hbase := compactSupportCohomologyIntegral_singleton_chart O c x
      (mem_chart_source V x) α
    change compactSupportCohomologyIntegral OT
      (compactSupportCohomologyThomMap ℚ r E o.rationalization n
        (compactSupportCohomologyClass ℚ M K n α)) = _
    rw [compactSupportCohomologyThomMap_representative, hclass, htotal, hbase,
      hsign, hvalue, Int.cast_mul]
    rcases Int.isUnit_iff.mp hfs with hs | hs
    · rw [hs]
      norm_num [baseEval, aChart]
    · rw [hs]
      norm_num [baseEval, aChart]
  exact LinearMap.congr_fun hmaps a

end Thom

end AtiyahSinger
