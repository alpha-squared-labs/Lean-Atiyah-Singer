/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleHomologicalOrientation
public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.PoincareGysin
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.SingularCapEvaluation
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality
public import AtiyahSinger.Topology.SupportedCohomologyThomVanishing
public import AtiyahSinger.Topology.SupportedThomAction
public import AtiyahSinger.Topology.ThomIntegralNormalization
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Independent Poincare Gysin and the ordered compact-support Thom map

Public module ID: M2247.

E03. The total orientation is constructed from the same integral base and
fiber orientations in grouped base-first native charts. The Thom map is
the original pi*(a) cup U, and Gysin is independently D_target^-1 f_* D_source.
For the original front-face cap convention their comparison has the sign
(-1)^(r*(n-p)), where n is the base dimension, r the rank and p the base
cohomology degree. It is not generally an unsigned comparison.

Spin Geometry III.12, (12.2)--(12.3) and Definition 12.1 defines its Thom
map by Gysin. Its unspecified cap/product conventions must not be silently
identified with the present right-Thom multiplication. The signed comparison
below is the explicit project convention translation. The two PD-defined
maps are mutual inverses. Their top-degree integral comparison is unsigned.

No base compactness is assumed. All supports use the original compact-support
colimit, including over a noncompact tangent base. Signed zero-rank fiber
orientations are retained. The comparison uses the original cap evaluation
and an independently proved local-to-global Thom integral normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Opposite

variable {n : ℕ} (r : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [T2Space M] [SecondCountableTopology M]
  (E : M → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

local notation "F" => EuclideanSpace ℝ (Fin r)
local notation "TE" => TotalSpace F E

attribute [local instance] t2Space_fiberBundleTotal secondCountable_fiberBundleTotal
  bundleTotalEuclideanChartedSpace

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The independently defined zero-section Gysin equals the signed original ordered Thom map. -/
theorem compactSupportGysin_zeroSection (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) (p : ℕ) (a : compactSupportCohomology ℚ M p) :
    compactSupportGysin (bundleHomologicalOrientation r E O o) O
        (bundleZeroSection r E) p (p + r) (by omega) a =
      (-1 : ℚ) ^ (r * (n - p)) •
        compactSupportCohomologyThomMap ℚ r E o.rationalization p a := by
  /- Pair both homology classes with every ordinary cohomology class. The
  bundle contraction writes every test class as a projection pullback.
  The actual cap evaluation formula, ordinary-left Thom compatibility,
  and independently normalized top integral then give the same pairing.
  Its two cap signs differ by the fiber/complementary-degree sign. Finally
  the exact target Poincare duality is injective. Above dimension the base
  compact-support class is zero; no negative homological degree is used. -/
  by_cases hp : p ≤ n
  · let q := n - p
    let OT := bundleHomologicalOrientation r E O o
    have hbase : p + q = n := Nat.add_sub_of_le hp
    have htotal : (p + r) + q = n + r := by omega
    have hbaseAction : q + p = n := by omega
    have htotalAction : q + (p + r) = n + r := by omega
    let := RealBundle.isFiniteRank_of_vectorBundle F E
    let := isIso_singularCohomologyPullback_of_homotopyInverse ℚ
      (bundleProjection r E) (bundleZeroSection r E)
      ⟨RealBundle.scalingHomotopy F E⟩ ⟨ContinuousMap.Homotopy.refl _⟩ q
    -- The field Kronecker pairing detects every actual ordinary homology class.
    have hsep (x y : singularHomology ℚ TE q)
        (h : ∀ b : singularCohomology ℚ TE q,
          (singularCochainHomologyEvaluation ℚ (singularChains ℚ TE) q b x).down =
            (singularCochainHomologyEvaluation ℚ (singularChains ℚ TE) q b y).down) :
        x = y := by
      apply Module.eval_apply_injective ℚ
      apply LinearMap.ext
      intro φ
      let ψ : singularHomology ℚ TE q →ₗ[ℚ] singularCoefficient ℚ :=
        { toFun := fun z ↦ ULift.up (φ z)
          map_add' := by intros; apply ULift.ext; exact φ.map_add _ _
          map_smul' := by intros; apply ULift.ext; exact φ.map_smul _ _ }
      obtain ⟨b, hb⟩ :=
        (singularCochainHomologyEvaluation_bijective ℚ (singularChains ℚ TE) q).surjective ψ
      have hh := h b
      rw [hb] at hh
      exact hh
    -- Functoriality uses the original zero section and projection, whose composite is identity.
    have hnatural (b : singularCohomology ℚ M q) (z : singularHomology ℚ M q) :
        singularCochainHomologyEvaluation ℚ (singularChains ℚ TE) q
          (singularCohomologyPullback ℚ (bundleProjection r E) q b)
          (singularHomologyMap ℚ (bundleZeroSection r E) q z) =
          singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q b z := by
      have h := singularCochainHomologyEvaluation_naturality ℚ
        (singularChains ℚ M) (singularChains ℚ TE)
        ((singularChainsFunctor ℚ).map (TopCat.ofHom (bundleZeroSection r E))) q
        (singularCohomologyPullback ℚ (bundleProjection r E) q b) z
      change singularCochainHomologyEvaluation ℚ (singularChains ℚ TE) q
        (singularCohomologyPullback ℚ (bundleProjection r E) q b)
        (singularHomologyMap ℚ (bundleZeroSection r E) q z) =
          singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q
            (singularCohomologyPullback ℚ (bundleZeroSection r E) q
              (singularCohomologyPullback ℚ (bundleProjection r E) q b)) z at h
      rw [h]
      have hcomp : singularCohomologyPullback ℚ (bundleProjection r E) q ≫
          singularCohomologyPullback ℚ (bundleZeroSection r E) q = 𝟙 _ := by
        let P := singularCohomologyFunctor ℚ q
        change P.map (TopCat.ofHom (bundleProjection r E)).op ≫
          P.map (TopCat.ofHom (bundleZeroSection r E)).op = _
        rw [← CategoryTheory.Functor.map_comp, ← op_comp]
        exact P.map_id _
      exact congrArg (fun f ↦ singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q
        (f b) z) hcomp
    -- The same ordinary-left action becomes a top-degree Thom image after degree transport.
    have haction (b : singularCohomology ℚ M q) :
        (eqToIso (congrArg (compactSupportCohomology ℚ TE) htotalAction)).hom
          (compactSupportCohomologyAction ℚ TE q (p + r)
            (singularCohomologyPullback ℚ (bundleProjection r E) q b)
            (compactSupportCohomologyThomMap ℚ r E o.rationalization p a)) =
          compactSupportCohomologyThomMap ℚ r E o.rationalization n
            ((eqToIso (congrArg (compactSupportCohomology ℚ M) hbaseAction)).hom
              (compactSupportCohomologyAction ℚ M q p b a)) := by
      have hdegree (i j : ℕ) (hij : i = j) (c : compactSupportCohomology ℚ M i) :
          compactSupportCohomologyThomMap ℚ r E o.rationalization j
              ((eqToIso (congrArg (compactSupportCohomology ℚ M) hij)).hom c) =
            (eqToIso (congrArg (fun k ↦ compactSupportCohomology ℚ TE (k + r)) hij)).hom
              (compactSupportCohomologyThomMap ℚ r E o.rationalization i c) := by
        subst j
        rfl
      rw [← compactSupportCohomologyThomMap_action, hdegree (q + p) n hbaseAction]
      simp only [eqToIso, ← ModuleCat.comp_apply, eqToHom_trans]
    have hsign : (-1 : ℚ) ^ (r * q) * (-1 : ℚ) ^ ((p + r) * q) =
        (-1 : ℚ) ^ (p * q) := by
      have hsquare : (-1 : ℚ) ^ (r * q) * (-1 : ℚ) ^ (r * q) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [Nat.add_mul, pow_add]
      calc
        _ = (-1 : ℚ) ^ (p * q) * ((-1 : ℚ) ^ (r * q) * (-1 : ℚ) ^ (r * q)) := by ring
        _ = (-1 : ℚ) ^ (p * q) := by rw [hsquare, mul_one]
    have hcomparison :
        singularHomologyMap ℚ (bundleZeroSection r E) q (compactPoincareDuality O p q hbase a) =
          (-1 : ℚ) ^ (r * q) • compactPoincareDuality OT (p + r) q htotal
            (compactSupportCohomologyThomMap ℚ r E o.rationalization p a) := by
      apply hsep
      intro β
      obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
        (singularCohomologyPullback ℚ (bundleProjection r E) q)).surjective β
      rw [hnatural, map_smul]
      change (singularCochainHomologyEvaluation ℚ (singularChains ℚ M) q b
        (compactPoincareDuality O p q hbase a)).down =
          (-1 : ℚ) ^ (r * q) *
            (singularCochainHomologyEvaluation ℚ (singularChains ℚ TE) q
              (singularCohomologyPullback ℚ (bundleProjection r E) q b)
              (compactPoincareDuality OT (p + r) q htotal
                (compactSupportCohomologyThomMap ℚ r E o.rationalization p a))).down
      rw [compactPoincareDuality_evaluation, compactPoincareDuality_evaluation,
        haction, compactSupportCohomologyIntegral_thomMap]
      rw [← mul_assoc, hsign]
    -- Cancel the very target duality used in the original Gysin definition.
    apply (compactPoincareDualityEquiv OT (p + r) q htotal).injective
    simp only [compactSupportGysin, dite_eq_left hp, LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    change compactPoincareDualityEquiv OT (p + r) q htotal
      ((compactPoincareDualityEquiv OT (p + r) q htotal).symm
        (singularHomologyMap ℚ (bundleZeroSection r E) q
          (compactPoincareDuality O p q hbase a))) =
        compactPoincareDualityEquiv OT (p + r) q htotal
          ((-1 : ℚ) ^ (r * q) • compactSupportCohomologyThomMap ℚ r E o.rationalization p a)
    rw [LinearEquiv.apply_symm_apply, map_smul]
    exact hcomparison
  · let := compactSupportCohomology_subsingleton_above_dim O p (by omega)
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero, map_zero, smul_zero]

/-- The independently defined projection Gysin is the signed original inverse Thom map. -/
theorem compactSupportGysin_projection (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) (p : ℕ)
    (a : compactSupportCohomology ℚ TE (p + r)) :
    compactSupportGysin O (bundleHomologicalOrientation r E O o)
        (bundleProjection r E) (p + r) p (by omega) a =
      (-1 : ℚ) ^ (r * (n - p)) •
        compactSupportCohomologyThomIntegral ℚ r E o.rationalization p a := by
  /- Projection composed with the actual zero section is the identity.
  Functoriality gives the same left inverse for their independently defined
  Gysin maps. The signed zero-section comparison and actual surjectivity of
  the Thom map identify this inverse on every total compact-support class.
  The sign squares to one; above the base dimension the target vanishes. -/
  by_cases hp : p ≤ n
  · let b := compactSupportCohomologyThomIntegral ℚ r E o.rationalization p a
    let OT := bundleHomologicalOrientation r E O o
    have hzero : compactSupportGysin OT O (bundleZeroSection r E) p (p + r)
        (by omega) b = (-1 : ℚ) ^ (r * (n - p)) • a := by
      rw [compactSupportGysin_zeroSection]
      exact congrArg (fun x ↦ (-1 : ℚ) ^ (r * (n - p)) • x)
        (compactSupportCohomologyThomMap_thomIntegral ℚ r E o.rationalization p a)
    have hid : compactSupportGysin O O (ContinuousMap.id M) p p (by omega) b = b := by
      have hmap : singularHomologyMap ℚ (ContinuousMap.id M) (n - p) = 𝟙 _ := by
        change HomologicalComplex.homologyMap
          ((singularChainsFunctor ℚ).map (𝟙 (TopCat.of M))) (n - p) = 𝟙 _
        rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
      simp only [compactSupportGysin, dite_eq_left hp, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hmap, ModuleCat.id_apply, LinearEquiv.symm_apply_apply]
    have hcomp := congrArg (fun f ↦ f b)
      (compactSupportGysin_comp O OT O (bundleProjection r E) (bundleZeroSection r E)
        p (p + r) p (by omega) (by omega))
    change compactSupportGysin O OT (bundleProjection r E) (p + r) p (by omega)
      (compactSupportGysin OT O (bundleZeroSection r E) p (p + r) (by omega) b) =
        compactSupportGysin O O (ContinuousMap.id M) p p (by omega) b at hcomp
    rw [hid, hzero, map_smul] at hcomp
    have hsign : (-1 : ℚ) ^ (r * (n - p)) * (-1 : ℚ) ^ (r * (n - p)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h := congrArg (fun x ↦ (-1 : ℚ) ^ (r * (n - p)) • x) hcomp
    rw [smul_smul, hsign, one_smul] at h
    exact h
  · let := compactSupportCohomology_subsingleton_above_dim O p (by omega)
    exact Subsingleton.elim _ _


set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Compact-support cohomology of an oriented rank-r bundle vanishes below the fiber rank. -/
theorem compactSupportCohomology_subsingleton_below_rank
    (O : HomologicalOrientation n M) (o : CohomologyOrientation ℤ r E)
    (k : ℕ) (hk : k < r) : Subsingleton (compactSupportCohomology ℚ TE k) := by
  /- The complete cochain Thom comparisons give vanishing for the nonzero-vector pair
  over the whole base and over the base complement. The joint relative exact row
  transfers this to each compact zero-section support; radial compact controls then
  give vanishing in the total compact-support colimit. The argument works over any
  Hausdorff base and uses the specified rationalized orientation. -/
  exact compactSupportCohomology_subsingleton_below_rank_of_orientation
    ℚ r E o.rationalization k hk

/-- The original Thom inverse preserves the integral of top-degree supported classes. -/
theorem compactSupportCohomologyIntegral_thomIntegral
    (O : HomologicalOrientation n M) (o : CohomologyOrientation ℤ r E)
    (a : compactSupportCohomology ℚ TE (n + r)) :
    compactSupportCohomologyIntegral O
        (compactSupportCohomologyThomIntegral ℚ r E o.rationalization n a) =
      compactSupportCohomologyIntegral (bundleHomologicalOrientation r E O o) a := by
  /- Apply the independently normalized forward Thom map to its actual
  specified inverse. Their original right-inverse identity reduces the
  total class to the given a, with the same two orientations. -/
  have h := compactSupportCohomologyIntegral_thomMap r E O o
    (compactSupportCohomologyThomIntegral ℚ r E o.rationalization n a)
  rw [compactSupportCohomologyThomMap_thomIntegral] at h
  exact h.symm

end AtiyahSinger
