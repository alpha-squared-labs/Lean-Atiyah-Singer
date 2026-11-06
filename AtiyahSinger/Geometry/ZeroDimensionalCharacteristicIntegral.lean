/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinTangentOrientation
public import AtiyahSinger.Topology.CompactManifoldPairing
public import AtiyahSinger.Topology.SingularCohomologyChangeCoefficients
public import AtiyahSinger.Topology.SingularCohomologyUnits

/-!
# Fundamental-class integration in dimension zero

Public module ID: M1515.

The canonical empty tangent bases give the positive point cycles. Integration
on a compact zero-dimensional manifold is therefore the sum of the original
degree-zero cocycle values at its finitely many points. All comparisons use
the original relative singular chain projections and normalized fundamental
class. This is the signed-point endpoint of Hatcher, Algebraic Topology,
Section 3.3, with the positive sign fixed by the native tangent orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory HomologicalComplex Opposite
open scoped Manifold ContDiff Simplicial

set_option maxSynthPendingDepth 40

universe u

section PointClasses

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The original relative homology class of a point with coefficient one. -/
def relativeSingularPointClass (A : Set X) (x : X) : relativeSingularHomology R A 0 :=
  relativeSingularCycleClass R A 0
    ⟨(relativeSingularChainsProjection R A).f 0
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R)
        (((TopCat.of X).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ x))
        (ULift.up 1)), by
      change (relativeSingularChains R A).dFrom 0 _ = 0
      simp⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A map of pairs sends the class of the original point to the class of its image. -/
theorem relativeSingularPointClass_map (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (x : X) :
    relativeSingularHomologyMap R f hf 0 (relativeSingularPointClass R A x) =
      relativeSingularPointClass R B (f x) := by
  apply homologyMap_cycleClass R (relativeSingularChains R A)
    (relativeSingularChains R B) (relativeSingularChainsMap R f hf) 0
  -- The quotient square commutes, and the ordinary singular map composes the point simplex.
  have hπ : relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
      (singularChainsFunctor R).map (TopCat.ofHom f) ≫
        relativeSingularChainsProjection R B := by
    simp [relativeSingularChainsProjection, relativeSingularChainsMap]
  have hπ₀ := congrArg (fun F ↦ F.f 0) hπ
  let τ := ((TopCat.of X).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ x)
  change ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex τ ≫
    (relativeSingularChainsProjection R A).f 0 ≫
      (relativeSingularChainsMap R f hf).f 0) (ULift.up 1) = _
  rw [show (relativeSingularChainsProjection R A).f 0 ≫
    (relativeSingularChainsMap R f hf).f 0 =
      ((singularChainsFunctor R).map (TopCat.ofHom f)).f 0 ≫
        (relativeSingularChainsProjection R B).f 0 from hπ₀]
  rw [← Category.assoc]
  change (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex τ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
      (singularCoefficient R)).f 0) ≫ _) (ULift.up 1) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A point in the relative subspace represents zero in the original relative homology. -/
theorem relativeSingularPointClass_eq_zero_of_mem (A : Set X) (x : X) (hx : x ∈ A) :
    relativeSingularPointClass R A x = 0 := by
  let τ := ((TopCat.of A).toSSetObjEquiv (op ⦋0⦌)).symm
    (ContinuousMap.const _ (⟨x, hx⟩ : A))
  have hchain : (relativeSingularChainsProjection R A).f 0
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R)
        (((TopCat.of X).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ x))
        (ULift.up 1)) = 0 := by
    have hzero := congrArg (fun F ↦ F.f 0)
      (Limits.cokernel.condition (singularSubspaceChains R A))
    change (singularSubspaceChains R A).f 0 ≫
      (relativeSingularChainsProjection R A).f 0 = 0 at hzero
    have hsimplex : (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (singularSubspaceChains R A).f 0 =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (((TopCat.of X).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ x)) := by
      change (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom
          (ContinuousMap.subtypeVal A))) (singularCoefficient R)).f 0 = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    have h := congrArg (fun F ↦ (F ≫ (relativeSingularChainsProjection R A).f 0)
      (ULift.up 1)) hsimplex
    rw [Category.assoc, hzero, Limits.comp_zero] at h
    exact h.symm
  unfold relativeSingularPointClass
  rw [show (⟨_, _⟩ : relativeSingularCycles R A 0) = 0 from Subtype.ext hchain, map_zero]

end PointClasses

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Integer-to-rational coefficient change preserves the original coefficient-one point. -/
theorem relativeSingularPointClass_rationalization {X : Type u} [TopologicalSpace X]
    (A : Set X) (x : X) :
    relativeSingularHomologyRationalization A 0 (relativeSingularPointClass ℤ A x) =
      relativeSingularPointClass ℚ A x := by
  apply homologyMap_restrictScalars_cocycleClass ℤ ℚ (Int.castRingHom ℚ)
    (relativeSingularChains ℤ A) (relativeSingularChains ℚ A)
    (relativeSingularChainsRationalization A) 0
  -- The chosen coefficient maps have the prescribed quotient square and simplex values.
  have hπ := (existsUnique_relativeSingularChainsRationalization A).exists.choose_spec
  let τ := ((TopCat.of X).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ x)
  have hvalue := congrArg (fun F ↦ F.f 0
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient ℤ) τ (ULift.up 1))) hπ
  change (relativeSingularChainsRationalization A).f 0
    ((relativeSingularChainsProjection ℤ A).f 0 _) =
      (relativeSingularChainsProjection ℚ A).f 0
        ((singularChainsRationalization X).f 0 _) at hvalue
  change (relativeSingularChainsRationalization A).f 0
    ((relativeSingularChainsProjection ℤ A).f 0 _) = _
  rw [hvalue]
  have hsimplex := (existsUnique_singularChainsRationalization X).exists.choose_spec 0 τ 1
  exact congrArg ((relativeSingularChainsProjection ℚ A).f 0) hsimplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native empty tangent basis gives precisely the positive original local point class. -/
theorem zeroTangentHomologicalOrientation_localGenerator
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M] [T2Space M]
    (g : SmoothTangentMetric (n := 0) (M := M)) (x : M) :
    (zeroTangentHomologicalOrientation g).localGenerator x 1 =
      relativeSingularPointClass ℤ ({x}ᶜ : Set M) x := by
  let V := EuclideanSpace ℝ (Fin 0)
  let TM := (TangentSpace 𝓘(ℝ, V) : M → Type)
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let b : Module.Basis (Fin 0) ℝ (TM x) := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.map
    (VectorBundle.continuousLinearEquivAt ℝ V TM x).symm.toLinearEquiv
  let c := chartAt V x
  have hx : x ∈ c.source := mem_chart_source V x
  let e := localHomologyChartEquiv c x hx 0
  -- The actual chart's inclusion, homeomorphism and inclusion all preserve the point simplex.
  have hchart : e (relativeSingularPointClass ℤ ({x}ᶜ : Set M) x) =
      relativeSingularPointClass ℤ ({c x}ᶜ : Set V) (c x) := by
    let a : c.source := ⟨x, hx⟩
    let p := relativeSingularPointClass ℤ ({a}ᶜ : Set c.source) a
    have hi : localHomologyOpenInclusionEquiv c.source c.open_source a 0 p =
        relativeSingularPointClass ℤ ({x}ᶜ : Set M) x :=
      relativeSingularPointClass_map ℤ (ContinuousMap.subtypeVal c.source)
        (A := ({a}ᶜ : Set c.source)) (B := ({x}ᶜ : Set M))
        (fun _ hy h ↦ hy (Subtype.ext h)) a
    change (localHomologyOpenInclusionEquiv c.target c.open_target
      (c.toHomeomorphSourceTarget a) 0)
      ((localHomologyHomeomorphEquiv c.toHomeomorphSourceTarget a 0)
        ((localHomologyOpenInclusionEquiv c.source c.open_source a 0).symm _)) = _
    rw [← hi, LinearEquiv.symm_apply_apply]
    change relativeSingularHomologyMap ℤ (ContinuousMap.subtypeVal c.target) _ 0
      (relativeSingularHomologyMap ℤ
        (⟨c.toHomeomorphSourceTarget, c.toHomeomorphSourceTarget.continuous⟩ :
          C(c.source, c.target)) _ 0 p) = _
    rw [relativeSingularPointClass_map, relativeSingularPointClass_map]
    rfl
  -- In dimension zero the signed affine simplex of the canonical empty basis is +[0].
  have hsimplex : realOrientationSimplex b =
      (((TopCat.of (TM x)).toSSetObjEquiv (op ⦋0⦌)).symm (ContinuousMap.const _ 0)) := by
    unfold realOrientationSimplex
    apply congrArg (((TopCat.of (TM x)).toSSetObjEquiv (op ⦋0⦌)).symm)
    apply ContinuousMap.ext
    intro t
    change (∑ i : Fin 0, (t.weights i.succ - t.weights 0) • b i) = 0
    simp
  have hreal : realOrientationCycle b b.orientation =
      relativeSingularPointClass ℤ (Set.ofPred (fun v : TM x ↦ v ≠ 0)) 0 := by
    unfold realOrientationCycle relativeSingularPointClass
    apply congrArg (relativeSingularCycleClass ℤ _ 0)
    apply Subtype.ext
    simp only [realOrientationRelativeChain, ite_true, hsimplex]
  have hgenerator : (zeroTangentHomologicalOrientation g).localGenerator x 1 =
      tangentLocalHomologyEquiv (n := 0) (M := M) x
        (realOrientationCycle b b.orientation) := by
    dsimp only [zeroTangentHomologicalOrientation, geometricTangentHomologicalOrientation]
    exact (existsUnique_geometricTangentHomologicalOrientation g
      (zeroRankBundleOrientation TM)
        (isLocallyCompatibleBundleOrientation_zeroRank TM)).exists.choose_spec x
  rw [hgenerator]
  apply e.injective
  rw [hchart]
  have ht := tangentLocalHomologyEquiv_chartAt x x hx (realOrientationCycle b b.orientation)
  change e (tangentLocalHomologyEquiv x (realOrientationCycle b b.orientation)) = _ at ht
  rw [ht, hreal, relativeSingularPointClass_map]
  apply congrArg (relativeSingularPointClass ℤ ({c x}ᶜ : Set V))
  change c x + ((trivializationAt V TM x).continuousLinearEquivAt ℝ x hx) 0 = c x
  simp only [map_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On a finite zero-dimensional manifold the same normalized class is the sum of its points. -/
theorem rationalCompactRelativeFundamentalClass_zeroTangent
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Fintype M]
    (g : SmoothTangentMetric (n := 0) (M := M)) :
    rationalCompactRelativeFundamentalClass (zeroTangentHomologicalOrientation g)
      (⊤ : TopologicalSpace.Compacts M) =
      ∑ x : M, relativeSingularPointClass ℚ
        (((⊤ : TopologicalSpace.Compacts M) : Set M)ᶜ) x := by
  classical
  let K : TopologicalSpace.Compacts M := ⊤
  let O := zeroTangentHomologicalOrientation g
  -- Each local quotient kills all other points and retains this point with coefficient +1.
  have hsum : compactRelativeFundamentalClass O K =
      ∑ x : M, relativeSingularPointClass ℤ ((K : Set M)ᶜ) x := by
    apply (existsUnique_compactRelativeFundamentalClass O K).unique
    · exact compactRelativeFundamentalClass_restriction O K
    · intro x hx
      rw [map_sum]
      change (∑ y : M, relativeSingularHomologyMap ℤ (ContinuousMap.id M) _ 0
        (relativeSingularPointClass ℤ ((K : Set M)ᶜ) y)) = _
      simp_rw [relativeSingularPointClass_map]
      change (∑ y : M, relativeSingularPointClass ℤ ({x}ᶜ : Set M) y) = _
      rw [Finset.sum_eq_single x]
      · exact (zeroTangentHomologicalOrientation_localGenerator g x).symm
      · intro y _ hy
        exact relativeSingularPointClass_eq_zero_of_mem ℤ ({x}ᶜ : Set M) y hy
      · simp
  -- Rationalization is the original coefficient map, not a reselected rational generator.
  unfold rationalCompactRelativeFundamentalClass
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact relativeSingularPointClass_rationalization ((K : Set M)ᶜ) x

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original integral for the positive zero-dimensional orientation sums the point values. -/
theorem compactManifoldCohomologyIntegral_zeroTangent
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Fintype M]
    (g : SmoothTangentMetric (n := 0) (M := M))
    (a : singularCohomology ℚ M 0) (r : M → ℚ)
    (ha : ∀ x : M,
      singularCohomologyPullback ℚ (ContinuousMap.const PUnit x) 0 a =
        r x • singularCohomologyOne ℚ PUnit) :
    compactManifoldCohomologyIntegral (zeroTangentHomologicalOrientation g) a =
      ∑ x : M, r x := by
  classical
  let K : TopologicalSpace.Compacts M := ⊤
  let A : Set M := (K : Set M)ᶜ
  let O := zeroTangentHomologicalOrientation g
  let : IsEmpty A := ⟨fun x ↦ x.property (Set.mem_univ x.val)⟩
  let : IsIso (relativeSingularChainsProjection ℚ A) :=
    isIso_relativeSingularChainsProjection_of_isEmpty ℚ A
  let : IsIso (relativeSingularCohomologyToOrdinary ℚ A 0) := by
    change IsIso (homologyMap
      ((singularCochainDualFunctor ℚ).map (relativeSingularChainsProjection ℚ A).op) 0)
    infer_instance
  let I := asIso (relativeSingularCohomologyToOrdinary ℚ A 0)
  let α := I.inv a
  have hα : relativeSingularCohomologyToOrdinary ℚ A 0 α = a := I.inv_hom_id_apply a
  -- The original compact-support inverse is represented at the entire compact base.
  have hcompact : (compactSupportCohomologyIso ℚ M 0).inv a =
      compactSupportCohomologyClass ℚ M K 0 α := by
    apply (ConcreteCategory.isIso_iff_bijective
      (compactSupportCohomologyIso ℚ M 0).hom).mp inferInstance |>.injective
    rw [Iso.inv_hom_id_apply]
    have hleg : Limits.colimit.ι (compactSupportCohomologyFunctor ℚ M 0) K ≫
        compactSupportCohomologyToOrdinary ℚ M 0 =
          relativeSingularCohomologyToOrdinary ℚ A 0 := Limits.colimit.ι_desc _ _
    exact hα.symm.trans (congrArg (fun F ↦ F α) hleg).symm
  -- Evaluate each actual point using its constant simplex and the original pullback of a.
  have hpoint (x : M) :
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) 0 α
        (relativeSingularPointClass ℚ A x)).down = r x := by
    let f : C(PUnit, M) := ContinuousMap.const _ x
    let C := singularChains ℚ PUnit
    let τ := ((TopCat.of PUnit).toSSetObjEquiv (op ⦋0⦌)).symm
      (ContinuousMap.const _ PUnit.unit)
    let z : (C.sc 0).moduleCatLeftHomologyData.K :=
      ⟨(TopCat.toSSet.obj (TopCat.of PUnit)).ιChainComplex
        (R := singularCoefficient ℚ) τ (ULift.up 1), by
        change C.dFrom 0 _ = 0
        simp⟩
    let zc : C.homology 0 :=
      (C.sc 0).moduleCatHomologyIso.inv ((C.sc 0).moduleCatToCycles.range.mkQ z)
    let F := (singularChainsFunctor ℚ).map (TopCat.ofHom f) ≫
      relativeSingularChainsProjection ℚ A
    have hz : homologyMap F 0 zc = relativeSingularPointClass ℚ A x := by
      apply homologyMap_cycleClass ℚ C (relativeSingularChains ℚ A) F 0 z
      change (((TopCat.toSSet.obj (TopCat.of PUnit)).ιChainComplex τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (singularCoefficient ℚ)).f 0) ≫
            (relativeSingularChainsProjection ℚ A).f 0) (ULift.up 1) = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    have hdual : homologyMap ((singularCochainDualFunctor ℚ).map F.op) 0 =
        relativeSingularCohomologyToOrdinary ℚ A 0 ≫
          singularCohomologyPullback ℚ f 0 := by
      dsimp only [F]
      rw [op_comp, Functor.map_comp, homologyMap_comp]
      rfl
    rw [← hz, singularCochainHomologyEvaluation_naturality]
    have hvalue := congrArg (fun G ↦ G α) hdual
    change homologyMap ((singularCochainDualFunctor ℚ).map F.op) 0 α =
      singularCohomologyPullback ℚ f 0
        (relativeSingularCohomologyToOrdinary ℚ A 0 α) at hvalue
    rw [hvalue, hα, ha x, map_smul]
    change (r x • singularCochainHomologyEvaluation ℚ C 0
      (singularCocycleClass ℚ PUnit 0 (singularCocycleOne ℚ PUnit)) zc).down = r x
    have hunit := singularCochainHomologyEvaluation_cycleClass ℚ C 0
      (singularCocycleOne ℚ PUnit) z
    change singularCochainHomologyEvaluation ℚ C 0
      (singularCocycleClass ℚ PUnit 0 (singularCocycleOne ℚ PUnit)) zc =
        singularCochainEquiv ℚ PUnit 0 (singularCochainOne ℚ PUnit) τ at hunit
    rw [hunit]
    change (r x • singularCochainEquiv ℚ PUnit 0 (singularCochainOne ℚ PUnit) τ).down = r x
    rw [singularCochainOne, LinearEquiv.apply_symm_apply]
    change r x * 1 = r x
    exact mul_one _
  -- Cap augmentation pairs the same relative cocycle with the sum of these positive points.
  change compactSupportCohomologyIntegral O ((compactSupportCohomologyIso ℚ M 0).inv a) = _
  rw [hcompact, compactSupportCohomologyIntegral_eq_duality_augmentation,
    compactPoincareDuality_representative]
  change ((TopCat.of M).singularHomology₀ε (singularCoefficient ℚ)
    (relativeSingularCapProduct ℚ A 0 0 α
      (rationalCompactRelativeFundamentalClass O K))).down = _
  rw [relativeSingularCapProduct_augmentation,
    rationalCompactRelativeFundamentalClass_zeroTangent, map_sum]
  change (ULift.moduleEquiv : ULift ℚ ≃ₗ[ℚ] ℚ)
    (∑ x : M, singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) 0 α
      (relativeSingularPointClass ℚ A x)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ ↦ hpoint x

end AtiyahSinger
