/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolIndexSum
public import AtiyahSinger.Analysis.TrivialSymbolIndex
public import AtiyahSinger.Geometry.EquivariantNativeSum
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

/-!
# Smooth direct sums of elliptic representatives

Public module ID: M0966.

Two original order-zero elliptic operators admit a native smooth direct-sum
symbol and an actual quantization representing the sum of their support classes.
The full equivariant index sum for the one-element group supplies additivity
of their ordinary smooth indices. The topology comparison uses the same actual
sum maps as the analytic comparison, including zero rank and the empty base.

This is the direct-sum argument in SG III.13 (13.7)--(13.8), pp.246--247,
expressed in the project's fixed Euclidean bundle models. The statement does
not assert that every class on a disconnected base has one fixed-rank representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback isFiniteRank_sum sumTopology

set_option maxHeartbeats 1200000 in
-- The extended limit accommodates the original zero-order representatives and additive supported
-- symbol class.
/-- Two actual zero-order elliptic representatives admit a smooth sum with additive K class
and smooth index. The sum retains the original component maps through one native model. -/
theorem exists_elliptic_pseudodifferential_sum
    (E₁ F₁ E₂ F₂ : SmoothFiniteComplexBundle (n := n) M)
    (R₁ : QuantizationPresentation (n := n) (r := E₁.rank) (q := F₁.rank) E₁.Fiber F₁.Fiber)
    (s₁ : homogeneousGlobalSymbolSpace (n := n) (r := E₁.rank) (q := F₁.rank) E₁.Fiber F₁.Fiber 0)
    (P₁ : PseudodifferentialOperator (n := n) (r := E₁.rank) (q := F₁.rank) E₁.Fiber F₁.Fiber μ 0)
    (hp₁ : P₁.principalSymbol = globalPrincipalSymbolClass (n := n) (r := E₁.rank) (q := F₁.rank)
        E₁.Fiber F₁.Fiber 0
      (R₁.regularizedSymbol 0 s₁.val s₁.property.1 s₁.property.2)) (hi₁ : P₁.IsElliptic)
    (R₂ : QuantizationPresentation (n := n) (r := E₂.rank) (q := F₂.rank) E₂.Fiber F₂.Fiber)
    (s₂ : homogeneousGlobalSymbolSpace (n := n) (r := E₂.rank) (q := F₂.rank) E₂.Fiber F₂.Fiber 0)
    (P₂ : PseudodifferentialOperator (n := n) (r := E₂.rank) (q := F₂.rank) E₂.Fiber F₂.Fiber μ 0)
    (hp₂ : P₂.principalSymbol = globalPrincipalSymbolClass (n := n) (r := E₂.rank) (q := F₂.rank)
        E₂.Fiber F₂.Fiber 0
      (R₂.regularizedSymbol 0 s₂.val s₂.property.1 s₂.property.2)) (hi₂ : P₂.IsElliptic) :
    ∃ A B : SmoothFiniteComplexBundle (n := n) M,
      ∃ R : QuantizationPresentation (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber,
      ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber 0,
      ∃ P : PseudodifferentialOperator (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber μ 0,
      ∃ hp : P.principalSymbol = globalPrincipalSymbolClass (n := n) (r := A.rank) (q := B.rank)
        A.Fiber B.Fiber 0
        (R.regularizedSymbol 0 s.val s.property.1 s.property.2),
      ∃ hi : P.IsElliptic,
        P.symbolKClassOfHomogeneous R s hp hi =
          P₁.symbolKClassOfHomogeneous R₁ s₁ hp₁ hi₁ +
            P₂.symbolKClassOfHomogeneous R₂ s₂ hp₂ hi₂ ∧
        P.toLinearMap.index = P₁.toLinearMap.index + P₂.toLinearMap.index :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₂.rank)) E₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₂.rank)) F₂.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₂.rank)) E₂.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₂.rank)) F₂.Fiber
  let : ContinuousSMul PUnit.{1} M := ⟨continuous_snd⟩
  let := punitContMDiffSMul (n := n) (M := M)
  let IG := 𝓘(ℝ, PUnit.{1})
  let σE₁ := EquivariantStructure.ofSubsingleton (G := PUnit.{1}) E₁.Fiber
  let σF₁ := EquivariantStructure.ofSubsingleton (G := PUnit.{1}) F₁.Fiber
  let σE₂ := EquivariantStructure.ofSubsingleton (G := PUnit.{1}) E₂.Fiber
  let σF₂ := EquivariantStructure.ofSubsingleton (G := PUnit.{1}) F₂.Fiber
  have hσE₁ := σE₁.isSmooth_of_subsingleton (n := n) (r := E₁.rank) IG
  have hσF₁ := σF₁.isSmooth_of_subsingleton (n := n) (r := F₁.rank) IG
  have hσE₂ := σE₂.isSmooth_of_subsingleton (n := n) (r := E₂.rank) IG
  have hσF₂ := σF₂.isSmooth_of_subsingleton (n := n) (r := F₂.rank) IG
  -- The two native sums preserve both original inclusions and their product-fiber meaning.
  obtain ⟨A, _, σA, hσA, e, heg, he₁, he₂⟩ :=
    exists_equivariant_native_smooth_sum IG σE₁ σE₂ hσE₁ hσE₂
  obtain ⟨B, _, σB, hσB, f, hfg, hf₁, hf₂⟩ :=
    exists_equivariant_native_smooth_sum IG σF₁ σF₂ hσF₁ hσF₂
  let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
  have hproj := isSmoothBundleMap_sumInverse e.linearEquiv he₁ he₂
  obtain ⟨α₁, hα₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.fst ℂ (E₁.Fiber x) (E₂.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.1
  obtain ⟨α₂, hα₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.snd ℂ (E₁.Fiber x) (E₂.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.2
  obtain ⟨β₁, hβ₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp
      (LinearMap.inl ℂ (F₁.Fiber x) (F₂.Fiber x))) hf₁
  obtain ⟨β₂, hβ₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp
      (LinearMap.inr ℂ (F₁.Fiber x) (F₂.Fiber x))) hf₂
  -- Compose the actual projections, symbols and inclusions into one smooth block symbol.
  let t₁ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := F₁.rank) A.Fiber F₁.Fiber 0 :=
    ⟨globalSymbolComp s₁.val α₁.val, s₁.property.1.globalSymbolComp α₁.property.1,
      by simpa only [zero_add] using s₁.property.2.globalSymbolComp α₁.property.2⟩
  let c₁ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber 0 :=
    ⟨globalSymbolComp β₁.val t₁.val, β₁.property.1.globalSymbolComp t₁.property.1,
      by simpa only [zero_add] using β₁.property.2.globalSymbolComp t₁.property.2⟩
  let t₂ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := F₂.rank) A.Fiber F₂.Fiber 0 :=
    ⟨globalSymbolComp s₂.val α₂.val, s₂.property.1.globalSymbolComp α₂.property.1,
      by simpa only [zero_add] using s₂.property.2.globalSymbolComp α₂.property.2⟩
  let c₂ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber 0 :=
    ⟨globalSymbolComp β₂.val t₂.val, β₂.property.1.globalSymbolComp t₂.property.1,
      by simpa only [zero_add] using β₂.property.2.globalSymbolComp t₂.property.2⟩
  let s := c₁ + c₂
  have hvalue (x : M) (ξ : CotangentFiber (n := n) x) (v : A.Fiber x) :
      s.val x ξ v = f.linearEquiv x
        (s₁.val x ξ ((e.linearEquiv x).symm v).1,
          s₂.val x ξ ((e.linearEquiv x).symm v).2) := by
    change β₁.val x ξ (s₁.val x ξ (α₁.val x ξ v)) +
      β₂.val x ξ (s₂.val x ξ (α₂.val x ξ v)) = _
    rw [hα₁, hα₂, hβ₁, hβ₂]
    change f.linearEquiv x (_, 0) + f.linearEquiv x (0, _) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hsum (x : M) (ξ : CotangentFiber (n := n) x)
      (v : E₁.Fiber x) (w : E₂.Fiber x) :
      s.val x ξ (e.linearEquiv x (v, w)) =
        f.linearEquiv x (s₁.val x ξ v, s₂.val x ξ w) := by
    rw [hvalue, LinearEquiv.symm_apply_apply]
  have hj₁ := (P₁.isElliptic_iff_homogeneous R₁ s₁ hp₁).mp hi₁
  have hj₂ := (P₂.isElliptic_iff_homogeneous R₂ s₂ hp₂).mp hi₂
  have hj : IsEllipticGlobalSymbol A.Fiber B.Fiber s.val := by
    intro x ξ hξ
    let L := ((e.linearEquiv x).symm.trans
      ((LinearEquiv.ofBijective (s₁.val x ξ).toLinearMap (hj₁ x ξ hξ)).prodCongr
        (LinearEquiv.ofBijective (s₂.val x ξ).toLinearMap (hj₂ x ξ hξ)))).trans
          (f.linearEquiv x)
    have hmap : ⇑(s.val x ξ) = L := funext (hvalue x ξ)
    rw [hmap]
    exact L.bijective
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := n) (r := A.rank) (q := B.rank)
    (E := A.Fiber) (F := B.Fiber)
  let P := R.quantizeHomogeneous R μ 0 s.val s.property.1 s.property.2
  have hp := R.principalSymbol_quantizeHomogeneous R μ 0 s.val s.property.1 s.property.2
  have hi : P.IsElliptic := (P.isElliptic_iff_homogeneous R s hp).mpr hj
  refine ⟨A, B, R, s, P, hp, hi, ?_, ?_⟩
  · -- The same source and target sum maps identify the actual boundary triples.
    have hs₁c := s₁.property.1.continuous
    have hs₂c := s₂.property.1.continuous
    have hsc := s.property.1.continuous
    let πM := cotangentProjection (n := n) (M := M)
    let a := ellipticSymbolTriple s₁.val hs₁c hj₁
    let b := ellipticSymbolTriple s₂.val hs₂c hj₂
    let d := ellipticSymbolTriple s.val hsc hj
    let eπ := (sumPullbackIso πM (FiniteBundle.ofFamily E₁.Fiber)
      (FiniteBundle.ofFamily E₂.Fiber)).symm.trans (e.pullback πM)
    let fπ := (sumPullbackIso πM (FiniteBundle.ofFamily F₁.Fiber)
      (FiniteBundle.ofFamily F₂.Fiber)).symm.trans (f.pullback πM)
    let c := (a.sum b).congr eπ fπ
    have hc : c.control ⊆ cotangentZeroSet := Set.union_subset (Set.Subset.refl _)
      (Set.Subset.refl _)
    have hd : d.control ⊆ cotangentZeroSet := Set.Subset.refl _
    have hboundary : (c.enlarge cotangentZeroSet isCompact_cotangentZeroSet hc).boundary =
        (d.enlarge cotangentZeroSet isCompact_cotangentZeroSet hd).boundary := by
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro v
      have hleft := c.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet hc z v
      have hright := d.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet hd z v
      rw [hleft, hright]
      simp only [c, CompactSupportTriple.congr_apply, CompactSupportTriple.sum,
        RelativeTriple.sum_apply, Iso.restrictTo_apply]
      change f.linearEquiv z.val.proj
        ((ellipticSymbolBoundary s₁.val hs₁c hj₁).linearEquiv z
            ((e.linearEquiv z.val.proj).symm v).1,
          (ellipticSymbolBoundary s₂.val hs₂c hj₂).linearEquiv z
            ((e.linearEquiv z.val.proj).symm v).2) =
        (ellipticSymbolBoundary s.val hsc hj).linearEquiv z v
      rw [ellipticSymbolBoundary_apply, ellipticSymbolBoundary_apply,
        ellipticSymbolBoundary_apply]
      exact (hvalue z.val.proj z.val.snd v).symm
    have hhom : c.Homotopic d := by
      refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet, hc, hd, ?_⟩
      rw [hboundary]
      exact IsoHomotopy.nonempty_refl _
    change d.compactSupportClass = a.compactSupportClass + b.compactSupportClass
    exact (c.compactSupportClass_eq_of_homotopic d hhom).symm.trans
      (((a.sum b).compactSupportClass_congr eπ fπ).trans (a.compactSupportClass_sum b))
  · -- The trivial action lets the proved full representation-index sum compute smooth indices.
    have hg₁ : ∀ (g : PUnit.{1}) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE₁ σF₁ g s₁.val x ξ = s₁.val x ξ := by
      intro g x ξ _
      exact congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
        IG σE₁ σF₁ hσE₁ hσF₁ s₁.val g) x) ξ
    have hg₂ : ∀ (g : PUnit.{1}) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE₂ σF₂ g s₂.val x ξ = s₂.val x ξ := by
      intro g x ξ _
      exact congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
        IG σE₂ σF₂ hσE₂ hσF₂ s₂.val g) x) ξ
    have hg : ∀ (g : PUnit.{1}) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σA σB g s.val x ξ = s.val x ξ := by
      intro g x ξ _
      exact congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
        IG σA σB hσA hσB s.val g) x) ξ
    have hindex := congrArg (representationDimension PUnit.{1})
      (equivariantHomogeneousAnalyticIndex_eq_add_of_directSum IG σE₁ σF₁ σE₂ σF₂ σA σB
        hσE₁ hσF₁ hσE₂ hσF₂ hσA hσB s₁ hj₁ hg₁ s₂ hj₂ hg₂ s hj hg
        e f he₁ he₂ hf₁ hf₂ heg hfg (fun x ξ _ ↦ hsum x ξ))
    rw [map_add,
      representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
        IG σA σB hσA hσB s hj hg μ R P hi hp,
      representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
        IG σE₁ σF₁ hσE₁ hσF₁ s₁ hj₁ hg₁ μ R₁ P₁ hi₁ hp₁,
      representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
        IG σE₂ σF₂ hσE₂ hσF₂ s₂ hj₂ hg₂ μ R₂ P₂ hi₂ hp₂] at hindex
    exact hindex

end AtiyahSinger
