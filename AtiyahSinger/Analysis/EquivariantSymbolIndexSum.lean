/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantIndexOperations
public import AtiyahSinger.Analysis.HomogeneousSymbolOperatorComposition
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol
public import AtiyahSinger.Analysis.SmoothBundleSumDecomposition
public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Topology.EquivariantVectorBundle

/-!
# Additivity of the canonical equivariant homogeneous symbol index

Public module ID: M0594.

The direct sum is specified by two original continuous bundle isomorphisms
from the existing product-fiber bundles, with their existing sum topologies.
Smoothness is expressed by the four actual inclusion maps between the six
original modeled bundles. Inverse projections are then smooth by finite local
matrix inversion. No replacement smooth structure or Hilbert product norm is
introduced, and the original actions are compared with their existing sum actions.

Sources: SG III.5 Lemma 5.1, III.9 Definition 9.3 and Proposition 9.4,
pp.212--213, and the direct-sum well-definedness argument of III.13,
pp.246--247. This explicit smooth-equivariant symbol formulation is a project
supplement to the book's index construction, not a separately numbered lemma.

The result concerns actual degree-zero homogeneous symbols and equality of
full virtual representations. Descent through the relations of the original
equivariant compact-support K group is a separate construction. All six ranks
remain independent, allowing the empty base. The proof keeps the specified
section maps and their native metric-completion decompositions throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r₁ q₁ r₂ q₂ r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E₁ : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  {F₁ : M → Type*}
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin q₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q₁)) F₁]
  {E₂ : M → Type*}
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₂)) E₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₂)) E₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₂)) E₂]
  {F₂ : M → Type*}
  [∀ x, NormedAddCommGroup (F₂ x)] [∀ x, NormedSpace ℂ (F₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q₂)) F₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin q₂)) F₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q₂)) F₂]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE₁ : IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [hF₁ : IsSmoothComplexBundle (n := n) (r := q₁) F₁]
  [hE₂ : IsSmoothComplexBundle (n := n) (r := r₂) E₂]
  [hF₂ : IsSmoothComplexBundle (n := n) (r := q₂) F₂]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE₁ : letI := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
    EquivariantStructure G E₁)
  (σF₁ : letI := modelTopology (EuclideanSpace ℂ (Fin q₁)) F₁
    EquivariantStructure G F₁)
  (σE₂ : letI := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
    EquivariantStructure G E₂)
  (σF₂ : letI := modelTopology (EuclideanSpace ℂ (Fin q₂)) F₂
    EquivariantStructure G F₂)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE₁ : σE₁.IsSmooth (n := n) (r := r₁) IG)
  (hσF₁ : σF₁.IsSmooth (n := n) (r := q₁) IG)
  (hσE₂ : σE₂.IsSmooth (n := n) (r := r₂) IG)
  (hσF₂ : σF₂.IsSmooth (n := n) (r := q₂) IG)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE₁ hF₁ hE₂ hF₂ hE hF
  hLie hGC hGT hGM hGB hAction hσE₁ hσF₁ hσE₂ hσF₂ hσE hσF

set_option maxHeartbeats 1200000 in
-- The same six independent bundles are tracked through four compositions and two L² decompositions.
/-- An actual smooth equivariant direct-sum decomposition adds the full symbol indices. -/
theorem equivariantHomogeneousAnalyticIndex_eq_add_of_directSum
    (s₁ : homogeneousGlobalSymbolSpace (n := n) (r := r₁) (q := q₁) E₁ F₁ 0)
    (hi₁ : IsEllipticGlobalSymbol E₁ F₁ s₁.val)
    (hs₁ : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE₁ σF₁ g s₁.val x ξ = s₁.val x ξ)
    (s₂ : homogeneousGlobalSymbolSpace (n := n) (r := r₂) (q := q₂) E₂ F₂ 0)
    (hi₂ : IsEllipticGlobalSymbol E₂ F₂ s₂.val)
    (hs₂ : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE₂ σF₂ g s₂.val x ξ = s₂.val x ξ)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
    letI := modelTopology (EuclideanSpace ℂ (Fin q₁)) F₁
    letI := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
    letI := modelTopology (EuclideanSpace ℂ (Fin q₂)) F₂
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := sumTopology (E := E₁) (F := E₂)
    letI := sumTopology (E := F₁) (F := F₂)
    ∀ (e : Iso (E₁ ×ᵇ E₂) E) (f : Iso (F₁ ×ᵇ F₂) F),
      IsSmoothBundleMap (n := n) (r := r₁) (q := r)
        (fun x ↦ (e.linearEquiv x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))) →
      IsSmoothBundleMap (n := n) (r := r₂) (q := r)
        (fun x ↦ (e.linearEquiv x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))) →
      IsSmoothBundleMap (n := n) (r := q₁) (q := q)
        (fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inl ℂ (F₁ x) (F₂ x))) →
      IsSmoothBundleMap (n := n) (r := q₂) (q := q)
        (fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inr ℂ (F₁ x) (F₂ x))) →
      e.IsEquivariant (σE₁.sum σE₂) σE →
      f.IsEquivariant (σF₁.sum σF₂) σF →
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        ∀ (u : E₁ x) (v : E₂ x),
          s.val x ξ (e.linearEquiv x (u, v)) =
            f.linearEquiv x (s₁.val x ξ u, s₂.val x ξ v)) →
      equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
        equivariantHomogeneousAnalyticIndex IG σE₁ σF₁ hσE₁ hσF₁ s₁ hi₁ hs₁ +
          equivariantHomogeneousAnalyticIndex IG σE₂ σF₂ hσE₂ hσF₂ s₂ hi₂ hs₂ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r₁)) E₁
  let := modelTopology (EuclideanSpace ℂ (Fin q₁)) F₁
  let := modelTopology (EuclideanSpace ℂ (Fin r₂)) E₂
  let := modelTopology (EuclideanSpace ℂ (Fin q₂)) F₂
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := sumTopology (E := E₁) (F := E₂)
  let := sumTopology (E := F₁) (F := F₂)
  intro e f he₁ he₂ hf₁ hf₂ heg hfg hsum
  -- Recover the original inverse projections from the specified smooth inclusions.
  have heInv := isSmoothBundleMap_sumInverse e.linearEquiv he₁ he₂
  have hfInv := isSmoothBundleMap_sumInverse f.linearEquiv hf₁ hf₂
  let a₁ := fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e.linearEquiv x).symm.toLinearMap
  let a₂ := fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e.linearEquiv x).symm.toLinearMap
  let b₁ := fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inl ℂ (F₁ x) (F₂ x))
  let b₂ := fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inr ℂ (F₁ x) (F₂ x))
  let p₁ := smoothSectionMap a₁ heInv.1
  let p₂ := smoothSectionMap a₂ heInv.2
  let pF₁ := smoothSectionMap
    (fun x ↦ (LinearMap.fst ℂ (F₁ x) (F₂ x)).comp (f.linearEquiv x).symm.toLinearMap) hfInv.1
  let pF₂ := smoothSectionMap
    (fun x ↦ (LinearMap.snd ℂ (F₁ x) (F₂ x)).comp (f.linearEquiv x).symm.toLinearMap) hfInv.2
  -- All three realizations and both decompositions use one invariant measure.
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h₁, h₁Inv⟩ := exists_invariant_smoothHermitianMetric IG σE₁ hσE₁
  obtain ⟨k₁, k₁Inv⟩ := exists_invariant_smoothHermitianMetric IG σF₁ hσF₁
  obtain ⟨h₂, h₂Inv⟩ := exists_invariant_smoothHermitianMetric IG σE₂ hσE₂
  obtain ⟨k₂, k₂Inv⟩ := exists_invariant_smoothHermitianMetric IG σF₂ hσF₂
  obtain ⟨h, hInv⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInv⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨R₁⟩ := nonempty_quantizationPresentation
    (n := n) (r := r₁) (q := q₁) (E := E₁) (F := F₁)
  obtain ⟨P₁, hP₁g, hP₁class⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG σE₁ σF₁ hσE₁ hσF₁ 0
    (globalPrincipalSymbolClass E₁ F₁ 0
      (R₁.regularizedSymbol 0 s₁.val s₁.property.1 s₁.property.2))
    (fun g ↦ (R₁.equivariant_regularizedSymbol_class_eq_iff
      IG σE₁ σF₁ hσE₁ hσF₁ R₁ 0 s₁ s₁ g).mpr (hs₁ g))
  have hP₁ : P₁.IsElliptic := ⟨_, hP₁class,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R₁ 0 s₁.val
      s₁.property.1 s₁.property.2).mpr hi₁⟩
  obtain ⟨R₂⟩ := nonempty_quantizationPresentation
    (n := n) (r := r₂) (q := q₂) (E := E₂) (F := F₂)
  obtain ⟨P₂, hP₂g, hP₂class⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG σE₂ σF₂ hσE₂ hσF₂ 0
    (globalPrincipalSymbolClass E₂ F₂ 0
      (R₂.regularizedSymbol 0 s₂.val s₂.property.1 s₂.property.2))
    (fun g ↦ (R₂.equivariant_regularizedSymbol_class_eq_iff
      IG σE₂ σF₂ hσE₂ hσF₂ R₂ 0 s₂ s₂ g).mpr (hs₂ g))
  have hP₂ : P₂.IsElliptic := ⟨_, hP₂class,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R₂ 0 s₂.val
      s₂.property.1 s₂.property.2).mpr hi₂⟩
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  -- Each branch uses its actual projection, original PDO, and actual inclusion.
  let A₁ := smoothBundleMapOperator (μ := μ) a₁ heInv.1
  let B₁ := smoothBundleMapOperator (μ := μ) b₁ hf₁
  obtain ⟨α₁, hα₁, hA₁class⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) a₁ heInv.1
  obtain ⟨β₁, hβ₁, hB₁class⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) b₁ hf₁
  obtain ⟨RA₁⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := r₁) (E := E) (F := E₁)
  obtain ⟨RB₁⟩ := nonempty_quantizationPresentation
    (n := n) (r := q₁) (q := q) (E := F₁) (F := F)
  obtain ⟨RT₁⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q₁) (E := E) (F := F₁)
  let t₁ : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q₁) E F₁ 0 :=
    ⟨globalSymbolComp s₁.val α₁.val, s₁.property.1.globalSymbolComp α₁.property.1,
      by simpa only [zero_add] using s₁.property.2.globalSymbolComp α₁.property.2⟩
  let c₁ : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
    ⟨globalSymbolComp β₁.val t₁.val, β₁.property.1.globalSymbolComp t₁.property.1,
      by simpa only [zero_add] using β₁.property.2.globalSymbolComp t₁.property.2⟩
  let T₁ : PseudodifferentialOperator (n := n) (r := r) (q := q₁) E F₁ μ 0 :=
    ⟨P₁.toLinearMap.comp A₁.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (P₁.comp A₁).isPseudodifferentialOperator⟩
  let Q₁ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B₁.toLinearMap.comp T₁.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (B₁.comp T₁).isPseudodifferentialOperator⟩
  have hT₁class := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
    RA₁ R₁ RT₁ α₁ s₁ t₁ A₁ P₁ T₁ (hA₁class RA₁) hP₁class rfl
      (fun _ _ _ ↦ rfl)
  have hQ₁class := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
    RT₁ RB₁ R t₁ β₁ c₁ T₁ B₁ Q₁ hT₁class (hB₁class RB₁) rfl
      (fun _ _ _ ↦ rfl)
  let A₂ := smoothBundleMapOperator (μ := μ) a₂ heInv.2
  let B₂ := smoothBundleMapOperator (μ := μ) b₂ hf₂
  obtain ⟨α₂, hα₂, hA₂class⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) a₂ heInv.2
  obtain ⟨β₂, hβ₂, hB₂class⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) b₂ hf₂
  obtain ⟨RA₂⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := r₂) (E := E) (F := E₂)
  obtain ⟨RB₂⟩ := nonempty_quantizationPresentation
    (n := n) (r := q₂) (q := q) (E := F₂) (F := F)
  obtain ⟨RT₂⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q₂) (E := E) (F := F₂)
  let t₂ : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q₂) E F₂ 0 :=
    ⟨globalSymbolComp s₂.val α₂.val, s₂.property.1.globalSymbolComp α₂.property.1,
      by simpa only [zero_add] using s₂.property.2.globalSymbolComp α₂.property.2⟩
  let c₂ : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
    ⟨globalSymbolComp β₂.val t₂.val, β₂.property.1.globalSymbolComp t₂.property.1,
      by simpa only [zero_add] using β₂.property.2.globalSymbolComp t₂.property.2⟩
  let T₂ : PseudodifferentialOperator (n := n) (r := r) (q := q₂) E F₂ μ 0 :=
    ⟨P₂.toLinearMap.comp A₂.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (P₂.comp A₂).isPseudodifferentialOperator⟩
  let Q₂ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B₂.toLinearMap.comp T₂.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (B₂.comp T₂).isPseudodifferentialOperator⟩
  have hT₂class := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
    RA₂ R₂ RT₂ α₂ s₂ t₂ A₂ P₂ T₂ (hA₂class RA₂) hP₂class rfl
      (fun _ _ _ ↦ rfl)
  have hQ₂class := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
    RT₂ RB₂ R t₂ β₂ c₂ T₂ B₂ Q₂ hT₂class (hB₂class RB₂) rfl
      (fun _ _ _ ↦ rfl)
  let Q := Q₁.add Q₂
  have hsymbol (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      (c₁ + c₂).val x ξ = s.val x ξ := by
    apply ContinuousLinearMap.ext
    intro v
    change β₁.val x ξ (s₁.val x ξ (α₁.val x ξ v)) +
      β₂.val x ξ (s₂.val x ξ (α₂.val x ξ v)) = s.val x ξ v
    rw [hα₁, hα₂, hβ₁, hβ₂]
    change f.linearEquiv x (s₁.val x ξ ((e.linearEquiv x).symm v).1, 0) +
      f.linearEquiv x (0, s₂.val x ξ ((e.linearEquiv x).symm v).2) = s.val x ξ v
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta,
      LinearEquiv.apply_symm_apply] using
      (hsum x ξ hξ ((e.linearEquiv x).symm v).1 ((e.linearEquiv x).symm v).2).symm
  have hQclass : Q.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2) := by
    rw [Q₁.principalSymbol_add Q₂, hQ₁class, hQ₂class, ← map_add]
    have hreg : R.regularizedSymbol 0 c₁.val c₁.property.1 c₁.property.2 +
        R.regularizedSymbol 0 c₂.val c₂.property.1 c₂.property.2 =
        R.regularizedSymbol 0 (c₁ + c₂).val (c₁ + c₂).property.1 (c₁ + c₂).property.2 :=
      Subtype.ext (R.regularizedSymbolFunction_add c₁.val c₂.val).symm
    rw [hreg]
    exact (R.regularizedSymbol_class_eq_iff R 0 (c₁ + c₂).val s.val
      (c₁ + c₂).property.1 (c₁ + c₂).property.2 s.property.1 s.property.2).mpr hsymbol
  have hQ : Q.IsElliptic := ⟨_, hQclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 s.val
      s.property.1 s.property.2).mpr hi⟩
  have hQfiber (u : smoothSections (n := n) (r := r) E) (x : M) :
      (Q.toLinearMap u).val x = f.linearEquiv x
        ((P₁.toLinearMap (p₁ u)).val x, (P₂.toLinearMap (p₂ u)).val x) := by
    change f.linearEquiv x ((P₁.toLinearMap (p₁ u)).val x, 0) +
      f.linearEquiv x (0, (P₂.toLinearMap (p₂ u)).val x) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  -- The original inverse bundle maps intertwine the specified actions.
  have heInvg (g : G) (x : M) (u : E x) :
      (e.linearEquiv (g • x)).symm (σE.linearMap g x u) =
        (σE₁.linearMap g x ((e.linearEquiv x).symm u).1,
          σE₂.linearMap g x ((e.linearEquiv x).symm u).2) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (σE.linearMap g x) ((e.linearEquiv x).apply_symm_apply u)).symm.trans
      (heg g x ((e.linearEquiv x).symm u)).symm
  have hfInvg (g : G) (x : M) (u : F x) :
      (f.linearEquiv (g • x)).symm (σF.linearMap g x u) =
        (σF₁.linearMap g x ((f.linearEquiv x).symm u).1,
          σF₂.linearMap g x ((f.linearEquiv x).symm u).2) := by
    apply (f.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (σF.linearMap g x) ((f.linearEquiv x).apply_symm_apply u)).symm.trans
      (hfg g x ((f.linearEquiv x).symm u)).symm
  let RE := σE.smoothSectionRepresentation IG hσE
  let RE₁ := σE₁.smoothSectionRepresentation IG hσE₁
  let RE₂ := σE₂.smoothSectionRepresentation IG hσE₂
  let RF := σF.smoothSectionRepresentation IG hσF
  let RF₁ := σF₁.smoothSectionRepresentation IG hσF₁
  let RF₂ := σF₂.smoothSectionRepresentation IG hσF₂
  have heSection (g : G) (u : smoothSections (n := n) (r := r) E) :
      (p₁ (RE g u), p₂ (RE g u)) = (RE₁ g (p₁ u), RE₂ g (p₂ u)) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((e.linearEquiv (g • y)).symm
        (σE.sectionLinearMap g u.val (g • y))).1 =
        σE₁.sectionLinearMap g (p₁ u).val (g • y)
      rw [σE.sectionLinearMap_smul, σE₁.sectionLinearMap_smul]
      exact congrArg Prod.fst (heInvg g y (u.val y))
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((e.linearEquiv (g • y)).symm
        (σE.sectionLinearMap g u.val (g • y))).2 =
        σE₂.sectionLinearMap g (p₂ u).val (g • y)
      rw [σE.sectionLinearMap_smul, σE₂.sectionLinearMap_smul]
      exact congrArg Prod.snd (heInvg g y (u.val y))
  have hfSection (g : G) (u : smoothSections (n := n) (r := q) F) :
      (pF₁ (RF g u), pF₂ (RF g u)) = (RF₁ g (pF₁ u), RF₂ g (pF₂ u)) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((f.linearEquiv (g • y)).symm
        (σF.sectionLinearMap g u.val (g • y))).1 =
        σF₁.sectionLinearMap g (pF₁ u).val (g • y)
      rw [σF.sectionLinearMap_smul, σF₁.sectionLinearMap_smul]
      exact congrArg Prod.fst (hfInvg g y (u.val y))
    · apply Subtype.ext
      funext x
      obtain ⟨y, rfl⟩ := MulAction.surjective g x
      change ((f.linearEquiv (g • y)).symm
        (σF.sectionLinearMap g u.val (g • y))).2 =
        σF₂.sectionLinearMap g (pF₂ u).val (g • y)
      rw [σF.sectionLinearMap_smul, σF₂.sectionLinearMap_smul]
      exact congrArg Prod.snd (hfInvg g y (u.val y))
  have hQsection (u : smoothSections (n := n) (r := r) E) :
      (pF₁ (Q.toLinearMap u), pF₂ (Q.toLinearMap u)) =
        (P₁.toLinearMap (p₁ u), P₂.toLinearMap (p₂ u)) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change ((f.linearEquiv x).symm ((Q.toLinearMap u).val x)).1 = _
      rw [hQfiber, LinearEquiv.symm_apply_apply]
    · apply Subtype.ext
      funext x
      change ((f.linearEquiv x).symm ((Q.toLinearMap u).val x)).2 = _
      rw [hQfiber, LinearEquiv.symm_apply_apply]
  have hFInjective : Function.Injective (fun u ↦ (pF₁ u, pF₂ u)) := by
    intro u v huv
    apply Subtype.ext
    funext x
    apply (f.linearEquiv x).symm.injective
    exact Prod.ext
      (congrArg (fun z ↦ z.1.val x) huv) (congrArg (fun z ↦ z.2.val x) huv)
  have hQg : Q.IsEquivariant IG σE σF hσE hσF := by
    intro g
    apply LinearMap.ext
    intro u
    apply hFInjective
    change (pF₁ (Q.toLinearMap (RE g u)), pF₂ (Q.toLinearMap (RE g u))) =
      (pF₁ (RF g (Q.toLinearMap u)), pF₂ (RF g (Q.toLinearMap u)))
    have he₁ : p₁ (RE g u) = RE₁ g (p₁ u) := congrArg Prod.fst (heSection g u)
    have he₂ : p₂ (RE g u) = RE₂ g (p₂ u) := congrArg Prod.snd (heSection g u)
    have hf₁ : pF₁ (Q.toLinearMap u) = P₁.toLinearMap (p₁ u) :=
      congrArg Prod.fst (hQsection u)
    have hf₂ : pF₂ (Q.toLinearMap u) = P₂.toLinearMap (p₂ u) :=
      congrArg Prod.snd (hQsection u)
    rw [hQsection, hfSection, he₁, he₂, hf₁, hf₂]
    exact Prod.ext
      (congrArg (fun L ↦ L (p₁ u)) (hP₁g g))
      (congrArg (fun L ↦ L (p₂ u)) (hP₂g g))
  -- The same decompositions extend to the native products of the original metric completions.
  obtain ⟨eL, heL⟩ := exists_l2Equiv_of_smoothBundleSum (μ := μ) e.linearEquiv he₁ he₂ h₁ h₂ h
  obtain ⟨fL, hfL⟩ := exists_l2Equiv_of_smoothBundleSum (μ := μ) f.linearEquiv hf₁ hf₂ k₁ k₂ k
  let ρ := h.l2ContRepresentation μ IG σE hσE hInv hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInv hμInvariant
  let ρ₁ := h₁.l2ContRepresentation μ IG σE₁ hσE₁ h₁Inv hμInvariant
  let ρ₂ := h₂.l2ContRepresentation μ IG σE₂ hσE₂ h₂Inv hμInvariant
  let τ₁ := k₁.l2ContRepresentation μ IG σF₁ hσF₁ k₁Inv hμInvariant
  let τ₂ := k₂.l2ContRepresentation μ IG σF₂ hσF₂ k₂Inv hμInvariant
  let ρp := continuousRepresentationProd ρ₁ ρ₂
  let τp := continuousRepresentationProd τ₁ τ₂
  have hequiv (g : G) : eL.toContinuousLinearMap.comp (ρ g) =
      (ρp g).comp eL.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      (eL.toContinuousLinearMap.comp (ρ g)).continuous
      ((ρp g).comp eL.toContinuousLinearMap).continuous
    funext u
    change eL (h.l2IsometryRepresentation μ IG σE hσE hInv hμInvariant g
      (h.smoothToL2 μ u)) =
      (h₁.l2IsometryRepresentation μ IG σE₁ hσE₁ h₁Inv hμInvariant g
        (eL (h.smoothToL2 μ u)).1,
        h₂.l2IsometryRepresentation μ IG σE₂ hσE₂ h₂Inv hμInvariant g
          (eL (h.smoothToL2 μ u)).2)
    rw [h.l2IsometryRepresentation_smoothToL2, heL, heL,
      h₁.l2IsometryRepresentation_smoothToL2, h₂.l2IsometryRepresentation_smoothToL2]
    exact Prod.ext
      (congrArg (h₁.smoothToL2 μ) (congrArg Prod.fst (heSection g u)))
      (congrArg (h₂.smoothToL2 μ) (congrArg Prod.snd (heSection g u)))
  have hfequiv (g : G) : fL.toContinuousLinearMap.comp (τ g) =
      (τp g).comp fL.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (k.denseRange_smoothToL2 μ).equalizer
      (fL.toContinuousLinearMap.comp (τ g)).continuous
      ((τp g).comp fL.toContinuousLinearMap).continuous
    funext u
    change fL (k.l2IsometryRepresentation μ IG σF hσF kInv hμInvariant g
      (k.smoothToL2 μ u)) =
      (k₁.l2IsometryRepresentation μ IG σF₁ hσF₁ k₁Inv hμInvariant g
        (fL (k.smoothToL2 μ u)).1,
        k₂.l2IsometryRepresentation μ IG σF₂ hσF₂ k₂Inv hμInvariant g
          (fL (k.smoothToL2 μ u)).2)
    rw [k.l2IsometryRepresentation_smoothToL2, hfL, hfL,
      k₁.l2IsometryRepresentation_smoothToL2, k₂.l2IsometryRepresentation_smoothToL2]
    exact Prod.ext
      (congrArg (k₁.smoothToL2 μ) (congrArg Prod.fst (hfSection g u)))
      (congrArg (k₂.smoothToL2 μ) (congrArg Prod.snd (hfSection g u)))
  let eR : ContRepresentation.Equiv ρ ρp := ContRepresentation.Equiv.mk eL hequiv
  let fR : ContRepresentation.Equiv τ τp := ContRepresentation.Equiv.mk fL hfequiv
  let L₁ := P₁.metricL2Extension h₁ k₁
  let L₂ := P₂.metricL2Extension h₂ k₂
  have hL₁g := (P₁.isEquivariant_iff_metricL2Extension_intertwines
    IG σE₁ σF₁ hσE₁ hσF₁ h₁ k₁ h₁Inv k₁Inv hμInvariant).mp hP₁g
  have hL₂g := (P₂.isEquivariant_iff_metricL2Extension_intertwines
    IG σE₂ σF₂ hσE₂ hσF₂ h₂ k₂ h₂Inv k₂Inv hμInvariant).mp hP₂g
  have hLp (g : G) : (L₁.prodMap L₂).comp (ρp g) = (τp g).comp (L₁.prodMap L₂) := by
    apply ContinuousLinearMap.ext
    intro z
    exact Prod.ext (congrArg (fun T ↦ T z.1) (hL₁g g))
      (congrArg (fun T ↦ T z.2) (hL₂g g))
  have hρ₁ := h₁.continuous_l2ContRepresentation μ IG σE₁ hσE₁ h₁Inv hμInvariant
  have hρ₂ := h₂.continuous_l2ContRepresentation μ IG σE₂ hσE₂ h₂Inv hμInvariant
  have hτ₁ := k₁.continuous_l2ContRepresentation μ IG σF₁ hσF₁ k₁Inv hμInvariant
  have hτ₂ := k₂.continuous_l2ContRepresentation μ IG σF₂ hσF₂ k₂Inv hμInvariant
  have hρp := (hρ₁.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hρ₂.comp (continuous_fst.prodMk continuous_snd.snd))
  have hτp := (hτ₁.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hτ₂.comp (continuous_fst.prodMk continuous_snd.snd))
  obtain ⟨hFredp, hindexp⟩ := equivariantFredholmIndex_prod ρ₁ τ₁ ρ₂ τ₂ hρ₁ hτ₁ hρ₂ hτ₂
    L₁ L₂ hL₁g hL₂g (P₁.isFredholm_metricL2Extension h₁ k₁ hP₁)
      (P₂.isFredholm_metricL2Extension h₂ k₂ hP₂)
  -- The dense smooth core verifies the square for exactly this block operator.
  have hsquare : (L₁.prodMap L₂).comp eL.toContinuousLinearMap =
      fL.toContinuousLinearMap.comp (Q.metricL2Extension h k) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      ((L₁.prodMap L₂).comp eL.toContinuousLinearMap).continuous
      (fL.toContinuousLinearMap.comp (Q.metricL2Extension h k)).continuous
    funext u
    change (L₁.prodMap L₂) (eL (h.smoothToL2 μ u)) =
      fL (Q.metricL2Extension h k (h.smoothToL2 μ u))
    rw [heL, Q.metricL2Extension_smooth, hfL]
    change (P₁.metricL2Extension h₁ k₁ (h₁.smoothToL2 μ (p₁ u)),
      P₂.metricL2Extension h₂ k₂ (h₂.smoothToL2 μ (p₂ u))) = _
    rw [P₁.metricL2Extension_smooth, P₂.metricL2Extension_smooth]
    exact Prod.ext
      (congrArg (k₁.smoothToL2 μ) (congrArg Prod.fst (hQsection u)).symm)
      (congrArg (k₂.smoothToL2 μ) (congrArg Prod.snd (hQsection u)).symm)
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hi hs
    μ hμ h k hInv kInv hμInvariant R Q hQg hQ hQclass,
    equivariantHomogeneousAnalyticIndex_eq IG σE₁ σF₁ hσE₁ hσF₁ s₁ hi₁ hs₁
    μ hμ h₁ k₁ h₁Inv k₁Inv hμInvariant R₁ P₁ hP₁g hP₁ hP₁class,
    equivariantHomogeneousAnalyticIndex_eq IG σE₂ σF₂ hσE₂ hσF₂ s₂ hi₂ hs₂
    μ hμ h₂ k₂ h₂Inv k₂Inv hμInvariant R₂ P₂ hP₂g hP₂ hP₂class]
  unfold PseudodifferentialOperator.equivariantAnalyticIndex
  exact (equivariantFredholmIndex_eq_of_equiv ρ τ ρp τp _ _ hρp hτp eR fR
    (Q.metricL2Extension h k) (L₁.prodMap L₂) _ hLp hsquare _ hFredp).trans hindexp

end AtiyahSinger
