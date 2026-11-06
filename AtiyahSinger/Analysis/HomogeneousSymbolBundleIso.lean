/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousSymbolOperations
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol

/-!
# Bundle isomorphisms of homogeneous principal data

Public module ID: M0745.

Over a compact smooth manifold, source and target bundle isomorphisms preserve
the compact-support K class when they intertwine the nonzero-covector symbols.
Using a supplied smooth positive density, a smooth inverse input map and a
smooth forward output map also construct the transport of degree-zero data
in the native bundle models. The pullback square retains the same cotangent
zero-section support.

Source: SG III.13, bundle-coordinate invariance. The native-model adapters
are project deductions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
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
  {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) G]
  {H : M → Type*}
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) H]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

/-- The actual original bundle square preserves the ordinary homogeneous symbol K class. -/
theorem homogeneousSymbolKClass_eq_of_bundleIso (m : ℝ)
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
      Iso E G)
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
      Iso F H)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') G H m)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol G H t.val)
    (hst : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ u : E x,
      f.linearEquiv x (s.val x ξ u) = t.val x ξ (e.linearEquiv x u)) :
    homogeneousSymbolKClass m s hi = homogeneousSymbolKClass m t hj := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) G
  let := modelTopology (EuclideanSpace ℂ (Fin q')) H
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r')) G
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q')) H
  let πM := cotangentProjection (n := n) (M := M)
  let a := ellipticSymbolTriple s.val s.property.1.continuous hi
  let b := ellipticSymbolTriple t.val t.property.1.continuous hj
  -- Pull back exactly the two supplied maps; conjugation keeps the zero-section control.
  have hab : a.congr (e.pullback πM) (f.pullback πM) = b := by
    dsimp only [a, b, πM]
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change f.linearEquiv z.val.proj
      ((ellipticSymbolBoundary s.val s.property.1.continuous hi).linearEquiv z
        ((e.linearEquiv z.val.proj).symm v)) =
      (ellipticSymbolBoundary t.val t.property.1.continuous hj).linearEquiv z v
    have hs₀ := ellipticSymbolBoundary_apply s.val s.property.1.continuous hi
      ⟨z.val, z.property⟩ ((e.linearEquiv z.val.proj).symm v)
    have ht₀ := ellipticSymbolBoundary_apply t.val t.property.1.continuous hj
      ⟨z.val, z.property⟩ v
    exact (congrArg (f.linearEquiv z.val.proj) hs₀).trans
      ((hst z.val.proj z.val.snd z.property ((e.linearEquiv z.val.proj).symm v)).trans
        ((congrArg (t.val z.val.proj z.val.snd)
          ((e.linearEquiv z.val.proj).apply_symm_apply v)).trans ht₀.symm))
  -- The arbitrary-universe raw triple comparison already includes its small-model descent.
  change a.compactSupportClass = b.compactSupportClass
  rw [← hab]
  exact (a.compactSupportClass_congr (e.pullback πM) (f.pullback πM)).symm

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := r') G]
  [IsSmoothComplexBundle (n := n) (r := q') H]

/-- Smooth bundle isomorphisms transport a degree-zero homogeneous symbol by the same square. -/
theorem exists_homogeneousSymbol_of_bundleIso
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
      Iso E G)
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
      Iso F H)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
      IsSmoothBundleMap (n := n) (r := r') (q := r) e.symm.toHom.linearMap)
    (hf : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
      IsSmoothBundleMap (n := n) (r := q) (q := q') f.toHom.linearMap)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin r')) G
    letI := modelTopology (EuclideanSpace ℂ (Fin q')) H
    ∃ t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') G H 0,
      IsEllipticGlobalSymbol G H t.val ∧
        ∀ (x : M) (ξ : CotangentFiber (n := n) x) (u : E x),
          f.linearEquiv x (s.val x ξ u) = t.val x ξ (e.linearEquiv x u) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) G
  let := modelTopology (EuclideanSpace ℂ (Fin q')) H
  -- Quantized multiplication symbols give smoothness in the original native models.
  obtain ⟨a, ha, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    e.symm.toHom.linearMap he
  obtain ⟨b, hb, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    f.toHom.linearMap hf
  let as : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q) G F 0 :=
    ⟨globalSymbolComp s.val a.val, s.property.1.globalSymbolComp a.property.1,
      by simpa only [zero_add] using s.property.2.globalSymbolComp a.property.2⟩
  let t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') G H 0 :=
    ⟨globalSymbolComp b.val as.val, b.property.1.globalSymbolComp as.property.1,
      by simpa only [zero_add] using b.property.2.globalSymbolComp as.property.2⟩
  have ht (x : M) (ξ : CotangentFiber (n := n) x) (v : G x) :
      t.val x ξ v = f.linearEquiv x (s.val x ξ ((e.linearEquiv x).symm v)) := by
    change b.val x ξ (s.val x ξ (a.val x ξ v)) = _
    rw [ha, hb]
    rfl
  refine ⟨t, ?_, ?_⟩
  · -- Each transported nonzero-covector map is a composite of three actual bijections.
    intro x ξ hξ
    have heq : (t.val x ξ : G x → H x) =
        f.linearEquiv x ∘ s.val x ξ ∘ (e.linearEquiv x).symm := funext (ht x ξ)
    rw [heq]
    exact (f.linearEquiv x).bijective.comp ((hi x ξ hξ).comp (e.linearEquiv x).symm.bijective)
  · intro x ξ u
    rw [ht, LinearEquiv.symm_apply_apply]

end AtiyahSinger
