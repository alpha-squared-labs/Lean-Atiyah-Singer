/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAveragePrincipalSymbol
public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.HomogeneousSymbolAtInfinity

/-!
# Homogeneous tails of actual equivariant averages

Public module ID: M0520.

An invariant cotangent metric keeps every conjugated covector in the same
exterior. Thus exact degree-one homogeneity of a full symbol passes to its
actual weighted orbit integral with the original radius. The subsequent PDO
comparison retains the specified average and its original principal class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)


variable [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]

set_option maxHeartbeats 600000 in
-- Invariance preserves the same exterior before and after the original inverse lift.
/-- Weighted orbit integration preserves an exact degree-one homogeneous tail. -/
theorem equivariantWeightedSymbolIntegral_homogeneous_at_infinity
    (ν : Measure G) [IsFiniteMeasure ν] (w : G → ℂ) (hw : Continuous w)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (h : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ)
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ)
    (hscale : ∀ x ξ (t : ℝ), 0 < t → R ≤ h.length x ξ →
      R ≤ h.length x (t • ξ) → a.val x (t • ξ) = (t : ℂ) • a.val x ξ) :
    ∀ x ξ (t : ℝ), 0 < t → R ≤ h.length x ξ → R ≤ h.length x (t • ξ) →
      (equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν w hw 1 a).val x (t • ξ) =
        (t : ℂ) • (equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν w hw 1 a).val x ξ := by
  intro x ξ t ht hξ htξ
  have horbit (g : G) :
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x (t • ξ) =
        (t : ℂ) • equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ := by
    let D := (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm
    have hlarge : R ≤ h.length (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd := by
      dsimp only [D]
      rw [Diffeomorph.smul_symm, hInv]
      exact hξ
    have htlarge : R ≤ h.length (g⁻¹ • x)
        (cotangentDiffeomorphMap D ⟨x, t • ξ⟩).snd := by
      dsimp only [D]
      rw [Diffeomorph.smul_symm, hInv]
      exact htξ
    have ha := hscale (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd
      t ht hlarge htlarge
    have ha' : a.val (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, t • ξ⟩).snd =
        (t : ℂ) • a.val (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd := ha
    dsimp only [D] at ha'
    simp only [equivariantGlobalSymbolLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [ha']
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  -- The actual fiber integral commutes with its fixed complex scalar.
  rw [equivariantWeightedSymbolIntegral_apply, equivariantWeightedSymbolIntegral_apply,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [horbit, smul_comm]

variable [T2Space G] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {μ : Measure M}
  [IsSmoothPositiveMeasure (n := n) μ]

set_option maxHeartbeats 800000 in
-- Extract from the actual average, then use its fixed principal class for exact equivariance.
/-- A homogeneous invertible averaged tail represents the same specified averaged PDO. -/
theorem PseudodifferentialOperator.exists_ellipticHomogeneous_principalSymbol_average
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F 1 a)
    (h : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ)
    (hscale : ∀ x ξ (t : ℝ), 0 < t → R ≤ h.length x ξ →
      R ≤ h.length x (t • ξ) → a.val x (t • ξ) = (t : ℂ) • a.val x ξ)
    (hbij : ∀ x ξ, R ≤ h.length x ξ → Function.Bijective
      ((∫ g, equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ
        ∂Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) : E x →L[ℂ] F x)) :
    ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 1,
      IsEllipticGlobalSymbol E F b.val ∧
      (∀ x ξ, R ≤ h.length x ξ → b.val x ξ =
        ∫ g, equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ
          ∂Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) ∧
      (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σ τ g b.val x ξ = b.val x ξ) ∧
      ∀ C : QuantizationPresentation (n := n) (r := r) (q := q) E F,
        (P.average IG σ τ hσ hτ).principalSymbol = globalPrincipalSymbolClass E F 1
          (C.regularizedSymbol 1 b.val b.property.1 b.property.2) := by
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let ā := equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν (fun _ ↦ 1) continuous_const 1 a
  have hā (x : M) (ξ : CotangentFiber (n := n) x) :
      ā.val x ξ = ∫ g, equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ ∂ν := by
    simp only [ā, equivariantWeightedSymbolIntegral_apply, one_smul]
  have hāscale := equivariantWeightedSymbolIntegral_homogeneous_at_infinity
    IG σ τ hσ hτ ν (fun _ ↦ 1) continuous_const a h R hInv hscale
  have hābij (x : M) (ξ : CotangentFiber (n := n) x) (hξ : R ≤ h.length x ξ) :
      Function.Bijective (ā.val x ξ) := by
    rw [hā]
    exact hbij x ξ hξ
  obtain ⟨b, hb, hhigh, hclass⟩ :=
    exists_ellipticHomogeneousSymbol_of_degree_one_at_infinity ā h R hR hāscale hābij
  have hprincipal (C : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
      (P.average IG σ τ hσ hτ).principalSymbol = globalPrincipalSymbolClass E F 1
        (C.regularizedSymbol 1 b.val b.property.1 b.property.2) := by
    rw [P.principalSymbol_average IG σ τ hσ hτ, hP,
      equivariantWeightedPrincipalSymbolIntegral_class]
    exact hclass C
  refine ⟨b, hb, ?_, ?_, hprincipal⟩
  · intro x ξ hξ
    exact (hhigh x ξ hξ).trans (hā x ξ)
  · -- Homogeneous uniqueness turns the average's fixed quotient class into exact off-zero data.
    obtain ⟨C⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q) (E := E) (F := F)
    intro g
    apply (QuantizationPresentation.equivariant_regularizedSymbol_class_eq_iff
      IG σ τ hσ hτ C C 1 b b g).mp
    rw [← hprincipal C]
    exact (P.average IG σ τ hσ hτ).equivariant_principalSymbol IG σ τ hσ hτ
      (P.isEquivariant_average IG σ τ hσ hτ) g

end AtiyahSinger
