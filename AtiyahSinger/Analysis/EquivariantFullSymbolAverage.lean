/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.EquivariantWeightedSymbolIntegral
public import AtiyahSinger.Analysis.UniformSymbolRegularization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Invariant full symbols with the original homogeneous tail

Public module ID: M0511.

The actual normalized orbit integral is fixed as a full symbol. Applied to a
regularization of fixed degree-one data, an invariant metric ensures exact
recovery of those data above one common radius. These smooth invariant full
maps are suitable on the product axes as well as at infinity; their values
near the zero section are not taken from arbitrary homogeneous representatives.
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

set_option maxHeartbeats 800000 in
-- Conjugation is a continuous linear map between two genuine finite-dimensional Hom fibers.
/-- The normalized orbit integral is fixed on the entire original full-symbol space. -/
theorem equivariantWeightedSymbolIntegral_one_fixed {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) (g : G) :
    equivariantGlobalSymbolLinearMap IG σ τ g
      (equivariantWeightedSymbolIntegral IG σ τ hσ hτ
        (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G))
        (fun _ ↦ 1) continuous_const m a).val =
      (equivariantWeightedSymbolIntegral IG σ τ hσ hτ
        (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G))
        (fun _ ↦ 1) continuous_const m a).val := by
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let R := equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ
  funext x ξ
  let y := g⁻¹ • x
  let η : CotangentFiber (n := n) y := (cotangentDiffeomorphMap
    (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm ⟨x, ξ⟩).snd
  let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
    subst y
    exact ContinuousLinearMap.id ℂ (F x)
  let C : (E y →L[ℂ] F y) →L[ℂ] (E x →L[ℂ] F x) :=
    LinearMap.toContinuousLinearMap {
      toFun := fun L ↦ (transport (smul_inv_smul g x)).comp
        ((τ.linearMap g y).toContinuousLinearMap.comp
          (L.comp (σ.linearMap g⁻¹ x).toContinuousLinearMap))
      map_add' := by intro L K; simp
      map_smul' := by intro c L; simp }
  have hC (p : GlobalSymbolFunction (n := n) E F) : C (p y η) = R g p x ξ := rfl
  have hint : Integrable (fun z ↦ R z a.val y η) ν :=
    (continuous_equivariantGlobalSymbol_apply IG σ τ hσ hτ a y η)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmul := (equivariantGlobalSymbolAction_properties IG σ τ hσ hτ).2.2
  change R g _ x ξ = _
  rw [← hC]
  simp only [equivariantWeightedSymbolIntegral_apply, one_smul]
  rw [← C.integral_comp_comm hint]
  calc
    (∫ z, C (R z a.val y η) ∂ν) = ∫ z, R (g * z) a.val x ξ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hC]
      exact (congrArg (fun L : GlobalSymbolFunction (n := n) E F →ₗ[ℂ]
        GlobalSymbolFunction (n := n) E F ↦ L a.val x ξ) (hmul g z)).symm
    _ = ∫ z, R z a.val x ξ ∂ν :=
      integral_mul_left_eq_self (μ := ν) (fun z : G ↦ R z a.val x ξ) g

variable [T2Space M] [T2Space G]

include hσ hτ

set_option maxHeartbeats 800000 in
-- Every orbit point stays beyond the same recovery radius of the original regularization.
/-- Fixed degree-one data admit a smooth invariant full symbol with the exact original tail. -/
theorem QuantizationPresentation.exists_invariant_fullSymbol_eq_at_infinity
    (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (hfixed : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ)
    (h : SmoothCotangentMetric (n := n) (M := M))
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ) :
    ∃ b : globalSymbolSpace (n := n) (r := r) (q := q) E F 1,
      (∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g b.val = b.val) ∧
      (∃ R : ℝ, 1 ≤ R ∧ ∀ x ξ, R ≤ h.length x ξ → b.val x ξ = a.val x ξ) ∧
      globalPrincipalSymbolClass E F 1 b = globalPrincipalSymbolClass E F 1
        (C.regularizedSymbol 1 a.val a.property.1 a.property.2) := by
  classical
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  let p := C.regularizedSymbol 1 a.val a.property.1 a.property.2
  let b := equivariantWeightedSymbolIntegral IG σ τ hσ hτ ν (fun _ ↦ 1) continuous_const 1 p
  have hb (x : M) (ξ : CotangentFiber (n := n) x) :
      b.val x ξ = ∫ g, equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ ∂ν := by
    simp only [b, equivariantWeightedSymbolIntegral_apply, one_smul]
  refine ⟨b, ?_, ?_, ?_⟩
  · intro g
    exact equivariantWeightedSymbolIntegral_one_fixed IG σ τ hσ hτ p g
  · obtain ⟨R, hR, hrecover⟩ := C.exists_regularizedSymbolFunction_eq_of_length_ge h
    refine ⟨R, hR, ?_⟩
    intro x ξ hξ
    have hne : ξ ≠ 0 := by
      intro hz
      rw [hz, (h.length_eq_zero_iff x 0).mpr rfl] at hξ
      exact (not_le_of_gt (zero_lt_one.trans_le hR)) hξ
    have horbit (g : G) : equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ = a.val x ξ := by
      let D := (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm
      have hlarge : R ≤ h.length (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd := by
        dsimp only [D]
        rw [Diffeomorph.smul_symm, hInv]
        exact hξ
      have hsame : p.val (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd =
          a.val (g⁻¹ • x) (cotangentDiffeomorphMap D ⟨x, ξ⟩).snd :=
        hrecover a.val (g⁻¹ • x) _ hlarge
      have hconj : equivariantGlobalSymbolLinearMap IG σ τ g p.val x ξ =
          equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ := by
        dsimp only [D] at hsame
        simp only [equivariantGlobalSymbolLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hsame]
      exact hconj.trans (hfixed g x ξ hne)
    rw [hb]
    simp only [horbit, integral_const, probReal_univ, one_smul]
  · have hprincipal (g : G) : equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ 1 g
        (globalPrincipalSymbolClass E F 1 p) = globalPrincipalSymbolClass E F 1 p := by
      exact (QuantizationPresentation.equivariant_regularizedSymbol_class_eq_iff
        IG σ τ hσ hτ C C 1 a a g).mpr (hfixed g)
    have hclass := equivariantWeightedPrincipalSymbolIntegral_one_of_fixed
      IG σ τ hσ hτ ν 1 (globalPrincipalSymbolClass E F 1 p) hprincipal
    rw [equivariantWeightedPrincipalSymbolIntegral_class] at hclass
    simpa only [probReal_univ, Complex.ofReal_one, one_smul] using hclass

end AtiyahSinger
