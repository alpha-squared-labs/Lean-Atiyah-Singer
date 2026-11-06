/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.EquivariantOrderReduction
public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Analysis.OrderReduction

/-!
# Equivariant radial order reduction

Public module ID: M0559.

An invariant cotangent metric gives the actual scalar homogeneous principal
symbol of an invertible equivariant PDO of every real order. The original
invariant fiber metric and density are retained in the finite-rank correction.
The smooth inverse and all Sobolev inverses belong to this same operator.
No identification with a prescribed spectral power is required or asserted.

Source: SG III.13, the existence form of elliptic order reduction, with the
actual equivariant Fredholm correction made explicit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) = h.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

set_option maxHeartbeats 1000000 in
-- The scalar symbol and the original equivariant finite-rank correction share all metrics.
include hInvariant hμInvariant in
/-- Every real order has an actual invertible equivariant radial representative. -/
theorem exists_equivariant_elliptic_orderReduction
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hg : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (γ • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ) ⟨x, ξ⟩).snd =
        g.length x ξ)
    (R : QuantizationPresentation (n := n) (r := r) (q := r) E E) (l : ℝ) :
    ∃ (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l)
      (J : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ l),
      (∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x)) ∧
      J.principalSymbol = globalPrincipalSymbolClass E E l
        (R.regularizedSymbol l a.val a.property.1 a.property.2) ∧
      J.IsEquivariant IG σ σ hσ hσ ∧ J.IsElliptic ∧ Function.Bijective J.toLinearMap ∧
      ∀ (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ),
        Function.Bijective (J.sobolevExtension A A s) := by
  classical
  -- Radial extension of the identity gives the requested scalar symbol at every real order.
  let a₀ := cosphereRestriction g (globalSymbolId (n := n) E)
  have hs₀ : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := r)
      E E (globalSymbolId E) := by
    intro c hc e f _ _
    exact ((isGlobalSymbol_globalSymbolId (E := E) (r := r)) c hc e f).1.mono
      (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩)
  let a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := r) E E l :=
    ⟨cosphereExtension g l a₀,
      (isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g l a₀).mpr
        (isSmoothCosphereSymbol_restriction g _ hs₀),
      isHomogeneousGlobalSymbol_cosphereExtension g l a₀⟩
  have ha (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      a.val x ξ = (g.length x ξ ^ l : ℝ) • ContinuousLinearMap.id ℂ (E x) := by
    change cosphereExtension g l a₀ x ξ = _
    rw [cosphereExtension_of_ne_zero g l a₀ x ξ hξ]
    simp only [a₀, cosphereRestriction, globalSymbolId, ← Complex.coe_smul]
    rfl
  have he : IsEllipticGlobalSymbol E E a.val := by
    intro x ξ hξ
    rw [ha x ξ hξ]
    exact (IsUnit.smul_bijective
      (isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (g.length_pos x ξ hξ) l).ne')).comp
      Function.bijective_id
  let p := R.regularizedSymbol l a.val a.property.1 a.property.2
  let P := R.quantize μ p
  have hP : P.IsElliptic :=
    (PseudodifferentialOperator.isElliptic_quantize_iff (μ := μ) R p).mpr
      ((isEllipticFullGlobalSymbol_regularizedSymbol_iff R l a.val
        a.property.1 a.property.2).mpr he)
  -- The radial weight is real, so adjunction fixes this actual homogeneous symbol.
  have haself (x : M) (ξ : CotangentFiber (n := n) x) :
      h.adjoint h x (a.val x ξ) = a.val x ξ := by
    by_cases hξ : ξ = 0
    · subst ξ
      simp only [a, cosphereExtension_zero_covector, h.adjoint_zero]
    · rw [ha x ξ hξ, ← Complex.coe_smul, h.adjoint_smul, h.adjoint_id,
        Complex.conj_ofReal]
  have hpself : h.symbolSpaceAdjoint h p = p := by
    apply Subtype.ext
    funext x ξ
    change h.adjoint h x (R.regularizedSymbolFunction a.val x ξ) =
      R.regularizedSymbolFunction a.val x ξ
    unfold QuantizationPresentation.regularizedSymbolFunction
    induction (Finset.univ : Finset (Fin R.size)) using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, h.adjoint_zero]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, h.adjoint_add, ih, h.adjoint_smul, haself,
        Complex.conj_ofReal]
  have hself : h.principalSymbolAdjoint h P.principalSymbol = P.principalSymbol := by
    rw [R.principalSymbol_quantize, h.principalSymbolAdjoint_class, hpself]
  -- Invariant length and the same moving-fiber identity give the exact conjugation fixed point.
  have hcov : ∀ (γ : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ σ γ a.val x ξ = a.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σ σ a.val).mpr
    intro γ x ξ hξ v
    let ξ' : CotangentFiber (n := n) (γ • x) := (cotangentDiffeomorphMap
      (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ γ) ⟨x, ξ⟩).snd
    have hξ' : ξ' ≠ 0 := by
      intro hz
      have hlen := hg γ x ξ
      change g.length (γ • x) ξ' = g.length x ξ at hlen
      have hzlen : g.length (γ • x) ξ' = 0 :=
        (g.length_eq_zero_iff (γ • x) ξ').mpr hz
      exact (g.length_pos x ξ hξ).ne' (hlen.symm.trans hzlen)
    rw [ha (γ • x) ξ' hξ', ha x ξ hξ, hg γ x ξ]
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      ← Complex.coe_smul, map_smul]
  have hfixed (γ : G) : equivariantPrincipalSymbolRepresentation IG σ σ hσ hσ l γ
      P.principalSymbol = P.principalSymbol := by
    rw [R.principalSymbol_quantize]
    exact (R.equivariant_regularizedSymbol_class_eq_iff IG σ σ hσ hσ R l a a γ).mpr
      (hcov γ)
  -- This correction preserves the same symbol and is invertible on the actual smooth carriers.
  obtain ⟨J, hJ, hJg, hJe, hJbij, hSob⟩ :=
    exists_equivariant_bijective_of_selfAdjoint_principalSymbol μ IG σ hσ h
      hInvariant hμInvariant P hP hfixed hself
  exact ⟨a, J, ha, hJ.trans (R.principalSymbol_quantize μ p), hJg, hJe, hJbij, hSob⟩

end AtiyahSinger.PseudodifferentialOperator
