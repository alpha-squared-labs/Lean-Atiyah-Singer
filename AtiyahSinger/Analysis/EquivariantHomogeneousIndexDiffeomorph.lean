/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DiffeomorphOperatorTransport
public import AtiyahSinger.Analysis.EquivariantSmoothIndexEquivalence
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex

/-!
# Equivariant homogeneous indices under the same diffeomorphism

Public module ID: M0521.

The specified bundle and section identifications transport one actual
equivariant elliptic operator. Its original homogeneous principal square,
source and target action squares, kernel, and quotient cokernel are retained.
The conclusion is equality in the full representation ring. This naturality
is used when interchanging the two nested open carriers of a clopen refinement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace Filter Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (hU : U = ⊤) (hV : V = ⊤)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (α : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (α x).toLinearMap))
  (β : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (β x).toLinearMap))
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]


variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

variable {VG Γ : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [ChartedSpace VG Γ]
  [LieGroup 𝓘(ℝ, VG) ∞ Γ] [CompactSpace Γ] [T2Space Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  [MulAction Γ M] [ContinuousSMul Γ M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Γ M]
  [MulAction Γ N] [ContinuousSMul Γ N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Γ N]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure Γ E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure Γ F.Fiber)
  (τG : letI := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
    EquivariantStructure Γ G.Fiber)
  (τH : letI := modelTopology (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
    EquivariantStructure Γ H.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG))
  (hτG : τG.IsSmooth (n := n) (r := G.rank) 𝓘(ℝ, VG))
  (hτH : τH.IsSmooth (n := n) (r := H.rank) 𝓘(ℝ, VG))

include hU hV hα hβ μ ν

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine diffeomorphism and the same equivariant section square preserve the full index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_diffeomorph
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (hb : IsEllipticGlobalSymbol G.Fiber H.Fiber b.val)
    (hga : ∀ (g : Γ) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g a.val x ξ = a.val x ξ)
    (hgb : ∀ (g : Γ) (x : N) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) τG τH g b.val x ξ = b.val x ξ)
    (hab : ∀ (x : U) η (v : E.Fiber x.val),
      b.val (e x).val η (α x v) = β x
        (a.val x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (S : smoothSections (n := n) (r := E.rank) E.Fiber ≃ₗ[ℂ]
      smoothSections (n := n) (r := G.rank) G.Fiber)
    (T : smoothSections (n := n) (r := F.rank) F.Fiber ≃ₗ[ℂ]
      smoothSections (n := n) (r := H.rank) H.Fiber)
    (hS : ∀ u x, (S u).val (e x).val = α x (u.val x.val))
    (hT : ∀ u x, (T u).val (e x).val = β x (u.val x.val))
    (hSg : ∀ g u, S (σE.smoothSectionRepresentation 𝓘(ℝ, VG) hσE g u) =
      τG.smoothSectionRepresentation 𝓘(ℝ, VG) hτG g (S u))
    (hTg : ∀ g u, T (σF.smoothSectionRepresentation 𝓘(ℝ, VG) hσF g u) =
      τH.smoothSectionRepresentation 𝓘(ℝ, VG) hτH g (T u)) :
    equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF a ha hga =
      equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) τG τH hτG hτH b hb hgb := by
  classical
  obtain ⟨A⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := G.rank) (q := H.rank) (E := G.Fiber) (F := H.Fiber)
  let p := A.regularizedSymbol 0 a.val a.property.1 a.property.2
  have hfixed (g : Γ) : equivariantPrincipalSymbolRepresentation
      𝓘(ℝ, VG) σE σF hσE hσF 0 g (globalPrincipalSymbolClass E.Fiber F.Fiber 0 p) =
        globalPrincipalSymbolClass E.Fiber F.Fiber 0 p :=
    (A.equivariant_regularizedSymbol_class_eq_iff
      𝓘(ℝ, VG) σE σF hσE hσF A 0 a a g).mpr (hga g)
  -- Quantize the prescribed source equivariantly, then transport this very operator.
  obtain ⟨P, hPg, hPa⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) 𝓘(ℝ, VG) σE σF hσE hσF 0
      (globalPrincipalSymbolClass E.Fiber F.Fiber 0 p) hfixed
  have hP : P.IsElliptic := (P.isElliptic_iff_homogeneous A a hPa).mpr ha
  obtain ⟨Q, hQb, hact⟩ := P.exists_diffeomorph_transport
    E F G H U V hU hV e α hα β hβ ν μ A R a ha b hPa hab
  have hQ : Q.IsElliptic := (Q.isElliptic_iff_homogeneous R b hQb).mpr hb
  have hinter (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      Q.toLinearMap (S u) = T (P.toLinearMap u) := by
    apply Subtype.ext
    funext y
    obtain ⟨x, hx⟩ := e.surjective ⟨y, by simp [hV]⟩
    have hy : (e x).val = y := congrArg Subtype.val hx
    rw [← hy, hT]
    exact hact u (S u) (hS u) x
  have hQg : Q.IsEquivariant 𝓘(ℝ, VG) τG τH hτG hτH := by
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := S.surjective v
    change Q.toLinearMap (τG.smoothSectionRepresentation 𝓘(ℝ, VG) hτG g (S u)) =
      τH.smoothSectionRepresentation 𝓘(ℝ, VG) hτH g (Q.toLinearMap (S u))
    rw [← hSg, hinter, hinter, ← hTg]
    exact congrArg T (LinearMap.congr_fun (hPg g) u)
  -- The given source and target equivalences identify the same two finite defect representations.
  rw [equivariantHomogeneousAnalyticIndex_eq_smooth
    𝓘(ℝ, VG) σE σF hσE hσF a ha hga μ A P hPg hP hPa,
    equivariantHomogeneousAnalyticIndex_eq_smooth
      𝓘(ℝ, VG) τG τH hτG hτH b hb hgb ν R Q hQg hQ hQb]
  exact P.smoothEquivariantAnalyticIndex_eq_of_sectionEquiv
    𝓘(ℝ, VG) E F G H σE σF τG τH hσE hσF hτG hτH μ ν Q hPg hP hQg hQ
      S T hSg hTg hinter

end AtiyahSinger
