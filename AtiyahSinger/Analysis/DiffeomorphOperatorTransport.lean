/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClopenPseudodifferential
public import AtiyahSinger.Analysis.DiffeomorphEllipticRepresentative

/-!
# Transport of a specified elliptic operator under a diffeomorphism

Public module ID: M0430.

Transport the original operator, including its smoothing remainder, through
the given whole-base bundle identifications. Its actual section action and
the prescribed homogeneous principal data are retained together. This is the
coordinate covariance needed to transfer equivariance and full kernel and
cokernel representations; merely selecting two equal integer indices would
not supply those comparisons. Sources: SG III.3 and III.13.
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

include hU hV hα hβ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in

/-- The specified operator transports with its actual action and prescribed homogeneous class. -/
theorem PseudodifferentialOperator.exists_diffeomorph_transport
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0)
    (A : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (R : QuantizationPresentation (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber 0)
    (hPa : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (A.regularizedSymbol 0 a.val a.property.1 a.property.2))
    (hab : ∀ (x : U) η (v : E.Fiber x.val),
      b.val (e x).val η (α x v) = β x
        (a.val x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν 0,
      Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0
        (R.regularizedSymbol 0 b.val b.property.1 b.property.2) ∧
      ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
        (v : smoothSections (n := n) (r := G.rank) G.Fiber),
        (∀ x : U, v.val (e x).val = α x (u.val x.val)) →
        ∀ x : U, (Q.toLinearMap v).val (e x).val = β x ((P.toLinearMap u).val x.val) := by
  classical
  have hKU : (univ : Set M) ⊆ (U : Set M) := by simp [hU]
  have hLV : (univ : Set N) ⊆ (V : Set N) := by simp [hV]
  have hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' (univ : Set N)) =
      (Subtype.val : U → M) ⁻¹' (univ : Set M) := by simp
  have hPs : HasSectionOperatorSupport univ P.toLinearMap := by
    refine ⟨fun _ ↦ subset_univ _, ?_⟩
    intro u hu
    have hz : u = 0 := by
      apply Subtype.ext
      funext x
      by_contra hne
      exact Set.disjoint_left.mp hu (subset_closure hne) (mem_univ x)
    rw [hz, map_zero]
  -- Extend the specified whole operator, retaining its finite pieces and smoothing remainder.
  obtain ⟨Q, ⟨hQs, hact⟩, _⟩ := P.existsUnique_openExtension
    E F G H U V e univ univ isCompact_univ isCompact_univ hKU hLV hKL
    α hα β hβ ν μ hPs
  obtain ⟨p, q, _, _, _, _, hPp, hQq, hpq, _⟩ := exists_principalSymbols_openExtension
    E F G H U V e univ univ isCompact_univ hKU hLV hKL α hα β hβ ν μ P hPs Q hQs hact
  -- Use one radial representative to compare the two independent regularization presentations.
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
  let AF := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
  obtain ⟨ℓ⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  let p₀ : GlobalSymbolFunction (n := n) E.Fiber F.Fiber := fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (ℓ.length x ξ)) : ℂ) • a.val x ξ
  have hprops := nativeAtlasSymbolFunction_homogeneous_properties
    (n := n) (r := E.rank) (q := F.rank) 0 a.val a.property.1 a.property.2 ha
  have hp₀ : IsGlobalSymbol (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 p₀ := by
    apply (isAtlasGlobalSymbol_native_iff (n := n) (r := E.rank) (q := F.rank) 0 p₀).mp
    exact isAtlasGlobalSymbol_atlasRegularizedSymbolFunction AE AF ℓ 0
      (nativeAtlasSymbolFunction a.val) hprops.1 hprops.2.1
  let pAtlas := atlasRegularizedSymbol AE AF ℓ 0 (nativeAtlasSymbolFunction a.val)
    hprops.1 hprops.2.1
  have hcompare : atlasGlobalPrincipalSymbolClass AE AF 0 pAtlas =
      atlasGlobalPrincipalSymbolClass AE AF 0
        (nativeAtlasGlobalSymbol 0 (A.regularizedSymbol 0 a.val a.property.1 a.property.2)) :=
    atlasRegularizedSymbol_principalClass_native ℓ A 0 a.val a.property.1 a.property.2 ha
  have hdelta := (atlasGlobalPrincipalSymbolClass_eq_iff AE AF 0 _ _).mp hcompare
  have hradial : globalPrincipalSymbolClass E.Fiber F.Fiber 0 ⟨p₀, hp₀⟩ =
      globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.val a.property.1 a.property.2) := by
    apply (globalPrincipalSymbolClass_eq_iff _ _ 0 _ _).mpr
    exact (isAtlasGlobalSymbol_native_iff (n := n) (r := E.rank) (q := F.rank)
      (0 - 1) (p₀ - A.regularizedSymbolFunction a.val)).mp hdelta
  have hd : IsGlobalSymbol (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber (0 - 1)
      (p.val - p₀) :=
    (globalPrincipalSymbolClass_eq_iff _ _ 0 p ⟨p₀, hp₀⟩).mp
      (hPp.symm.trans (hPa.trans hradial.symm))
  obtain ⟨q₀, hq₀, _⟩ := exists_supported_openGlobalSymbol E F G H U V e
    univ univ isCompact_univ hLV hKL α hα β hβ ⟨p₀, hp₀⟩
    (fun _ hx ↦ (hx (mem_univ _)).elim)
  obtain ⟨d, hd, _⟩ := exists_supported_openGlobalSymbol E F G H U V e
    univ univ isCompact_univ hLV hKL α hα β hβ ⟨p.val - p₀, hd⟩
    (fun _ hx ↦ (hx (mem_univ _)).elim)
  -- The transported lower-order difference is literally the difference on every target fiber.
  have hdval : d.val = q.val - q₀.val := by
    funext y η
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hLV (mem_univ y)⟩
    have hy : (e x).val = y := congrArg Subtype.val hx
    subst y
    obtain ⟨w, rfl⟩ := (α x).surjective v
    rw [hd]
    change β x (p.val x.val _ w - p₀ x.val _ w) =
      q.val (e x).val η (α x w) - q₀.val (e x).val η (α x w)
    rw [hpq, hq₀]
    exact (β x).map_sub _ _
  have hclasses : globalPrincipalSymbolClass G.Fiber H.Fiber 0 q =
      globalPrincipalSymbolClass G.Fiber H.Fiber 0 q₀ := by
    apply (globalPrincipalSymbolClass_eq_iff _ _ 0 _ _).mpr
    exact hdval ▸ d.property
  have hhigh : ∀ x ξ, 1 ≤ ℓ.length x ξ → p₀ x ξ = a.val x ξ := by
    intro x ξ hξ
    have h := (atlasRegularizedSymbolFunction_cutoff ℓ (nativeAtlasSymbolFunction a.val)).2
      x ξ hξ
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  refine ⟨Q, ?_, fun u v huv ↦ hact u v (Eventually.of_forall huv)⟩
  rw [hQq, hclasses]
  exact globalPrincipalSymbolClass_openTransport_eq_regularizedSymbol
    E F G H U V e α hα β hβ univ isCompact_univ hLV ℓ p₀ a.val hhigh q₀ b hq₀ hab
      (fun _ hx ↦ (hx (mem_univ _)).elim) R

end AtiyahSinger
