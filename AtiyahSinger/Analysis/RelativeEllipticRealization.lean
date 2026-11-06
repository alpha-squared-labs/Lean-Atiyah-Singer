/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenExtensionPrincipal
public import AtiyahSinger.Analysis.OpenHomogeneousComparison
public import AtiyahSinger.Analysis.OpenHomogeneousSymbol
public import AtiyahSinger.Analysis.OpenOperatorExtension
public import AtiyahSinger.Analysis.OpenPrincipalSymbol
public import AtiyahSinger.Analysis.RelativeHomogeneousTriple
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Analysis.RelativeQuantization
public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

import all AtiyahSinger.Analysis.ExcisionLocalization

/-!
# Ambient elliptic realization of one relative finite quantization

Public module ID: M0914.

UL03/P02: the operator construction in SG III.13.4, pp.248--249, with the
specified source pieces, bundle identifications and ambient zero-order map.
Only the target is compact and carries a density. The principal-symbol equality
is an output, as are ellipticity and a raw triple with the smaller compact
zero-section control. That triple keeps the actual boundary action, allowing
subsequent open-pushforward comparison without assuming its K-class equality.

The source symbol is smooth off zero, homogeneous of degree zero and elliptic.
Its exterior action agrees with the supplied smooth bundle map at zero as well
as at nonzero covectors. Exterior invertibility on the target is required
separately; off-zero ellipticity alone says nothing in dimension zero.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

-- Use native pullback instances for the bundle identifications in this construction.
attribute [local instance 2000] FiberBundle.pullback VectorBundle.pullback

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
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
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

include hM hN hT hT' hSC hSC' hC' hB' hν hK hL hKU hLV hKL hα hβ

-- The ambient construction uses smoothness of d and its compatibility with c.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in

/-- One relative finite quantization has an exact ambient elliptic realization and symbol triple. -/
theorem exists_relative_elliptic_openExtension_of_pieces
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (haext : ∀ x, x ∉ K → ∀ ξ, a.val x ξ = c x)
    (d : ∀ y, G.Fiber y →L[ℂ] H.Fiber y)
    (hd : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
      (fun y ↦ (d y).toLinearMap))
    (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (α x v) = β x (c x.val v))
    (hdext : ∀ y, y ∉ L → Function.Bijective (d y))
    (g : SmoothCotangentMetric (n := n) (M := M)) (k : ℕ)
    (T : Fin k → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hsupport : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ K)
    (hprincipal : ∀ x ξ, 1 ≤ g.length x ξ →
      (∑ j, (T j).globalSymbol).val x ξ + c x = a.val x ξ)
    (R : QuantizationPresentation (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν 0,
      ∃ a' : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
          G.Fiber H.Fiber 0,
        ∃ ha' : IsEllipticGlobalSymbol G.Fiber H.Fiber a'.val,
          Q.IsElliptic ∧
          Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0
            (R.regularizedSymbol 0 a'.val a'.property.1 a'.property.2) ∧
          HasSectionOperatorSupport L
            (Q.toLinearMap - smoothSectionMap (fun y ↦ (d y).toLinearMap) hd) ∧
          (∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
            (v : smoothSections (n := n) (r := G.rank) G.Fiber),
            (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
              v.val (e x).val = α x (u.val x.val)) →
            ∀ x : U,
              ((Q.toLinearMap - smoothSectionMap (fun y ↦ (d y).toLinearMap) hd) v).val
                  (e x).val = β x (((∑ j, (T j).toLinearMap) u).val x.val)) ∧
          (∀ (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
            a'.val (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) =
              β x (a.val x.val ξ v)) ∧
          (∀ y, y ∉ L → ∀ η, a'.val y η = d y) ∧
          (letI := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
           letI := modelTopology (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
           letI := isFiniteRank_model (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
           letI := isFiniteRank_model (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
           ∃ b : CompactSupportTriple
               ((cotangentProjection (n := n) (M := N) : _ → N) *ᵖ G.Fiber)
               ((cotangentProjection (n := n) (M := N) : _ → N) *ᵖ H.Fiber),
             b.control = cotangentZeroSection '' L ∧
             (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := N))))
               (v : G.Fiber z.val.proj),
               b.boundary.linearEquiv z v = a'.val z.val.proj z.val.snd v) ∧
             b.compactSupportClass = homogeneousSymbolKClass 0 a' ha') := by
  /- Stage 1: apply exact open extension to the specified finite family T.
  Add the actual order-zero operator of d. Its difference from d is exactly
  the extended finite sum, with both support laws and the stated germ action.
  Every coordinate-change remainder and lower-order cutoff term stays in Q.
  Stage 2: transport a by the inverse dual differential and the two given
  fiber equivalences on V. On N minus L set it equal to d at every covector.
  The identities haext and hcd identify these formulas on their overlap.
  Because L is closed inside V, the gluing is smooth off zero. Its degree is
  zero, and the fiber formula includes zero covectors without asserting any
  smoothness there over L. Source ellipticity and hdext imply target ellipticity.
  Stage 3: on the common region the sum of the pieces' specified principal
  representatives plus c equals a at sufficiently large cotangent length.
  Transport this equality in the original coordinates and frames. Two-sided
  cutoff reduction retains the principal part and loses only lower orders;
  off L the operator is d. Compare with the supplied R's regularization in
  compact target charts to obtain the actual principal quotient equality.
  Apply the homogeneous ellipticity criterion to Q and this same a'.
  Stage 4: off zero(L), a' is a continuous fiber isomorphism: away from zero
  use ellipticity; at zero over N minus L use the smooth, invertible d.
  This constructs b on the actual cotangent pullbacks with control zero(L).
  Enlarging that control to the whole compact zero section gives the original
  elliptic symbol triple with exactly the same boundary. Control invariance
  proves its class equals homogeneousSymbolKClass of this a'. The later open
  pushforward comparison still requires the source triple and matching data;
  its class equality is not an input here. No source compactness or measure,
  finite CW witness, preconnectedness, orientation or positive dimension is used. -/
  classical
  -- First extend the specified finite section action, preserving its exact supported germ law.
  obtain ⟨Q₀, hQ₀, _⟩ := existsUnique_openExtension_of_pieces E F G H U V e
    K L hK hL hKU hLV hKL α hα β hβ ν k T hsupport
  let p₀ : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0 := ∑ j, (T j).globalSymbol
  have hp₀zero : ∀ x, x ∉ K → ∀ ξ, p₀.val x ξ = 0 := by
    intro x hx ξ
    simp only [p₀, Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact (T j).globalSymbolFunction_eq_zero x (fun h ↦ hx (hsupport j (by
      obtain ⟨z, hz, rfl⟩ := h
      exact ⟨z, Or.inr hz.1, rfl⟩))) ξ
  obtain ⟨p, hpraw, hpzero⟩ := exists_supported_openGlobalSymbol E F G H U V e
    K L hL hLV hKL α hα β hβ p₀ hp₀zero
  have hQ₀class : Q₀.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0 p :=
    principalSymbol_openExtension_of_pieces E F G H U V e K L hK hL hKU hLV hKL
      α hα β hβ ν k T hsupport Q₀ hQ₀.1 hQ₀.2 p hpraw hpzero
  -- Add the actual exterior bundle map and identify its order-zero polynomial on each fiber.
  let B : DifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber 0 :=
    ⟨smoothSectionMap (fun y ↦ (d y).toLinearMap) hd,
      isDifferentialOperator_smoothSectionMap _ hd⟩
  let bD : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0 :=
    ⟨B.principalSymbolFunction, by
      change IsGlobalSymbol G.Fiber H.Fiber 0 B.principalSymbolFunction
      simpa only [Nat.cast_zero] using B.isGlobalSymbol_principalSymbolFunction⟩
  have hbD (y : N) (η : CotangentFiber (n := n) y) : bD.val y η = d y := by
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := exists_smoothSection_apply_eq (n := n) (r := G.rank) y w
    have hact := zeroOrder_apply_eq_principalSymbol B v y η
    change d y (v.val y) = B.principalSymbol y η (v.val y) at hact
    change B.principalSymbol y η w = d y w
    simpa only [hv] using hact.symm
  let B₀ : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν 0 :=
    ⟨B.toLinearMap, by simpa only [Nat.cast_zero] using
      B.isPseudodifferentialOperator (μ := ν)⟩
  have hBclass : B₀.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0 bD := by
    have htransport (s : ℝ) (hs : ((0 : ℕ) : ℝ) = s)
        (B' : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
          G.Fiber H.Fiber ν s)
        (b' : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber s)
        (hop : B'.toLinearMap = B.toLinearMap) (hsym : b'.val = B.principalSymbolFunction) :
        B'.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber s b' := by
      subst s
      rw [B'.principalSymbol_eq_of_toLinearMap_eq ν (B.toPseudodifferentialOperator ν) hop,
        B.principalSymbol_toPseudodifferentialOperator ν]
      congr 1
      exact Subtype.ext hsym.symm
    exact htransport 0 Nat.cast_zero B₀ bD rfl rfl
  let Q := Q₀.add B₀
  have hQdiff : Q.toLinearMap - smoothSectionMap (fun y ↦ (d y).toLinearMap) hd =
      Q₀.toLinearMap := by
    change Q₀.toLinearMap + B.toLinearMap - B.toLinearMap = Q₀.toLinearMap
    exact add_sub_cancel_right _ _
  -- The homogeneous transport glues to d at every exterior covector, including zero.
  obtain ⟨a', ha', ha'action, ha'ext⟩ := exists_openHomogeneousSymbol E F G H U V e
    K L hL hLV hKL α hα β hβ a ha c haext d hd hcd hdext
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hright (x : U) : (mfderiv I I e x).comp (mfderiv I I e.symm (e x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hcomp := mfderiv_comp (e x) (e.mdifferentiable (by simp) (e.symm (e x)))
      (e.symm.mdifferentiable (by simp) (e x))
    rw [show (e : U → V) ∘ e.symm = id from funext e.apply_symm_apply,
      mfderiv_id, e.symm_apply_apply] at hcomp
    exact hcomp.symm
  have ha'raw (x : U) (η : CotangentFiber (n := n) (e x).val) (v : E.Fiber x.val) :
      a'.val (e x).val η (α x v) = β x (a.val x.val (η.comp (mfderiv I I e x)) v) := by
    have hη : (cotangentDiffeomorphMap e ⟨x, η.comp (mfderiv I I e x)⟩).snd = η := by
      change (η.comp (mfderiv I I e x)).comp (mfderiv I I e.symm (e x)) = η
      erw [ContinuousLinearMap.comp_assoc, hright, ContinuousLinearMap.comp_id]
    simpa only [hη] using ha'action x (η.comp (mfderiv I I e x)) v
  let q := p + bD
  have hqraw (x : U) (η : CotangentFiber (n := n) (e x).val) (v : E.Fiber x.val) :
      q.val (e x).val η (α x v) = β x
        ((p₀.val x.val (η.comp (mfderiv I I e x)) + c x.val) v) := by
    change (p.val (e x).val η + bD.val (e x).val η) (α x v) = _
    rw [hbD]
    simp only [add_apply, hpraw, hcd, map_add]
    rfl
  have hqext (y : N) (hy : y ∉ L) (η : CotangentFiber (n := n) y) :
      q.val y η = a'.val y η := by
    change p.val y η + bD.val y η = a'.val y η
    rw [hpzero y hy, hbD, ha'ext y hy, zero_add]
  -- The prescribed high-frequency equality determines the class for this exact operator.
  have hclass : Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0
      (R.regularizedSymbol 0 a'.val a'.property.1 a'.property.2) := by
    rw [PseudodifferentialOperator.principalSymbol_add, hQ₀class, hBclass, ← map_add]
    exact globalPrincipalSymbolClass_openTransport_eq_regularizedSymbol E F G H U V e
      α hα β hβ L hL hLV g (fun x ξ ↦ p₀.val x ξ + c x) a.val hprincipal
      q a' hqraw ha'raw hqext R
  refine ⟨Q, a', ha', (Q.isElliptic_iff_homogeneous R a' hclass).mpr ha', hclass, ?_,
    ?_, ha'action, ha'ext, ?_⟩
  · rw [hQdiff]
    exact hQ₀.1
  · rw [hQdiff]
    exact hQ₀.2
  · exact exists_relativeHomogeneousSymbolTriple G H L hL a' ha' d hd ha'ext hdext

end AtiyahSinger
