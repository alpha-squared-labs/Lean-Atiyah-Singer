/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.OpenFullSymbolEllipticity
public import AtiyahSinger.Analysis.OpenGlobalPrincipalSymbol
public import AtiyahSinger.Analysis.OpenOperatorExtension
public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

import all AtiyahSinger.Analysis.ExcisionLocalization

/-!
# Extending elliptic operators with a supported correction

Public module ID: M0451.

UL03/P02: extend the actual supported correction and add the specified ambient
zero-order bundle map. Coordinate covariance transfers ellipticity on the common
region; exterior invertibility supplies it elsewhere. The supported action is
an output of the construction. This spells out an analytic part of SG III.13.4,
pp.248--249, without constructing a noncompact K representative or identifying
its extended symbol K class. Both global PDO carriers here have compact bases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Filter
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
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hN hT hT' hSC hSC' hC' hB' hν hK hL hKU hLV hKL ha hb

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (c : ∀ x, E.Fiber x →ₗ[ℂ] F.Fiber x)
  (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) c)
  (d : ∀ y, G.Fiber y →ₗ[ℂ] H.Fiber y)
  (hd : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank) d)
  (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (a x v) = b x (c x.val v))

include hC hB hμ hcd

/-- Extend a supported zero-order correction while preserving ellipticity and the actual action. -/
theorem PseudodifferentialOperator.exists_elliptic_openExtension
    (P R : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0)
    (hP : P.toLinearMap = smoothSectionMap c hc + R.toLinearMap)
    (hR : HasSectionOperatorSupport K R.toLinearMap) (hPe : P.IsElliptic)
    (hdext : ∀ y, y ∉ L → Function.Bijective (d y)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν 0,
      Q.IsElliptic ∧ HasSectionOperatorSupport L (Q.toLinearMap - smoothSectionMap d hd) ∧
        ∀ u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K,
          ∃ v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K,
            P.toLinearMap u.val = v.val ∧
              Q.toLinearMap (supportedSmoothSectionOpenEquiv E G U V e K L
                hK.isClosed hL.isClosed hKU hLV hKL a ha u).val =
              (supportedSmoothSectionOpenEquiv F H U V e K L
                hK.isClosed hL.isClosed hKU hLV hKL b hb v).val := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    -- Realize the two supplied bundle maps as their original order-zero differential operators.
    let Dc : DifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
      ⟨smoothSectionMap c hc, isDifferentialOperator_smoothSectionMap c hc⟩
    let Dd : DifferentialOperator (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0 :=
      ⟨smoothSectionMap d hd, isDifferentialOperator_smoothSectionMap d hd⟩
    let Pc : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber μ 0 :=
      ⟨Dc.toLinearMap, by simpa only [Nat.cast_zero] using Dc.isPseudodifferentialOperator (μ := μ)⟩
    let Pd : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν 0 :=
      ⟨Dd.toLinearMap, by simpa only [Nat.cast_zero] using Dd.isPseudodifferentialOperator (μ := ν)⟩
    let sc : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
      ⟨Dc.principalSymbolFunction, by
        change IsGlobalSymbol E.Fiber F.Fiber 0 Dc.principalSymbolFunction
        simpa only [Nat.cast_zero] using Dc.isGlobalSymbol_principalSymbolFunction⟩
    let sd : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0 :=
      ⟨Dd.principalSymbolFunction, by
        change IsGlobalSymbol G.Fiber H.Fiber 0 Dd.principalSymbolFunction
        simpa only [Nat.cast_zero] using Dd.isGlobalSymbol_principalSymbolFunction⟩
    have hsc (x : M) (η) (v : E.Fiber x) : sc.val x η v = c x v := by
      obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := E.rank) x v
      have h := zeroOrder_apply_eq_principalSymbol Dc u x η
      change c x (u.val x) = sc.val x η (u.val x) at h
      simpa only [hu] using h.symm
    have hsd (y : N) (η) (v : G.Fiber y) : sd.val y η v = d y v := by
      obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := G.rank) y v
      have h := zeroOrder_apply_eq_principalSymbol Dd u y η
      change d y (u.val y) = sd.val y η (u.val y) at h
      simpa only [hu] using h.symm
    have hPc : Pc.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 sc := by
      have htransport (s : ℝ) (hs : ((0 : ℕ) : ℝ) = s)
          (T : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
            E.Fiber F.Fiber μ s)
          (a : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber s)
          (hop : T.toLinearMap = Dc.toLinearMap) (hsym : a.val = Dc.principalSymbolFunction) :
          T.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber s a := by
        subst s
        rw [T.principalSymbol_eq_of_toLinearMap_eq μ (Dc.toPseudodifferentialOperator μ) hop,
          Dc.principalSymbol_toPseudodifferentialOperator μ]
        congr 1
        exact Subtype.ext hsym.symm
      exact htransport 0 (Nat.cast_zero) Pc sc rfl rfl
    have hPd : Pd.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0 sd := by
      have htransport (s : ℝ) (hs : ((0 : ℕ) : ℝ) = s)
          (T : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
            G.Fiber H.Fiber ν s)
          (a : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber s)
          (hop : T.toLinearMap = Dd.toLinearMap) (hsym : a.val = Dd.principalSymbolFunction) :
          T.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber s a := by
        subst s
        rw [T.principalSymbol_eq_of_toLinearMap_eq ν (Dd.toPseudodifferentialOperator ν) hop,
          Dd.principalSymbol_toPseudodifferentialOperator ν]
        congr 1
        exact Subtype.ext hsym.symm
      exact htransport 0 (Nat.cast_zero) Pd sd rfl rfl
    -- The same exact supported extension supplies both the action and principal-symbol witnesses.
    obtain ⟨Q₀, ⟨hQ₀, hQgerm⟩, _⟩ := R.existsUnique_openExtension E F G H U V e K L
      hK hL hKU hLV hKL a ha b hb ν μ hR
    obtain ⟨p, p', C', hC', hLC', hC'V, hRp, hQp, hpp', hp'zero⟩ :=
      exists_principalSymbols_openExtension E F G H U V e K L hK hKU hLV hKL
        a ha b hb ν μ R hR Q₀ hQ₀ hQgerm
    let Q := Pd.add Q₀
    let aFull := sc + p
    let bFull := sd + p'
    -- Keep the original full representatives when adding the prescribed exterior maps.
    have hPclass : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0 aFull := by
      have hmap : P.toLinearMap = (Pc.add R).toLinearMap := hP
      rw [P.principalSymbol_eq_of_toLinearMap_eq μ (Pc.add R) hmap,
        principalSymbol_add, hPc, hRp, ← map_add]
    have hQclass : Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber 0 bFull := by
      change (Pd.add Q₀).principalSymbol = _
      rw [principalSymbol_add, hPd, hQp, ← map_add]
    have hsource := (P.isElliptic_iff_of_principalSymbol_eq aFull hPclass).mp hPe
    -- Representative invariance transfers source ellipticity; the exact open formula transfers it.
    have htarget : IsEllipticFullGlobalSymbol (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber 0 bFull.val := by
      refine IsEllipticFullGlobalSymbol.of_openTransport E F G H U V e a ha b hb
        aFull.val hsource bFull ?_ C' hC' hC'V d
        (fun y hy ↦ hdext y (fun h ↦ hy (hLC' h))) ?_
      · intro x η v
        change sd.val (e x).val η (a x v) + p'.val (e x).val η (a x v) =
          b x (sc.val x.val _ v + p.val x.val _ v)
        rw [hsd, hsc, map_add, hcd, hpp']
      · intro y hy η v
        change sd.val y η v + p'.val y η v = d y v
        rw [hsd, hp'zero y hy η, zero_apply, add_zero]
    refine ⟨Q, (Q.isElliptic_iff_of_principalSymbol_eq bFull hQclass).mpr htarget, ?_, ?_⟩
    · have heq : Q.toLinearMap - smoothSectionMap d hd = Q₀.toLinearMap := by
        change smoothSectionMap d hd + Q₀.toLinearMap - smoothSectionMap d hd = _
        abel
      rw [heq]
      exact hQ₀
    · -- Support of the original input and correction puts the complete output in the same space.
      intro u
      have hRu (x : M) (hx : x ∉ K) : (R.toLinearMap u.val).val x = 0 := by
        by_contra hne
        exact hx (hR.1 u.val (subset_closure hne))
      have hPu : P.toLinearMap u.val ∈ supportedSmoothSections (n := n) (r := F.rank)
          F.Fiber K := by
        intro x hx
        rw [hP]
        change c x (u.val.val x) + (R.toLinearMap u.val).val x = 0
        rw [u.property x hx, map_zero, hRu x hx, add_zero]
      let v : supportedSmoothSections (n := n) (r := F.rank) F.Fiber K :=
        ⟨P.toLinearMap u.val, hPu⟩
      let Au := supportedSmoothSectionOpenEquiv E G U V e K L
        hK.isClosed hL.isClosed hKU hLV hKL a ha u
      let Bv := supportedSmoothSectionOpenEquiv F H U V e K L
        hK.isClosed hL.isClosed hKU hLV hKL b hb v
      have hAu (x : U) : Au.val.val (e x).val = a x (u.val.val x.val) :=
        supportedSmoothSectionOpenEquiv_apply E G U V e K L hK hL hKU hLV hKL a ha u x
      have hBv (x : U) : Bv.val.val (e x).val = b x (v.val.val x.val) :=
        supportedSmoothSectionOpenEquiv_apply F H U V e K L hK hL hKU hLV hKL b hb v x
      refine ⟨v, rfl, ?_⟩
      apply Subtype.ext
      funext y
      change (Q.toLinearMap Au.val).val y = Bv.val.val y
      by_cases hyV : y ∈ V
      · let x : U := e.symm ⟨y, hyV⟩
        have hxy : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyV⟩)
        rw [← hxy]
        change d (e x).val (Au.val.val (e x).val) + (Q₀.toLinearMap Au.val).val (e x).val = _
        rw [hAu, hQgerm u.val Au.val (Filter.Eventually.of_forall hAu) x, hBv, hcd]
        calc
          b x (c x.val (u.val.val x.val)) + b x ((R.toLinearMap u.val).val x.val) =
              b x (c x.val (u.val.val x.val) + (R.toLinearMap u.val).val x.val) :=
            ((b x).map_add _ _).symm
          _ = b x (v.val.val x.val) := by
            have hvalue := congrArg (fun T : smoothSections (n := n) (r := E.rank) E.Fiber →ₗ[ℂ]
              smoothSections (n := n) (r := F.rank) F.Fiber ↦ (T u.val).val x.val) hP
            exact congrArg (b x) hvalue.symm
      · have hyL : y ∉ L := fun h ↦ hyV (hLV h)
        have hQzero : (Q₀.toLinearMap Au.val).val y = 0 := by
          by_contra hne
          exact hyL (hQ₀.1 Au.val (subset_closure hne))
        change d y (Au.val.val y) + (Q₀.toLinearMap Au.val).val y = Bv.val.val y
        rw [Au.property y hyL, map_zero, hQzero, add_zero, Bv.property y hyL]

end AtiyahSinger
