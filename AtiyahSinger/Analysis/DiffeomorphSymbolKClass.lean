/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousSymbolPullback
public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Geometry.DiffeomorphBundlePullback
public import AtiyahSinger.Topology.OpenCotangentKZero

/-!
# Symbol classes for the specified diffeomorphism transport

Public module ID: M0431.

The inverse-dual cotangent map and the canonical inverse-pullback fiber
identifications give the original K-theory transport. The same full-open
symbol square used in elliptic realization determines this class equality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [CompactSpace N] [T2Space N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- The dependent original fibers and inverse-dual formulas are compared before passing to K theory.
/-- The original full-open symbol square gives precisely cotangent K transport. -/
theorem homogeneousSymbolKClass_diffeomorphPullback
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N)
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0) (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val) :
    let G := E.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
    let H := F.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
    ∀ (b : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber 0) (hb : IsEllipticGlobalSymbol G.Fiber H.Fiber b.val),
    (∀ (x : (⊤ : Opens M)) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
      b.val (e x.val) (cotangentDiffeomorphMap (diffeomorphTop e) ⟨x, ξ⟩).snd
        (LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x.val).symm v) =
      LinearEquiv.cast (R := ℂ) (M := F.Fiber) (e.symm_apply_apply x.val).symm
        (a.val x.val ξ v)) →
    cotangentKZeroDiffeomorph e (homogeneousSymbolKClass 0 a ha) =
      homogeneousSymbolKClass 0 b hb := by
  intro G H b hb hsquare
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let f : C(N, M) := ⟨e.symm, e.symm.continuous⟩
  let d (y : N) (η : CotangentFiber (n := n) y) : CotangentFiber (n := n) (f y) :=
    η.comp (mfderiv I I e (e.symm y))
  let g := cotangentDiffeomorph e
  let h := cotangentDiffeomorph e.symm
  -- Differentiate the actual inverse identity, retaining the original cotangent fibers.
  have hcomp (y : N) : (mfderiv I I e (e.symm y)).comp (mfderiv I I e.symm y) =
      ContinuousLinearMap.id ℝ (TangentSpace I y) := by
    have hd := mfderiv_comp y (e.mdifferentiable (by simp) (e.symm y))
      (e.symm.mdifferentiable (by simp) y)
    rw [show (e : M → N) ∘ e.symm = id from funext e.apply_symm_apply, mfderiv_id] at hd
    exact hd.symm
  have hright (z : CotangentTotalSpace (n := n) (M := N)) : g (h z) = z := by
    rcases z with ⟨y, η⟩
    change (⟨e (e.symm y), (η.comp (mfderiv I I e (e.symm y))).comp
      (mfderiv I I e.symm (e (e.symm y)))⟩ : CotangentTotalSpace (n := n) (M := N)) = ⟨y, η⟩
    erw [e.apply_symm_apply]
    congr 1
    rw [ContinuousLinearMap.comp_assoc, hcomp, ContinuousLinearMap.comp_id]
  have hinverse : g.symm = h := by
    apply Homeomorph.ext
    intro z
    apply g.injective
    exact (g.apply_symm_apply z).trans (hright z).symm
  have hzero (y : N) (η : CotangentFiber (n := n) y) : d y η = 0 ↔ η = 0 := by
    constructor
    · intro hη
      have hz := congrArg (fun T ↦ T.comp (mfderiv I I e.symm y)) hη
      change (η.comp (mfderiv I I e (e.symm y))).comp (mfderiv I I e.symm y) = _ at hz
      rw [ContinuousLinearMap.comp_assoc, hcomp, ContinuousLinearMap.comp_id] at hz
      exact hz
    · rintro rfl
      exact ContinuousLinearMap.zero_comp _
  have hderiv (y : (⊤ : Opens N)) : mfderiv I I (diffeomorphTop e).symm y =
      mfderiv I I e.symm y.val := by
    have hleft := mfderiv_comp y
      ((contMDiff_subtype_val (U := (⊤ : Opens M)) (n := ∞)).mdifferentiable
        (by simp) ((diffeomorphTop e).symm y))
      ((diffeomorphTop e).symm.mdifferentiable (by simp) y)
    have hright := mfderiv_comp y (e.symm.mdifferentiable (by simp) y.val)
      ((contMDiff_subtype_val (U := (⊤ : Opens N)) (n := ∞)).mdifferentiable (by simp) y)
    rw [mfderiv_openSubtypeVal] at hleft hright
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T ↦ T v) (hleft.symm.trans hright)
  have hsymbol (y : N) (η : CotangentFiber (n := n) y) (_hη : η ≠ 0)
      (v : E.Fiber (f y)) : b.val y η v = a.val (f y) (d y η) v := by
    have hs := hsquare ⟨e.symm y, mem_univ _⟩ (d y η) v
    dsimp only [cotangentDiffeomorphMap] at hs
    rw [hderiv] at hs
    let η' : CotangentFiber (n := n) (e (e.symm y)) :=
      (d y η).comp (mfderiv I I e.symm (e (e.symm y)))
    have retype (y' : N) (hy : y' = y) (θ : CotangentFiber (n := n) y')
        (hθ : HEq θ η) (w : F.Fiber (e.symm y))
        (heq : b.val y' θ
          (LinearEquiv.cast (R := ℂ) (M := E.Fiber) (congrArg e.symm hy).symm v) =
          LinearEquiv.cast (R := ℂ) (M := F.Fiber) (congrArg e.symm hy).symm w) :
        b.val y η v = w := by
      subst y'
      cases hθ
      exact heq
    have hs' : b.val (e (e.symm y)) η'
        (LinearEquiv.cast (R := ℂ) (M := E.Fiber)
          (congrArg e.symm (e.apply_symm_apply y)).symm v) =
        LinearEquiv.cast (R := ℂ) (M := F.Fiber)
          (congrArg e.symm (e.apply_symm_apply y)).symm (a.val (f y) (d y η) v) := hs
    have hsnd (u w : CotangentTotalSpace (n := n) (M := N)) (huw : u = w) :
        HEq u.snd w.snd := by
      cases huw
      rfl
    exact retype (e (e.symm y)) (e.apply_symm_apply y) η'
      (hsnd _ _ (hright ⟨y, η⟩)) _ hs'
  have hK := homogeneousSymbolKClass_pullback E F f d h.continuous h.isProperMap
    hzero 0 a b ha hb hsymbol
  change compactSupportKZeroPullback ⟨g.symm, g.symm.continuous⟩ g.symm.isProperMap
    (homogeneousSymbolKClass 0 a ha) = homogeneousSymbolKClass 0 b hb
  rw [hinverse]
  exact hK.symm

end AtiyahSinger
