/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Geometry.SmoothSectionPullback

/-!
# Proper pullback of homogeneous symbol classes

Public module ID: M0749.

The actual cotangent map and native pullback bundles determine the pullback
symbol class. A fiber map detecting the zero covector pulls back precisely the
original zero-section control. This naturality supplies both clopen restriction
and diffeomorphism transport without changing either symbol's fiber action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N] [CompactSpace N] [T2Space N]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent
attribute [local instance 2000] FiberBundle.pullback VectorBundle.pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in

/-- A proper cotangent pullback retaining the zero covectors preserves the original symbol class. -/
theorem homogeneousSymbolKClass_pullback
    (E F : SmoothFiniteComplexBundle (n := n) M) (f : C(N, M))
    (d : ∀ y : N, CotangentFiber (n := m) y → CotangentFiber (n := n) (f y))
    (hd : Continuous (fun z : CotangentTotalSpace (n := m) (M := N) ↦
      (⟨f z.proj, d z.proj z.snd⟩ : CotangentTotalSpace (n := n) (M := M))))
    (hp : IsProperMap (fun z : CotangentTotalSpace (n := m) (M := N) ↦
      (⟨f z.proj, d z.proj z.snd⟩ : CotangentTotalSpace (n := n) (M := M))))
    (hzero : ∀ y ξ, d y ξ = 0 ↔ ξ = 0) (l : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber l)
    (b : homogeneousGlobalSymbolSpace (n := m) (r := E.rank) (q := F.rank)
      ((f : N → M) *ᵖ E.Fiber) ((f : N → M) *ᵖ F.Fiber) l)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (hb : IsEllipticGlobalSymbol ((f : N → M) *ᵖ E.Fiber)
      ((f : N → M) *ᵖ F.Fiber) b.val)
    (hab : ∀ y ξ, ξ ≠ 0 → ∀ v : E.Fiber (f y), b.val y ξ v = a.val (f y) (d y ξ) v) :
    homogeneousSymbolKClass l b hb = compactSupportKZeroPullback
      ⟨fun z ↦ ⟨f z.proj, d z.proj z.snd⟩, hd⟩ hp (homogeneousSymbolKClass l a ha) := by
  let Φ : C(CotangentTotalSpace (n := m) (M := N),
      CotangentTotalSpace (n := n) (M := M)) := ⟨fun z ↦ ⟨f z.proj, d z.proj z.snd⟩, hd⟩
  let πM := cotangentProjection (n := n) (M := M)
  let πN := cotangentProjection (n := m) (M := N)
  -- Canonical reassociation keeps each vector and also its native pullback topology.
  have comparison (B : SmoothFiniteComplexBundle (n := n) M) :
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber)
      ∃ e : Iso ((Φ : _ → _) *ᵖ ((πM : _ → M) *ᵖ B.Fiber))
          ((πN : _ → N) *ᵖ ((f : N → M) *ᵖ B.Fiber)),
        ∀ z v, e.linearEquiv z v = v := by
    let tB : TopologicalSpace (TotalSpace Unit B.Fiber) :=
      modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
    have htop : modelTopology (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber) =
        (inferInstance : TopologicalSpace (TotalSpace Unit ((f : N → M) *ᵖ B.Fiber))) := by
      change TopologicalSpace.induced
          (unitTotalEquiv (EuclideanSpace ℂ (Fin B.rank)) ((f : N → M) *ᵖ B.Fiber))
          (Pullback.TotalSpace.topologicalSpace (EuclideanSpace ℂ (Fin B.rank)) B.Fiber f) =
        Pullback.TotalSpace.topologicalSpace Unit B.Fiber f
      simp only [Pullback.TotalSpace.topologicalSpace, pullbackTopology_def, tB,
        modelTopology, induced_inf, induced_compose]
      rfl
    let e₀ := (pullbackCompIso (E := B.Fiber) πM Φ).trans
      (pullbackCompIso (E := B.Fiber) f πN).symm
    have he₀ (z : CotangentTotalSpace (n := m) (M := N)) (v : B.Fiber (f z.proj)) :
        e₀.linearEquiv z v = v := by
      apply ((pullbackCompIso (E := B.Fiber) f πN).linearEquiv z).injective
      change (pullbackCompIso (E := B.Fiber) f πN).linearEquiv z
        (((pullbackCompIso (E := B.Fiber) f πN).linearEquiv z).symm
          ((pullbackCompIso (E := B.Fiber) πM Φ).linearEquiv z v)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    rw [htop]
    exact ⟨e₀, he₀⟩
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) ((f : N → M) *ᵖ E.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) ((f : N → M) *ᵖ F.Fiber)
  obtain ⟨e, he⟩ := comparison E
  obtain ⟨g, hg⟩ := comparison F
  let A := ellipticSymbolTriple a.val a.property.1.continuous ha
  let B := ellipticSymbolTriple b.val b.property.1.continuous hb
  let C := (A.pullback Φ hp).congr e g
  have hcontrol : C.control = cotangentZeroSet (n := m) (M := N) := by
    ext z
    exact hzero z.proj z.snd
  -- Both triples use the same zero-section control and the same exterior fiber map.
  have hhom : C.Homotopic B := by
    have hC : C.control ⊆ cotangentZeroSet := hcontrol.le
    have hB : B.control ⊆ cotangentZeroSet := Subset.refl _
    refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet, hC, hB, ?_⟩
    have hboundary : (C.enlarge cotangentZeroSet isCompact_cotangentZeroSet hC).boundary =
        (B.enlarge cotangentZeroSet isCompact_cotangentZeroSet hB).boundary := by
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro v
      rw [C.enlarge_apply, B.enlarge_apply]
      rw [CompactSupportTriple.congr_apply, hg]
      have hev : (e.linearEquiv z.val).symm v = v := by
        exact ((he z.val _).symm.trans ((e.linearEquiv z.val).apply_symm_apply v))
      dsimp only [Iso.symm]
      rw [hev]
      let zA : (Φ ⁻¹' A.controlᶜ : Set (CotangentTotalSpace (n := m) (M := N))) :=
        ⟨z.val, fun h ↦ z.property ((hzero z.val.proj z.val.snd).mp h)⟩
      change (A.boundary.pullback Φ).linearEquiv zA v = B.boundary.linearEquiv z v
      rw [RelativeTriple.pullback_apply]
      change (ellipticSymbolBoundary a.val a.property.1.continuous ha).linearEquiv
        ⟨Φ z.val, zA.property⟩ v =
        (ellipticSymbolBoundary b.val b.property.1.continuous hb).linearEquiv z v
      rw [ellipticSymbolBoundary_apply, ellipticSymbolBoundary_apply]
      exact (hab z.val.proj z.val.snd z.property v).symm
    rw [hboundary]
    exact IsoHomotopy.nonempty_refl _
  change B.compactSupportClass = compactSupportKZeroPullback Φ hp A.compactSupportClass
  exact (C.compactSupportClass_eq_of_homotopic B hhom).symm.trans
    (((A.pullback Φ hp).compactSupportClass_congr e g).trans (A.compactSupportClass_pullback Φ hp))

end AtiyahSinger
