/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Analysis.EquivariantSymbolIndexOperations
public import AtiyahSinger.Analysis.EquivariantSymbolIndexSum
public import AtiyahSinger.Geometry.EquivariantNativeSum

/-!
# Smooth equivariant stabilization of the original homogeneous symbol

Public module ID: M0602.

Adding the identity of a specified smooth equivariant bundle produces a symbol
on compatible native smooth sums. The same two sum comparisons specify its
fiber maps and show that its full equivariant analytic index is unchanged.
This is the elementary stabilization used in the index descent of SG III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option maxHeartbeats 800000 in
-- The original symbol and its identity summand retain all four specified sum maps.
/-- Adding the identity of the supplied smooth equivariant bundle preserves the full index. -/
theorem exists_equivariant_homogeneous_stabilization
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (hσE : σE.IsSmooth (n := n) (r := r) IG)
    (hσF : σF.IsSmooth (n := n) (r := q) IG)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (C : SmoothFiniteComplexBundle (n := n) M)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
      EquivariantStructure G C.Fiber)
    (hτ : τ.IsSmooth (n := n) (r := C.rank) IG) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
    letI := sumTopology (E := E) (F := C.Fiber)
    letI := sumTopology (E := F) (F := C.Fiber)
    ∃ A B : SmoothFiniteComplexBundle (n := n) M,
      letI := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
      ∃ (σA : EquivariantStructure G A.Fiber) (σB : EquivariantStructure G B.Fiber),
      ∃ (hσA : σA.IsSmooth (n := n) (r := A.rank) IG)
        (hσB : σB.IsSmooth (n := n) (r := B.rank) IG),
      ∃ (e : Iso (E ×ᵇ C.Fiber) A.Fiber) (f : Iso (F ×ᵇ C.Fiber) B.Fiber),
        e.IsEquivariant (σE.sum τ) σA ∧ f.IsEquivariant (σF.sum τ) σB ∧
        ∃ S : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank)
            A.Fiber B.Fiber 0,
        ∃ hSi : IsEllipticGlobalSymbol A.Fiber B.Fiber S.val,
        ∃ hSg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
            equivariantGlobalSymbolLinearMap IG σA σB g S.val x ξ = S.val x ξ,
          (∀ (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) (w : C.Fiber x),
            S.val x ξ (e.linearEquiv x (v, w)) = f.linearEquiv x (s.val x ξ v, w)) ∧
          equivariantHomogeneousAnalyticIndex IG σA σB hσA hσB S hSi hSg =
            equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
  let := sumTopology (E := E) (F := C.Fiber)
  let := sumTopology (E := F) (F := C.Fiber)
  -- Each native sum keeps the supplied stabilizer and the original componentwise action.
  obtain ⟨A, _, σA, hσA, e, heg, he₁, he₂⟩ :=
    exists_equivariant_native_smooth_sum IG σE τ hσE hτ
  obtain ⟨B, _, σB, hσB, f, hfg, hf₁, hf₂⟩ :=
    exists_equivariant_native_smooth_sum IG σF τ hσF hτ
  let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
  have hproj := isSmoothBundleMap_sumInverse e.linearEquiv he₁ he₂
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨α₁, hα₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.fst ℂ (E x) (C.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.1
  obtain ⟨α₂, hα₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.snd ℂ (E x) (C.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.2
  obtain ⟨β₁, hβ₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inl ℂ (F x) (C.Fiber x))) hf₁
  obtain ⟨β₂, hβ₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp (LinearMap.inr ℂ (F x) (C.Fiber x))) hf₂
  let t₁ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := q) A.Fiber F 0 :=
    ⟨globalSymbolComp s.val α₁.val, s.property.1.globalSymbolComp α₁.property.1,
      by simpa only [zero_add] using s.property.2.globalSymbolComp α₁.property.2⟩
  let c₁ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank)
      A.Fiber B.Fiber 0 :=
    ⟨globalSymbolComp β₁.val t₁.val, β₁.property.1.globalSymbolComp t₁.property.1,
      by simpa only [zero_add] using β₁.property.2.globalSymbolComp t₁.property.2⟩
  let c₂ : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank)
      A.Fiber B.Fiber 0 :=
    ⟨globalSymbolComp β₂.val α₂.val, β₂.property.1.globalSymbolComp α₂.property.1,
      by simpa only [zero_add] using β₂.property.2.globalSymbolComp α₂.property.2⟩
  let S := c₁ + c₂
  have hvalue (x : M) (ξ : CotangentFiber (n := n) x) (v : A.Fiber x) :
      S.val x ξ v = f.linearEquiv x
        (s.val x ξ ((e.linearEquiv x).symm v).1, ((e.linearEquiv x).symm v).2) := by
    change β₁.val x ξ (s.val x ξ (α₁.val x ξ v)) + β₂.val x ξ (α₂.val x ξ v) = _
    rw [hα₁, hα₂, hβ₁, hβ₂]
    change f.linearEquiv x (_, 0) + f.linearEquiv x (0, _) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hsum (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) (w : C.Fiber x) :
      S.val x ξ (e.linearEquiv x (v, w)) = f.linearEquiv x (s.val x ξ v, w) := by
    rw [hvalue, LinearEquiv.symm_apply_apply]
  have hSi : IsEllipticGlobalSymbol A.Fiber B.Fiber S.val := by
    intro x ξ hξ
    let L := ((e.linearEquiv x).symm.trans
      ((LinearEquiv.ofBijective (s.val x ξ).toLinearMap (hi x ξ hξ)).prodCongr
        (LinearEquiv.refl ℂ (C.Fiber x)))).trans (f.linearEquiv x)
    have hmap : ⇑(S.val x ξ) = L := funext (hvalue x ξ)
    rw [hmap]
    exact L.bijective
  -- The same sum comparison identifies the inverse moving action before applying the symbol.
  have heInv (g : G) (x : M) (v : A.Fiber x) :
      (e.linearEquiv (g • x)).symm (σA.linearMap g x v) =
        (σE.linearMap g x ((e.linearEquiv x).symm v).1,
          τ.linearMap g x ((e.linearEquiv x).symm v).2) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (σA.linearMap g x) ((e.linearEquiv x).apply_symm_apply v)).symm.trans
      (heg g x ((e.linearEquiv x).symm v)).symm
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF s.val).mp hs
  have hSg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σA σB g S.val x ξ = S.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σA σB S.val).mpr
    intro g x ξ hξ v
    rw [hvalue, heInv, hvalue]
    dsimp only
    rw [hcov g x ξ hξ]
    exact hfg g x (s.val x ξ ((e.linearEquiv x).symm v).1, ((e.linearEquiv x).symm v).2)
  -- The identity is smooth in the original stabilizer charts and has zero full index.
  have hId : IsSmoothBundleMap (n := n) (r := C.rank) (q := C.rank)
      (fun x ↦ LinearMap.id (R := ℂ) (M := C.Fiber x)) := by
    intro d hd k hk j
    have h := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := C.Fiber) d k
    have hv : ContDiff ℝ ∞
        (fun L : EuclideanSpace ℂ (Fin C.rank) →L[ℂ] EuclideanSpace ℂ (Fin C.rank) ↦
          L (EuclideanSpace.single j 1)) :=
      (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
    apply (hv.contMDiff.comp_contMDiffOn h).congr
    intro x hx
    change (k ⟨x, d.symmL ℂ x (EuclideanSpace.single j 1)⟩).2 =
      d.coordChangeL ℂ k x (EuclideanSpace.single j 1)
    rw [d.symmL_apply hx.1]
    exact (d.coordChangeL_apply k hx (EuclideanSpace.single j 1)).symm
  obtain ⟨sC, hsC, _⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) (fun _ ↦ LinearMap.id) hId
  have hiC : IsEllipticGlobalSymbol C.Fiber C.Fiber sC.val := by
    intro x ξ _
    have hc : ⇑(sC.val x ξ) = id := funext (hsC x ξ)
    rw [hc]
    exact Function.bijective_id
  have hgC : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG τ τ g sC.val x ξ = sC.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG τ τ sC.val).mpr
    intro g x ξ _ v
    rw [hsC, hsC]
    rfl
  have hzero := equivariantHomogeneousAnalyticIndex_eq_zero_of_bundleIso IG τ τ hτ hτ
    (Iso.refl C.Fiber) hId (fun _ _ _ ↦ rfl) sC hiC hgC (fun x ξ _ v ↦ hsC x ξ v)
  have hadd := equivariantHomogeneousAnalyticIndex_eq_add_of_directSum IG
    σE σF τ τ σA σB hσE hσF hτ hτ hσA hσB s hi hs sC hiC hgC S hSi hSg
    e f he₁ he₂ hf₁ hf₂ heg hfg (by
      intro x ξ _ v w
      rw [hsC]
      exact hsum x ξ v w)
  exact ⟨A, B, σA, σB, hσA, hσB, e, f, heg, hfg, S, hSi, hSg, hsum,
    by simpa only [hzero, add_zero] using hadd⟩

end AtiyahSinger
