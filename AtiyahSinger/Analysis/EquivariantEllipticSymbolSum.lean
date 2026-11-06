/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantSymbolIndexSum
public import AtiyahSinger.Geometry.EquivariantNativeSum
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

/-!
# Simultaneous addition of original equivariant symbol classes and indices

Public module ID: M0504.

The native smooth direct sums retain both specified component actions and
smooth inclusions. Their actual block symbol gives the sum in the original
support-triple group and the sum of full equivariant indices. The same bundle
comparisons prove both equalities; no rank or dimension substitute is used.
This is the direct-sum step of the equivariant clopen index descent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Retain the same six modeled bundles, four inclusions, and actual equivariant support square.
/-- An actual direct-sum symbol adds both original K classes and full indices. -/
theorem EquivariantEllipticSymbolData.exists_add
    (a b : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G)) :
    ∃ c : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G),
      c.kClass = a.kClass + b.kClass ∧ c.index = a.index + b.index := by
  classical
  let IG := 𝓘(ℝ, VG)
  let E₁ := a.source
  let F₁ := a.target
  let E₂ := b.source
  let F₂ := b.target
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₂.rank)) E₂.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₂.rank)) F₂.Fiber
  let := sumTopology (E := E₁.Fiber) (F := E₂.Fiber)
  let := sumTopology (E := F₁.Fiber) (F := F₂.Fiber)
  -- Construct the genuine native sums with their original componentwise actions.
  obtain ⟨E, _, σE, hσE, e, heg, he₁, he₂⟩ :=
    exists_equivariant_native_smooth_sum IG a.sourceAction b.sourceAction
      a.source_smooth b.source_smooth
  obtain ⟨F, _, σF, hσF, f, hfg, hf₁, hf₂⟩ :=
    exists_equivariant_native_smooth_sum IG a.targetAction b.targetAction
      a.target_smooth b.target_smooth
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  have hproj := isSmoothBundleMap_sumInverse e.linearEquiv he₁ he₂
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨α₁, hα₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.fst ℂ (E₁.Fiber x) (E₂.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.1
  obtain ⟨α₂, hα₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (LinearMap.snd ℂ (E₁.Fiber x) (E₂.Fiber x)).comp
      (e.linearEquiv x).symm.toLinearMap) hproj.2
  obtain ⟨β₁, hβ₁, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp
      (LinearMap.inl ℂ (F₁.Fiber x) (F₂.Fiber x))) hf₁
  obtain ⟨β₂, hβ₂, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (f.linearEquiv x).toLinearMap.comp
      (LinearMap.inr ℂ (F₁.Fiber x) (F₂.Fiber x))) hf₂
  let t₁ : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F₁.rank)
      E.Fiber F₁.Fiber 0 :=
    ⟨globalSymbolComp a.symbol.val α₁.val, a.symbol.property.1.globalSymbolComp α₁.property.1,
      by simpa only [zero_add] using a.symbol.property.2.globalSymbolComp α₁.property.2⟩
  let t₂ : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F₂.rank)
      E.Fiber F₂.Fiber 0 :=
    ⟨globalSymbolComp b.symbol.val α₂.val, b.symbol.property.1.globalSymbolComp α₂.property.1,
      by simpa only [zero_add] using b.symbol.property.2.globalSymbolComp α₂.property.2⟩
  let c₁ : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0 :=
    ⟨globalSymbolComp β₁.val t₁.val, β₁.property.1.globalSymbolComp t₁.property.1,
      by simpa only [zero_add] using β₁.property.2.globalSymbolComp t₁.property.2⟩
  let c₂ : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0 :=
    ⟨globalSymbolComp β₂.val t₂.val, β₂.property.1.globalSymbolComp t₂.property.1,
      by simpa only [zero_add] using β₂.property.2.globalSymbolComp t₂.property.2⟩
  let S := c₁ + c₂
  have hvalue (x : M) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x) :
      S.val x ξ v = f.linearEquiv x
        (a.symbol.val x ξ ((e.linearEquiv x).symm v).1,
          b.symbol.val x ξ ((e.linearEquiv x).symm v).2) := by
    change β₁.val x ξ (a.symbol.val x ξ (α₁.val x ξ v)) +
      β₂.val x ξ (b.symbol.val x ξ (α₂.val x ξ v)) = _
    rw [hα₁, hα₂, hβ₁, hβ₂]
    change f.linearEquiv x (_, 0) + f.linearEquiv x (0, _) = _
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hsum (x : M) (ξ : CotangentFiber (n := n) x) (v : E₁.Fiber x) (w : E₂.Fiber x) :
      S.val x ξ (e.linearEquiv x (v, w)) =
        f.linearEquiv x (a.symbol.val x ξ v, b.symbol.val x ξ w) := by
    rw [hvalue, LinearEquiv.symm_apply_apply]
  have hi : IsEllipticGlobalSymbol E.Fiber F.Fiber S.val := by
    intro x ξ hξ
    let L := ((e.linearEquiv x).symm.trans
      ((LinearEquiv.ofBijective (a.symbol.val x ξ).toLinearMap (a.elliptic x ξ hξ)).prodCongr
        (LinearEquiv.ofBijective (b.symbol.val x ξ).toLinearMap (b.elliptic x ξ hξ)))).trans
          (f.linearEquiv x)
    have hmap : ⇑(S.val x ξ) = L := funext (hvalue x ξ)
    rw [hmap]
    exact L.bijective
  -- The same sum comparisons intertwine both moving-fiber actions.
  have heInv (g : G) (x : M) (v : E.Fiber x) :
      (e.linearEquiv (g • x)).symm (σE.linearMap g x v) =
        (a.sourceAction.linearMap g x ((e.linearEquiv x).symm v).1,
          b.sourceAction.linearMap g x ((e.linearEquiv x).symm v).2) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg (σE.linearMap g x) ((e.linearEquiv x).apply_symm_apply v)).symm.trans
      (heg g x ((e.linearEquiv x).symm v)).symm
  have hcov₁ := (equivariantGlobalSymbolLinearMap_eq_iff
    IG a.sourceAction a.targetAction a.symbol.val).mp a.equivariant
  have hcov₂ := (equivariantGlobalSymbolLinearMap_eq_iff
    IG b.sourceAction b.targetAction b.symbol.val).mp b.equivariant
  have hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g S.val x ξ = S.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF S.val).mpr
    intro g x ξ hξ v
    rw [hvalue, heInv, hvalue]
    dsimp only
    rw [hcov₁ g x ξ hξ, hcov₂ g x ξ hξ]
    exact hfg g x (a.symbol.val x ξ ((e.linearEquiv x).symm v).1,
      b.symbol.val x ξ ((e.linearEquiv x).symm v).2)
  let c : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G) := {
    source := E
    target := F
    sourceAction := σE
    targetAction := σF
    source_smooth := hσE
    target_smooth := hσF
    symbol := S
    elliptic := hi
    equivariant := hs }
  refine ⟨c, ?_, ?_⟩
  · let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₂.rank)) E₂.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₂.rank)) F₂.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let πM := cotangentProjection (n := n) (M := M)
    let A := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E₁.Fiber))
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F₁.Fiber))
      (ellipticSymbolTriple a.symbol.val a.symbol.property.1.continuous a.elliptic)
      (a.sourceAction.pullback πM (fun _ _ ↦ rfl))
      (a.targetAction.pullback πM (fun _ _ ↦ rfl))
      (ellipticSymbolTriple_isEquivariant IG a.sourceAction a.targetAction a.symbol.val
        a.symbol.property.1.continuous a.elliptic a.equivariant)
    let B := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E₂.Fiber))
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F₂.Fiber))
      (ellipticSymbolTriple b.symbol.val b.symbol.property.1.continuous b.elliptic)
      (b.sourceAction.pullback πM (fun _ _ ↦ rfl))
      (b.targetAction.pullback πM (fun _ _ ↦ rfl))
      (ellipticSymbolTriple_isEquivariant IG b.sourceAction b.targetAction b.symbol.val
        b.symbol.property.1.continuous b.elliptic b.equivariant)
    let C := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E.Fiber))
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F.Fiber))
      (ellipticSymbolTriple S.val S.property.1.continuous hi)
      (σE.pullback πM (fun _ _ ↦ rfl)) (σF.pullback πM (fun _ _ ↦ rfl))
      (ellipticSymbolTriple_isEquivariant IG σE σF S.val S.property.1.continuous hi hs)
    let jE := ((sumPullbackIso πM (FiniteBundle.ofFamily E₁.Fiber)
      (FiniteBundle.ofFamily E₂.Fiber)).symm).trans (e.pullback πM)
    let jF := ((sumPullbackIso πM (FiniteBundle.ofFamily F₁.Fiber)
      (FiniteBundle.ofFamily F₂.Fiber)).symm).trans (f.pullback πM)
    -- Pull back precisely the two original sum comparisons; their vector maps do not change.
    have hIso : (A.sum B).IsIsomorphic C := by
      refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
        C.2.isEquivariant.invariant_control, ?_, Set.Subset.rfl, jE, jF,
        (fun g z v ↦ heg g z.proj v), (fun g z v ↦ hfg g z.proj v), ?_⟩
      · intro z hz
        exact hz.elim id id
      · intro z v
        simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
        change f.linearEquiv z.val.proj
          (((ellipticSymbolTriple a.symbol.val a.symbol.property.1.continuous a.elliptic).sum
            (ellipticSymbolTriple b.symbol.val b.symbol.property.1.continuous
              b.elliptic)).boundary.linearEquiv
                ⟨z.val, fun hz ↦ z.property (hz.elim id id)⟩ v) =
          (ellipticSymbolTriple S.val S.property.1.continuous hi).boundary.linearEquiv z
            (e.linearEquiv z.val.proj v)
        simp only [CompactSupportTriple.sum, RelativeTriple.sum_apply,
          CompactSupportTriple.enlarge, Iso.restrictTo_apply,
          ellipticSymbolTriple_boundary_apply]
        exact (hsum z.val.proj z.val.snd v.1 v.2).symm
    change C.kZeroClass = A.kZeroClass + B.kZeroClass
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _ hIso).symm.trans
      (equivariantSupportTripleKZero_generator_relations.2.1 A B)
  · exact equivariantHomogeneousAnalyticIndex_eq_add_of_directSum IG
      a.sourceAction a.targetAction b.sourceAction b.targetAction σE σF
      a.source_smooth a.target_smooth b.source_smooth b.target_smooth hσE hσF
      a.symbol a.elliptic a.equivariant b.symbol b.elliptic b.equivariant S hi hs
      e f he₁ he₂ hf₁ hf₂ heg hfg (fun x ξ _ v w ↦ hsum x ξ v w)

end AtiyahSinger
