/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFullSymbolSupport
public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct
public import AtiyahSinger.Topology.EquivariantHermitianProductRealization

/-!
# The original product class represented by full Hermitian symbol tails

Public module ID: M0513.

The same invariant full symbols and their actual adjoints realize the original
independent-group external product on the original cotangent pullback bundles.
The compact controls are the prescribed metric disks; no replacement factor
class or tensor action is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 50
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {VG VH G H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [IsManifold 𝓘(ℝ, VG) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [IsManifold 𝓘(ℝ, VH) ∞ H]
  {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [MulAction G M] [ContinuousSMul G M] [MulAction H N] [ContinuousSMul H N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]
  (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)
  (σ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    EquivariantStructure G E₀.Fiber)
  (σ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    EquivariantStructure G E₁.Fiber)
  (τ₀ : letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    EquivariantStructure H F₀.Fiber)
  (τ₁ : letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    EquivariantStructure H F₁.Fiber)


variable [CompactSpace G] [CompactSpace H]
  [T2Space M] [CompactSpace M] [T2Space N] [CompactSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum

set_option maxHeartbeats 12000000 in
-- Keep the complete native tensor and restricted-action instances in the original product class.
/-- The full Hermitian exterior realizes the original independent-group factor classes. -/
theorem exists_equivariantFullSymbolProduct_of_tail
    (p₀ : homogeneousGlobalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank)
      E₀.Fiber E₁.Fiber 1)
    (q₀ : homogeneousGlobalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank)
      F₀.Fiber F₁.Fiber 1)
    (hp₀ : IsEllipticGlobalSymbol E₀.Fiber E₁.Fiber p₀.val)
    (hq₀ : IsEllipticGlobalSymbol F₀.Fiber F₁.Fiber q₀.val)
    (hp₀Eq : ∀ (z : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ z p₀.val x ξ = p₀.val x ξ)
    (hq₀Eq : ∀ (z : H) (x : N) (ξ : CotangentFiber (n := m) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ z q₀.val x ξ = q₀.val x ξ)
    (p : globalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (pi : globalSymbolSpace (n := n) (r := E₁.rank) (q := E₀.rank) E₁.Fiber E₀.Fiber 1)
    (q : globalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (qi : globalSymbolSpace (n := m) (r := F₁.rank) (q := F₀.rank) F₁.Fiber F₀.Fiber 1)
    (hp : ∀ z : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₀ σ₁ z p.val = p.val)
    (hpi : ∀ z : G, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σ₁ σ₀ z pi.val = pi.val)
    (hq : ∀ z : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₀ τ₁ z q.val = q.val)
    (hqi : ∀ z : H, equivariantGlobalSymbolLinearMap 𝓘(ℝ, VH) τ₁ τ₀ z qi.val = qi.val)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (gInv : ∀ (a : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := M)
        𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ a) ⟨x, ξ⟩).snd = g.length x ξ)
    (kInv : ∀ (a : H) (x : N) (ξ : CotangentFiber (n := m) x),
      k.length (a • x) (cotangentDiffeomorphMap (Diffeomorph.smul (M := N)
        𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ a) ⟨x, ξ⟩).snd = k.length x ξ)
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hpTail : ∀ x ξ, R₁ ≤ g.length x ξ → p.val x ξ = p₀.val x ξ)
    (hqTail : ∀ x ξ, R₂ ≤ k.length x ξ → q.val x ξ = q₀.val x ξ)
    (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
    (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
    (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
    (hpAdj : ∀ x ξ u v, h₁.pairing x (p.val x ξ u) v = h₀.pairing x u (pi.val x ξ v))
    (hqAdj : ∀ x ξ u v, k₁.pairing x (q.val x ξ u) v = k₀.pairing x u (qi.val x ξ v)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
    letI : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
    letI : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    let pM := cotangentProjection (n := n) (M := M)
    let pN := cotangentProjection (n := m) (M := N)
    let A₀ := FiniteBundle.ofFamily (pM *ᵖ E₀.Fiber)
    let A₁ := FiniteBundle.ofFamily (pM *ᵖ E₁.Fiber)
    let B₀ := FiniteBundle.ofFamily (pN *ᵖ F₀.Fiber)
    let B₁ := FiniteBundle.ofFamily (pN *ᵖ F₁.Fiber)
    let fM : C(CotangentTotalSpace (n := n) (M := M) ×
        CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := n) (M := M)) :=
      ContinuousMap.fst
    let fN : C(CotangentTotalSpace (n := n) (M := M) ×
        CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := m) (M := N)) :=
      ContinuousMap.snd
    letI := ((A₀.pullback fM).tensor (B₀.pullback fN)).totalTopology
    letI := ((A₁.pullback fM).tensor (B₁.pullback fN)).totalTopology
    letI := ((A₁.pullback fM).tensor (B₀.pullback fN)).totalTopology
    letI := ((A₀.pullback fM).tensor (B₁.pullback fN)).totalTopology
    let S := ((A₀.pullback fM).tensor (B₀.pullback fN)).sum
      ((A₁.pullback fM).tensor (B₁.pullback fN))
    let T := ((A₁.pullback fM).tensor (B₀.pullback fN)).sum
      ((A₀.pullback fM).tensor (B₁.pullback fN))
    letI := S.totalTopology
    letI := T.totalTopology
    let ρ₀ := (σ₀.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
    let ρ₁ := (σ₁.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
    let κ₀ := (τ₀.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
    let κ₁ := (τ₁.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
    let ρS := ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor
      (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
        ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
    let ρT := ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor
      (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
        ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
    ∃ d : CompactSupportTriple S.Fiber T.Fiber,
      d.control = {z | g.length z.proj z.snd ≤ R₁} ×ˢ
        {z | k.length z.proj z.snd ≤ R₂} ∧
      ∃ hd : d.IsEquivariant ρS ρT,
        (∀ z : (d.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M) ×
            CotangentTotalSpace (n := m) (M := N))),
          (d.boundary.linearEquiv z).toLinearMap = reciprocalTensorSymbol
            (p.val z.val.1.proj z.val.1.snd).toLinearMap
            (pi.val z.val.1.proj z.val.1.snd).toLinearMap
            (q.val z.val.2.proj z.val.2.snd).toLinearMap
            (qi.val z.val.2.proj z.val.2.snd).toLinearMap) ∧
        (EquivariantSupportBundleTriple.ofBoundary S T d ρS ρT hd).kZeroClass =
          equivariantSupportKZeroDifferentGroupExternalProduct
            (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σ₀ σ₁ 1 p₀ hp₀ hp₀Eq)
            (equivariantHomogeneousSymbolKClass 𝓘(ℝ, VH) τ₀ τ₁ 1 q₀ hq₀ hq₀Eq) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let := contMDiffSMul_smoothCotangent (n := m) (G := H) (M := N) 𝓘(ℝ, VH)
  let : ContinuousSMul H (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VH))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  let : MulAction (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let pM := cotangentProjection (n := n) (M := M)
  let pN := cotangentProjection (n := m) (M := N)
  let A₀ := FiniteBundle.ofFamily (pM *ᵖ E₀.Fiber)
  let A₁ := FiniteBundle.ofFamily (pM *ᵖ E₁.Fiber)
  let B₀ := FiniteBundle.ofFamily (pN *ᵖ F₀.Fiber)
  let B₁ := FiniteBundle.ofFamily (pN *ᵖ F₁.Fiber)
  let fM : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := n) (M := M)) :=
    ContinuousMap.fst
  let fN : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := m) (M := N)) :=
    ContinuousMap.snd
  let := ((A₀.pullback fM).tensor (B₀.pullback fN)).totalTopology
  let := ((A₁.pullback fM).tensor (B₁.pullback fN)).totalTopology
  let := ((A₁.pullback fM).tensor (B₀.pullback fN)).totalTopology
  let := ((A₀.pullback fM).tensor (B₁.pullback fN)).totalTopology
  let S := ((A₀.pullback fM).tensor (B₀.pullback fN)).sum
    ((A₁.pullback fM).tensor (B₁.pullback fN))
  let T := ((A₁.pullback fM).tensor (B₀.pullback fN)).sum
    ((A₀.pullback fM).tensor (B₁.pullback fN))
  let := S.totalTopology
  let := T.totalTopology
  let ρ₀ := (σ₀.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let ρ₁ := (σ₁.pullback pM (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.fst G H)
  let κ₀ := (τ₀.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let κ₁ := (τ₁.pullback pN (fun _ _ ↦ rfl)).restrict (ContinuousMonoidHom.snd G H)
  let ρS := ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor
    (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
      ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
  let ρT := ((ρ₁.pullback fM (fun _ _ ↦ rfl)).tensor
    (κ₀.pullback fN (fun _ _ ↦ rfl))).sum
      ((ρ₀.pullback fM (fun _ _ ↦ rfl)).tensor (κ₁.pullback fN (fun _ _ ↦ rfl)))
  -- The two specified full tails represent the original homogeneous factor classes.
  obtain ⟨a, haControl, ha, haFormula, haClass⟩ :=
    exists_equivariantFullSymbolSupport_of_tail 𝓘(ℝ, VG) σ₀ σ₁
      1 p₀ hp₀ hp₀Eq g gInv R₁ hR₁ p hpTail
  obtain ⟨b, hbControl, hb, hbFormula, hbClass⟩ :=
    exists_equivariantFullSymbolSupport_of_tail 𝓘(ℝ, VH) τ₀ τ₁
      1 q₀ hq₀ hq₀Eq k kInv R₂ hR₂ q hqTail
  let A := EquivariantSupportBundleTriple.ofBoundary A₀ A₁ a
    (σ₀.pullback pM (fun _ _ ↦ rfl)) (σ₁.pullback pM (fun _ _ ↦ rfl)) ha
  let B := EquivariantSupportBundleTriple.ofBoundary B₀ B₁ b
    (τ₀.pullback pN (fun _ _ ↦ rfl)) (τ₁.pullback pN (fun _ _ ↦ rfl)) hb
  let A' := A.restrict (ContinuousMonoidHom.fst G H)
  let B' := B.restrict (ContinuousMonoidHom.snd G H)
  have hpg := fullSymbolBundleHom_isEquivariant 𝓘(ℝ, VG) σ₀ σ₁ p hp
  have hpig := fullSymbolBundleHom_isEquivariant 𝓘(ℝ, VG) σ₁ σ₀ pi hpi
  have hqg := fullSymbolBundleHom_isEquivariant 𝓘(ℝ, VH) τ₀ τ₁ q hq
  have hqig := fullSymbolBundleHom_isEquivariant 𝓘(ℝ, VH) τ₁ τ₀ qi hqi
  -- Restriction changes only the acting group; the full maps and their adjoints are unchanged.
  obtain ⟨d, hdControl, hd, hdFormula, hdClass⟩ :=
    exists_equivariantHermitianSupportProduct A' B'
      (fun z ↦ h₀.toCore z.proj) (fun z ↦ h₁.toCore z.proj)
      (fun z ↦ k₀.toCore z.proj) (fun z ↦ k₁.toCore z.proj)
      (fullSymbolBundleHom p) (fullSymbolBundleHom pi)
      (fullSymbolBundleHom q) (fullSymbolBundleHom qi)
      (fun z ↦ hpAdj z.proj z.snd) (fun z ↦ hqAdj z.proj z.snd)
      (fun z ↦ hpg z.1) (fun z ↦ hpig z.1)
      (fun z ↦ hqg z.2) (fun z ↦ hqig z.2) haFormula hbFormula
  refine ⟨d, hdControl.trans ?_, hd, hdFormula, ?_⟩
  · change a.control ×ˢ b.control = _
    rw [haControl, hbControl]
  · apply hdClass.trans
    change equivariantSupportKZeroExternalProduct A'.kZeroClass B'.kZeroClass = _
    rw [← equivariantSupportTripleKZeroRestrict_apply,
      ← equivariantSupportTripleKZeroRestrict_apply]
    change equivariantSupportKZeroDifferentGroupExternalProduct A.kZeroClass B.kZeroClass = _
    rw [haClass, hbClass]

end AtiyahSinger
