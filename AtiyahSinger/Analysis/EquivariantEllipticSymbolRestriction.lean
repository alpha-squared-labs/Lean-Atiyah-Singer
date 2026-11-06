/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantSmoothIndexRestriction
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex

/-!
# Restriction of the same original elliptic symbol and its full index

Public module ID: M0503.

Precompose both original bundle actions with the given smooth group
homomorphism. The symbol and its bundles remain unchanged. Equality of the
actual base diffeomorphisms compares the native cotangent lifts, while the
same equivariant realization compares the smooth defect representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G VH H : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace VH H]
  [LieGroup 𝓘(ℝ, VH) ∞ H]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
  (φ : H →ₜ* G) (hφ : ContMDiff 𝓘(ℝ, VH) 𝓘(ℝ, VG) ∞ φ)

/-- The original symbol with both bundle actions precomposed by the given smooth homomorphism. -/
def EquivariantEllipticSymbolData.restrict :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    EquivariantEllipticSymbolData (n := n) (M := M) (VG := VH) (G := H) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
  letI := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
  letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
  letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  refine {
    source := a.source
    target := a.target
    sourceAction := a.sourceAction.restrict φ
    targetAction := a.targetAction.restrict φ
    source_smooth := a.sourceAction.restrict_isSmooth 𝓘(ℝ, VG) 𝓘(ℝ, VH) a.source_smooth φ hφ
    target_smooth := a.targetAction.restrict_isSmooth 𝓘(ℝ, VG) 𝓘(ℝ, VH) a.target_smooth φ hφ
    symbol := a.symbol
    elliptic := a.elliptic
    equivariant := ?_ }
  -- The native lift comes from the identical base diffeomorphism, with its same inverse derivative.
  apply (equivariantGlobalSymbolLinearMap_eq_iff
    𝓘(ℝ, VH) (a.sourceAction.restrict φ) (a.targetAction.restrict φ) a.symbol.val).mpr
  intro h x ξ hξ v
  have he : Diffeomorph.smul (M := M) 𝓘(ℝ, VH)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ h =
      Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (φ h) := by
    apply Diffeomorph.ext
    intro y
    rfl
  rw [he]
  exact (equivariantGlobalSymbolLinearMap_eq_iff
    𝓘(ℝ, VG) a.sourceAction a.targetAction a.symbol.val).mp a.equivariant (φ h) x ξ hξ v

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/-- The same original symbol's full index restricts with its unchanged smooth defect carriers. -/
theorem EquivariantEllipticSymbolData.index_restrict :
    letI : MulAction H M := MulAction.compHom M φ.toMonoidHom
    letI : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
    letI : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
      MulAction.contMDiffSMul_compHom hφ
    representationRestriction φ a.index = (a.restrict φ hφ).index := by
  let := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
  let : MulAction H M := MulAction.compHom M φ.toMonoidHom
  let : ContinuousSMul H M := MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ H M :=
    MulAction.contMDiffSMul_compHom hφ
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := a.source.rank) (q := a.target.rank)
    (E := a.source.Fiber) (F := a.target.Fiber)
  let p := R.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2
  have hfixed (g : G) : equivariantPrincipalSymbolRepresentation
      𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0 g
        (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p) =
          globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p :=
    (R.equivariant_regularizedSymbol_class_eq_iff 𝓘(ℝ, VG) a.sourceAction a.targetAction
      a.source_smooth a.target_smooth R 0 a.symbol a.symbol g).mpr (a.equivariant g)
  obtain ⟨P, hPg, hp⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) 𝓘(ℝ, VG) a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
      (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0 p) hfixed
  have hi : P.IsElliptic := (P.isElliptic_iff_homogeneous R a.symbol hp).mpr a.elliptic
  let b := a.restrict φ hφ
  have hPHg : P.IsEquivariant 𝓘(ℝ, VH)
      b.sourceAction b.targetAction b.source_smooth b.target_smooth :=
    P.isEquivariant_restrict 𝓘(ℝ, VG) 𝓘(ℝ, VH) a.source a.target a.sourceAction a.targetAction
      a.source_smooth a.target_smooth hPg φ hφ
  have hG := equivariantHomogeneousAnalyticIndex_eq_smooth 𝓘(ℝ, VG)
    a.sourceAction a.targetAction a.source_smooth a.target_smooth
    a.symbol a.elliptic a.equivariant μ R P hPg hi hp
  have hH := equivariantHomogeneousAnalyticIndex_eq_smooth 𝓘(ℝ, VH)
    b.sourceAction b.targetAction b.source_smooth b.target_smooth
    b.symbol b.elliptic b.equivariant μ R P hPHg hi hp
  change representationRestriction φ a.index = b.index
  change a.index = _ at hG
  change b.index = _ at hH
  rw [hG, hH]
  exact P.smoothEquivariantAnalyticIndex_restrict 𝓘(ℝ, VG) 𝓘(ℝ, VH)
    a.source a.target a.sourceAction a.targetAction a.source_smooth a.target_smooth hPg φ hφ hi

end AtiyahSinger
