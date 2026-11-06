/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Geometry.TangentDualMetric
public import AtiyahSinger.Geometry.ZeroTwistedSpinDirac
public import AtiyahSinger.Topology.SpinTwistedSymbol

/-!
# The original twisted symbol class at the native rank-zero endpoint

Public module ID: M1058.

The operator is the actual zero differential operator between the original
positive and negative associated half-spin bundles tensored with W. Every
tangent direction is zero, so no twisting-connection parameter affects this
operator. The symbol has an empty exterior but retains its original source
minus target bundle class; it is not declared to have zero K class.

Proper pullback along the supplied metric's original flat homeomorphism gives
exactly zeroSpinThomHom applied to the class of the original W. This is the
same native rank-zero extension used by ZeroSpinThom, separate from the
positive-rank twofold spin lift. It neither assumes a two-sheeted Spin(0)
cover nor replaces the original positive associated line by a trivial line.

Sources: the degenerate exterior spinor model of SG I.5, and the explicit
project extension of III.13.10 and Appendix C.12 already recorded for rank
zero. The comparison below keeps the original bundles and the supplied metric map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 40

variable {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)
  (A : SmoothSpinPrincipalAtlas 0 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) projection)
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 0) W)
  (g : SmoothTangentMetric (n := 0) (M := M))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
local notation "TM" => (TangentSpace I : M → Type _)

set_option maxHeartbeats 1500000 in

/-- The actual zero-dimensional twisted Dirac symbol realizes the original zero-spin Thom action. -/
theorem zeroTwistedDiracPlus_symbolClass :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI := B.isFiniteRank
    let H := halfSpinorBundleSmoothAtlas 0 hP A
    let D := zeroTwistedDiracPlus hP A B
    let flat : C(TangentBundle I M, CotangentTotalSpace (n := 0) (M := M)) :=
      ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
    compactSupportKZeroPullback flat g.flatHomeomorph.isProperMap
        (atlasSymbolKClass (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B)
          D.principalSymbol (zeroTwistedDiracPlus_symbol_properties hP A B).1
          (zeroTwistedDiracPlus_symbol_properties hP A B).2) =
      zeroSpinThomHom TM hP (ComplexBundle.kZeroClass W) := by
  /- Stage 1: the raw symbol triple of this actual zero operator retains
  both original twisted bundles and the entire cotangent zero section as
  its compact control. The exterior is empty in dimension zero, so its
  zero boundary imposes no false invertibility or equal-rank condition.
  Stage 2: pull this triple back along the same g.flatHomeomorph. The
  pullback-composition isomorphisms preserve every original tensor vector
  and identify its bundles with zeroTwistedSpinorSymbolTriple TM hP W.
  Their controls are the same entire tangent zero section, and the two
  empty-domain boundaries agree uniquely. This compares the raw triples
  without replacing their positive associated line or their negative zero
  fiber by a new bundle. The i phase would be vacuous on the same exterior.
  Stage 3: apply proper-pullback and original bundle-isomorphism invariance
  of the support class, then zeroTwistedSpinorSymbolTriple_class. Its graph
  action is exactly zeroSpinThomHom on the class of the original W. Every
  tangent direction is zero, so this native endpoint needs no twisting
  connection. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let := B.isFiniteRank
  let H := halfSpinorBundleSmoothAtlas 0 hP A
  let D := zeroTwistedDiracPlus hP A B
  let flat : C(TangentBundle I M, CotangentTotalSpace (n := 0) (M := M)) :=
    ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
  let E₀ := fun x ↦ HalfSpinorBundle 0 hP (0 : ZMod 2) x ⊗[ℂ] W x
  let E₁ := fun x ↦ HalfSpinorBundle 0 hP (1 : ZMod 2) x ⊗[ℂ] W x
  let := (tensorSmoothAtlas (H 0) B).isFiniteRank
  let := (tensorSmoothAtlas (H 1) B).isFiniteRank
  let p := cotangentProjection (n := 0) (M := M)
  let q : C(TangentBundle I M, M) := ⟨π (EuclideanSpace ℝ (Fin 0)) TM,
    FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin 0)) TM⟩
  let := ComplexBundle.isFiniteRank_pullback (E := E₀) p
  let := ComplexBundle.isFiniteRank_pullback (E := E₁) p
  let := ComplexBundle.isFiniteRank_pullback (E := (p : _ → M) *ᵖ E₀) flat
  let := ComplexBundle.isFiniteRank_pullback (E := (p : _ → M) *ᵖ E₁) flat
  let := ComplexBundle.isFiniteRank_pullback (E := E₀) q
  let := ComplexBundle.isFiniteRank_pullback (E := E₁) q
  have hcomp : p.comp flat = q := by
    ext z
    rfl
  -- Reassociate the original cotangent pullbacks along exactly the supplied flat map.
  let e₀ : ComplexBundle.Iso ((flat : _ → _) *ᵖ ((p : _ → M) *ᵖ E₀))
      ((q : _ → M) *ᵖ E₀) := by
    have e := ComplexBundle.pullbackCompIso (E := E₀) p flat
    rw [hcomp] at e
    exact e
  let e₁ : ComplexBundle.Iso ((flat : _ → _) *ᵖ ((p : _ → M) *ᵖ E₁))
      ((q : _ → M) *ᵖ E₁) := by
    have e := ComplexBundle.pullbackCompIso (E := E₁) p flat
    rw [hcomp] at e
    exact e
  let a := atlasEllipticSymbolTriple (tensorSmoothAtlas (H 0) B)
    (tensorSmoothAtlas (H 1) B) D.principalSymbol
    (zeroTwistedDiracPlus_symbol_properties hP A B).1
    (zeroTwistedDiracPlus_symbol_properties hP A B).2
  let b := (a.pullback flat g.flatHomeomorph.isProperMap).congr e₀ e₁
  let c := zeroTwistedSpinorSymbolTriple TM hP W
  -- Both controls are the full original zero section; their exterior is empty.
  have hb : b.control = Set.univ := by
    ext z
    simp only [Set.mem_univ, iff_true]
    change (flat z).snd = 0
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = 0 := by
      exact @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) inferInstance v 0
    rw [hv, map_zero]
    rfl
  have hc : c.control = Set.univ := by
    ext z
    simp only [Set.mem_univ, iff_true]
    change z ∈ Set.range (zeroSection (EuclideanSpace ℝ (Fin 0)) TM)
    exact ⟨z.proj, (zeroRankBundleProjectionHomeomorph TM).symm_apply_apply z⟩
  have htriple : b = c := by
    rcases b with ⟨K, hK, β⟩
    rcases c with ⟨L, hL, γ⟩
    dsimp only at hb hc
    subst K
    subst L
    congr 1
    apply ComplexBundle.Iso.ext
    intro z
    exact False.elim (z.property (Set.mem_univ z.val))
  -- Proper pullback and these same bundle comparisons preserve the original support class.
  change compactSupportKZeroPullback flat g.flatHomeomorph.isProperMap
    a.compactSupportClass = zeroSpinThomHom TM hP (ComplexBundle.kZeroClass W)
  rw [← a.compactSupportClass_pullback flat g.flatHomeomorph.isProperMap]
  calc
    _ = b.compactSupportClass :=
      ((a.pullback flat g.flatHomeomorph.isProperMap).compactSupportClass_congr e₀ e₁).symm
    _ = c.compactSupportClass := congrArg ComplexBundle.CompactSupportTriple.compactSupportClass
      htriple
    _ = _ := zeroTwistedSpinorSymbolTriple_class TM hP W

end AtiyahSinger
