/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Geometry.TwistedSpinDirac
public import AtiyahSinger.Topology.SpinTwistedSymbol

/-!
# The symbol class of the actual twisted chiral Dirac operator

Public module ID: M1040.

S02. The operator is the original contraction of the Levi-Civita-induced
positive half-spin connection tensored with the specified connection on W.
Its selected principal symbol is smooth and elliptic on the same original
tensor fibers. The resulting support class uses the actual cotangent zero
section and its original exterior map, including the factor +i.

Proper pullback along the supplied tangent metric's flat homeomorphism
identifies that class with the original spin Thom action on [W]. The proof
uses the actual sharp-flat inverse and the explicit i-to-one phase homotopy
on the same zero-section exterior. It does not assume equality with a desired
K class, replace the differential operator by a quantization, or replace W
by its rank. W may have different finite ranks on different components.

Source: Lawson--Michelsohn, Spin Geometry II.5 and III.13.10 with its proof,
pp.256--257. The +i factor is due to the project's D_j=-i partial_j convention.
The class comparison needs compactness of the base; construction and the
principal-symbol properties do not. A unitary twisting connection is a
standard special case, and its compatibility is supplied by TwistedSpinDirac.
The proof retains the original spin structure, metric, chirality, coefficient
bundle and actual differential operator throughout the comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 40

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 2 * m) W) (covW : AtlasComplexConnection B)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

set_option maxHeartbeats 800000 in
-- Normalize the exact symbol of the original contracted twisted Dirac operator.
/-- The selected symbol of the original twisted Dirac operator is smooth and elliptic. -/
theorem twistedDiracPlus_symbol_properties :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    ∀ S : TopologicalSpinStructure m TM o hm hP,
      let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
      let D := S.twistedDiracPlus g B covW
      IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B)
          D.principalSymbol ∧ IsEllipticAtlasSymbol D.principalSymbol := by
  /- Stage 1: retain the exact symbol selected from the actual contracted
  differential operator. twistedDiracPlus_principalSymbol identifies it
  pointwise with +i times tensorAtlasSymbol of the original cotangent
  Clifford map. The latter is smooth in the same half-spin and W tensor
  charts by cotangentCliffordPlus_properties and the smooth-base tensor theorem.
  Multiplication by the fixed complex scalar i preserves these smooth
  coordinate expressions, including the original base and fiber maps.
  Stage 2: a nonzero cotangent vector has nonzero sharp image for the
  same positive metric. The original parity Clifford map is invertible
  there. Tensor its actual inverse with identity on W and multiply by
  i inverse. This gives a two-sided inverse of that selected principal
  symbol, also when W has zero rank. No constant-rank or unitary-connection
  premise is needed for these symbol properties. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  dsimp only
  let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
  let A := tensorSmoothAtlas (H 0) B
  let C := tensorSmoothAtlas (H 1) B
  let c := tensorAtlasSymbol (W := W) (S.cotangentCliffordPlus g)
  have hc := tensorAtlasSymbol_properties_of_isManifold (H 0) (H 1) B
    (S.cotangentCliffordPlus g) (S.isLinearMap_cotangentCliffordPlus g)
    (S.cotangentCliffordPlus_properties g).1
  have hi : IsEllipticAtlasSymbol c := hc.2.2 (S.cotangentCliffordPlus_properties g).2.2.1
  have hsymbol : (S.twistedDiracPlus g B covW).principalSymbol =
      fun x ξ ↦ Complex.I • c x ξ := by
    funext x ξ
    exact S.twistedDiracPlus_principalSymbol g B covW x ξ
  rw [hsymbol]
  constructor
  · intro d hd i j
    have hcoord : atlasGlobalSymbolInChart A C (fun x ξ ↦ Complex.I • c x ξ) d i j =
        fun z η ↦ Complex.I • atlasGlobalSymbolInChart A C c d i j z η := by
      funext z η
      apply ContinuousLinearMap.ext
      intro v
      by_cases h : d.symm z ∈ (A.chart i).baseSet ∧ d.symm z ∈ (C.chart j).baseSet
      · simp [atlasGlobalSymbolInChart, h]
      · simp [atlasGlobalSymbolInChart, h]
    change ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A C (fun x ξ ↦ Complex.I • c x ξ) d i j)) _
    rw [hcoord]
    exact (hc.2.1 d hd i j).const_smul Complex.I
  · intro x ξ hξ
    exact (LinearEquiv.smulOfNeZero ℂ _ Complex.I Complex.I_ne_zero).bijective.comp (hi x ξ hξ)

variable [CompactSpace M]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 3000000 in
-- Normalize the original twisted Dirac symbol class and the same spin Thom coefficient.
/-- The actual twisted Dirac symbol class is the original spin Thom class times the original W. -/
theorem twistedDiracPlus_symbolClass :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := B.isFiniteRank
    ∀ S : TopologicalSpinStructure m TM o hm hP,
      let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
      let D := S.twistedDiracPlus g B covW
      let flat : C(TangentBundle I M, CotangentTotalSpace (n := 2 * m) (M := M)) :=
        ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
      compactSupportKZeroPullback flat g.flatHomeomorph.isProperMap
          (atlasSymbolKClass (tensorSmoothAtlas (H 0) B) (tensorSmoothAtlas (H 1) B)
            D.principalSymbol (S.twistedDiracPlus_symbol_properties g B covW).1
            (S.twistedDiracPlus_symbol_properties g B covW).2) =
        S.spinThomHom (ComplexBundle.kZeroClass W) := by
  /- Stage 1: start from the raw atlasEllipticSymbolTriple of this actual
  D.principalSymbol. Its original source and target are the cotangent
  pullbacks of S+ tensor W and S- tensor W, with the same tensor atlases
  and topologies. Its control is the original cotangent zero section.
  Pull back along precisely g.flatHomeomorph, which is proper as a
  homeomorphism. Its inverse image of that control is the original tangent
  zero section. The original pullback-composition isomorphisms preserve
  each tensor vector and identify the bundles with those of the actual
  S.twistedSpinorSymbolTriple W; no topology equality is silently assumed.
  Stage 2: on that same exterior, twistedDiracPlus_principalSymbol and
  g.sharp_flat_inverse identify the boundary with exactly
  i times (S.cliffordParity(x,v,0) tensor id_W). This is the i-scaled
  boundary of the original twisted spin triple, by its pure-tensor
  specification and linearity. Both comparisons use the same principal
  spin lift, chirality labels, supplied tangent metric and coefficient W.
  Stage 3: SupportTriplePhase supplies the explicit nonvanishing phase
  exp(((1-t)pi/2)i) from i to one on this very exterior. Its single control
  is the original zero section. Therefore compactSupportClass_smul_I
  removes i without exchanging source and target or asserting equality
  of their raw boundary maps. Proper-pullback and bundle-isomorphism
  invariance identify the starting class with this phase-related class.
  Stage 4: twistedSpinorSymbolTriple_class identifies the remaining
  c tensor identity class with exactly S.spinThomHom(kZeroClass W).
  That theorem uses the original proper-graph action, so the original
  tangent projection need not be proper. No assumed target equality,
  substitute operator, global rank or replacement spinor model enters. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := B.isFiniteRank
  intro S
  dsimp only
  let H := halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I)
  let D := S.twistedDiracPlus g B covW
  let flat : C(TangentBundle I M, CotangentTotalSpace (n := 2 * m) (M := M)) :=
    ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
  let E₀ := fun x ↦ HalfSpinorBundle m hP (0 : ZMod 2) x ⊗[ℂ] W x
  let E₁ := fun x ↦ HalfSpinorBundle m hP (1 : ZMod 2) x ⊗[ℂ] W x
  let := (tensorSmoothAtlas (H 0) B).isFiniteRank
  let := (tensorSmoothAtlas (H 1) B).isFiniteRank
  let p := cotangentProjection (n := 2 * m) (M := M)
  let q : C(TangentBundle I M, M) :=
    ⟨π TModel TM, FiberBundle.continuous_proj TModel TM⟩
  let := ComplexBundle.isFiniteRank_pullback (E := E₀) p
  let := ComplexBundle.isFiniteRank_pullback (E := E₁) p
  let := ComplexBundle.isFiniteRank_pullback (E := (p : _ → M) *ᵖ E₀) flat
  let := ComplexBundle.isFiniteRank_pullback (E := (p : _ → M) *ᵖ E₁) flat
  let := ComplexBundle.isFiniteRank_pullback (E := E₀) q
  let := ComplexBundle.isFiniteRank_pullback (E := E₁) q
  -- Reassociate the literal pullbacks; these isomorphisms retain every original vector.
  let e₀ : ComplexBundle.Iso ((flat : _ → _) *ᵖ ((p : _ → M) *ᵖ E₀))
      ((q : _ → M) *ᵖ E₀) := ComplexBundle.pullbackCompIso (E := E₀) p flat
  let e₁ : ComplexBundle.Iso ((flat : _ → _) *ᵖ ((p : _ → M) *ᵖ E₁))
      ((q : _ → M) *ᵖ E₁) := ComplexBundle.pullbackCompIso (E := E₁) p flat
  let a := atlasEllipticSymbolTriple (tensorSmoothAtlas (H 0) B)
    (tensorSmoothAtlas (H 1) B) D.principalSymbol
    (S.twistedDiracPlus_symbol_properties g B covW).1
    (S.twistedDiracPlus_symbol_properties g B covW).2
  let b := (a.pullback flat g.flatHomeomorph.isProperMap).congr e₀ e₁
  let c := (S.twistedSpinorSymbolTriple W).smul Complex.I Complex.I_ne_zero
  -- The metric flat map takes precisely the original tangent zero section to zero.
  have hcontrol : b.control = c.control := by
    ext z
    change g.inner z.proj z.snd = 0 ↔ z ∈ Set.range (zeroSection TModel TM)
    constructor
    · intro hz
      have hv := congrArg (g.sharp z.proj) hz
      rw [(g.sharp_flat_inverse z.proj z.snd 0).1, map_zero] at hv
      refine ⟨z.proj, ?_⟩
      cases z
      simpa only [zeroSection, TotalSpace.mk.injEq, heq_eq_eq, true_and] using hv.symm
    · rintro ⟨x, rfl⟩
      exact map_zero (g.inner x)
  -- Compare the two actual exterior maps on spanning pure tensor vectors.
  have he₀ (y : TangentBundle I M) (v : E₀ y.proj) :
      (e₀.linearEquiv y).symm v = v := by
    apply (e₀.linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (ComplexBundle.pullbackCompIso_apply (E := E₀) p flat y v).symm
  have he₁ (y : TangentBundle I M) (v : E₁ y.proj) :
      e₁.linearEquiv y v = v := ComplexBundle.pullbackCompIso_apply (E := E₁) p flat y v
  have hb (z : (b.controlᶜ : Set (TangentBundle I M)))
      (s : HalfSpinorBundle m hP (0 : ZMod 2) z.val.proj) (w : W z.val.proj) :
      b.boundary.linearEquiv z (s ⊗ₜ[ℂ] w) =
        Complex.I • (S.cliffordParity z.val.proj z.val.snd 0 s ⊗ₜ[ℂ] w) := by
    have hboundary : b.boundary.linearEquiv z (s ⊗ₜ[ℂ] w) =
        a.boundary.linearEquiv ⟨flat z.val, z.property⟩ (s ⊗ₜ[ℂ] w) := by
      calc
        _ = e₁.linearEquiv z.val
            ((a.boundary.pullback flat).linearEquiv z
              ((e₀.linearEquiv z.val).symm (s ⊗ₜ[ℂ] w))) := rfl
        _ = e₁.linearEquiv z.val
            ((a.boundary.pullback flat).linearEquiv z (s ⊗ₜ[ℂ] w)) :=
          congrArg (fun v ↦ e₁.linearEquiv z.val
            ((a.boundary.pullback flat).linearEquiv z v)) (he₀ z.val (s ⊗ₜ[ℂ] w))
        _ = e₁.linearEquiv z.val
            (a.boundary.linearEquiv ⟨flat z.val, z.property⟩ (s ⊗ₜ[ℂ] w)) :=
          congrArg (e₁.linearEquiv z.val)
            (ComplexBundle.RelativeTriple.pullback_apply a.boundary flat z (s ⊗ₜ[ℂ] w))
        _ = _ := he₁ z.val _
    have hsymbol := congrArg (fun L : E₀ z.val.proj →ₗ[ℂ] E₁ z.val.proj ↦
      L (s ⊗ₜ[ℂ] w))
      (S.twistedDiracPlus_principalSymbol g B covW z.val.proj (g.inner z.val.proj z.val.snd))
    refine hboundary.trans (hsymbol.trans ?_)
    change Complex.I •
      (TensorProduct.map (S.cliffordParity z.val.proj
        (g.sharp z.val.proj (g.inner z.val.proj z.val.snd)) 0)
        (LinearMap.id : W z.val.proj →ₗ[ℂ] W z.val.proj) (s ⊗ₜ[ℂ] w)) = _
    exact congrArg (fun v : TM z.val.proj ↦
      (Complex.I • (S.cliffordParity z.val.proj v 0 s ⊗ₜ[ℂ] w) : E₁ z.val.proj))
      (g.sharp_flat_inverse z.val.proj z.val.snd 0).1
  have hc (z : (c.controlᶜ : Set (TangentBundle I M)))
      (s : HalfSpinorBundle m hP (0 : ZMod 2) z.val.proj) (w : W z.val.proj) :
      c.boundary.linearEquiv z (s ⊗ₜ[ℂ] w) =
        Complex.I • (S.cliffordParity z.val.proj z.val.snd 0 s ⊗ₜ[ℂ] w) := by
    change Complex.I • ((S.twistedSpinorSymbolTriple W).boundary.linearEquiv z
      (s ⊗ₜ[ℂ] w) : E₁ z.val.proj) = _
    rw [(S.twistedSpinorSymbolTriple_properties W).2]
  -- Equal controls and equal exterior maps on pure tensors identify the two support triples.
  have tripleExt (u v : ComplexBundle.CompactSupportTriple
      ((q : _ → M) *ᵖ E₀) ((q : _ → M) *ᵖ E₁))
      (hK : u.control = v.control)
      (hvalue : ∀ (x : TangentBundle I M) (hu : x ∉ u.control) (hv : x ∉ v.control)
        (s : HalfSpinorBundle m hP (0 : ZMod 2) x.proj) (w : W x.proj),
        u.boundary.linearEquiv ⟨x, hu⟩ (s ⊗ₜ[ℂ] w) =
          v.boundary.linearEquiv ⟨x, hv⟩ (s ⊗ₜ[ℂ] w)) : u = v := by
    rcases u with ⟨K, hKc, β⟩
    rcases v with ⟨L, hLc, γ⟩
    dsimp only at hK hvalue
    subst L
    congr 1
    apply ComplexBundle.Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul s w => exact hvalue z.val z.property z.property s w
    | add v w hv hw => simpa only [map_add] using congrArg₂ HAdd.hAdd hv hw
  have htriple : b = c := tripleExt b c hcontrol (fun x hx hy s w ↦
    (hb ⟨x, hx⟩ s w).trans (hc ⟨x, hy⟩ s w).symm)
  -- Proper pullback and the explicit i-to-one phase preserve the same support class.
  change compactSupportKZeroPullback flat g.flatHomeomorph.isProperMap
    a.compactSupportClass = S.spinThomHom (ComplexBundle.kZeroClass W)
  rw [← a.compactSupportClass_pullback flat g.flatHomeomorph.isProperMap]
  calc
    _ = b.compactSupportClass :=
      ((a.pullback flat g.flatHomeomorph.isProperMap).compactSupportClass_congr e₀ e₁).symm
    _ = c.compactSupportClass :=
      congrArg ComplexBundle.CompactSupportTriple.compactSupportClass htriple
    _ = (S.twistedSpinorSymbolTriple W).compactSupportClass :=
      (S.twistedSpinorSymbolTriple W).compactSupportClass_smul_I
    _ = _ := S.twistedSpinorSymbolTriple_class W

end TopologicalSpinStructure

end AtiyahSinger
