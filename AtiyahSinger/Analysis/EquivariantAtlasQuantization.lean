/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleMapPseudodifferential
public import AtiyahSinger.Analysis.AtlasPseudodifferentialComposition
public import AtiyahSinger.Analysis.EquivariantAtlasBundleMap
public import AtiyahSinger.Analysis.EquivariantQuantization
public import AtiyahSinger.Geometry.SmoothAtlasEquivariantRetract

/-!
# Equivariant quantization on the prescribed smooth bundle atlases

Public module ID: M0467.

Embed each prescribed smooth equivariant atlas as an actual smooth summand
of a native fixed-rank bundle. Extend the full symbol by the same projection
and inclusion, quantize equivariantly in the native bundles, and sandwich
the operator back by the original zero-order maps. Their left inverses
identify the original principal class exactly. This is SG III.3.19 and
III.9, with the variable-rank reduction supplied by smooth complements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option maxHeartbeats 1600000 in
-- Keep the four original retract maps through native quantization and both quotient products.
set_option maxSynthPendingDepth 30 in
/-- An invariant full symbol has an equivariant PDO on the same original atlas section spaces. -/
theorem exists_equivariant_atlasPseudodifferentialOperator_of_fullSymbol
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (hσE : σE.IsSmoothAtlas 𝓘(ℝ, VG) A) (hσF : σF.IsSmoothAtlas 𝓘(ℝ, VG) B)
    (m : ℝ) (a : atlasGlobalSymbolSpace A B m)
    (he : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x) (v : E x),
      a.val (g • x) (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd (σE.linearMap g x v) = σF.linearMap g x (a.val x ξ v)) :
    ∃ P : AtlasPseudodifferentialOperator A B m,
      P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  -- The four smooth maps retain both original atlases and their original group actions.
  obtain ⟨E₀, τE, hτE, iE, pE, hiE, hpE, hieE, hpeE, hpiE⟩ :=
    A.exists_equivariant_native_retract σE hσE
  obtain ⟨F₀, τF, hτF, iF, pF, hiF, hpF, hieF, hpeF, hpiF⟩ :=
    B.exists_equivariant_native_retract σF hσF
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let A₀ := nativeSmoothComplexBundleAtlas (n := n) (r := E₀.rank) E₀.Fiber
  let B₀ := nativeSmoothComplexBundleAtlas (n := n) (r := F₀.rank) F₀.Fiber
  let hτEA := τE.isSmoothAtlas_native 𝓘(ℝ, VG) hτE
  let hτFA := τF.isSmoothAtlas_native 𝓘(ℝ, VG) hτF
  obtain ⟨hgiE, IE, hIE, hIEsymbol⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap A A₀ iE.linearMap hiE
  obtain ⟨hgpE, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap A₀ A pE.linearMap hpE
  obtain ⟨hgiF, _, _, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B B₀ iF.linearMap hiF
  obtain ⟨hgpF, PF, hPF, hPFsymbol⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B₀ B pF.linearMap hpF
  let b : AtlasSymbolFunction (n := n) E₀.Fiber F₀.Fiber := fun x ξ ↦
    (iF.linearMap x).comp ((a.val x ξ).comp (pE.linearMap x))
  have hb : IsAtlasGlobalSymbol A₀ B₀ m b := by
    have h := hgiF.atlasSymbolComp (a.property.atlasSymbolComp hgpE)
    change IsAtlasGlobalSymbol A₀ B₀ (0 + (m + 0)) b at h
    have hm : (0 : ℝ) + (m + 0) = m := by simp only [zero_add, add_zero]
    exact hm ▸ h
  -- The same rectangular full symbol intertwines the native actions at every covector.
  have hbe (g : G) (x : M) (ξ : CotangentFiber (n := n) x) (v : E₀.Fiber x) :
      b (g • x) (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd (τE.linearMap g x v) = τF.linearMap g x (b x ξ v) := by
    change iF.linearMap (g • x) (a.val (g • x) _
      (pE.linearMap (g • x) (τE.linearMap g x v))) = _
    rw [hpeE g x v, he g x ξ (pE.linearMap x v), hieF g x (a.val x ξ (pE.linearMap x v))]
    rfl
  let (x : M) : FiniteDimensional ℂ (E₀.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber x
  let (x : M) : FiniteDimensional ℂ (F₀.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber x
  let q : GlobalSymbolFunction (n := n) E₀.Fiber F₀.Fiber :=
    fun x ξ ↦ (b x ξ).toContinuousLinearMap
  have hq : IsGlobalSymbol (n := n) (r := E₀.rank) (q := F₀.rank) E₀.Fiber F₀.Fiber m q :=
    (isAtlasGlobalSymbol_native_iff m q).mp hb
  let Qs : globalSymbolSpace (n := n) (r := E₀.rank) (q := F₀.rank) E₀.Fiber F₀.Fiber m :=
    ⟨q, hq⟩
  have hqfixed (g : G) : equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) τE τF g q = q := by
    funext x ξ
    ext v
    let transport : ∀ {x y : M}, x = y → F₀.Fiber x →L[ℂ] F₀.Fiber y :=
      fun {x y} h ↦ by
        subst y
        exact ContinuousLinearMap.id ℂ (F₀.Fiber x)
    change transport (smul_inv_smul g x)
      (τF.linearMap g (g⁻¹ • x)
        (b (g⁻¹ • x) (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG)
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm ⟨x, ξ⟩).snd
          (τE.linearMap g⁻¹ x v))) = b x ξ v
    rw [Diffeomorph.smul_symm, hbe g⁻¹ x ξ v]
    have htransport {x y : M} (h : x = y) (w : F₀.Fiber x) :
        (⟨y, transport h w⟩ : TotalSpace Unit F₀.Fiber) = ⟨x, w⟩ := by
      subst y
      rfl
    let : MulAction G (TotalSpace Unit F₀.Fiber) := τF.toMulAction
    apply TotalSpace.mk_injective x
    exact (htransport (smul_inv_smul g x) _).trans
      (smul_inv_smul g (⟨x, b x ξ v⟩ : TotalSpace Unit F₀.Fiber))
  have hclass (g : G) :
      equivariantPrincipalSymbolRepresentation 𝓘(ℝ, VG) τE τF hτE hτF m g
        (globalPrincipalSymbolClass E₀.Fiber F₀.Fiber m Qs) =
          globalPrincipalSymbolClass E₀.Fiber F₀.Fiber m Qs := by
    rw [equivariantPrincipalSymbolRepresentation_class]
    congr 1
    apply Subtype.ext
    exact hqfixed g
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨Q, hQ, hQsymbol⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) 𝓘(ℝ, VG) τE τF hτE hτF m
      (globalPrincipalSymbolClass E₀.Fiber F₀.Fiber m Qs) hclass
  let QA := Q.toAtlasPseudodifferentialOperator
  have hQA : QA.IsEquivariant 𝓘(ℝ, VG) τE τF hτEA hτFA :=
    (Q.isEquivariant_toAtlas_iff 𝓘(ℝ, VG) τE τF hτE hτF).mpr hQ
  have hQAsymbol : QA.principalSymbol = atlasGlobalPrincipalSymbolClass A₀ B₀ m ⟨b, hb⟩ :=
    Q.principalSymbol_toAtlasPseudodifferentialOperator Qs hQsymbol
  have hIEeq (g : G) : IE.toLinearMap.comp
      (σE.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) A hσE g) =
        (τE.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) A₀ hτEA g).comp IE.toLinearMap := by
    rw [hIE]
    exact iE.atlasSmoothSectionMap_intertwines 𝓘(ℝ, VG) A A₀ σE τE hσE hτEA hiE hieE g
  have hPFeq (g : G) : PF.toLinearMap.comp
      (τF.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) B₀ hτFA g) =
        (σF.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) B hσF g).comp PF.toLinearMap := by
    rw [hPF]
    exact pF.atlasSmoothSectionMap_intertwines 𝓘(ℝ, VG) B₀ B τF σF hτFA hσF hpF hpeF g
  -- Both zero-order outer operators use exactly the original retraction maps.
  have hraw : ∃ P : AtlasPseudodifferentialOperator A B (0 + (m + 0)),
      P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B (0 + (m + 0))
          ⟨a.val, by simpa only [zero_add, add_zero] using a.property⟩ := by
    refine ⟨PF.comp (QA.comp IE), ?_, ?_⟩
    · intro g
      apply LinearMap.ext
      intro u
      have h₁ := congrArg (fun L : A.smoothSections →ₗ[ℂ] A₀.smoothSections ↦ L u) (hIEeq g)
      have h₂ := congrArg (fun L : A₀.smoothSections →ₗ[ℂ] B₀.smoothSections ↦
        L (IE.toLinearMap u)) (hQA g)
      have h₃ := congrArg (fun L : B₀.smoothSections →ₗ[ℂ] B.smoothSections ↦
        L (QA.toLinearMap (IE.toLinearMap u))) (hPFeq g)
      dsimp only [LinearMap.comp_apply] at h₁ h₂ h₃
      change QA.toLinearMap ((τE.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) A₀ hτEA g)
        (IE.toLinearMap u)) = (τF.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) B₀ hτFA g)
          (QA.toLinearMap (IE.toLinearMap u)) at h₂
      change PF.toLinearMap (QA.toLinearMap (IE.toLinearMap
        ((σE.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) A hσE g) u))) =
          (σF.atlasSmoothSectionRepresentation 𝓘(ℝ, VG) B hσF g)
            (PF.toLinearMap (QA.toLinearMap (IE.toLinearMap u)))
      rw [h₁, h₂]
      exact h₃
    · rw [AtlasPseudodifferentialOperator.principalSymbol_comp,
        AtlasPseudodifferentialOperator.principalSymbol_comp,
        hPFsymbol, hIEsymbol, hQAsymbol,
        atlasGlobalPrincipalSymbolComp_class, atlasGlobalPrincipalSymbolComp_class]
      congr 1
      apply Subtype.ext
      funext x ξ
      apply LinearMap.ext
      intro v
      change pF.linearMap x (iF.linearMap x
        (a.val x ξ (pE.linearMap x (iE.linearMap x v)))) = a.val x ξ v
      have hE := congrArg (fun L : E x →ₗ[ℂ] E x ↦ L v) (hpiE x)
      have hF := congrArg (fun L : F x →ₗ[ℂ] F x ↦ L (a.val x ξ v)) (hpiF x)
      change pE.linearMap x (iE.linearMap x v) = v at hE
      rw [hE]
      exact hF
  have htransfer (l : ℝ) (hl : l = m) (hm : IsAtlasGlobalSymbol A B l a.val)
      (h : ∃ P : AtlasPseudodifferentialOperator A B l,
        P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
          P.principalSymbol = atlasGlobalPrincipalSymbolClass A B l ⟨a.val, hm⟩) :
      ∃ P : AtlasPseudodifferentialOperator A B m,
        P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
          P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a := by
    subst l
    exact h
  exact htransfer _ (by simp only [zero_add, add_zero]) _ hraw

end AtiyahSinger
