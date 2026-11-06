/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClopenDiagonalOperator
public import AtiyahSinger.Analysis.ClopenPseudodifferential
public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbolPullback
public import AtiyahSinger.Analysis.EquivariantSectionPullback
public import AtiyahSinger.Analysis.EquivariantSmoothIndexFiniteSum
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex
public import AtiyahSinger.Geometry.ClopenSmoothSections
public import AtiyahSinger.Topology.EquivariantCotangentClopen

/-!
# Full equivariant index under actual finite clopen restriction

Public module ID: M0485.

An actual equivariant realization supplies its native restricted operators.
Restriction and zero extension intertwine the specified actions, and the
same-symbol diagonal realization has their finite product of section maps.
Its full kernel and quotient-cokernel representation classes add. The original
proper cotangent pullback identifies the classes of these very same symbols.
This proves the invariant clopen assembly step without assuming connectedness,
nonempty pieces, invariant connected components, or a global rank for arbitrary
K classes. It is the finite equivariant supplement to SG III.13, pp.246--247.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
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
  (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
  {k : ℕ} (U : Fin k → Opens M)
  [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
  [∀ i, ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i)]
  [∀ i, CompactSpace (U i)]
  (hclosed : ∀ i, IsClosed (U i : Set M))
  (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
  (hcover : (⋃ i, (U i : Set M)) = Set.univ)
  (heq : ∀ (i : Fin k) (g : G) (x : U i), ((g • x : U i) : M) = g • (x : M))

attribute [local instance] isSmoothPositiveMeasure_comap_opens

include hdisjoint hcover

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Retain the native pullback instances throughout the actual operator and symbol comparison.
/-- Actual invariant clopen restrictions have the original K restrictions and sum index. -/
theorem EquivariantEllipticSymbolData.exists_clopen_decomposition :
    ∃ b : ∀ i, EquivariantEllipticSymbolData (n := n) (M := U i) (VG := VG) (G := G),
      (∀ i, (b i).kClass =
        equivariantCotangentClopenRestrict 𝓘(ℝ, VG) U hclosed heq a.kClass i) ∧
      a.index = ∑ i, (b i).index := by
  classical
  let E := a.source
  let F := a.target
  let IG := 𝓘(ℝ, VG)
  let f (i : Fin k) : C(U i, M) := ContinuousMap.subtypeVal (U i : Set M)
  let : ∀ i, IsSmoothComplexBundle (n := n) (r := E.rank)
      ((f i : U i → M) *ᵖ a.source.Fiber) := fun i ↦
    isSmoothComplexBundle_pullback a.source.Fiber (f i) contMDiff_subtype_val
  let : ∀ i, IsSmoothComplexBundle (n := n) (r := F.rank)
      ((f i : U i → M) *ᵖ a.target.Fiber) := fun i ↦
    isSmoothComplexBundle_pullback a.target.Fiber (f i) contMDiff_subtype_val
  let τE (i : Fin k) := a.sourceAction.modelPullback (f i) (heq i)
  let τF (i : Fin k) := a.targetAction.modelPullback (f i) (heq i)
  have hτE (i : Fin k) : (τE i).IsSmooth (n := n) (r := E.rank) IG :=
    a.sourceAction.modelPullback_isSmooth IG a.source_smooth (f i) (heq i)
      contMDiff_subtype_val
  have hτF (i : Fin k) : (τF i).IsSmooth (n := n) (r := F.rank) IG :=
    a.targetAction.modelPullback_isSmooth IG a.target_smooth (f i) (heq i)
      contMDiff_subtype_val
  -- Realize precisely the supplied homogeneous symbol with its specified bundle actions.
  obtain ⟨μ, hμ, _⟩ := exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  let p := R.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2
  have hfixed (g : G) : equivariantPrincipalSymbolRepresentation
      IG a.sourceAction a.targetAction a.source_smooth a.target_smooth 0 g
        (globalPrincipalSymbolClass E.Fiber F.Fiber 0 p) =
          globalPrincipalSymbolClass E.Fiber F.Fiber 0 p :=
    (R.equivariant_regularizedSymbol_class_eq_iff IG a.sourceAction a.targetAction
      a.source_smooth a.target_smooth R 0 a.symbol a.symbol g).mpr (a.equivariant g)
  obtain ⟨P, hPg, hp⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
      (globalPrincipalSymbolClass E.Fiber F.Fiber 0 p) hfixed
  have hi : P.IsElliptic := ⟨p, hp,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 a.symbol.val
      a.symbol.property.1 a.symbol.property.2).mpr a.elliptic⟩
  choose PU RU aU hpU hiU haU haction using fun i ↦
    PseudodifferentialOperator.exists_clopen_restriction
      μ E F P R a.symbol hp hi (U i) (hclosed i)
  let Z (i : Fin k)
      (u : smoothSections (n := n) (r := E.rank) (E.restrictOpen (U i)).Fiber) :
      smoothSections (n := n) (r := E.rank) E.Fiber :=
    smoothSectionZeroExtension E.Fiber (U i) (U i : Set M) (hclosed i) Set.Subset.rfl
      ⟨u, fun y hy ↦ False.elim (hy y.property)⟩
  have hact (i : Fin k) (u : smoothSections (n := n) (r := E.rank)
      (E.restrictOpen (U i)).Fiber) :
      (PU i).toLinearMap u = smoothSectionRestriction F.Fiber (U i) (P.toLinearMap (Z i u)) :=
    Subtype.ext (funext (haction i u))
  have hresE (i : Fin k) (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      smoothSectionRestriction E.Fiber (U i)
        (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g u) =
      (τE i).smoothSectionRepresentation IG (hτE i) g
        (smoothSectionRestriction E.Fiber (U i) u) :=
    a.sourceAction.smoothSectionPullback_intertwines
      IG a.source_smooth (f i) (heq i) contMDiff_subtype_val g u
  have hresF (i : Fin k) (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      smoothSectionRestriction F.Fiber (U i)
        (a.targetAction.smoothSectionRepresentation IG a.target_smooth g v) =
      (τF i).smoothSectionRepresentation IG (hτF i) g
        (smoothSectionRestriction F.Fiber (U i) v) :=
    a.targetAction.smoothSectionPullback_intertwines
      IG a.target_smooth (f i) (heq i) contMDiff_subtype_val g v
  have hZ (i : Fin k) (g : G) (u : smoothSections (n := n) (r := E.rank)
      (E.restrictOpen (U i)).Fiber) :
      Z i ((τE i).smoothSectionRepresentation IG (hτE i) g u) =
        a.sourceAction.smoothSectionRepresentation IG a.source_smooth g (Z i u) :=
    a.sourceAction.smoothSectionZeroExtension_intertwines
      IG a.source_smooth (U i) (hclosed i) (heq i) g u
  -- Each actual block intertwines by the restriction-P-zero-extension square.
  have hPUg (i : Fin k) : (PU i).IsEquivariant IG (τE i) (τF i) (hτE i) (hτF i) := by
    intro g
    apply LinearMap.ext
    intro u
    change (PU i).toLinearMap ((τE i).smoothSectionRepresentation IG (hτE i) g u) =
      (τF i).smoothSectionRepresentation IG (hτF i) g ((PU i).toLinearMap u)
    rw [hact, hZ, hact]
    have h := congrArg (fun L ↦ L (Z i u)) (hPg g)
    change P.toLinearMap (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g
      (Z i u)) = a.targetAction.smoothSectionRepresentation IG a.target_smooth g
        (P.toLinearMap (Z i u)) at h
    rw [h, hresF]
  have hell (i : Fin k) : IsEllipticGlobalSymbol
      (E.restrictOpen (U i)).Fiber (F.restrictOpen (U i)).Fiber (aU i).val := by
    intro x ξ hξ
    rw [haU]
    exact a.elliptic x.val ξ hξ
  have hequiv (i : Fin k) (g : G) : ∀ (x : U i) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG (τE i) (τF i) g (aU i).val x ξ = (aU i).val x ξ := by
    have h := (PU i).equivariant_principalSymbol IG (τE i) (τF i) (hτE i) (hτF i) (hPUg i) g
    rw [hpU] at h
    exact ((RU i).equivariant_regularizedSymbol_class_eq_iff
      IG (τE i) (τF i) (hτE i) (hτF i) (RU i) 0 (aU i) (aU i) g).mp h
  let b (i : Fin k) : EquivariantEllipticSymbolData (n := n) (M := U i)
      (VG := VG) (G := G) := {
    source := E.restrictOpen (U i)
    target := F.restrictOpen (U i)
    sourceAction := τE i
    targetAction := τF i
    source_smooth := hτE i
    target_smooth := hτF i
    symbol := aU i
    elliptic := hell i
    equivariant := hequiv i }
  refine ⟨b, ?_, ?_⟩
  · intro i
    -- The same native symbol has the original proper equivariant cotangent pullback class.
    exact equivariantHomogeneousSymbolKClass_pullback IG E F a.sourceAction a.targetAction
      (f i) (τE i) (τF i)
      (a.sourceAction.modelPullback_lift (f i) (heq i))
      (a.targetAction.modelPullback_lift (f i) (heq i))
      (fun _ ξ ↦ ξ) (isOpenEmbedding_cotangentOpenInclusion (U i)).continuous
      (isProperMap_cotangentOpenInclusion (U i) (hclosed i)) (fun _ _ ↦ Iff.rfl)
      (cotangentOpenInclusion_smul IG (U i) (heq i)) 0 a.symbol (aU i)
      a.elliptic (hell i) a.equivariant (hequiv i)
      (fun x ξ _ v ↦ congrArg (fun L ↦ L v) (haU i x ξ))
  · -- Use the same-symbol diagonal realization, with precisely those restricted blocks.
    obtain ⟨Q, hQ, hdiag⟩ := P.exists_clopen_diagonal μ E F R a.symbol hp
      U hclosed hdisjoint hcover
    have hpQ := hQ.trans hp
    have hiQ : Q.IsElliptic := (Q.isElliptic_iff_of_principalSymbol_eq_operator P hQ).mpr hi
    obtain ⟨S, hSval, _⟩ := exists_smoothSectionClopenEquiv
      (n := n) (r := E.rank) E.Fiber U hclosed hdisjoint hcover
    obtain ⟨T, hTval, _⟩ := exists_smoothSectionClopenEquiv
      (n := n) (r := F.rank) F.Fiber U hclosed hdisjoint hcover
    have hSr (u : smoothSections (n := n) (r := E.rank) E.Fiber) (i : Fin k) :
        S u i = smoothSectionRestriction E.Fiber (U i) u :=
      Subtype.ext (funext (hSval u i))
    have hTr (v : smoothSections (n := n) (r := F.rank) F.Fiber) (i : Fin k) :
        T v i = smoothSectionRestriction F.Fiber (U i) v :=
      Subtype.ext (funext (hTval v i))
    have hS (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) (i : Fin k) :
        S (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g u) i =
          (τE i).smoothSectionRepresentation IG (hτE i) g (S u i) := by
      rw [hSr, hSr, hresE]
    have hT (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) (i : Fin k) :
        T (a.targetAction.smoothSectionRepresentation IG a.target_smooth g v) i =
          (τF i).smoothSectionRepresentation IG (hτF i) g (T v i) := by
      rw [hTr, hTr, hresF]
    have hinter (u : smoothSections (n := n) (r := E.rank) E.Fiber) (i : Fin k) :
        (PU i).toLinearMap (S u i) = T (Q.toLinearMap u) i := by
      apply Subtype.ext
      funext x
      change ((PU i).toLinearMap (S u i)).val x = (T (Q.toLinearMap u) i).val x
      rw [hTval, hdiag, haction, hSr]
    have hQg : Q.IsEquivariant IG a.sourceAction a.targetAction
        a.source_smooth a.target_smooth := by
      intro g
      apply LinearMap.ext
      intro u
      change Q.toLinearMap (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g u) =
        a.targetAction.smoothSectionRepresentation IG a.target_smooth g (Q.toLinearMap u)
      apply T.injective
      funext i
      have h := congrArg (fun L ↦ L (S u i)) (hPUg i g)
      change (PU i).toLinearMap ((τE i).smoothSectionRepresentation IG (hτE i) g (S u i)) =
        (τF i).smoothSectionRepresentation IG (hτF i) g ((PU i).toLinearMap (S u i)) at h
      rw [← hinter, hS, h, hT, ← hinter]
    have hindex := Q.smoothEquivariantAnalyticIndex_eq_sum_of_sectionEquiv
      IG E F (fun i ↦ E.restrictOpen (U i)) (fun i ↦ F.restrictOpen (U i))
      a.sourceAction a.targetAction τE τF a.source_smooth a.target_smooth hτE hτF
      μ (fun i ↦ μ.comap (Subtype.val : U i → M)) PU hQg hiQ hPUg hiU S T hS hT hinter
    have hglobal : a.index = Q.smoothEquivariantAnalyticIndex
        IG a.sourceAction a.targetAction a.source_smooth a.target_smooth hQg hiQ :=
      equivariantHomogeneousAnalyticIndex_eq_smooth IG a.sourceAction a.targetAction
        a.source_smooth a.target_smooth a.symbol a.elliptic a.equivariant μ R Q hQg hiQ hpQ
    refine hglobal.trans (hindex.trans ?_)
    apply Finset.sum_congr rfl
    intro i _
    exact (equivariantHomogeneousAnalyticIndex_eq_smooth IG (τE i) (τF i) (hτE i) (hτF i)
      (aU i) (hell i) (hequiv i) (μ.comap (Subtype.val : U i → M))
      (RU i) (PU i) (hPUg i) (hiU i) (hpU i)).symm

variable [FiniteDimensional ℝ VG]

/-- Any specified local representatives of the original restrictions have the same sum index. -/
theorem EquivariantEllipticSymbolData.index_eq_sum_of_clopen
    (b : ∀ i, EquivariantEllipticSymbolData (n := n) (M := U i) (VG := VG) (G := G))
    (hb : ∀ i, (b i).kClass =
      equivariantCotangentClopenRestrict 𝓘(ℝ, VG) U hclosed heq a.kClass i) :
    a.index = ∑ i, (b i).index := by
  obtain ⟨c, hc, hindex⟩ := a.exists_clopen_decomposition U hclosed hdisjoint hcover heq
  refine hindex.trans (Finset.sum_congr rfl (fun i _ ↦ ?_))
  exact equivariantHomogeneousAnalyticIndex_eq_of_equivariantSymbolKClass_eq
    (c i).sourceAction (c i).targetAction (b i).sourceAction (b i).targetAction
    (c i).source_smooth (c i).target_smooth (b i).source_smooth (b i).target_smooth
    (c i).symbol (b i).symbol (c i).elliptic (b i).elliptic
    (c i).equivariant (b i).equivariant ((hc i).trans (hb i).symm)

end AtiyahSinger
