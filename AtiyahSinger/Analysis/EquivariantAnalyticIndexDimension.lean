/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentIndexClopen
public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantSymbolIndexDimension

/-!
# Forgetting the arbitrary-class equivariant analytic index

Public module ID: M0460.

The representation dimension of the analytic index on the original equivariant
support K group equals the ordinary component analytic index of the same class
after forgetting its actions. The comparison uses the existing specified
support-triple-to-compact-support map. It is an equality of additive maps on
all original classes, including classes whose bundle ranks vary by component.

The ordinary positive smooth density need not be invariant. The equivariant
map already has its independent full representation-valued construction; this
theorem does not define it by its dimension or claim dimension is injective.
No connectedness, positive base dimension or nonempty-base assumption is made.

Sources: SG III.9, Definition 9.3 and equation (9.1), pp.211--212, identifies
the equivariant index with the actual kernel-minus-cokernel representation;
SG III.13 (13.7)--(13.8), pp.246--247, gives the ordinary symbol-class index.
Compatibility of the original forgetful maps with finite clopen assembly is
an explicit project argument using the geometric index dimension theorem.
An exact independent source for the arbitrary-class comparison has not been
identified. The proof retains the same classes and realizations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff BigOperators

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Forgetting the original actions commutes with the analytic index on every K class. -/
theorem representationDimension_equivariantAnalyticIndexMap
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    (representationDimension G).comp
        (equivariantAnalyticIndexMap (n := n) (M := M) (VG := VG) (G := G)) =
      (analyticIndexOfComponents μ).comp
        (supportTripleKZeroToCompactSupport.comp
          (equivariantSupportTripleKZeroForget (G := G)
            (X := CotangentTotalSpace (n := n) (M := M)))) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  apply AddMonoidHom.ext
  intro x
  -- Keep one actual invariant clopen family representing the arbitrary original K class.
  obtain ⟨b, hb⟩ := exists_equivariantClopenSymbolFamily
    (n := n) (M := M) (VG := VG) x
  let P := b.partition
  let := P.mulAction
  let := P.continuousSMul
  let := P.contMDiffSMul (n := n) (VG := VG)
  let := P.compactSpace
  let : ∀ i, IsSmoothPositiveMeasure (n := n)
      (μ.comap (Subtype.val : P.piece i → M)) :=
    fun i ↦ isSmoothPositiveMeasure_comap_opens μ (P.piece i)
  let Φ := equivariantCotangentClopenEquiv (n := n) 𝓘(ℝ, VG) P.piece P.isClosed
    P.equivariant P.disjoint P.cover
  have hclasses (i : Fin P.size) : (b.symbols i).kClass =
      equivariantCotangentClopenRestrict 𝓘(ℝ, VG) P.piece P.isClosed P.equivariant b.kClass i := by
    change (b.symbols i).kClass = Φ (Φ.symm (fun j ↦ (b.symbols j).kClass)) i
    rw [Φ.apply_symm_apply]
  have heval := equivariantAnalyticIndexMap_clopen (n := n) (M := M) (VG := VG) (G := G)
    P.size P.piece P.isClosed P.disjoint P.cover P.mulAction P.continuousSMul
    (P.contMDiffSMul (n := n) (VG := VG)) P.equivariant P.compactSpace
    (fun i ↦ (b.symbols i).source) (fun i ↦ (b.symbols i).target)
    (fun i ↦ (b.symbols i).sourceAction) (fun i ↦ (b.symbols i).targetAction)
    (fun i ↦ (b.symbols i).source_smooth) (fun i ↦ (b.symbols i).target_smooth)
    (fun i ↦ (b.symbols i).symbol) (fun i ↦ (b.symbols i).elliptic)
    (fun i ↦ (b.symbols i).equivariant)
  change equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) b.kClass = b.index at heval
  rw [← hb]
  change representationDimension G
      (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) b.kClass) =
    analyticIndexOfComponents μ
      (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget b.kClass))
  rw [heval]
  change representationDimension G (∑ i, (b.symbols i).index) = _
  rw [map_sum, analyticIndexOfComponents_eq_sum_clopen μ P.piece P.isClosed
    P.disjoint P.cover]
  apply Finset.sum_congr rfl
  intro i _
  -- Both forgetful comparisons commute with the same original proper cotangent restriction.
  let f : C(CotangentTotalSpace (n := n) (M := P.piece i),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion (P.piece i),
      (isOpenEmbedding_cotangentOpenInclusion (P.piece i)).continuous⟩
  have hf : IsProperMap f := isProperMap_cotangentOpenInclusion (P.piece i) (P.isClosed i)
  let := smoothCotangentMulAction (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := P.piece i) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := P.piece i)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  have hfG : ∀ g y, f (g • y) = g • f y :=
    cotangentOpenInclusion_smul 𝓘(ℝ, VG) (P.piece i) (P.equivariant i)
  have hc := hclasses i
  change (b.symbols i).kClass = equivariantSupportTripleKZeroPullback f hfG hf b.kClass at hc
  have hforget := DFunLike.congr_fun
    (equivariantSupportTripleKZeroForget_pullback f hfG hf) b.kClass
  have hcompact := DFunLike.congr_fun
    (supportTripleKZeroToCompactSupport_pullback f hf)
    (equivariantSupportTripleKZeroForget b.kClass)
  simp only [AddMonoidHom.comp_apply] at hforget hcompact
  change equivariantSupportTripleKZeroForget
      (equivariantSupportTripleKZeroPullback f hfG hf b.kClass) = _ at hforget
  rw [← hc] at hforget
  have hk : compactSupportKZeroPullback f hf
      (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget b.kClass)) =
        homogeneousSymbolKClass 0 (b.symbols i).symbol (b.symbols i).elliptic := by
    refine hcompact.symm.trans ?_
    rw [← hforget]
    exact equivariantHomogeneousSymbolKClass_forget 𝓘(ℝ, VG)
      (b.symbols i).sourceAction (b.symbols i).targetAction 0
      (b.symbols i).symbol (b.symbols i).elliptic (b.symbols i).equivariant
  -- Taking dimension on the piece uses its same symbol and an arbitrary restricted density.
  change representationDimension G (b.symbols i).index =
    analyticIndexOfComponents (μ.comap (Subtype.val : P.piece i → M))
      (compactSupportKZeroPullback f hf
        (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget b.kClass)))
  rw [hk]
  exact (b.symbols i).index_dimension (μ.comap (Subtype.val : P.piece i → M))

end AtiyahSinger
