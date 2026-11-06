/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndex
public import AtiyahSinger.Analysis.ClopenIndex
public import AtiyahSinger.Analysis.HomogeneousSymbolPullback
public import AtiyahSinger.Analysis.PreconnectedAnalyticNaturality
public import AtiyahSinger.Analysis.SmallEllipticRepresentative
public import AtiyahSinger.Geometry.OpenDensity
public import AtiyahSinger.Topology.CotangentComponents

/-!
# The analytic index assembled over the connected components

Public module ID: M0376.

A10: extend the compact preconnected construction to every compact manifold by
summing its component indices after the specified cotangent K restrictions.
Different components may carry classes of different virtual ranks; no global
fixed-rank representative of every class is asserted. Compatibility with a
supplied global PDO uses actual diagonal blocks and the proved same-symbol
index comparison, retaining the original off-diagonal section action.
Sources: SG III.13 (13.7)--(13.8), pp.246--247, and the finite-disjoint-union
K-theory argument from Karoubi II.1.26. Component assembly is a project bridge
for the present fixed-rank analytic model, not an additional source axiom.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

/-- The analytic-index homomorphism on an arbitrary compact base, summed over its components. -/
def analyticIndexOfComponents :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+ ℤ :=
  letI := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  letI := Fintype.ofFinite (ConnectedComponents M)
  ∑ c : ConnectedComponents M,
    (analyticIndex (n := n)
      (μ.comap (Subtype.val : manifoldComponent (n := n) c → M))).comp
      ((Pi.evalAddMonoidHom _ c).comp (cotangentKZeroComponents (n := n) (M := M)))

/-- Component assembly agrees with the original preconnected analytic-index construction. -/
theorem analyticIndexOfComponents_eq_analyticIndex [PreconnectedSpace M] :
    analyticIndexOfComponents (n := n) μ = analyticIndex (n := n) μ := by
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  -- Empty bases have no components and every smooth operator has zero index.
  rcases isEmpty_or_nonempty M with hEmpty | hNonempty
  · let : IsEmpty (ConnectedComponents M) := ⟨fun c ↦ by
      obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe c
      exact isEmptyElim x⟩
    have hz : analyticIndexOfComponents (n := n) μ = 0 := by
      unfold analyticIndexOfComponents
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
    apply AddMonoidHom.ext
    intro u
    rw [hz, AddMonoidHom.zero_apply]
    obtain ⟨E, F, R, a, P, hp, hi, hclass⟩ :=
      exists_elliptic_pseudodifferential_representative_of_preconnected (n := n) μ u 0
    rw [← hclass, P.analyticIndex_symbolKClassOfHomogeneous μ R a hp hi]
    simp only [LinearMap.index_eq_finrank_sub, Module.finrank_zero_of_subsingleton,
      Nat.cast_zero, sub_zero]
  · -- The single component is the original base with its inherited open atlas.
    let c : ConnectedComponents M := ConnectedComponents.mk (Classical.choice hNonempty)
    let U := manifoldComponent (n := n) c
    have hU (x : M) : x ∈ U := Subsingleton.elim (ConnectedComponents.mk x) c
    let into (x : M) : U := ⟨x, hU x⟩
    let e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ M := {
      toEquiv := {
        toFun := Subtype.val
        invFun := into
        left_inv x := Subtype.ext rfl
        right_inv _ := rfl }
      contMDiff_toFun := contMDiff_subtype_val
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U into).mp contMDiff_id }
    -- Its cotangent lift is the actual component inclusion, with identity native derivative.
    have hinv (x : M) : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e.symm x =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      have h := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x
        ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) (e.symm x))
        (e.symm.contMDiff.mdifferentiable (by simp) x)
      change mfderiv _ _ (id : M → M) x = _ at h
      rw [mfderiv_id, mfderiv_openSubtypeVal] at h
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun T ↦ T v) h.symm
    have hcot : cotangentDiffeomorphMap e = cotangentOpenInclusion U := by
      funext z
      change (⟨z.proj.val, z.snd.comp (mfderiv _ _ e.symm (e z.proj))⟩ :
        CotangentTotalSpace (n := n) (M := M)) = ⟨z.proj.val, z.snd⟩
      rw [hinv]
      exact congrArg (fun ξ : CotangentFiber (n := n) z.proj.val ↦
        (⟨z.proj.val, ξ⟩ : CotangentTotalSpace (n := n) (M := M)))
          (ContinuousLinearMap.ext (fun _ ↦ rfl))
    have hrestriction (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
        cotangentKZeroComponents u c =
          compactSupportKZeroHomeomorph (cotangentDiffeomorph e).symm u := by
      change compactSupportKZeroPullback _ _ u = compactSupportKZeroPullback _ _ u
      congr 2
      exact ContinuousMap.ext (congrFun hcot.symm)
    -- Naturality cancels this inclusion with its exact inverse pullback.
    apply AddMonoidHom.ext
    intro u
    unfold analyticIndexOfComponents
    rw [AddMonoidHom.finsetSum_apply, Finset.sum_eq_single c]
    · change analyticIndex (μ.comap (Subtype.val : U → M)) (cotangentKZeroComponents u c) = _
      rw [← analyticIndex_diffeomorph (μ.comap (Subtype.val : U → M)) μ e,
        AddMonoidHom.comp_apply, hrestriction]
      change analyticIndex μ
        (((compactSupportKZeroHomeomorph (cotangentDiffeomorph e)).comp
          (compactSupportKZeroHomeomorph (cotangentDiffeomorph e).symm)) u) = _
      have hcancel := compactSupportKZeroHomeomorph_symm (cotangentDiffeomorph e).symm
      simpa only [Homeomorph.symm_symm, AddMonoidHom.id_apply] using
        congrArg (analyticIndex μ) (DFunLike.congr_fun hcancel u)
    · intro d _ hdc
      exact False.elim (hdc (Subsingleton.elim d c))
    · intro hc
      exact False.elim (hc (Finset.mem_univ c))

/-- The component construction is independent of the auxiliary positive smooth density. -/
theorem analyticIndexOfComponents_independent_measure
    (ν : Measure M) [IsSmoothPositiveMeasure (n := n) ν] :
    analyticIndexOfComponents (n := n) μ = analyticIndexOfComponents (n := n) ν := by
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  unfold analyticIndexOfComponents
  apply Finset.sum_congr rfl
  intro c _
  -- The same open component carries both restricted densities and the same K restriction.
  rw [analyticIndex_independent_measure
    (μ.comap (Subtype.val : manifoldComponent (n := n) c → M))
    (ν.comap (Subtype.val : manifoldComponent (n := n) c → M))]

variable {r q : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hC hB hμ hE hF in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The component index recovers the original global PDO index, including cross-component terms. -/
theorem PseudodifferentialOperator.analyticIndexOfComponents_symbolKClassOfHomogeneous {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    analyticIndexOfComponents μ (P.symbolKClassOfHomogeneous R a hp hi) =
      P.toLinearMap.index := by
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  -- Reduce this supplied operator, without asserting that every global K class has fixed rank.
  obtain ⟨A, B, S, b, Q, hQ, hj, hclass, hindex⟩ :=
    P.exists_small_orderZero_representative R a hp hi
  rw [← hclass, ← hindex]
  let U := manifoldComponent (n := n) (M := M)
  have hclosed (c : ConnectedComponents M) : IsClosed (U c : Set M) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have hdisjoint : Pairwise (fun c d ↦ Disjoint (U c : Set M) (U d : Set M)) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro x hc hd
    exact hcd (hc.symm.trans hd)
  have hcover : (⋃ c, (U c : Set M)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨ConnectedComponents.mk x, rfl⟩
  -- Use the actual component restrictions and their already proved finite index decomposition.
  obtain ⟨PU, RU, aU, hpU, hiU, haU, hsum⟩ :=
    Q.exists_clopen_index_decomposition μ A B S b hQ hj U hclosed hdisjoint hcover
  unfold analyticIndexOfComponents
  rw [AddMonoidHom.finsetSum_apply, hsum]
  apply Finset.sum_congr rfl
  intro c _
  change analyticIndex (μ.comap (Subtype.val : U c → M))
    (cotangentKZeroComponents (Q.symbolKClassOfHomogeneous S b hQ hj) c) = _
  -- The same restricted homogeneous symbol realizes the specified proper cotangent pullback.
  have hK : (PU c).symbolKClassOfHomogeneous (RU c) (aU c) (hpU c) (hiU c) =
      cotangentKZeroComponents (Q.symbolKClassOfHomogeneous S b hQ hj) c := by
    change homogeneousSymbolKClass 0 (aU c) _ =
      compactSupportKZeroPullback _ _ (homogeneousSymbolKClass 0 b _)
    exact homogeneousSymbolKClass_pullback (m := n) (N := U c) A B
      (ContinuousMap.subtypeVal (U c : Set M))
      (fun _ ξ ↦ ξ) (isOpenEmbedding_cotangentOpenInclusion (U c)).continuous
      (isProperMap_cotangentOpenInclusion (U c) (hclosed c)) (fun _ _ ↦ Iff.rfl)
      0 b (aU c) ((Q.isElliptic_iff_homogeneous S b hQ).mp hj)
      (((PU c).isElliptic_iff_homogeneous (RU c) (aU c) (hpU c)).mp (hiU c))
      (fun x ξ _ v ↦ congrArg (fun L ↦ L v) (haU c x ξ))
  rw [← hK]
  exact (PU c).analyticIndex_symbolKClassOfHomogeneous
    (μ.comap (Subtype.val : U c → M)) (RU c) (aU c) (hpU c) (hiU c)

end AtiyahSinger
