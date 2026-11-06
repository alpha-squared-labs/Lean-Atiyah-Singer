/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantIndexOperations
public import AtiyahSinger.Analysis.EquivariantPseudodifferentialOperator

/-!
# The geometric equivariant index of an actual order-zero elliptic PDO

Public module ID: M0656.

The supplied original smooth bundle actions extend to the already specified
integral completions. Ellipticity makes the original metric L² realization
Fredholm. Its actual finite kernel and quotient-cokernel representations define
the virtual representation index. No equivariant quantization or realization
of an arbitrary equivariant K class is assumed by this construction.

Sources: SG III.5.2, III.9.3--9.4 and Corollary 9.6, pp.193--195 and 211--214. The order-zero
specialization, explicit invariant-metric independence, and equality for the
same principal quotient class make the geometric-to-Hilbert comparison precise.
The smooth compact base, fixed bundle ranks and positive smooth density remain
those of the original PDO. The acting group need not be compact after invariant
data have been supplied. The results include the dimension comparison,
invariant-metric independence,
and equality for the same principal class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction hInvariant kInvariant hμInvariant

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
  (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)

/-- The virtual representation index of this actual geometric order-zero elliptic operator. -/
def equivariantAnalyticIndex : RepresentationGrothendieckGroup G :=
  equivariantFredholmIndex
    (h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
    (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
    (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
    (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
    (P.metricL2Extension h k)
    ((P.isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
      h k hInvariant kInvariant hμInvariant).mp hPg)
    (P.isFredholm_metricL2Extension h k hP)

/-- Forgetting the geometric action recovers the index of the original smooth-section map. -/
theorem representationDimension_equivariantAnalyticIndex :
    representationDimension G
        (P.equivariantAnalyticIndex IG σE σF hσE hσF
          h k hInvariant kInvariant hμInvariant hPg hP) = P.toLinearMap.index := by
  /- Stage 1: apply representationDimension_equivariantFredholmIndex to the
  very same L² representations and bounded realization used in the definition.
  This gives the integer index of P.metricL2Extension h k, without replacing
  a representation by its dimension before taking the explicit forgetting map.
  Stage 2: index_metricL2Extension identifies this integer with the original
  smooth-section index by its actual kernel and quotient-cokernel maps and
  elliptic regularity. The measure, metrics and operator are unchanged. -/
  -- Forget the action only after forming the two actual finite representation classes.
  unfold equivariantAnalyticIndex
  rw [representationDimension_equivariantFredholmIndex]
  exact P.index_metricL2Extension h k hP

/-- Invariant metrics change the realization but not its full virtual representation index. -/
theorem equivariantAnalyticIndex_metric_independent
    (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F)
    (hInvariant' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (g : G) (x : M) (u v : E x),
        h'.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h'.pairing x u v)
    (kInvariant' : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : M) (u v : F x),
        k'.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k'.pairing x u v) :
    P.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP =
      P.equivariantAnalyticIndex IG σE σF hσE hσF
        h' k' hInvariant' kInvariant' hμInvariant hPg hP := by
  /- Stage 1: the same-section comparisons h.l2Equiv μ h' and k.l2Equiv μ k'
  intertwine the completed group actions: verify on the common dense smooth
  domain using l2Equiv_smoothToL2 and the geometric action formula, then extend
  by continuity. These equivalences need not be isometries.
  Stage 2: metricL2Extension_change says that these exact comparisons conjugate
  the original two realizations. Restrict the input comparison to the actual
  kernels, and descend the output comparison to the actual quotient-cokernels.
  The resulting continuous linear equivalences intertwine the same group.
  Stage 3: representationClass_eq_of_equiv equates the two kernel classes and
  the two quotient-cokernel classes. Subtract these equalities in R(G). This
  compares full virtual representations, not merely their dimensions. -/
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let ρ' := h'.l2ContRepresentation μ IG σE hσE hInvariant' hμInvariant
  let τ' := k'.l2ContRepresentation μ IG σF hσF kInvariant' hμInvariant
  -- The identity comparisons intertwine the same geometric actions on a dense core.
  have he (g : G) : (h.l2Equiv μ h').toContinuousLinearMap.comp (ρ g) =
      (ρ' g).comp (h.l2Equiv μ h').toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      ((h.l2Equiv μ h').toContinuousLinearMap.comp (ρ g)).continuous
      ((ρ' g).comp (h.l2Equiv μ h').toContinuousLinearMap).continuous
    funext u
    change h.l2Equiv μ h' (h.l2IsometryRepresentation μ IG σE hσE hInvariant
      hμInvariant g (h.smoothToL2 μ u)) =
        h'.l2IsometryRepresentation μ IG σE hσE hInvariant' hμInvariant g
          (h.l2Equiv μ h' (h.smoothToL2 μ u))
    rw [h.l2IsometryRepresentation_smoothToL2, h.l2Equiv_smoothToL2,
      h.l2Equiv_smoothToL2, h'.l2IsometryRepresentation_smoothToL2]
  have hf (g : G) : (k.l2Equiv μ k').toContinuousLinearMap.comp (τ g) =
      (τ' g).comp (k.l2Equiv μ k').toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (k.denseRange_smoothToL2 μ).equalizer
      ((k.l2Equiv μ k').toContinuousLinearMap.comp (τ g)).continuous
      ((τ' g).comp (k.l2Equiv μ k').toContinuousLinearMap).continuous
    funext u
    change k.l2Equiv μ k' (k.l2IsometryRepresentation μ IG σF hσF kInvariant
      hμInvariant g (k.smoothToL2 μ u)) =
        k'.l2IsometryRepresentation μ IG σF hσF kInvariant' hμInvariant g
          (k.l2Equiv μ k' (k.smoothToL2 μ u))
    rw [k.l2IsometryRepresentation_smoothToL2, k.l2Equiv_smoothToL2,
      k.l2Equiv_smoothToL2, k'.l2IsometryRepresentation_smoothToL2]
  let e : ContRepresentation.Equiv ρ ρ' := ContRepresentation.Equiv.mk (h.l2Equiv μ h') he
  let f : ContRepresentation.Equiv τ τ' := ContRepresentation.Equiv.mk (k.l2Equiv μ k') hf
  -- The same comparisons form a commuting square for the actual two realizations.
  have hsquare : (P.metricL2Extension h' k').comp e.toContinuousLinearEquiv.toContinuousLinearMap =
      f.toContinuousLinearEquiv.toContinuousLinearMap.comp (P.metricL2Extension h k) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      ((P.metricL2Extension h' k').comp e.toContinuousLinearEquiv.toContinuousLinearMap).continuous
      (f.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (P.metricL2Extension h k)).continuous
    funext u
    change P.metricL2Extension h' k' (h.l2Equiv μ h' (h.smoothToL2 μ u)) =
      k.l2Equiv μ k' (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [h.l2Equiv_smoothToL2, P.metricL2Extension_smooth,
      P.metricL2Extension_smooth, k.l2Equiv_smoothToL2]
  unfold equivariantAnalyticIndex
  exact equivariantFredholmIndex_eq_of_equiv ρ τ ρ' τ' _ _ _ _ e f _ _ _ _
    hsquare _ _

/-- Actual equivariant elliptic operators with the same principal class have the same index. -/
theorem equivariantAnalyticIndex_eq_of_principalSymbol_eq
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hQg : Q.IsEquivariant IG σE σF hσE hσF) (hQ : Q.IsElliptic)
    (hSymbol : P.principalSymbol = Q.principalSymbol) :
    P.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP =
      Q.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hQg hQ := by
  /- Stage 1: equality in the original S⁰/S⁻¹ quotient implies that P-Q has
  order minus one, including its actual smoothing remainder. Its realization
  gains one Sobolev derivative, so compact embedding on the compact base makes
  the difference of the same two metric L² extensions compact.
  Stage 2: both extensions intertwine the fixed original unitary actions by
  the smooth-to-L² equivalence; their difference is an equivariant compact
  operator. Apply invariance of the full equivariant Fredholm index under
  compact perturbations (or the straight norm-continuous Fredholm path).
  Stage 3: unfold the two geometric indices and identify their Fredholm
  certificates by proof irrelevance. This only compares supplied operators
  on the same bundles; it does not construct representatives or descend an
  index to arbitrary equivariant symbol K classes. -/
  classical
  let T := Q.metricL2Extension h k
  let K := P.metricL2Extension h k - T
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  -- The exact lower-order difference is compact after the same metric L² comparisons.
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  let R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (0 - 1) :=
    ⟨P.toLinearMap - Q.toLinearMap, (P.principalSymbol_eq_iff Q).mp hSymbol⟩
  let e := h.sobolevZeroEquivL2 (μ := μ) A
  let f := k.sobolevZeroEquivL2 (μ := μ) B
  let K₀ := f.symm.toContinuousLinearMap.comp (K.comp e.toContinuousLinearMap)
  have hK₀ : IsCompactOperator K₀ := by
    apply R.isCompactOperator_of_order_neg A B (by norm_num) 0 K₀
    intro u
    change f.symm ((P.metricL2Extension h k - Q.metricL2Extension h k)
      (e (A.smoothToSobolev 0 u))) = B.smoothToSobolev 0 (R.toLinearMap u)
    rw [h.sobolevZeroEquivL2_smooth, sub_apply,
      P.metricL2Extension_smooth, Q.metricL2Extension_smooth, ← map_sub]
    change f.symm (k.smoothToL2 μ ((P.toLinearMap - Q.toLinearMap) u)) = _
    rw [← k.sobolevZeroEquivL2_smooth B]
    exact f.symm_apply_apply _
  have hK : IsCompactOperator K := by
    have heq : K = f.toContinuousLinearMap.comp (K₀.comp e.symm.toContinuousLinearMap) := by
      ext u
      change K u = f (f.symm (K (e (e.symm u))))
      rw [e.apply_symm_apply, f.apply_symm_apply]
    rw [heq]
    exact (hK₀.comp_clm e.symm.toContinuousLinearMap).clm_comp f.toContinuousLinearMap
  -- Equivariance uses the same fixed representations for the difference and the path.
  have hTg : ∀ g : G, T.comp (ρ g) = (τ g).comp T :=
    (Q.isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
      h k hInvariant kInvariant hμInvariant).mp hQg
  have hPg' : ∀ g : G, (P.metricL2Extension h k).comp (ρ g) =
      (τ g).comp (P.metricL2Extension h k) :=
    (P.isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
    h k hInvariant kInvariant hμInvariant).mp hPg
  have hKg (g : G) : K.comp (ρ g) = (τ g).comp K := by
    simp only [K, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      hPg' g, hTg g]
  have heq : T + K = P.metricL2Extension h k := by dsimp [K]; abel
  have hindex := equivariantFredholmIndex_add_compact ρ τ
    (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant)
    (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
    (fun g ↦ (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g).isometry)
    (fun g ↦ (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g).isometry)
    T K hTg hKg (Q.isFredholm_metricL2Extension h k hQ) hK
  unfold equivariantAnalyticIndex
  simpa only [heq, T, ρ, τ] using hindex

end AtiyahSinger.PseudodifferentialOperator
