/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOrderReduction
public import AtiyahSinger.Analysis.SmoothGreenPseudodifferential

/-!
# Equivariance of the same smooth Green operator

Public module ID: M0572.

The original invariant metric and measure make both smooth actions unitary.
The original kernel projections therefore commute with these same actions.
Uniqueness of the orthogonal smooth solution proves equivariance of the
specified Green map and hence of its actual pseudodifferential realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    ∀ (g : G) (x : M) (u v : E.Fiber x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : G) (x : M) (u v : F.Fiber x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
  (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
    E.Fiber F.Fiber μ 1)
  (hPg : P.IsEquivariant IG σE σF hσE hσF)


include hPg hInvariant kInvariant hμInvariant

/-- The specified canonical smooth Green PDO intertwines the original two group actions. -/
theorem PseudodifferentialOperator.isEquivariant_smoothGreenOperator
    (A : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
    (B : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber) (hP : P.IsElliptic) :
    let W : Submodule ℂ (h.SmoothL2Section μ) := P.toLinearMap.ker
    let W' : Submodule ℂ (k.SmoothL2Section μ) := (P.metricFormalAdjoint h k).toLinearMap.ker
    letI : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
    letI : FiniteDimensional ℂ W' :=
      (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
        ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
    ∀ (Green : k.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ)
      (hGreen : IsPseudodifferentialOperator F.Fiber E.Fiber μ (-1) Green.toLinearMap),
      (∀ v : k.SmoothL2Section μ,
        P.toLinearMap (Green v) = v - W'.starProjection v) →
      (∀ v : k.SmoothL2Section μ, Green v ∈ W.orthogonal) →
      (∀ (v : k.SmoothL2Section μ) (u : h.SmoothL2Section μ),
        P.toLinearMap u = v - W'.starProjection v → u ∈ W.orthogonal → u = Green v) →
      (⟨Green.toLinearMap, hGreen⟩ : PseudodifferentialOperator
        (n := n) (r := F.rank) (q := E.rank) F.Fiber E.Fiber μ (-1)).IsEquivariant
          IG σF σE hσF hσE := by
  classical
  intro W W'
  let : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
  let : FiniteDimensional ℂ W' :=
    (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
      ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
  intro Green hGreen hPG horth hunique
  let R := σE.smoothSectionRepresentation IG hσE
  let T := σF.smoothSectionRepresentation IG hσF
  let green : smoothSections (n := n) (r := F.rank) F.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := E.rank) E.Fiber := Green.toLinearMap
  let K' := smoothOrthogonalProjection μ k W'
  have hact (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      P.toLinearMap (R g u) = T g (P.toLinearMap u) :=
    LinearMap.congr_fun (hPg g) u
  have hAdjg := P.isEquivariant_metricFormalAdjoint IG σE σF hσE hσF h k
    hInvariant kInvariant hμInvariant hPg
  have hactAdj (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      (P.metricFormalAdjoint h k).toLinearMap (T g v) =
        R g ((P.metricFormalAdjoint h k).toLinearMap v) :=
    LinearMap.congr_fun (hAdjg g) v
  have hW (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) (hu : u ∈ W) :
      R g u ∈ W := by
    change P.toLinearMap (R g u) = 0
    rw [hact, show P.toLinearMap u = 0 from hu, map_zero]
  have hW' (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) (hv : v ∈ W') :
      T g v ∈ W' := by
    change (P.metricFormalAdjoint h k).toLinearMap (T g v) = 0
    rw [hactAdj, show (P.metricFormalAdjoint h k).toLinearMap v = 0 from hv, map_zero]
  have hRcancel (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      R g (R g⁻¹ u) = u := by
    change (R g * R g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hTcancel (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      T g (T g⁻¹ v) = v := by
    change (T g * T g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  -- The same invariant fiber metrics and density make the complete smooth actions unitary.
  have hpair (g : G) (u v : smoothSections (n := n) (r := E.rank) E.Fiber) :
      h.sectionPairing μ (R g u) (R g v) = h.sectionPairing μ u v := by
    rw [← h.inner_smoothToL2, ← h.inner_smoothToL2,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant]
    exact (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g).inner_map_map _ _
  have hpair' (g : G) (u v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      k.sectionPairing μ (T g u) (T g v) = k.sectionPairing μ u v := by
    rw [← k.inner_smoothToL2, ← k.inner_smoothToL2,
      ← k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant,
      ← k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant]
    exact (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g).inner_map_map _ _
  have hK'g (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      K' (T g v) = T g (K' v) := by
    apply W'.eq_starProjection_of_mem_of_inner_eq_zero
      (hW' g (K' v) (W'.starProjection_apply_mem v))
    intro w hw
    change smoothSections (n := n) (r := F.rank) F.Fiber at w
    change k.sectionPairing μ (T g v - T g (K' v)) w = 0
    calc
      _ = k.sectionPairing μ (T g (v - K' v)) (T g (T g⁻¹ w)) := by
        rw [map_sub, hTcancel]
      _ = k.sectionPairing μ (v - K' v) (T g⁻¹ w) := hpair' g _ _
      _ = 0 := W'.starProjection_inner_eq_zero v _ (hW' g⁻¹ w hw)
  -- The transformed Green output solves the same projected equation in the same complement.
  have hsolve (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      P.toLinearMap (green v) = v - K' v := hPG v
  intro g
  apply LinearMap.ext
  intro v
  change green (T g v) = R g (green v)
  symm
  apply hunique (T g v) (R g (green v))
  · change P.toLinearMap (R g (green v)) = T g v - K' (T g v)
    rw [hact, hsolve, map_sub, hK'g]
  · intro w hw
    change smoothSections (n := n) (r := E.rank) E.Fiber at w
    change h.sectionPairing μ w (R g (green v)) = 0
    calc
      _ = h.sectionPairing μ (R g (R g⁻¹ w)) (R g (green v)) := by rw [hRcancel]
      _ = h.sectionPairing μ (R g⁻¹ w) (green v) := hpair g _ _
      _ = 0 := horth v _ (hW g⁻¹ w hw)

end AtiyahSinger
