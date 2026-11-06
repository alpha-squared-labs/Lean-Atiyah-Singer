/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantOperatorAverage
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

import AtiyahSinger.Analysis.EquivariantSectionTopologyWeak
import AtiyahSinger.Analysis.PseudodifferentialDistributions
import AtiyahSinger.Analysis.SmoothSectionIntegral

/-!
# Averaging an operator with a specified exterior multiplier

Public module ID: M0565.

The normalized Haar average preserves a specified equivariant bundle multiplier
in an actual relative operator decomposition. Thus its supported correction can
be averaged on the original fibers without changing the exterior identification.
The statement concerns the same smooth-section operators, not only their symbols.

This is the relative form of the averaging argument in SG III.9.7 and III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
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
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

/-- Averaging keeps the same equivariant multiplier and averages precisely its correction. -/
theorem average_toLinearMap_of_equivariant_multiplier
    {m : ℝ} (P R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (c : ∀ x, E x →ₗ[ℂ] F x) (hc : IsSmoothBundleMap (n := n) (r := r) (q := q) c)
    (hcg : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : M) (v : E x),
        c (g • x) (σE.linearMap g x v) = σF.linearMap g x (c x v))
    (hP : P.toLinearMap = smoothSectionMap c hc + R.toLinearMap) :
    (P.average IG σE σF hσE hσF).toLinearMap =
      smoothSectionMap c hc + (R.average IG σE σF hσE hσF).toLinearMap := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  let ρE := σE.smoothSectionRepresentation IG hσE
  let ρF := σF.smoothSectionRepresentation IG hσF
  let C := AtiyahSinger.smoothSectionMap c hc
  let ν := Measure.haarMeasure (⊤ : PositiveCompacts G)
  -- Bundle equivariance gives equality of these actual section operators.
  have hcomm (g : G) (u : smoothSections (n := n) (r := r) E) :
      C (ρE g u) = ρF g (C u) := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    change c (g • y) (σE.sectionLinearMap g u.val (g • y)) =
      σF.sectionLinearMap g (C u).val (g • y)
    rw [σE.sectionLinearMap_smul, σF.sectionLinearMap_smul]
    exact hcg g y (u.val y)
  have hfixed (g : G) (u : smoothSections (n := n) (r := r) E) :
      ρF g (C (ρE g⁻¹ u)) = C u := by
    rw [← hcomm]
    have hin : ρE g (ρE g⁻¹ u) = u := by
      change (ρE g * ρE g⁻¹) u = u
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hin]
  -- Continuity in the original section presentations proves fiber integrability.
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  have hint (u : smoothSections (n := n) (r := r) E) (x : M) :
      Integrable (fun g : G ↦ (ρF g (R.toLinearMap (ρE g⁻¹ u))).val x) ν := by
    have hinput : Continuous (fun g : G ↦ A.smoothSectionEquiv.symm (ρE g⁻¹ u)) :=
      (A.continuous_smoothSectionAction_of_isManifold IG σE hσE).comp
        (continuous_inv.prodMk (continuous_const (y := A.smoothSectionEquiv.symm u)))
    have hoperator := (R.continuous_smoothSectionMap A B).comp hinput
    have hfamily := (B.continuous_smoothSectionAction_of_isManifold IG σF hσF).comp
      (continuous_id.prodMk hoperator)
    exact ((B.continuous_section_evaluation x).comp hfamily).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmass : ν.real Set.univ = 1 := by
    change (Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ).toReal = 1
    rw [show Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ = 1 from
      Measure.haarMeasure_self, ENNReal.toReal_one]
  -- Integrate the constant multiplier and the same conjugated correction in each fiber.
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  change ((P.average IG σE σF hσE hσF).toLinearMap u).val x =
    (C u).val x + ((R.average IG σE σF hσE hσF).toLinearMap u).val x
  rw [P.average_apply IG σE σF hσE hσF, R.average_apply IG σE σF hσE hσF]
  change (∫ g : G, (ρF g (P.toLinearMap (ρE g⁻¹ u))).val x ∂ν) =
    (C u).val x + ∫ g : G, (ρF g (R.toLinearMap (ρE g⁻¹ u))).val x ∂ν
  have hsplit (g : G) : (ρF g (P.toLinearMap (ρE g⁻¹ u))).val x =
      (C u).val x + (ρF g (R.toLinearMap (ρE g⁻¹ u))).val x := by
    rw [hP]
    change (ρF g (C (ρE g⁻¹ u) + R.toLinearMap (ρE g⁻¹ u))).val x = _
    rw [map_add, hfixed]
    rfl
  simp_rw [hsplit]
  rw [integral_add (integrable_const _) (hint u x), integral_const, hmass, one_smul]

end AtiyahSinger.PseudodifferentialOperator

namespace AtiyahSinger

open Bundle ComplexBundle Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

private theorem section_transport_action
    {Z : Type*} [MulAction G Z] (f : Z → M) (j : Z → N)
    (hf : ∀ (g : G) (z : Z), f (g • z) = g • f z)
    (hj : ∀ (g : G) (z : Z), j (g • z) = g • j z)
    (E : SmoothFiniteComplexBundle (n := n) M)
    (E' : SmoothFiniteComplexBundle (n := n) N)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      EquivariantStructure G E'.Fiber)
    (hσ : σ.IsSmooth (n := n) (r := E.rank) IG)
    (hτ : τ.IsSmooth (n := n) (r := E'.rank) IG)
    (a : ∀ z : Z, E.Fiber (f z) ≃ₗ[ℂ] E'.Fiber (j z))
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      ∀ (g : G) (z : Z) (v : E.Fiber (f z)),
        (⟨j (g • z), a (g • z)
          (cast (congrArg E.Fiber (hf g z).symm) (σ.linearMap g (f z) v))⟩ :
            TotalSpace Unit E'.Fiber) =
          ⟨g • j z, τ.linearMap g (j z) (a z v)⟩)
    (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber)
    (v : smoothSections (n := n) (r := E'.rank) E'.Fiber) (z : Z)
    (huv : v.val (j z) = a z (u.val (f z))) :
    ((τ.smoothSectionRepresentation IG hτ g) v).val (j (g • z)) =
      a (g • z) (((σ.smoothSectionRepresentation IG hσ g) u).val (f (g • z))) := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  have hsource :
      (⟨f (g • z), σ.sectionLinearMap g u.val (f (g • z))⟩ : TotalSpace Unit E.Fiber) =
        ⟨g • f z, σ.linearMap g (f z) (u.val (f z))⟩ := by
    rw [hf, σ.sectionLinearMap_smul]
  have hsourceValue : σ.sectionLinearMap g u.val (f (g • z)) =
      cast (congrArg E.Fiber (hf g z).symm) (σ.linearMap g (f z) (u.val (f z))) :=
    eq_of_heq ((TotalSpace.mk.inj hsource).2.trans (cast_heq _ _).symm)
  apply TotalSpace.mk_injective (F := Unit) (j (g • z))
  change (⟨j (g • z), τ.sectionLinearMap g v.val (j (g • z))⟩ : TotalSpace Unit E'.Fiber) =
    ⟨j (g • z), a (g • z) (σ.sectionLinearMap g u.val (f (g • z)))⟩
  calc
    (⟨j (g • z), τ.sectionLinearMap g v.val (j (g • z))⟩ : TotalSpace Unit E'.Fiber) =
        ⟨g • j z, τ.linearMap g (j z) (v.val (j z))⟩ := by
      rw [hj, τ.sectionLinearMap_smul]
    _ = ⟨g • j z, τ.linearMap g (j z) (a z (u.val (f z)))⟩ := by rw [huv]
    _ = ⟨j (g • z), a (g • z)
        (cast (congrArg E.Fiber (hf g z).symm) (σ.linearMap g (f z) (u.val (f z))))⟩ :=
      (ha g z (u.val (f z))).symm
    _ = ⟨j (g • z), a (g • z) (σ.sectionLinearMap g u.val (f (g • z)))⟩ := by
      rw [hsourceValue]

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

set_option maxHeartbeats 1600000 in
-- Compare the same two conjugated operators on every original fiber before integration.
/-- Equivariant germ transport between two actual operators is preserved by Haar averaging. -/
theorem PseudodifferentialOperator.average_intertwines_of_germ
    {Z : Type*} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
    (f : Z → M) (j : Z → N)
    (hf : ∀ (g : G) (z : Z), f (g • z) = g • f z)
    (hj : ∀ (g : G) (z : Z), j (g • z) = g • j z)
    (K : Set Z) (hKi : ∀ (g : G) (z : Z), z ∈ K → g • z ∈ K)
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (E' F' : SmoothFiniteComplexBundle (n := n) N)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (τE : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      EquivariantStructure G E'.Fiber)
    (τF : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      EquivariantStructure G F'.Fiber)
    (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
    (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
    (hτE : τE.IsSmooth (n := n) (r := E'.rank) IG)
    (hτF : τF.IsSmooth (n := n) (r := F'.rank) IG)
    (a : ∀ z : Z, E.Fiber (f z) ≃ₗ[ℂ] E'.Fiber (j z))
    (b : ∀ z : Z, F.Fiber (f z) ≃ₗ[ℂ] F'.Fiber (j z))
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      ∀ (g : G) (z : Z) (v : E.Fiber (f z)),
        (⟨j (g • z), a (g • z)
          (cast (congrArg E.Fiber (hf g z).symm) (σE.linearMap g (f z) v))⟩ :
            TotalSpace Unit E'.Fiber) =
          ⟨g • j z, τE.linearMap g (j z) (a z v)⟩)
    (hb : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (z : Z) (v : F.Fiber (f z)),
        (⟨j (g • z), b (g • z)
          (cast (congrArg F.Fiber (hf g z).symm) (σF.linearMap g (f z) v))⟩ :
            TotalSpace Unit F'.Fiber) =
          ⟨g • j z, τF.linearMap g (j z) (b z v)⟩)
    {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
    {ν : Measure N} [IsSmoothPositiveMeasure (n := n) ν]
    {m m' : ℝ}
    (R : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m)
    (S : PseudodifferentialOperator (n := n) (r := E'.rank) (q := F'.rank)
      E'.Fiber F'.Fiber ν m')
    (hRS : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := E'.rank) E'.Fiber),
      (∀ᶠ z : Z in 𝓝ˢ K, v.val (j z) = a z (u.val (f z))) →
      ∀ z : Z, (S.toLinearMap v).val (j z) = b z ((R.toLinearMap u).val (f z)))
    (u : smoothSections (n := n) (r := E.rank) E.Fiber)
    (v : smoothSections (n := n) (r := E'.rank) E'.Fiber)
    (huv : ∀ᶠ z : Z in 𝓝ˢ K, v.val (j z) = a z (u.val (f z))) :
    ∀ z : Z, ((S.average IG τE τF hτE hτF).toLinearMap v).val (j z) =
      b z (((R.average IG σE σF hσE hσF).toLinearMap u).val (f z)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let : ∀ x, FiniteDimensional ℂ (F.Fiber x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x
  let : ∀ x, FiniteDimensional ℂ (F'.Fiber x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber x
  let ρE := σE.smoothSectionRepresentation IG hσE
  let ρF := σF.smoothSectionRepresentation IG hσF
  let ρE' := τE.smoothSectionRepresentation IG hτE
  let ρF' := τF.smoothSectionRepresentation IG hτF
  -- The same invariant germ is retained after inverse translation of both input sections.
  have hgerm (g : G) : ∀ᶠ z : Z in 𝓝ˢ K,
      (ρE' g⁻¹ v).val (j z) = a z ((ρE g⁻¹ u).val (f z)) := by
    have hmove : Tendsto (fun z : Z ↦ g • z) (𝓝ˢ K) (𝓝ˢ K) :=
      (Homeomorph.smul g).continuous.tendsto_nhdsSet (hKi g)
    filter_upwards [hmove.eventually huv] with z hz
    have h := section_transport_action IG f j hf hj E E' σE τE hσE hτE a ha
      g⁻¹ u v (g • z) hz
    exact (congrArg (fun w : Z ↦ (ρE' g⁻¹ v).val (j w) =
      a w ((ρE g⁻¹ u).val (f w))) (inv_smul_smul g z)).mp h
  -- The output transport intertwines the forward action in the same original fibers.
  have hconjugates (g : G) (z : Z) :
      (ρF' g (S.toLinearMap (ρE' g⁻¹ v))).val (j z) =
        b z ((ρF g (R.toLinearMap (ρE g⁻¹ u))).val (f z)) := by
    have houtputs := hRS (ρE g⁻¹ u) (ρE' g⁻¹ v) (hgerm g) (g⁻¹ • z)
    have h := section_transport_action IG f j hf hj F F' σF τF hσF hτF b hb
      g (R.toLinearMap (ρE g⁻¹ u)) (S.toLinearMap (ρE' g⁻¹ v)) (g⁻¹ • z) houtputs
    exact (congrArg (fun w : Z ↦ (ρF' g (S.toLinearMap (ρE' g⁻¹ v))).val (j w) =
      b w ((ρF g (R.toLinearMap (ρE g⁻¹ u))).val (f w))) (smul_inv_smul g z)).mp h
  -- The prescribed finite-dimensional fiber equivalence commutes with the Haar integral.
  intro z
  rw [S.average_apply IG τE τF hτE hτF, R.average_apply IG σE σF hσE hσF]
  change (∫ g : G, (ρF' g (S.toLinearMap (ρE' g⁻¹ v))).val (j z)
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts G))) =
    b z (∫ g : G, (ρF g (R.toLinearMap (ρE g⁻¹ u))).val (f z)
      ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)))
  simp_rw [hconjugates]
  exact (b z).toContinuousLinearEquiv.integral_comp_comm _

end AtiyahSinger
