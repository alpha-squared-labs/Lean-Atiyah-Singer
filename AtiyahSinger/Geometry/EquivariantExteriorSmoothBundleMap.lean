/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleMapAverage
public import AtiyahSinger.Geometry.ExteriorSmoothBundleMap
public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Topology.EquivariantSupportCutoff
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth equivariant extension of a prescribed exterior bundle map

Public module ID: M1188.

Extend an exterior map smoothly, choose an invariant compact exception, and
average with normalized Haar measure. Outside that invariant exception every
integrand is the same original exterior map, so the extension retains it
exactly. Neither compactness of the base nor equality of bundle ranks is used.

This is the relative compact-group averaging supplement needed for analytic
excision. It combines the ordinary buffered extension with the original smooth
bundle-map average; no exterior index equality is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle MeasureTheory TopologicalSpace Topology
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hE hF hG hGC hGT hAction hσE hσF

/-- A smooth equivariant exterior map extends after enlarging its compact exception invariantly. -/
theorem exists_smooth_equivariant_extension_of_exterior (U : Opens M)
    (hUi : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U)
    (K : Set M) (hK : IsCompact K) (hKU : Kᶜ ⊆ (U : Set M))
    (a : ∀ x : U, E x.val →L[ℂ] F x.val)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E))
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F))
      (fun x ↦ (a x).toLinearMap))
    (haEq : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : U) (v : E x.val),
        a ⟨g • x.val, (hUi g x.val).mpr x.property⟩ (σE.linearMap g x.val v) =
          σF.linearMap g x.val (a x v)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ L : Set M, IsCompact L ∧ K ⊆ interior L ∧
      (∀ (g : G) (x : M), g • x ∈ L ↔ x ∈ L) ∧
      ∃ c : Hom E F,
        IsSmoothBundleMap (n := n) (r := r) (q := q) c.linearMap ∧
        c.IsEquivariant σE σF ∧
        ∀ (x : U), x.val ∉ L → ∀ v : E x.val, c.linearMap x.val v = a x v := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  -- The ordinary extension is retained on the complement of its compact exception.
  obtain ⟨L₀, hL₀, hKL₀, c₀, hc₀, hc₀a⟩ :=
    exists_smoothBundleMap_extension_of_exterior U K hK hKU a ha
  let d : Hom E F := ⟨fun x ↦ (c₀ x).toLinearMap, hc₀.continuous_total⟩
  obtain ⟨W, hW, hL₀W, _hWi, L, hL, hWL, hLi, _, _, _, _⟩ :=
    exists_invariant_time_cutoff (G := G) L₀ hL₀
  have hL₀L : L₀ ⊆ L := hL₀W.trans hWL
  have hKL : K ⊆ interior L :=
    (hKL₀.trans interior_subset).trans (hL₀W.trans (interior_maximal hWL hW))
  let c := d.equivariantAverage σE σF
  refine ⟨L, hL, hKL, hLi, c,
    d.isSmoothBundleMap_equivariantAverage σE σF IG hσE hσF hc₀,
    d.isEquivariant_equivariantAverage σE σF, ?_⟩
  intro x hx v
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  rw [Hom.equivariantAverage_apply]
  -- Invariance keeps the entire orbit in the region where the old extension equals a.
  have hterm (g : G) : (smul_inv_smul g x.val) ▸
      (σF.linearMap g (g⁻¹ • x.val)
        (d.linearMap (g⁻¹ • x.val) (σE.linearMap g⁻¹ x.val v))) = a x v := by
    let xg : U := ⟨g⁻¹ • x.val, (hUi g⁻¹ x.val).mpr x.property⟩
    have hxg : xg.val ∉ L₀ := fun h₀ ↦ hx ((hLi g⁻¹ x.val).mp (hL₀L h₀))
    have hdvalue : d.linearMap xg.val (σE.linearMap g⁻¹ x.val v) =
        a xg (σE.linearMap g⁻¹ x.val v) :=
      congrArg (fun A : E xg.val →L[ℂ] F xg.val ↦ A (σE.linearMap g⁻¹ x.val v))
        (hc₀a xg hxg)
    apply TotalSpace.mk_injective (F := Unit) x.val
    calc
      (⟨x.val, (smul_inv_smul g x.val) ▸ (σF.linearMap g (g⁻¹ • x.val)
        (d.linearMap (g⁻¹ • x.val) (σE.linearMap g⁻¹ x.val v)))⟩ : TotalSpace Unit F) =
          g • (⟨xg.val, d.linearMap xg.val (σE.linearMap g⁻¹ x.val v)⟩ :
            TotalSpace Unit F) := by
              change (⟨x.val, (smul_inv_smul g x.val) ▸
                (σF.linearMap g (g⁻¹ • x.val)
                  (d.linearMap (g⁻¹ • x.val) (σE.linearMap g⁻¹ x.val v)))⟩ :
                    TotalSpace Unit F) =
                ⟨g • (g⁻¹ • x.val), σF.linearMap g (g⁻¹ • x.val)
                  (d.linearMap (g⁻¹ • x.val) (σE.linearMap g⁻¹ x.val v))⟩
              simpa only [eqRec_eq_cast] using (TotalSpace.mk_cast (F := Unit)
                (smul_inv_smul g x.val) (σF.linearMap g (g⁻¹ • x.val)
                  (d.linearMap (g⁻¹ • x.val) (σE.linearMap g⁻¹ x.val v))))
      _ = g • (g⁻¹ • (⟨x.val, a x v⟩ : TotalSpace Unit F)) := by
        rw [hdvalue, haEq g⁻¹ x v]
        rfl
      _ = _ := smul_inv_smul g _
  change (∫ g : G, _ ∂μ) = _
  simp_rw [hterm]
  simp

end AtiyahSinger.ComplexBundle
