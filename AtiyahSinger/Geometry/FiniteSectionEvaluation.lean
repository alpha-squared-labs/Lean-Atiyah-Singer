/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.SmoothAtlasSections
public import AtiyahSinger.Topology.BundleTrivial

/-!
# Evaluation of a finite family of smooth sections

Public module ID: M1236.

A linear finite family of the original smooth sections defines a continuous
bundle map from the standard trivial bundle. Its joint evaluation is smooth
in every specified target chart, including the coefficient variable. This is
the evaluation map used to descend the actual finite kernel representation
over an associated sphere bundle (SG III.13.6).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Topology

attribute [local instance] trivialTopology

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

set_option backward.isDefEq.respectTransparency false in
/-- A finite family evaluates smoothly in the original bundle, jointly with its coefficients. -/
theorem exists_finiteSectionEvaluation (A : SmoothComplexBundleAtlas (n := n) E)
    (s : (Fin k → ℂ) →ₗ[ℂ] A.smoothSections) :
    ∃ f : Hom (Trivial M (Fin k → ℂ)) E,
      (∀ (x : M) (v : Fin k → ℂ), f.linearMap x v = (s v).val x) ∧
      ∀ i : A.Index,
        ContMDiffOn ((I).prod 𝓘(ℝ, Fin k → ℂ)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
          (fun z : M × (Fin k → ℂ) ↦ (A.chart i ⟨z.1, f.linearMap z.1 z.2⟩).2)
          ((A.chart i).baseSet ×ˢ Set.univ) := by
  classical
  let ev (x : M) : (Fin k → ℂ) →ₗ[ℂ] E x :=
    (LinearMap.proj x).comp (A.smoothSections.subtype.comp s)
  -- In each original frame, evaluation is the finite sum of its smooth columns.
  have hcoords (i : A.Index) :
      ContMDiffOn ((I).prod 𝓘(ℝ, Fin k → ℂ)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun z : M × (Fin k → ℂ) ↦ (A.chart i ⟨z.1, ev z.1 z.2⟩).2)
        ((A.chart i).baseSet ×ˢ Set.univ) := by
    have hs : ContMDiffOn ((I).prod 𝓘(ℝ, Fin k → ℂ))
        𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun z : M × (Fin k → ℂ) ↦
          ∑ j, z.2 j • (A.chart i ⟨z.1, (s (Pi.single j 1)).val z.1⟩).2)
        ((A.chart i).baseSet ×ˢ Set.univ) := by
      apply contMDiffOn_finsetSum
      intro j _
      have hfst : ContMDiffOn ((I).prod 𝓘(ℝ, Fin k → ℂ)) I ∞
          (Prod.fst : M × (Fin k → ℂ) → M)
          ((A.chart i).baseSet ×ˢ Set.univ) := contMDiff_fst.contMDiffOn
      have hc := ((s (Pi.single j 1)).property i).comp
        hfst
        (fun z (hz : z ∈ (A.chart i).baseSet ×ˢ Set.univ) ↦ hz.1)
      have hv : ContMDiff ((I).prod 𝓘(ℝ, Fin k → ℂ)) 𝓘(ℝ, ℂ) ∞
          (fun z : M × (Fin k → ℂ) ↦ z.2 j) :=
        (contMDiff_pi_space.mp contMDiff_snd j)
      have hmul : ContDiff ℝ ∞
          (fun z : ℂ × (Fin (A.rank i) → ℂ) ↦ z.1 • z.2) := contDiff_smul
      exact hmul.contMDiff.comp_contMDiffOn (hv.contMDiffOn.prodMk_space hc)
    apply hs.congr
    intro z hz
    let L := (A.frameLinearEquiv i z.1 hz.1).toLinearMap.comp (ev z.1)
    have he := congrArg L ((Pi.basisFun ℂ (Fin k)).sum_repr z.2)
    change L z.2 = ∑ j, z.2 j • L (Pi.single j 1)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using he.symm
  -- These local coordinates prove continuity in the unchanged total topology.
  have hc : Continuous (fun z : M × (Fin k → ℂ) ↦
      (⟨z.1, ev z.1 z.2⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨i, hi⟩ := A.covers z.1
    have hlocal := (hcoords i).continuousOn.continuousAt
      (((A.chart i).open_baseSet.prod isOpen_univ).mem_nhds ⟨hi, Set.mem_univ _⟩)
    apply (A.chart i).continuousAt_of_comp_left continuous_fst.continuousAt hi
    apply (continuous_fst.continuousAt.prodMk hlocal).congr_of_eventuallyEq
    filter_upwards [(A.chart i).open_baseSet.preimage continuous_fst |>.mem_nhds hi]
      with w hw
    exact Prod.ext ((A.chart i).proj_toFun ⟨w.1, ev w.1 w.2⟩
      ((A.chart i).mem_source.mpr hw)) rfl
  let f : Hom (Trivial M (Fin k → ℂ)) E :=
    { linearMap := ev
      continuous_total := by
        have hprod : Continuous (fun z : TotalSpace Unit (Trivial M (Fin k → ℂ)) ↦
            (z.proj, z.snd)) := continuous_induced_dom
        exact hc.comp hprod }
  exact ⟨f, fun _ _ ↦ rfl, hcoords⟩

end AtiyahSinger
