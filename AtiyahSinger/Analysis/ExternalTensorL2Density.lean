/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Multiplication
public import AtiyahSinger.Analysis.SmoothProductApproximation
public import AtiyahSinger.Geometry.ExternalTensorSectionDecomposition

/-!
# Density of pure smooth sections in the geometric product L2 space

Public module ID: M0615.

Finite separated frame generators reduce the assertion to uniform approximation
of scalar coefficients. The original integral norm bound transfers that
approximation to L2, and the original completion of smooth sections supplies
the final density. The result applies to every smooth positive product-base
measure, without changing the specified tensor bundle or its metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

variable {n m r s : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

set_option maxHeartbeats 1200000 in
-- Finite frame reconstruction reduces the L2 comparison to separated scalar approximation.
/-- Original pure smooth sections span densely in the specified product-bundle L2 completion. -/
theorem dense_span_externalTensorL2 (ρ : Measure (M × N)) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    ∀ [IsSmoothPositiveMeasure (n := n + m) ρ]
      (g : SmoothHermitianMetric (n := n + m) (r := r * s) (externalTensorFiber E F)),
      Dense (Submodule.span ℂ (Set.range fun p :
        smoothSections (n := n) (r := r) E × smoothSections (n := m) (r := s) F ↦
        g.smoothToL2 ρ (externalTensorSection E F p.1 p.2)) :
          Set (g.L2SectionSpace ρ)) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  intro hρ g
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  -- Undo the fixed concatenation before applying the smooth product projections.
  have hproj :
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Prod.fst : M × N → M) ∧
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Prod.snd : M × N → N) := by
    let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
    let J := 𝓘(ℝ, P)
    let c := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
    let : ChartedSpace P (M × N) := prodChartedSpace _ M _ N
    have hid : ContMDiff I J ∞ (id : M × N → M × N) := by
      intro z
      apply contMDiffAt_iff.mpr
      refine ⟨continuousAt_id, ?_⟩
      have heq : writtenInExtChartAt I J z (id : M × N → M × N) =ᶠ[
          nhds (extChartAt I z z)] c.symm := by
        have hmem : c.symm (extChartAt I z z) ∈ (chartAt P z).target := by
          change c.symm (c ((chartAt P z) z)) ∈ (chartAt P z).target
          rw [c.symm_apply_apply]
          exact (chartAt P z).map_source (mem_chart_source P z)
        filter_upwards [((chartAt P z).open_target.preimage c.symm.continuous).mem_nhds hmem]
          with y hy
        change (chartAt P z) ((chartAt P z).symm (c.symm y)) = c.symm y
        exact (chartAt P z).right_inv hy
      exact (c.symm.contDiff.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt
    have hf : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (Prod.fst : M × N → M) := by
      simpa only [J, P, modelWithCornersSelf_prod] using
        (contMDiff_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    have hg : ContMDiff J 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (Prod.snd : M × N → N) := by
      simpa only [J, P, modelWithCornersSelf_prod] using
        (contMDiff_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞))
    exact ⟨hf.comp hid, hg.comp hid⟩
  let SM := {f : C(M, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ f}
  let SN := {f : C(N, ℂ) // ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℂ) ∞ f}
  let t (p : SM × SN) : C(M × N, ℂ) :=
    ⟨fun z ↦ p.1.val z.1 * p.2.val z.2,
      (p.1.val.continuous.comp continuous_fst).mul
        (p.2.val.continuous.comp continuous_snd)⟩
  have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
  have ht (p : SM × SN) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (t p) :=
    hmul.contMDiff.comp ((p.1.property.comp hproj.1).prodMk_space
      (p.2.property.comp hproj.2))
  let S : Submodule ℂ C(M × N, ℂ) := {
    carrier := {f | ContMDiff I 𝓘(ℝ, ℂ) ∞ f}
    zero_mem' := contMDiff_const
    add_mem' := by
      intro f k hf hk
      exact (show ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 + z.2) from contDiff_add)
        |>.contMDiff.comp (hf.prodMk_space hk)
    smul_mem' := by
      intro c f hf
      exact hmul.contMDiff.comp (contMDiff_const.prodMk_space hf) }
  let L := Submodule.span ℂ (Set.range t)
  have hLS : L ≤ S := Submodule.span_le.mpr (by rintro f ⟨p, rfl⟩; exact ht p)
  have hLdense : Dense (L : Set C(M × N, ℂ)) := dense_span_smooth_products
  have hSdense : DenseRange S.subtype := by
    have hd : Dense (S : Set C(M × N, ℂ)) := hLdense.mono hLS
    have heq : Set.range S.subtype = (S : Set C(M × N, ℂ)) := by
      ext f
      constructor
      · rintro ⟨k, rfl⟩
        exact k.property
      · intro hf
        exact ⟨⟨f, hf⟩, rfl⟩
    change Dense (Set.range S.subtype)
    rw [heq]
    exact hd
  let D := Submodule.span ℂ (Set.range fun p :
    smoothSections (n := n) (r := r) E × smoothSections (n := m) (r := s) F ↦
    g.smoothToL2 ρ (externalTensorSection E F p.1 p.2))
  let C := D.topologicalClosure
  -- A fixed pure section times any smooth coefficient is approximated by pure sections.
  have hcoeff (u : smoothSections (n := n) (r := r) E)
      (v : smoothSections (n := m) (r := s) F) (f : C(M × N, ℂ))
      (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) :
      g.smoothToL2 ρ (smoothSectionMul (externalTensorFiber E F) f hf
        (externalTensorSection E F u v)) ∈ C := by
    let w := externalTensorSection E F u v
    let T₀ : S →ₗ[ℂ] g.L2SectionSpace ρ := {
      toFun f := g.smoothToL2 ρ (smoothSectionMul (externalTensorFiber E F) f.val f.property w)
      map_add' f k := by
        rw [← map_add]
        apply congrArg (g.smoothToL2 ρ)
        apply Subtype.ext
        funext z
        exact add_smul (f.val z) (k.val z) (w.val z)
      map_smul' c f := by
        rw [← map_smul]
        apply congrArg (g.smoothToL2 ρ)
        apply Subtype.ext
        funext z
        exact mul_smul c (f.val z) (w.val z) }
    have hbound (f : S) : ‖T₀ f‖ ≤ ‖g.smoothToL2 ρ w‖ * ‖S.subtype f‖ := by
      change ‖g.smoothToL2 ρ (smoothSectionMul (externalTensorFiber E F) f.val f.property w)‖ ≤
        ‖g.smoothToL2 ρ w‖ * ‖f.val‖
      exact (g.norm_smoothToL2_mul_le ρ f.val f.property w).trans_eq
        (mul_comm ‖f.val‖ ‖g.smoothToL2 ρ w‖)
    let T := T₀.extendOfNorm S.subtype
    have hT (f : C(M × N, ℂ)) (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) :
        T f = g.smoothToL2 ρ (smoothSectionMul (externalTensorFiber E F) f hf w) :=
      T₀.extendOfNorm_eq hSdense ⟨‖g.smoothToL2 ρ w‖, hbound⟩ ⟨f, hf⟩
    have hall (f : C(M × N, ℂ)) : T f ∈ C := by
      refine hLdense.induction (P := fun f ↦ T f ∈ C) ?_ ?_ f
      · intro f hf
        induction hf using Submodule.span_induction with
        | mem f hf =>
          obtain ⟨p, rfl⟩ := hf
          rw [hT (t p) (ht p)]
          have heq : smoothSectionMul (externalTensorFiber E F) (t p) (ht p) w =
              externalTensorSection E F
                (smoothSectionMul E p.1.val p.1.property u)
                (smoothSectionMul F p.2.val p.2.property v) := by
            apply Subtype.ext
            funext z
            change (p.1.val z.1 * p.2.val z.2) • (u.val z.1 ⊗ₜ[ℂ] v.val z.2) =
              (p.1.val z.1 • u.val z.1) ⊗ₜ[ℂ] (p.2.val z.2 • v.val z.2)
            exact (TensorProduct.smul_tmul_smul _ _ _ _).symm
          rw [heq]
          exact D.le_topologicalClosure (Submodule.subset_span ⟨(_, _), rfl⟩)
        | zero => simpa only [map_zero] using C.zero_mem
        | add x y hx hy ihx ihy => simpa only [map_add] using C.add_mem ihx ihy
        | smul c x hx ih => simpa only [map_smul] using C.smul_mem c ih
      · exact D.isClosed_topologicalClosure.preimage T.continuous
    rw [← hT f hf]
    exact hall f
  -- The finite weighted factor frames reconstruct every original smooth product section.
  let A := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r) E)
  let B := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s) F)
  have hsmooth (w : smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F)) :
      g.smoothToL2 ρ w ∈ C := by
    obtain ⟨f, hf, hsum⟩ := exists_externalTensorSection_decomposition A B w
    let u (i : Fin A.size × Fin r) := A.weightedFrameSection i.1 (EuclideanSpace.single i.2 1)
    let v (j : Fin B.size × Fin s) := B.weightedFrameSection j.1 (EuclideanSpace.single j.2 1)
    let c (i : Fin A.size × Fin r) (j : Fin B.size × Fin s) : C(M × N, ℂ) :=
      ⟨f i j, (hf i j).continuous⟩
    have heq : w = ∑ i, ∑ j,
        smoothSectionMul (externalTensorFiber E F) (c i j) (hf i j)
          (externalTensorSection E F (u i) (v j)) := by
      apply Subtype.ext
      funext z
      simp only [Submodule.coe_sum, Finset.sum_apply]
      exact hsum z
    rw [heq, map_sum]
    apply Submodule.sum_mem C
    intro i _
    rw [map_sum]
    exact Submodule.sum_mem C (fun j _ ↦ hcoeff (u i) (v j) (c i j) (hf i j))
  -- Smooth sections themselves are dense in the exact integral completion under consideration.
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  refine (g.denseRange_smoothToL2 ρ).induction ?_ D.isClosed_topologicalClosure z
  rintro _ ⟨w, rfl⟩
  exact hsmooth w

end AtiyahSinger
