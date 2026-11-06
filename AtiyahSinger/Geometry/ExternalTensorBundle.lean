/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Geometry.HermitianMetric
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ModelBundleTopology
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

import AtiyahSinger.Geometry.NativeSmoothAtlas
import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# The original external tensor bundle with its smooth product metric

Public module ID: M1228.

UL01 uses the fibers E_x tensor F_y on the original product manifold. Their
total topology is the existing pullback/tensor topology, transported only
across the phantom model parameter. Auxiliary norms are put on these new
tensor fibers using the original factor chart equivalences; no factor norm
or factor topology is changed. The selected native atlas and its smoothness
certificates come from one tensor-chart existence witness.

The product metric is specified by its exact pairing on every pair of pure
tensors. It uses the two supplied smooth metrics, independently of auxiliary
coordinate norms. Sources: SG III.13.5, pp.249--250, for the geometric external
product; SG II.3 and Appendix A for associated tensor constructions, and
Hatcher, Vector Bundles and K-Theory, pp.13--15, for tensor bundle charts.
The explicit native-model bookkeeping is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n m r s : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  (E : M → Type*) (F : N → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]

/-- The standard external tensor fibers, with their original algebraic tensor vectors. -/
abbrev externalTensorFiber (z : M × N) : Type _ := E z.1 ⊗[ℂ] F z.2

/-- Original chart equivalences provide auxiliary coordinates on each new tensor fiber. -/
def externalTensorFiberCoordinates (z : M × N) :
    externalTensorFiber E F z ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin r) ⊗[ℂ] EuclideanSpace ℂ (Fin s)) :=
  TensorProduct.congr
    (VectorBundle.continuousLinearEquivAt ℂ (EuclideanSpace ℂ (Fin r)) E z.1).toLinearEquiv
    (VectorBundle.continuousLinearEquivAt ℂ (EuclideanSpace ℂ (Fin s)) F z.2).toLinearEquiv

/-- Auxiliary coordinate norms on the new tensor fibers, without changing either factor norm. -/
@[instance_reducible]
def externalTensorFiberNormedAddCommGroup :
    ∀ z : M × N, NormedAddCommGroup (externalTensorFiber E F z) :=
  fun z ↦ NormedAddCommGroup.induced _ _ (externalTensorFiberCoordinates (r := r) (s := s) E F z)
    (externalTensorFiberCoordinates (r := r) (s := s) E F z).injective

/-- Complex normed scalar multiplication for those same tensor coordinate norms. -/
@[instance_reducible]
def externalTensorFiberNormedSpace :
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    ∀ z : M × N, NormedSpace ℂ (externalTensorFiber E F z) :=
  letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  fun z ↦ NormedSpace.induced ℂ _ _ (externalTensorFiberCoordinates (r := r) (s := s) E F z)

/-- Retype the existing pullback/tensor total topology to its native product-rank model. -/
@[instance_reducible]
def externalTensorTopology :
    TopologicalSpace
      (TotalSpace (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)) := by
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin s)) F
  letI : TopologicalSpace (TotalSpace Unit (externalTensorFiber E F)) :=
    ComplexBundle.tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F)
  exact TopologicalSpace.induced
    (fun z : TotalSpace (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit (externalTensorFiber E F))) inferInstance

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := m) (r := s) F]

include hE hF

/-- The standard product tensor charts supply one native smooth bundle and pure sections. -/
theorem exists_externalTensorBundle :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    ∃ hB : FiberBundle (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F),
      letI := hB
      ∃ hV : VectorBundle ℂ (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F),
        letI := hV
        IsSmoothComplexBundle (n := n + m) (r := r * s) (externalTensorFiber E F) ∧
          (∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
              (π (EuclideanSpace ℂ (Fin r)) E)), MemTrivializationAtlas e →
            ∀ (f : Trivialization (EuclideanSpace ℂ (Fin s))
              (π (EuclideanSpace ℂ (Fin s)) F)), MemTrivializationAtlas f →
              ∃ t : Trivialization (EuclideanSpace ℂ (Fin (r * s)))
                  (π (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)),
                MemTrivializationAtlas t ∧ t.baseSet = e.baseSet ×ˢ f.baseSet ∧
                  ∀ (z : M × N), z ∈ e.baseSet ×ˢ f.baseSet →
                    ∀ (a : E z.1) (b : F z.2) (i : Fin r) (j : Fin s),
                      (t ⟨z, a ⊗ₜ[ℂ] b⟩).2 (finProdFinEquiv (i, j)) =
                        (e ⟨z.1, a⟩).2 i * (f ⟨z.2, b⟩).2 j) ∧
          ∀ (u : smoothSections (n := n) (r := r) E)
            (v : smoothSections (n := m) (r := s) F),
            IsSmoothSection (n := n + m) (r := r * s) (externalTensorFiber E F)
              (fun z ↦ u.val z.1 ⊗ₜ[ℂ] v.val z.2) := by
  /- Stage 1: pull the original factor charts back along the two projections.
  Their tensor charts use the standard tensor basis, ordered by finProdFinEquiv,
  and Euclidean coordinates of dimension r*s. The existing tensor topology
  makes these charts genuine local homeomorphisms. Retyping keeps every base
  point and tensor vector; coordinate norms on individual fibers are equivalent
  to these finite-dimensional chart norms, even at zero rank.
  Stage 2: choose the atlas generated by these product tensor charts and
  retain every original chart pair, its exact product base set and its pure
  coordinate formula in the same witness. Its
  transitions are the tensor products of the two original transitions, hence
  their matrix entries are products of the original smooth coefficients.
  Compose base coordinates with the fixed Euclidean concatenation used by
  euclideanProductChartedSpace. This supplies the native complex bundle and
  its smoothness for precisely the selected atlas and unchanged total topology.
  Stage 3: in these same charts the pure section has coordinates u_i(x)*v_j(y).
  These functions are smooth; compatible chart changes preserve the property.
  No compactness, global frame, equal ranks, nonempty base, or positive rank
  is needed. No geometric L2 identification is assumed in this construction. -/
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin s)) F
  let : TopologicalSpace (TotalSpace Unit (externalTensorFiber E F)) :=
    ComplexBundle.tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F)
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := m) (r := s) F
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  -- The projections are smooth for the specified concatenated charts, without a manifold axiom.
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
          with w hw
        change (chartAt P z) ((chartAt P z).symm (c.symm w)) = c.symm w
        exact (chartAt P z).right_inv hw
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
  -- Pull back the actual native charts and their transition columns along each projection.
  let : TopologicalSpace (TotalSpace Unit (Prod.fst *ᵖ E)) :=
    Pullback.TotalSpace.topologicalSpace Unit E (Prod.fst : M × N → M)
  let : TopologicalSpace (TotalSpace Unit (Prod.snd *ᵖ F)) :=
    Pullback.TotalSpace.topologicalSpace Unit F (Prod.snd : M × N → N)
  let : TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) (Prod.fst *ᵖ E)) :=
    Pullback.TotalSpace.topologicalSpace (EuclideanSpace ℂ (Fin r)) E (Prod.fst : M × N → M)
  let : TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) (Prod.snd *ᵖ F)) :=
    Pullback.TotalSpace.topologicalSpace (EuclideanSpace ℂ (Fin s)) F (Prod.snd : M × N → N)
  let HE : TotalSpace Unit (Prod.fst *ᵖ E) ≃ₜ
      TotalSpace (EuclideanSpace ℂ (Fin r)) (Prod.fst *ᵖ E) := {
    toEquiv := ComplexBundle.unitTotalEquiv (EuclideanSpace ℂ (Fin r)) (Prod.fst *ᵖ E)
    continuous_toFun := by
      apply (inducing_pullbackTotalSpaceEmbedding (EuclideanSpace ℂ (Fin r)) E
        (ContinuousMap.fst : C(M × N, M))).continuous_iff.mpr
      exact (Pullback.continuous_proj Unit E (ContinuousMap.fst : C(M × N, M))).prodMk
        ((ComplexBundle.unitTotalHomeomorph (EuclideanSpace ℂ (Fin r)) E).continuous.comp
          (Pullback.continuous_lift Unit E (ContinuousMap.fst : C(M × N, M))))
    continuous_invFun := by
      apply (inducing_pullbackTotalSpaceEmbedding Unit E
        (ContinuousMap.fst : C(M × N, M))).continuous_iff.mpr
      exact (Pullback.continuous_proj (EuclideanSpace ℂ (Fin r)) E
        (ContinuousMap.fst : C(M × N, M))).prodMk
        ((ComplexBundle.unitTotalHomeomorph (EuclideanSpace ℂ (Fin r)) E).symm.continuous.comp
          (Pullback.continuous_lift (EuclideanSpace ℂ (Fin r)) E
            (ContinuousMap.fst : C(M × N, M)))) }
  let HF : TotalSpace Unit (Prod.snd *ᵖ F) ≃ₜ
      TotalSpace (EuclideanSpace ℂ (Fin s)) (Prod.snd *ᵖ F) := {
    toEquiv := ComplexBundle.unitTotalEquiv (EuclideanSpace ℂ (Fin s)) (Prod.snd *ᵖ F)
    continuous_toFun := by
      apply (inducing_pullbackTotalSpaceEmbedding (EuclideanSpace ℂ (Fin s)) F
        (ContinuousMap.snd : C(M × N, N))).continuous_iff.mpr
      exact (Pullback.continuous_proj Unit F (ContinuousMap.snd : C(M × N, N))).prodMk
        ((ComplexBundle.unitTotalHomeomorph (EuclideanSpace ℂ (Fin s)) F).continuous.comp
          (Pullback.continuous_lift Unit F (ContinuousMap.snd : C(M × N, N))))
    continuous_invFun := by
      apply (inducing_pullbackTotalSpaceEmbedding Unit F
        (ContinuousMap.snd : C(M × N, N))).continuous_iff.mpr
      exact (Pullback.continuous_proj (EuclideanSpace ℂ (Fin s)) F
        (ContinuousMap.snd : C(M × N, N))).prodMk
        ((ComplexBundle.unitTotalHomeomorph (EuclideanSpace ℂ (Fin s)) F).symm.continuous.comp
          (Pullback.continuous_lift (EuclideanSpace ℂ (Fin s)) F
            (ContinuousMap.snd : C(M × N, N)))) }
  let ae (i : A.Index) : Trivialization (Fin r → ℂ) (π Unit (Prod.fst *ᵖ E)) :=
    ((i.val.pullback (ContinuousMap.fst : C(M × N, M))).compHomeomorph HE)
      |>.transFiberHomeomorph (EuclideanSpace.equiv (Fin r) ℂ).toHomeomorph
  let bf (j : B.Index) : Trivialization (Fin s → ℂ) (π Unit (Prod.snd *ᵖ F)) :=
    ((j.val.pullback (ContinuousMap.snd : C(M × N, N))).compHomeomorph HF)
      |>.transFiberHomeomorph (EuclideanSpace.equiv (Fin s) ℂ).toHomeomorph
  let A' : SmoothComplexBundleAtlas (n := n + m) (Prod.fst *ᵖ E) := {
    Index := A.Index
    rank := A.rank
    chart := ae
    covers := fun z ↦ A.covers z.1
    linear := fun i z hz ↦ A.linear i z.1 hz
    contMDiffOn_coordChange := by
      intro i j a
      refine ((A.contMDiffOn_coordChange i j a).comp hproj.1.contMDiffOn
        (fun z hz ↦ hz)).congr ?_
      intro z hz
      change (EuclideanSpace.equiv (Fin r) ℂ)
        (j.val ⟨z.1, i.val.symm z.1
          ((EuclideanSpace.equiv (Fin r) ℂ).symm (Pi.single a 1))⟩).2 = _
      rw [i.val.mk_symm hz.1]
      rfl }
  let B' : SmoothComplexBundleAtlas (n := n + m) (Prod.snd *ᵖ F) := {
    Index := B.Index
    rank := B.rank
    chart := bf
    covers := fun z ↦ B.covers z.2
    linear := fun j z hz ↦ B.linear j z.2 hz
    contMDiffOn_coordChange := by
      intro i j a
      refine ((B.contMDiffOn_coordChange i j a).comp hproj.2.contMDiffOn
        (fun z hz ↦ hz)).congr ?_
      intro z hz
      change (EuclideanSpace.equiv (Fin s) ℂ)
        (j.val ⟨z.2, i.val.symm z.2
          ((EuclideanSpace.equiv (Fin s) ℂ).symm (Pi.single a 1))⟩).2 = _
      rw [i.val.mk_symm hz.1]
      rfl }
  let : TopologicalSpace (TotalSpace Unit
      (fun z : M × N ↦ (Prod.fst *ᵖ E) z ⊗[ℂ] (Prod.snd *ᵖ F) z)) :=
    ComplexBundle.tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F)
  let C := tensorSmoothAtlas A' B'
  let K := EuclideanSpace ℂ (Fin (r * s))
  let c := EuclideanSpace.equiv (Fin (r * s)) ℂ
  let H : TotalSpace K (externalTensorFiber E F) ≃ₜ
      TotalSpace Unit (externalTensorFiber E F) :=
    (ComplexBundle.unitTotalEquiv K (externalTensorFiber E F)).symm.toHomeomorphOfIsInducing
      ⟨rfl⟩
  let t (p : A.Index × B.Index) : Trivialization K (π K (externalTensorFiber E F)) :=
    ((C.chart p).compHomeomorph H).transFiberHomeomorph c.symm.toHomeomorph
  have hbase (p : A.Index × B.Index) :
      (t p).baseSet = p.1.val.baseSet ×ˢ p.2.val.baseSet :=
    (ComplexBundle.exists_tensor_trivialization (A'.chart p.1) (B'.chart p.2)
      (A'.linear p.1) (B'.linear p.2)).choose_spec.1
  let (p : A.Index × B.Index) : (t p).IsLinear ℂ := {
    linear := by
      intro z hz
      change IsLinearMap ℂ (fun v ↦ c.symm (C.chart p ⟨z, v⟩).2)
      exact (c.symm.toLinearMap.comp ((C.linear p z hz).mk' _)).isLinear }
  have hcover (z : M × N) : ∃ p : A.Index × B.Index, z ∈ (t p).baseSet := C.covers z
  have hpure (p : A.Index × B.Index) (z : M × N)
      (hz : z ∈ p.1.val.baseSet ×ˢ p.2.val.baseSet) (a : E z.1) (b : F z.2)
      (i : Fin r) (j : Fin s) :
      (t p ⟨z, a ⊗ₜ[ℂ] b⟩).2 (finProdFinEquiv (i, j)) =
        (p.1.val ⟨z.1, a⟩).2 i * (p.2.val ⟨z.2, b⟩).2 j := by
    exact (ComplexBundle.exists_tensor_trivialization (A'.chart p.1) (B'.chart p.2)
      (A'.linear p.1) (B'.linear p.2)).choose_spec.2.2 z hz a b i j
  -- Each fiber chart is a homeomorphism for the prescribed finite-dimensional fiber norm.
  have hinducing (z : M × N) :
      Topology.IsInducing (@TotalSpace.mk (M × N) K (externalTensorFiber E F) z) := by
    obtain ⟨p, hp⟩ := hcover z
    let : FiniteDimensional ℂ (E z.1) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E z.1
    let : FiniteDimensional ℂ (F z.2) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin s)) F z.2
    let L := ((t p).linearEquivAt ℂ z hp).toContinuousLinearEquiv
    have hs (v : externalTensorFiber E F z) :
        (⟨z, v⟩ : TotalSpace K (externalTensorFiber E F)) ∈ (t p).source :=
      (t p).mem_source.mpr hp
    have hc : Continuous (@TotalSpace.mk (M × N) K (externalTensorFiber E F) z) := by
      rw [(t p).toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
        (Set.eq_univ_of_forall hs)]
      apply ((continuous_const (y := z)).prodMk L.continuous).congr
      intro v
      have hv : t p ⟨z, v⟩ = (z, L v) :=
        Prod.ext ((t p).proj_toFun _ (hs v)) rfl
      exact hv.symm
    apply Topology.IsInducing.of_codRestrict hs
    have htc : Continuous (fun w : (t p).source ↦ t p w.val) :=
      continuousOn_iff_continuous_domRestrict.mp (t p).toOpenPartialHomeomorph.continuousOn
    apply Topology.IsInducing.of_comp (hc.codRestrict hs) htc
    have heq : (t p ∘ @TotalSpace.mk (M × N) K (externalTensorFiber E F) z) =
        (Prod.mk z ∘ L) := by
      funext v
      exact Prod.ext ((t p).proj_toFun _ (hs v)) rfl
    change Topology.IsInducing (t p ∘ @TotalSpace.mk (M × N) K (externalTensorFiber E F) z)
    rw [heq]
    exact (isInducing_prodMkRight z).comp L.toHomeomorph.isInducing
  let hB : FiberBundle K (externalTensorFiber E F) := {
    totalSpaceMk_isInducing' := hinducing
    trivializationAtlas' := Set.range t
    trivializationAt' := fun z ↦ t (hcover z).choose
    mem_baseSet_trivializationAt' := fun z ↦ (hcover z).choose_spec
    trivialization_mem_atlas' := fun z ↦ ⟨(hcover z).choose, rfl⟩ }
  let := hB
  -- Smooth tensor columns determine the operator-valued native coordinate changes.
  have htrans (p q : A.Index × B.Index) :
      ContMDiffOn I 𝓘(ℝ, K →L[ℂ] K) ∞
        (fun z ↦ ((t p).coordChangeL ℂ (t q) z : K →L[ℂ] K))
        ((t p).baseSet ∩ (t q).baseSet) := by
    let L := (c.arrowCongr (ContinuousLinearEquiv.refl ℂ K)).trans
      (ContinuousLinearEquiv.piRing (𝕜 := ℂ) (E := K) (Fin (r * s)))
    have hcols : ContMDiffOn I 𝓘(ℝ, Fin (r * s) → K) ∞
        (fun z ↦ L ((t p).coordChangeL ℂ (t q) z : K →L[ℂ] K))
        ((t p).baseSet ∩ (t q).baseSet) := by
      apply contMDiffOn_pi_space.mpr
      intro a
      have hc := (c.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
        (n := ∞) |>.comp_contMDiffOn (C.contMDiffOn_coordChange p q a)
      refine hc.congr ?_
      intro z hz
      change ((t p).coordChangeL ℂ (t q) z) (c.symm (Pi.single a 1)) = _
      rw [(t p).coordChangeL_apply' (t q) hz]
      change c.symm ((C.chart q)
        ((C.chart p).toPartialEquiv.symm (z, c (c.symm (Pi.single a 1))))).2 = _
      rw [c.apply_symm_apply]
      rfl
    apply ((L.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      (n := ∞) |>.comp_contMDiffOn hcols).congr
    intro z hz
    exact (L.symm_apply_apply _).symm
  let hV : VectorBundle ℂ K (externalTensorFiber E F) := {
    trivialization_linear' := by
      rintro _ ⟨p, rfl⟩
      infer_instance
    continuousOn_coordChange' := by
      rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
      exact (htrans p q).continuousOn }
  let := hV
  refine ⟨hB, hV, ⟨?_, ?_, ?_⟩⟩
  · constructor
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact htrans p q
  · intro e he f hf
    exact ⟨t (⟨e, he⟩, ⟨f, hf⟩), ⟨(⟨e, he⟩, ⟨f, hf⟩), rfl⟩,
      hbase (⟨e, he⟩, ⟨f, hf⟩), hpure (⟨e, he⟩, ⟨f, hf⟩)⟩
  · intro u v
    let u' : A'.smoothSections := ⟨fun z ↦ u.val z.1, by
      intro i
      exact ((isSmoothSection_nativeSmoothComplexBundleAtlas_iff
        (n := n) (r := r) E u.val).mpr u.property i).comp
          hproj.1.contMDiffOn (fun z hz ↦ hz)⟩
    let v' : B'.smoothSections := ⟨fun z ↦ v.val z.2, by
      intro j
      exact ((isSmoothSection_nativeSmoothComplexBundleAtlas_iff
        (n := m) (r := s) F v.val).mpr v.property j).comp
          hproj.2.contMDiffOn (fun z hz ↦ hz)⟩
    rintro _ ⟨p, rfl⟩
    exact (c.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      (n := ∞) |>.comp_contMDiffOn (isSmoothSection_tensor A' B' u' v' p)

/-- The native fiber atlas selected from the single product tensor-chart witness. -/
@[reducible]
def externalTensorFiberBundle :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    FiberBundle (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) :=
  (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F).choose

set_option linter.defProp false in
/-- Fiberwise linearity belongs to the same selected native tensor atlas. -/
@[reducible]
def externalTensorVectorBundle :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    VectorBundle ℂ (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) :=
  (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F).choose_spec.choose

set_option linter.defProp false in
/-- The selected actual native tensor atlas has smooth transition functions. -/
@[reducible]
def externalTensorIsSmoothComplexBundle :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    IsSmoothComplexBundle (n := n + m) (r := r * s) (externalTensorFiber E F) :=
  (exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F).choose_spec.choose_spec.1

/-- The actual smooth external tensor section has pointwise value u(x) tensor v(y). -/
def externalTensorSection (u : smoothSections (n := n) (r := r) E)
    (v : smoothSections (n := m) (r := s) F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F) :=
  let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  ⟨fun z ↦ u.val z.1 ⊗ₜ[ℂ] v.val z.2, result.choose_spec.choose_spec.2.2 u v⟩

variable {E F}
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := m) (r := s) F)

/-- The product of the two specified forms defines the unique smooth tensor metric. -/
theorem existsUnique_externalTensorMetric :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    ∃! l : SmoothHermitianMetric (n := n + m) (r := r * s) (externalTensorFiber E F),
      ∀ (z : M × N) (a c : E z.1) (b d : F z.2),
        l.pairing z (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
          h.pairing z.1 a c * k.pairing z.2 b d := by
  /- Stage 1: extend the displayed product pairing sesquilinearly through the
  actual algebraic tensor relations. At each point orthonormal bases for the
  two positive forms give an orthonormal tensor basis, proving positivity and
  definiteness, including the zero-dimensional tensor space.
  Stage 2: in the selected product tensor charts the Gram matrix is the
  Kronecker product of the two original smooth Gram matrices. Its entries
  are smooth on each actual overlap, giving a SmoothHermitianMetric for the
  same native atlas. The auxiliary tensor norm is left unchanged.
  Stage 3: pure tensors span every fiber. Sesquilinearity therefore determines
  the whole pairing from this formula; the remaining core and smoothness
  fields are proof-irrelevant, giving uniqueness of the metric data. -/
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let T := externalTensorFiber E F
  let K := EuclideanSpace ℂ (Fin (r * s))
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  -- The temporary factor norms construct only the positive algebraic core, not a new bundle norm.
  let core (z : M × N) : InnerProductSpace.Core ℂ (T z) := by
    set_option backward.isDefEq.respectTransparency false in
      let ce := h.toCore z.1
      let cf := k.toCore z.2
      let me : Module ℂ (E z.1) := inferInstance
      let mf : Module ℂ (F z.2) := inferInstance
      let : NormedAddCommGroup (E z.1) := ce.toNormedAddCommGroup
      let : Module ℂ (E z.1) := me
      let : InnerProductSpace ℂ (E z.1) := InnerProductSpace.ofCore ce.toCore
      let : NormedAddCommGroup (F z.2) := cf.toNormedAddCommGroup
      let : Module ℂ (F z.2) := mf
      let : InnerProductSpace ℂ (F z.2) := InnerProductSpace.ofCore cf.toCore
      let : NormedAddCommGroup (E z.1 ⊗[ℂ] F z.2) := TensorProduct.instNormedAddCommGroup
      let : InnerProductSpace ℂ (E z.1 ⊗[ℂ] F z.2) := TensorProduct.instInnerProductSpace
      exact InnerProductSpace.toCore (𝕜 := ℂ) (E := E z.1 ⊗[ℂ] F z.2)
  have hpure (z : M × N) (a c : E z.1) (b d : F z.2) :
      (core z).inner (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
        h.pairing z.1 a c * k.pairing z.2 b d := by
    rfl
  -- This full-model identity comparison needs no compatibility axiom for other base charts.
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
          with w hw
        change (chartAt P z) ((chartAt P z).symm (c.symm w)) = c.symm w
        exact (chartAt P z).right_inv hw
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
  -- A pure-coordinate chart sends the tensor of the original inverse-frame vectors to one basis.
  have hproduct
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (f : Trivialization (EuclideanSpace ℂ (Fin s))
        (π (EuclideanSpace ℂ (Fin s)) F)) [MemTrivializationAtlas f]
      (t : Trivialization K (π K T)) [MemTrivializationAtlas t]
      (htbase : t.baseSet = e.baseSet ×ˢ f.baseSet)
      (htpure : ∀ (z : M × N), z ∈ e.baseSet ×ˢ f.baseSet →
        ∀ (a : E z.1) (b : F z.2) (i : Fin r) (j : Fin s),
          (t ⟨z, a ⊗ₜ[ℂ] b⟩).2 (finProdFinEquiv (i, j)) =
            (e ⟨z.1, a⟩).2 i * (f ⟨z.2, b⟩).2 j)
      (a b : Fin (r * s)) :
      ContMDiffOn I 𝓘(ℝ, ℂ) ∞
        (fun z ↦ (core z).inner (t.symmL ℂ z (EuclideanSpace.single a 1))
          (t.symmL ℂ z (EuclideanSpace.single b 1))) t.baseSet := by
    have hframe (z : M × N) (hz : z ∈ t.baseSet) (a : Fin (r * s)) :
        t.symmL ℂ z (EuclideanSpace.single a 1) =
          e.symmL ℂ z.1 (EuclideanSpace.single (finProdFinEquiv.symm a).1 1) ⊗ₜ[ℂ]
            f.symmL ℂ z.2 (EuclideanSpace.single (finProdFinEquiv.symm a).2 1) := by
      have hze : z.1 ∈ e.baseSet := ((htbase ▸ hz) : z ∈ e.baseSet ×ˢ f.baseSet).1
      have hzf : z.2 ∈ f.baseSet := ((htbase ▸ hz) : z ∈ e.baseSet ×ˢ f.baseSet).2
      have he (i : Fin r) :
          (e ⟨z.1, e.symmL ℂ z.1 (EuclideanSpace.single i 1)⟩).2 =
            EuclideanSpace.single i 1 := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hze]
        exact e.continuousLinearMapAt_symmL hze _
      have hf (j : Fin s) :
          (f ⟨z.2, f.symmL ℂ z.2 (EuclideanSpace.single j 1)⟩).2 =
            EuclideanSpace.single j 1 := by
        rw [← f.continuousLinearMapAt_apply_of_mem ℂ hzf]
        exact f.continuousLinearMapAt_symmL hzf _
      apply (t.continuousLinearEquivAt ℂ z hz).injective
      have hleft : (t ⟨z, t.symmL ℂ z (EuclideanSpace.single a 1)⟩).2 =
          EuclideanSpace.single a 1 := by
        rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz]
        exact t.continuousLinearMapAt_symmL hz _
      change (t ⟨z, t.symmL ℂ z (EuclideanSpace.single a 1)⟩).2 =
        (t ⟨z, e.symmL ℂ z.1 (EuclideanSpace.single (finProdFinEquiv.symm a).1 1) ⊗ₜ[ℂ]
          f.symmL ℂ z.2 (EuclideanSpace.single (finProdFinEquiv.symm a).2 1)⟩).2
      rw [hleft]
      ext c
      symm
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective c
      rw [htpure z (htbase ▸ hz), he, hf]
      obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
      by_cases h₁ : i = a₁ <;> by_cases h₂ : j = a₂ <;>
        simp [h₁, h₂, finProdFinEquiv.injective.eq_iff]
    have hE := (h.contMDiffOn_gram e (finProdFinEquiv.symm a).1
      (finProdFinEquiv.symm b).1).comp hproj.1.contMDiffOn
        (show Set.MapsTo Prod.fst t.baseSet e.baseSet from
          fun z hz ↦ ((htbase ▸ hz) : z ∈ e.baseSet ×ˢ f.baseSet).1)
    have hF := (k.contMDiffOn_gram f (finProdFinEquiv.symm a).2
      (finProdFinEquiv.symm b).2).comp hproj.2.contMDiffOn
        (show Set.MapsTo Prod.snd t.baseSet f.baseSet from
          fun z hz ↦ ((htbase ▸ hz) : z ∈ e.baseSet ×ˢ f.baseSet).2)
    apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      (hE.prodMk_space hF)).congr
    intro z hz
    rw [hframe z hz a, hframe z hz b, hpure]
    rfl
  -- Expand the same positive core in any designated native chart, with both original slots.
  have hformula (t : Trivialization K (π K T)) [MemTrivializationAtlas t]
      (z : M × N) (hz : z ∈ t.baseSet) (u v : T z) :
      (core z).inner u v = ∑ a, ∑ b,
        starRingEnd ℂ ((t ⟨z, u⟩).2 a) *
          (core z).inner (t.symmL ℂ z (EuclideanSpace.single a 1))
            (t.symmL ℂ z (EuclideanSpace.single b 1)) * (t ⟨z, v⟩).2 b := by
    let : InnerProductSpace.Core ℂ (T z) := core z
    let L : T z →ₗ⋆[ℂ] T z →ₗ[ℂ] ℂ :=
      LinearMap.mk₂'ₛₗ _ _ (core z).inner
        (fun a b c ↦ (core z).add_left a b c)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
        (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
        (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
    have hexpand (w : T z) :
        ∑ a, (t ⟨z, w⟩).2 a • t.symmL ℂ z (EuclideanSpace.single a 1) = w := by
      have heq := congrArg (t.symmL ℂ z)
        ((EuclideanSpace.basisFun (Fin (r * s)) ℂ).sum_repr ((t ⟨z, w⟩).2))
      calc
        _ = t.symmL ℂ z ((t ⟨z, w⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = w := by
          rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz w]
          exact t.symmL_continuousLinearMapAt hz w
    change L u v = _
    conv_lhs => rw [← hexpand u, map_sum]
    simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs => rw [← hexpand v, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change starRingEnd ℂ ((t ⟨z, u⟩).2 a) *
      ((t ⟨z, v⟩).2 b * (core z).inner _ _) = _
    ring
  let l : SmoothHermitianMetric (n := n + m) (r := r * s) T := {
    toCore := core
    isSmoothBundle := inferInstance
    contMDiffOn_gram := by
      intro q hq i j z hz
      let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.1
      let f := trivializationAt (EuclideanSpace ℂ (Fin s)) F z.2
      let result := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
      obtain ⟨t, ht, htbase, htpure⟩ :=
        result.choose_spec.choose_spec.2.1 e inferInstance f inferInstance
      let := ht
      have hzt : z ∈ t.baseSet := htbase.symm ▸
        (show z ∈ e.baseSet ×ˢ f.baseSet from
          ⟨mem_baseSet_trivializationAt _ _ z.1, mem_baseSet_trivializationAt _ _ z.2⟩)
      let U := q.baseSet ∩ t.baseSet
      have hcoord (a b : Fin (r * s)) : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
          (fun y ↦ (t ⟨y, q.symmL ℂ y (EuclideanSpace.single a 1)⟩).2 b) U := by
        have heval : ContDiff ℝ ∞ (fun L : K →L[ℂ] K ↦
            (L (EuclideanSpace.single a 1)) b) := by
          have hv : ContDiff ℂ ∞ (fun L : K →L[ℂ] K ↦
              L (EuclideanSpace.single a 1)) := contDiff_id.clm_apply contDiff_const
          exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin (r * s) ↦ ℂ) b).contDiff.comp
            hv).restrict_scalars ℝ
        apply (heval.contMDiff.comp_contMDiffOn
          (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n + m) q t)).congr
        intro y hy
        change _ = (((q.coordChangeL ℂ t y) : K →L[ℂ] K)
          (EuclideanSpace.single a 1)) b
        have heq := q.coordChangeL_apply (R := ℂ) t hy (EuclideanSpace.single a 1)
        rw [← q.symmL_apply (R := ℂ) hy.1] at heq
        exact congrArg (fun w : K ↦ w b) heq.symm
      have hsum : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
          (fun y ↦ ∑ a, ∑ b,
            starRingEnd ℂ ((t ⟨y, q.symmL ℂ y (EuclideanSpace.single i 1)⟩).2 a) *
              (core y).inner (t.symmL ℂ y (EuclideanSpace.single a 1))
                (t.symmL ℂ y (EuclideanSpace.single b 1)) *
              (t ⟨y, q.symmL ℂ y (EuclideanSpace.single j 1)⟩).2 b) U := by
        apply contMDiffOn_finsetSum
        intro a _
        apply contMDiffOn_finsetSum
        intro b _
        have hc := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i a)
        have hg := (hproduct e f t htbase htpure a b).mono
          (show U ⊆ t.baseSet from Set.inter_subset_right)
        have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
        exact hmul.contMDiff.comp_contMDiffOn
          ((hmul.contMDiff.comp_contMDiffOn (hc.prodMk_space hg)).prodMk_space (hcoord j b))
      have hlocal : ContMDiffOn I 𝓘(ℝ, ℂ) ∞
          (fun y ↦ (core y).inner (q.symmL ℂ y (EuclideanSpace.single i 1))
            (q.symmL ℂ y (EuclideanSpace.single j 1))) U :=
        hsum.congr (fun y hy ↦
          hformula t y hy.2 (q.symmL ℂ y (EuclideanSpace.single i 1))
            (q.symmL ℂ y (EuclideanSpace.single j 1)))
      -- All selected charts are handled by their smooth transition to this covering product chart.
      exact (hlocal.contMDiffAt ((q.open_baseSet.inter t.open_baseSet).mem_nhds
        ⟨hz, hzt⟩)).contMDiffWithinAt }
  refine ⟨l, hpure, ?_⟩
  intro l' hl'
  -- Pure tensors span both slots, so equality of their pairings determines the metric data.
  have hinner (z : M × N) (u v : T z) :
      (l'.toCore z).inner u v = (core z).inner u v := by
    induction u using TensorProduct.inductionOn with
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | tmul c d => exact (hl' z a c b d).trans (hpure z a c b d).symm
      | add v w hv hw =>
        rw [InnerProductSpace.Core.inner_add_right (c := (l'.toCore z).toCore),
          InnerProductSpace.Core.inner_add_right (c := (core z).toCore), hv, hw]
    | add u w hu hw => rw [(l'.toCore z).add_left, (core z).add_left, hu, hw]
  have hext (z : M × N) (a b : InnerProductSpace.Core ℂ (T z))
      (heq : ∀ u v : T z, a.inner u v = b.inner u v) : a = b := by
    cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        congr 1
        cases a with
        | mk ia h₁ h₂ h₃ h₄ =>
          cases b with
          | mk ib h₅ h₆ h₇ h₈ =>
            congr 1
            cases ia
            cases ib
            congr 1
            funext u v
            exact heq u v
  have hcores : l'.toCore = core := by
    funext z
    exact hext z (l'.toCore z) (core z) (hinner z)
  cases l' with
  | mk core' smooth' isSmooth' =>
    change core' = core at hcores
    cases hcores
    rfl

/-- The actual tensor metric selected with its specified pure-tensor pairing. -/
def externalTensorMetric :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    SmoothHermitianMetric (n := n + m) (r := r * s) (externalTensorFiber E F) :=
  (existsUnique_externalTensorMetric h k).exists.choose

/-- The selected tensor metric keeps precisely the two supplied factor pairings. -/
theorem externalTensorMetric_pairing (z : M × N) (a c : E z.1) (b d : F z.2) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    (externalTensorMetric h k).pairing z (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) =
      h.pairing z.1 a c * k.pairing z.2 b d := by
  /- Read the pure-tensor specification from the very existence witness
  selecting externalTensorMetric. Both supplied metrics and all four original
  fiber vectors are retained; no replacement pointwise norm is used. -/
  exact (existsUnique_externalTensorMetric h k).exists.choose_spec z a c b d

end AtiyahSinger
