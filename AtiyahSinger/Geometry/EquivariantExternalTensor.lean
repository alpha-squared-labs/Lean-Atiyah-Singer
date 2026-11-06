/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ExternalTensorBundle
public import AtiyahSinger.Geometry.SmoothEquivariantFrameCover
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantBundleTensor
public import AtiyahSinger.Topology.EquivariantRestriction

/-!
# Independent group actions on the original native external tensor bundle

Public module ID: M1189.

The moving-fiber map is the tensor product of the two original maps. The
existing external tensor topology, coordinate norms and native tensor atlas
are retained. This is the action needed by the geometric L² tensor comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40

attribute [local instance] isFiniteRank_pullback tensorTopology

variable {G H M N : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace M] [TopologicalSpace N]
  [MulAction G M] [ContinuousSMul G M]
  [MulAction H N] [ContinuousSMul H N]
  {r s : ℕ} (E : M → Type*) (F : N → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    EquivariantStructure H F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original independent actions on the specified native external tensor bundle. -/
def externalTensorEquivariantStructure :
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
    EquivariantStructure (G × H) (externalTensorFiber E F) := by
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin s)) F
  let σ' := (σ.restrict (ContinuousMonoidHom.fst G H)).pullback
    (ContinuousMap.fst : C(M × N, M)) (fun _ _ ↦ rfl)
  let τ' := (τ.restrict (ContinuousMonoidHom.snd G H)).pullback
    (ContinuousMap.snd : C(M × N, N)) (fun _ _ ↦ rfl)
  let θ := σ'.tensor τ'
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
  refine {
    linearMap := fun a z ↦ TensorProduct.map (σ.linearMap a.1 z.1) (τ.linearMap a.2 z.2)
    one_map := fun z v ↦ θ.one_map z v
    mul_map := fun a b z v ↦ θ.mul_map a b z v
    continuous_action := ?_ }
  -- Retyping the phantom model twice is identity on each original tensor and its base point.
  have htop : modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) =
      tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F) := by
    change TopologicalSpace.induced
      (fun z : TotalSpace Unit (externalTensorFiber E F) ↦
        (⟨z.proj, z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin (r * s)))
          (externalTensorFiber E F)))
      (TopologicalSpace.induced
        (fun z : TotalSpace (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) ↦
          (⟨z.proj, z.snd⟩ : TotalSpace Unit (externalTensorFiber E F)))
        (tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F))) = _
    rw [induced_compose]
    exact @induced_id (TotalSpace Unit (externalTensorFiber E F))
      (tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F))
  change @Continuous _ _ (@instTopologicalSpaceProd _ _ inferInstance
    (modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)))
    (modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)) _
  rw [htop]
  exact θ.continuous_action

variable {VG VH : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [NormedAddCommGroup VH] [NormedSpace ℝ VH]
  [ChartedSpace VG G] [ChartedSpace VH H]
  {n m : ℕ}
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [ContMDiffSMul 𝓘(ℝ, VH) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ H N]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Product frames are frames of the existing selected native tensor atlas.
/-- The original independent tensor action is jointly smooth in the specified native atlas. -/
theorem externalTensorEquivariantStructure_isSmooth
    (hσ : σ.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
    (hτ : τ.IsSmooth (n := m) (r := s) 𝓘(ℝ, VH)) :
    letI : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
    letI : MulAction (G × H) M :=
      MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
    letI : ContinuousSMul (G × H) M :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
    letI : MulAction (G × H) N :=
      MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
    letI : ContinuousSMul (G × H) N :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := contMDiffSMul_euclideanProduct (n := n) (m := m)
      (VG := VG) (VH := VH) (G := G) (H := H) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    (externalTensorEquivariantStructure E F σ τ).IsSmooth (n := n + m) (r := r * s)
      𝓘(ℝ, VG × VH) := by
  classical
  let : ChartedSpace (VG × VH) (G × H) := prodChartedSpace VG G VH H
  let : MulAction (G × H) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G H).toMonoidHom
  let : ContinuousSMul (G × H) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G H).continuous
  let : MulAction (G × H) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G H).toMonoidHom
  let : ContinuousSMul (G × H) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G H).continuous
  let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
  let : ChartedSpace P (M × N) := prodChartedSpace _ M _ N
  let : IsManifold 𝓘(ℝ, P) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M N
  let c := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VH) (G := G) (H := H) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
  let θ := externalTensorEquivariantStructure E F σ τ
  let IG := 𝓘(ℝ, VG × VH)
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m)))
  let VR := EuclideanSpace ℂ (Fin r)
  let VS := EuclideanSpace ℂ (Fin s)
  let VT := EuclideanSpace ℂ (Fin (r * s))
  let A := {e : Trivialization VR (π VR E) // MemTrivializationAtlas e}
  let B := {f : Trivialization VS (π VS F) // MemTrivializationAtlas f}
  let hTensor := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s) E F
  have hspec (i : A × B) :=
    hTensor.choose_spec.choose_spec.2.1 i.1.val i.1.property i.2.val i.2.property
  let t (i : A × B) : Trivialization VT (π VT (externalTensorFiber E F)) := (hspec i).choose
  have ht (i : A × B) : MemTrivializationAtlas (t i) := (hspec i).choose_spec.1
  have hbase (i : A × B) : (t i).baseSet = i.1.val.baseSet ×ˢ i.2.val.baseSet :=
    (hspec i).choose_spec.2.1
  have hpure (i : A × B) (z : M × N) (hz : z ∈ (t i).baseSet)
      (a : E z.1) (b : F z.2) (j : Fin r) (k : Fin s) :
      ((t i) ⟨z, a ⊗ₜ[ℂ] b⟩).2 (finProdFinEquiv (j, k)) =
        (i.1.val ⟨z.1, a⟩).2 j * (i.2.val ⟨z.2, b⟩).2 k :=
    (hspec i).choose_spec.2.2 z ((hbase i) ▸ hz) a b j k
  have hcover (z : M × N) : ∃ i, z ∈ (t i).baseSet := by
    let e := trivializationAt VR E z.1
    let f := trivializationAt VS F z.2
    refine ⟨(⟨e, inferInstance⟩, ⟨f, inferInstance⟩), ?_⟩
    rw [hbase]
    exact ⟨mem_baseSet_trivializationAt VR E z.1, mem_baseSet_trivializationAt VS F z.2⟩
  -- Native concatenated base coordinates are converted by the fixed original linear map.
  have hchange : ContMDiff I 𝓘(ℝ, P) ∞ (id : M × N → M × N) :=
    (contMDiff_mfderiv_linearModelId c (M × N)).1.2
  have hprojG : ContMDiff (IG.prod I)
      (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : (G × H) × (M × N) ↦ (z.1.1, z.2.1)) := by
    have hraw : ContMDiff (IG.prod 𝓘(ℝ, P))
        (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : (G × H) × (M × N) ↦ (z.1.1, z.2.1)) := by
      simp only [IG, P, modelWithCornersSelf_prod]
      exact contMDiff_fst.fst.prodMk contMDiff_snd.fst
    exact hraw.comp (contMDiff_fst.prodMk (hchange.comp contMDiff_snd))
  have hprojH : ContMDiff (IG.prod I)
      (𝓘(ℝ, VH).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
      (fun z : (G × H) × (M × N) ↦ (z.1.2, z.2.2)) := by
    have hraw : ContMDiff (IG.prod 𝓘(ℝ, P))
        (𝓘(ℝ, VH).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞
        (fun z : (G × H) × (M × N) ↦ (z.1.2, z.2.2)) := by
      simp only [IG, P, modelWithCornersSelf_prod]
      exact contMDiff_fst.snd.prodMk contMDiff_snd.snd
    exact hraw.comp (contMDiff_fst.prodMk (hchange.comp contMDiff_snd))
  -- Each inverse tensor-frame column is the tensor of its two original inverse-frame columns.
  have hframe (i : A × B) :
      letI := ht i
      letI := i.1.property
      letI := i.2.property
      ∀ (z : M × N) (hz : z ∈ (t i).baseSet) (k : Fin (r * s)),
      (t i).symmL ℂ z (EuclideanSpace.single k 1) =
        i.1.val.symmL ℂ z.1 (EuclideanSpace.single (finProdFinEquiv.symm k).1 1) ⊗ₜ[ℂ]
          i.2.val.symmL ℂ z.2 (EuclideanSpace.single (finProdFinEquiv.symm k).2 1) := by
    let := ht i
    let := i.1.property
    let := i.2.property
    intro z hz k
    have hz' := (hbase i) ▸ hz
    apply ((t i).continuousLinearEquivAt ℂ z hz).injective
    simp only [Trivialization.continuousLinearEquivAt_apply]
    change ((t i) ⟨z, (t i).symmL ℂ z (EuclideanSpace.single k 1)⟩).2 = _
    rw [← (t i).continuousLinearMapAt_apply_of_mem ℂ hz,
      (t i).continuousLinearMapAt_symmL hz]
    ext q
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective q
    rw [hpure i z hz]
    rw [← i.1.val.continuousLinearMapAt_apply_of_mem ℂ hz'.1,
      i.1.val.continuousLinearMapAt_symmL hz'.1,
      ← i.2.val.continuousLinearMapAt_apply_of_mem ℂ hz'.2,
      i.2.val.continuousLinearMapAt_symmL hz'.2]
    obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply, EuclideanSpace.single, PiLp.single_apply,
      finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    simpa only [Set.indicator, Set.mem_prod, Set.mem_singleton_iff, Pi.one_apply] using
      (Set.indicator_prod_one (s := {a'}) (t := {b'}) (i := a) (j := b) (M₀ := ℂ))
  apply EquivariantStructure.IsSmooth.of_frameCover IG θ t ht hcover
  intro i l k
  let := ht i
  let := ht l
  let := i.1.property
  let := i.2.property
  let := l.1.property
  let := l.2.property
  let S : Set ((G × H) × (M × N)) :=
    {z | z.2 ∈ (t i).baseSet ∧ z.1 • z.2 ∈ (t l).baseSet}
  let e₀ := EuclideanSpace.equiv (Fin (r * s)) ℂ
  have hpi : ContMDiffOn (IG.prod I) 𝓘(ℝ, Fin (r * s) → ℂ) ∞
      (fun z : (G × H) × (M × N) ↦ fun q ↦ ((t l) ⟨z.1 • z.2,
        θ.linearMap z.1 z.2 ((t i).symmL ℂ z.2 (EuclideanSpace.single k 1))⟩).2 q) S := by
    apply contMDiffOn_pi_space.mpr
    intro q
    have hleft := (hσ i.1.val l.1.val (finProdFinEquiv.symm k).1).comp
      hprojG.contMDiffOn (s := S) (by
        intro z hz
        exact ⟨((hbase i) ▸ hz.1).1, ((hbase l) ▸ hz.2).1⟩)
    have hright := (hτ i.2.val l.2.val (finProdFinEquiv.symm k).2).comp
      hprojH.contMDiffOn (s := S) (by
        intro z hz
        exact ⟨((hbase i) ▸ hz.1).2, ((hbase l) ▸ hz.2).2⟩)
    let leftProj := EuclideanSpace.proj (𝕜 := ℂ) (finProdFinEquiv.symm q).1
    let rightProj := EuclideanSpace.proj (𝕜 := ℂ) (finProdFinEquiv.symm q).2
    have ha := (leftProj.restrictScalars ℝ).contMDiff.comp_contMDiffOn hleft
    have hb := (rightProj.restrictScalars ℝ).contMDiff.comp_contMDiffOn hright
    apply (((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff).comp_contMDiffOn
      (ha.prodMk_space hb)).congr
    intro z hz
    rw [hframe i z.2 hz.1]
    change ((t l) ⟨z.1 • z.2,
      TensorProduct.map (σ.linearMap z.1.1 z.2.1) (τ.linearMap z.1.2 z.2.2) _⟩).2 q = _
    rw [TensorProduct.map_tmul]
    have hh := hpure l (z.1 • z.2) hz.2
      (σ.linearMap z.1.1 z.2.1
        (i.1.val.symmL ℂ z.2.1 (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)))
      (τ.linearMap z.1.2 z.2.2
        (i.2.val.symmL ℂ z.2.2 (EuclideanSpace.single (finProdFinEquiv.symm k).2 1)))
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at hh
    refine hh.trans ?_
    apply congrArg₂ (fun a b : ℂ ↦ a * b)
    · rfl
    · rfl
  exact (e₀.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn hpi

end AtiyahSinger
