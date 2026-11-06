/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.OpenOperatorRefinement
public import AtiyahSinger.Analysis.OpenOperatorTransport

/-!
# Original chart and frame coordinates for open operator transport

Public module ID: M0828.

The coordinate maps below retain the original open diffeomorphism and its two
specified fiber identifications. In particular, all finite matrix maps use the
original bundle atlases, including native pullback frames on the common region.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold SchwartzMap Topology

section BundleMapMatrix

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The original smooth bundle-map columns assemble into their actual rectangular matrix. -/
theorem IsSmoothBundleMap.contMDiffOn_matrix (a : ∀ x, E x →ₗ[ℂ] F x)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      (fun x ↦ ((f.linearMapAt ℂ x).comp
        ((a x).comp (e.symmL ℂ x).toLinearMap)).toContinuousLinearMap)
      (e.baseSet ∩ f.baseSet) := by
  classical
  let L (x : M) := ((f.linearMapAt ℂ x).comp
    ((a x).comp (e.symmL ℂ x).toLinearMap)).toContinuousLinearMap
  -- Assemble the specified columns; this also covers either model having rank zero.
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      (fun x ↦ ∑ j : Fin r,
        ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
          (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
          ((f ⟨x, a x (e.symmL ℂ x (EuclideanSpace.single j 1))⟩).2))
      (e.baseSet ∩ f.baseSet) := by
    apply contMDiffOn_finsetSum
    intro j _
    exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).restrictScalars
        ℝ).contMDiff.comp_contMDiffOn (ha e f j)
  apply hsum.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  have hexpand := congrArg (L x) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
  simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hx.2] using hexpand.symm

end BundleMapMatrix

section OpenFrames

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  (E : SmoothFiniteComplexBundle (n := n) M)
  (G : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))

include ha in
omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 40 in
/-- Native open-region frames give the actual smooth forward and inverse fiber matrices. -/
theorem contMDiffOn_openBundleMap_matrices
    (f : Trivialization (EuclideanSpace ℂ (Fin E.rank))
      (π (EuclideanSpace ℂ (Fin E.rank)) E.Fiber))
    (g : Trivialization (EuclideanSpace ℂ (Fin G.rank))
      (π (EuclideanSpace ℂ (Fin G.rank)) G.Fiber))
    [MemTrivializationAtlas f] [MemTrivializationAtlas g] :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin G.rank)) ∞
      (fun x : U ↦ ((g.linearMapAt ℂ (e x).val).comp
        ((a x).toLinearMap.comp (f.symmL ℂ x.val).toLinearMap)).toContinuousLinearMap)
      {x | x.val ∈ f.baseSet ∧ (e x).val ∈ g.baseSet} ∧
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank)) ∞
      (fun x : U ↦ ((f.linearMapAt ℂ x.val).comp
        ((a x).symm.toLinearMap.comp (g.symmL ℂ (e x).val).toLinearMap)).toContinuousLinearMap)
      {x | x.val ∈ f.baseSet ∧ (e x).val ∈ g.baseSet} := by
  let iU := (ContinuousMap.subtypeVal (U : Set M) : C(U, M))
  let iV := (ContinuousMap.subtypeVal (V : Set N) : C(V, N))
  let e₀ := (⟨e, e.continuous⟩ : C(U, V))
  let f₀ := f.pullback iU
  let g₀ := (g.pullback iV).pullback e₀
  let : MemTrivializationAtlas f₀ := ⟨f, inferInstance, rfl⟩
  let : MemTrivializationAtlas (g.pullback iV) := ⟨g, inferInstance, rfl⟩
  let : MemTrivializationAtlas g₀ := ⟨g.pullback iV, inferInstance, rfl⟩
  have hf (x : U) (hx : x.val ∈ f.baseSet) (v : EuclideanSpace ℂ (Fin E.rank)) :
      f₀.symmL ℂ x v = f.symmL ℂ x.val v := by
    rw [f₀.symmL_apply hx, f.symmL_apply hx, f₀.symm_apply hx]
    rfl
  have hg (x : U) (hx : (e x).val ∈ g.baseSet)
      (v : EuclideanSpace ℂ (Fin G.rank)) :
      g₀.symmL ℂ x v = g.symmL ℂ (e x).val v := by
    rw [g₀.symmL_apply hx, g.symmL_apply hx, g₀.symm_apply hx]
    change (g.pullback iV).symm (e x) v = g.symm (e x).val v
    rw [(g.pullback iV).symm_apply hx]
    rfl
  constructor
  · -- The designated double pullback frame evaluates at the same e(x), with no new frame choice.
    have h := ha.contMDiffOn_matrix (fun x ↦ (a x).toLinearMap) f₀ g₀
    apply h.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change g.linearMapAt ℂ (e x).val (a x (f.symmL ℂ x.val v)) =
      g₀.linearMapAt ℂ x (a x (f₀.symmL ℂ x v))
    rw [hf x hx.1, g₀.coe_linearMapAt_of_mem hx.2]
    erw [g.coe_linearMapAt_of_mem (show (e x).val ∈ g.baseSet from hx.2)]
    rfl
  · have h := (ha.symm a).contMDiffOn_matrix (fun x ↦ (a x).symm.toLinearMap) g₀ f₀
    have h' := h.mono (show {x : U | x.val ∈ f.baseSet ∧ (e x).val ∈ g.baseSet} ⊆
      g₀.baseSet ∩ f₀.baseSet from fun _ hx ↦ hx.symm)
    apply h'.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change f.linearMapAt ℂ x.val ((a x).symm (g.symmL ℂ (e x).val v)) =
      f₀.linearMapAt ℂ x ((a x).symm (g₀.symmL ℂ x v))
    rw [hg x hx.2, f₀.coe_linearMapAt_of_mem hx.1, f.coe_linearMapAt_of_mem hx.1]
    rfl

end OpenFrames

section OpenCharts

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)

/-- The original open diffeomorphism is smooth in the two restricted chart coordinates. -/
theorem contDiff_openChartTransition (hU : Nonempty U) (hV : Nonempty V)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) N) :
    let cU := c.subtypeRestr hU
    let dV := d.subtypeRestr hV
    let t := cU.symm.trans (e.toHomeomorph.toOpenPartialHomeomorph.trans dV)
    ContDiffOn ℝ ∞ t t.source ∧ ContDiffOn ℝ ∞ t.symm t.target ∧
      ∀ (x : U), x.val ∈ c.source → (e x).val ∈ d.source →
        c x.val ∈ t.source ∧ t (c x.val) = d (e x).val ∧
        t.symm (d (e x).val) = c x.val := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let cU := c.subtypeRestr hU
  let dV := d.subtypeRestr hV
  let t := cU.symm.trans (e.toHomeomorph.toOpenPartialHomeomorph.trans dV)
  have hcU : cU ∈ (contDiffGroupoid ∞ I).maximalAtlas U :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hc hU
  have hdV : dV ∈ (contDiffGroupoid ∞ I).maximalAtlas V :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hd hV
  -- Restriction gives maximal-atlas charts; no membership in the smaller native atlas is claimed.
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro z hz
    have hsource := contMDiffAt_symm_of_mem_maximalAtlas hcU hz.1
    have hmove := e.contMDiffAt.comp z hsource
    exact ((contMDiffAt_of_mem_maximalAtlas hdV hz.2.2).comp z hmove).contDiffAt.contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro z hz
    have htarget := contMDiffAt_symm_of_mem_maximalAtlas hdV hz.1.1
    have hmove := e.symm.contMDiffAt.comp z htarget
    exact ((contMDiffAt_of_mem_maximalAtlas hcU hz.2).comp z hmove).contDiffAt.contDiffWithinAt
  refine ⟨ht, hts, ?_⟩
  intro x hx hy
  have hxU : x ∈ cU.source := by simpa [cU] using hx
  have hyV : e x ∈ dV.source := by simpa [dV] using hy
  have htc : c x.val ∈ t.source := by
    refine ⟨cU.map_source hxU, Set.mem_univ _, ?_⟩
    change e (cU.symm (cU x)) ∈ dV.source
    rw [cU.left_inv hxU]
    exact hyV
  have htval : t (c x.val) = d (e x).val := by
    change dV (e (cU.symm (cU x))) = dV (e x)
    rw [cU.left_inv hxU]
  refine ⟨htc, htval, ?_⟩
  rw [← htval, t.left_inv htc]

end OpenCharts

section NativePiece

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))


include hK hKU hKL ha hb in
omit hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The same coordinate witness is compared with both original cutoff section maps.
/-- A supported piece in one target chart has an exact native transported piece. -/
theorem exists_openExtension_piece {m : ℝ}
    (P : PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
    (hP : P.chart.symm '' (tsupport P.input.cutoff ∪ tsupport P.output.cutoff) ⊆ K)
    (R : smoothSections (n := n) (r := G.rank) G.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := H.rank) H.Fiber)
    (hRsupport : HasSectionOperatorSupport L R)
    (hR : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (R v).val (e x).val = b x ((P.toLinearMap u).val x.val))
    (c : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) N)
    (A : BundleChartCutoff (r := G.rank) G.Fiber c)
    (B : BundleChartCutoff (r := H.rank) H.Fiber c)
    (hAB : A.cutoff = B.cutoff)
    (hbase : L ⊆ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' L ⊆ interior {z | A.cutoff z = 1})
    (hoverlap : ∀ z ∈ tsupport A.cutoff, ∃ x : U,
      (e x).val = c.symm z ∧
      x.val ∈ P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet)
    (hU : Nonempty U) (hV : Nonempty V) :
    letI := P.input.frame_mem_atlas
    letI := P.output.frame_mem_atlas
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    let t := (P.chart.subtypeRestr hU).symm.trans
      (e.toHomeomorph.toOpenPartialHomeomorph.trans (c.subtypeRestr hV))
    let x := fun z : EuclideanSpace ℝ (Fin n) ↦ e.symm ((c.subtypeRestr hV).symm z)
    let C := cutoffMatrix A.cutoff (fun z ↦
      ((P.input.frame.linearMapAt ℂ (x z).val).comp
        ((a (x z)).symm.toLinearMap.comp
          (A.frame.symmL ℂ (e (x z)).val).toLinearMap)).toContinuousLinearMap)
    let D := cutoffMatrix A.cutoff (fun z ↦
      ((B.frame.linearMapAt ℂ (e (x z)).val).comp
        ((b (x z)).toLinearMap.comp
          (P.output.frame.symmL ℂ (x z).val).toLinearMap)).toContinuousLinearMap)
    ∃ Q : PseudodifferentialPiece (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber m, Q.toLinearMap = R ∧ Q.chart = c ∧
        Q.input.frame = A.frame ∧ Q.output.frame = B.frame ∧
        Q.input.cutoff = A.cutoff ∧ Q.output.cutoff = B.cutoff ∧
        IsSymbol t.target (m - 1) (Q.symbol - matrixSymbol D C
          (cotangentSymbol t (cutoffSymbol P.output.cutoff P.input.cutoff P.symbol))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let cU := P.chart.subtypeRestr hU
  let cV := c.subtypeRestr hV
  let t := cU.symm.trans (e.toHomeomorph.toOpenPartialHomeomorph.trans cV)
  obtain ⟨ht, hts, hvalues⟩ := contDiff_openChartTransition U V e hU hV
    P.chart c P.chart_mem_atlas hc
  have hcVM : cV ∈ (contDiffGroupoid ∞ I).maximalAtlas V :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hc hV
  let x (z : X) : U := e.symm (cV.symm z)
  have hx : ContMDiffOn I I ∞ x t.target := by
    intro z hz
    exact (e.symm.contMDiffAt.comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hcVM hz.1.1)).contMDiffWithinAt
  let := P.input.frame_mem_atlas
  let := P.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let D : Set U := {y | y.val ∈ P.input.frame.baseSet ∧ (e y).val ∈ A.frame.baseSet} ∩
    {y | y.val ∈ P.output.frame.baseSet ∧ (e y).val ∈ B.frame.baseSet}
  have hD : IsOpen D :=
    ((P.input.frame.open_baseSet.preimage continuous_subtype_val).inter
      (A.frame.open_baseSet.preimage (continuous_subtype_val.comp e.continuous))).inter
        ((P.output.frame.open_baseSet.preimage continuous_subtype_val).inter
          (B.frame.open_baseSet.preimage (continuous_subtype_val.comp e.continuous)))
  let Ω := t.target ∩ x ⁻¹' D
  have hΩ : IsOpen Ω := hx.continuousOn.isOpen_inter_preimage t.open_target hD
  have hAΩ : tsupport A.cutoff ⊆ Ω := by
    intro z hz
    obtain ⟨y, hy, hyD⟩ := hoverlap z hz
    have hyc : (e y).val ∈ c.source := by
      rw [hy]
      exact c.map_target (A.support_subset hz).1
    have hycV : e y ∈ cV.source := by simpa [cV] using hyc
    have hzy : cV (e y) = z := by
      change c (e y).val = z
      rw [hy, c.right_inv (A.support_subset hz).1]
    have hxy : x z = y := by
      dsimp only [x]
      rw [← hzy, cV.left_inv hycV, e.symm_apply_apply]
    have hzB : z ∈ tsupport B.cutoff := by rwa [← hAB]
    refine ⟨⟨⟨?_, Set.mem_univ _⟩, ?_⟩, ?_⟩
    · rw [← hzy]
      exact cV.map_source hycV
    · change x z ∈ cU.source
      rw [hxy]
      simpa [cU] using hyD.1.1
    · change x z ∈ D
      rw [hxy]
      exact ⟨⟨hyD.1.2, hy.symm ▸ (A.support_subset hz).2⟩,
        ⟨hyD.2, hy.symm ▸ (B.support_subset hzB).2⟩⟩
  let Ain (z : X) : EuclideanSpace ℂ (Fin G.rank) →L[ℂ]
      EuclideanSpace ℂ (Fin E.rank) := ((P.input.frame.linearMapAt ℂ (x z).val).comp
    ((a (x z)).symm.toLinearMap.comp
      (A.frame.symmL ℂ (e (x z)).val).toLinearMap)).toContinuousLinearMap
  let Bout (z : X) : EuclideanSpace ℂ (Fin F.rank) →L[ℂ]
      EuclideanSpace ℂ (Fin H.rank) := ((B.frame.linearMapAt ℂ (e (x z)).val).comp
    ((b (x z)).toLinearMap.comp
      (P.output.frame.symmL ℂ (x z).val).toLinearMap)).toContinuousLinearMap
  have hAin : ContDiffOn ℝ ∞ Ain Ω :=
    ((contMDiffOn_openBundleMap_matrices E G U V e a ha P.input.frame A.frame).2.comp
      (hx.mono (show Ω ⊆ t.target from Set.inter_subset_left))
        (fun _ hz ↦ hz.2.1)).contDiffOn
  have hBout : ContDiffOn ℝ ∞ Bout Ω :=
    ((contMDiffOn_openBundleMap_matrices F H U V e b hb P.output.frame B.frame).1.comp
      (hx.mono (show Ω ⊆ t.target from Set.inter_subset_left))
        (fun _ hz ↦ hz.2.2)).contDiffOn
  let C := cutoffMatrix A.cutoff Ain
  let D := cutoffMatrix A.cutoff Bout
  have hC : ContDiff ℝ ∞ C :=
    contDiff_cutoffMatrix Ω hΩ Ain hAin A.cutoff A.smooth_cutoff hAΩ
  have hD' : ContDiff ℝ ∞ D :=
    contDiff_cutoffMatrix Ω hΩ Bout hBout A.cutoff A.smooth_cutoff hAΩ
  have hcC : HasCompactSupport C := hasCompactSupport_cutoffMatrix _ _ A.compact_support
  have hcD : HasCompactSupport D := hasCompactSupport_cutoffMatrix _ _ A.compact_support
  let K₀ := tsupport P.output.cutoff ∪ tsupport P.input.cutoff
  have hK₀ : IsCompact K₀ := P.output.compact_support.union P.input.compact_support
  have hKmoved (z : X) (hz : z ∈ K₀) : ∃ y : U,
      y.val = P.chart.symm z ∧ (e y).val ∈ L ∧
      z ∈ t.source ∧ t z = c (e y).val := by
    have hzOld : z ∈ P.chart.target := by
      rcases hz with hz | hz
      · exact (P.output.support_subset hz).1
      · exact (P.input.support_subset hz).1
    have hyK : P.chart.symm z ∈ K := hP ⟨z, hz.elim Or.inr Or.inl, rfl⟩
    let y : U := ⟨P.chart.symm z, hKU hyK⟩
    have hyL : (e y).val ∈ L := by
      change y ∈ e ⁻¹' ((Subtype.val : V → N) ⁻¹' L)
      rw [hKL]
      exact hyK
    have hv := hvalues y (P.chart.map_target hzOld) (hbase hyL).1.1
    have hzEq : P.chart y.val = z := P.chart.right_inv hzOld
    rw [hzEq] at hv
    exact ⟨y, rfl, hyL, hv.1, hv.2.1⟩
  have hK₀t : K₀ ⊆ t.source := fun z hz ↦ (hKmoved z hz).choose_spec.2.2.1
  have honeTarget : t '' K₀ ⊆ interior {z | A.cutoff z = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, _, hyL, _, htz⟩ := hKmoved z hz
    rw [htz]
    exact hone ⟨_, hyL, rfl⟩
  obtain ⟨χ, hχ, hcχ, hχt, hχone⟩ :=
    exists_compact_cutoff_one_near K₀ t.source hK₀ t.open_source hK₀t
  let p₀ := cutoffSymbol P.output.cutoff P.input.cutoff P.symbol
  have hp₀ : IsSymbol Set.univ m p₀ := isSymbol_cutoffSymbol m P.symbol P.isSymbol _ _
    P.output.smooth_cutoff P.input.smooth_cutoff P.output.compact_support P.input.compact_support
  let T₀ := coordinatePushforward t ht hts χ A.cutoff hχ hcχ hχt
    A.smooth_cutoff A.compact_support (hAΩ.trans Set.inter_subset_left) P.coordinateOperator
  let T := (matrixMultiplierCLM D hD' hcD).comp (T₀.comp (matrixMultiplierCLM C hC hcC))
  obtain ⟨q, hq, hcq, hTq, hTK, hprincipal⟩ := exists_compactSymbol_matrixCoordinatePushforward
    t ht hts χ A.cutoff hχ hcχ hχt A.smooth_cutoff A.compact_support
    (hAΩ.trans Set.inter_subset_left) m p₀ hp₀ P.coordinateOperator
    P.coordinateOperator_eq_quantize K₀ hK₀ hK₀t P.hasOperatorSupport_coordinateOperator
    hχone honeTarget D C hD' hcD hC hcC
  let Q : PseudodifferentialPiece (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber m :=
    { chart := c
      chart_mem_atlas := hc
      input := A
      output := B
      input_support_in_output_frame := fun z hz ↦
        (B.support_subset (by rwa [← hAB])).2
      output_support_in_input_frame := fun z hz ↦
        (A.support_subset (by rwa [hAB])).2
      operator := T
      symbol := q
      isSymbol := hq
      operator_apply := hTq }
  obtain ⟨γ, hγ, J, _, _, hγone, hJ⟩ :=
    exists_openSectionGermPullback E G U V e K hK hKU a ha
  have hγK (y : U) (hy : y.val ∈ K) : γ y.val = 1 :=
    interior_subset (s := {z | γ z = 1}) (subset_interior_iff_mem_nhdsSet.mpr hγone hy)
  have hJmatch (v : smoothSections (n := n) (r := G.rank) G.Fiber) :
      ∀ᶠ y : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e y).val = a y ((J v).val y.val) := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro y hy
    have hn := eventually_nhdsSet_iff_forall.mp hγone y.val hy
    filter_upwards [(continuous_subtype_val.tendsto y).eventually hn] with z hz
    rw [hJ, hz, Complex.ofReal_one, one_smul, LinearEquiv.apply_symm_apply]
  have hxTarget (z : X) (hz : z ∈ t.target) : (e (x z)).val = c.symm z := by
    change (e (e.symm (cV.symm z))).val = _
    rw [e.apply_symm_apply]
    exact c.subtypeRestr_symm_apply hV hz.1.1
  have hxSource (z : X) (hz : z ∈ t.target) : (x z).val ∈ P.chart.source := by
    have hh := hz.2
    change x z ∈ cU.source at hh
    simpa [cU] using hh
  have hxCoord (z : X) : P.chart (x z).val = t.symm z := rfl
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin G.rank))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin E.rank))
          (fun w ↦ (P.input.cutoff w : ℂ))
          (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt
            (matrixMultiplierCLM C hC hcC u)) =
        P.input.localize P.chart_mem_atlas (J (A.extend hc u)) := by
    apply SchwartzMap.ext
    intro w
    have hgrowth : (fun w ↦ (P.input.cutoff w : ℂ)).HasTemperateGrowth :=
      (P.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp P.input.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, cutoffPullbackCLM_apply,
      matrixMultiplierCLM_apply]
    by_cases hw : w ∈ tsupport P.input.cutoff
    · obtain ⟨y, hy, hyL, hwt, htval⟩ := hKmoved w (Or.inr hw)
      have hyc : e y ∈ cV.source := by simpa [cV] using (hbase hyL).1.1
      have hxy : x (t w) = y := by
        change e.symm (cV.symm (t w)) = y
        rw [htval]
        change e.symm (cV.symm (cV (e y))) = y
        rw [cV.left_inv hyc, e.symm_apply_apply]
      have hyK : y.val ∈ K := by rw [hy]; exact hP ⟨w, Or.inl hw, rfl⟩
      have hχw : χ w = 1 :=
        interior_subset (s := {z | χ z = 1}) (hχone (Or.inr hw))
      have hframe : y.val ∈ P.input.frame.baseSet := by
        rw [hy]
        exact (P.input.support_subset hw).2
      have hExt : (A.extend hc u).val (e y).val =
          (A.cutoff (t w) : ℂ) • A.frame.symmL ℂ (e y).val (u (t w)) := by
        change A.extendedFunction u (e y).val = _
        simp only [BundleChartCutoff.extendedFunction, (hbase hyL).1.1, ↓reduceIte,
          ← htval]
        rfl
      change (P.input.cutoff w : ℂ) •
          (χ w • (C (t w) (u (t w)))) = P.input.localizedFunction (J (A.extend hc u)) w
      rw [hχw, one_smul]
      simp only [BundleChartCutoff.localizedFunction, sectionInChart,
        (P.input.support_subset hw).1, ↓reduceIte]
      rw [← hy, hJ, hγK y hyK, Complex.ofReal_one, one_smul, hExt]
      change (P.input.cutoff w : ℂ) •
          (A.cutoff (t w) • (Ain (t w) (u (t w)))) = _
      have hAv : Ain (t w) (u (t w)) =
          (P.input.frame ⟨y.val, (a y).symm
            (A.frame.symmL ℂ (e y).val (u (t w)))⟩).2 := by
        change P.input.frame.linearMapAt ℂ (x (t w)).val
          ((a (x (t w))).symm (A.frame.symmL ℂ (e (x (t w))).val (u (t w)))) = _
        rw [hxy]
        erw [P.input.frame.coe_linearMapAt_of_mem hframe]
      rw [hAv]
      have hscale (v : G.Fiber (e y).val) (c : ℂ) :
          (P.input.frame ⟨y.val, (a y).symm (c • v)⟩).2 =
            c • (P.input.frame ⟨y.val, (a y).symm v⟩).2 := by
        change P.input.frame.linearEquivAt ℂ y.val hframe ((a y).symm (c • v)) =
          c • P.input.frame.linearEquivAt ℂ y.val hframe ((a y).symm v)
        rw [map_smul, map_smul]
      rw [hscale]
      simp only [Complex.coe_smul]
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  have houtputFrame (v : smoothSections (n := n) (r := F.rank) F.Fiber)
      (z : X) (hz : z ∈ Ω) :
      Bout z (P.output.frame ⟨(x z).val, v.val (x z).val⟩).2 =
        (B.frame ⟨(e (x z)).val, b (x z) (v.val (x z).val)⟩).2 := by
    change B.frame.linearMapAt ℂ (e (x z)).val
      (b (x z) (P.output.frame.symmL ℂ (x z).val
        (P.output.frame ⟨(x z).val, v.val (x z).val⟩).2)) = _
    erw [P.output.frame.symmL_apply hz.2.2.1,
      P.output.frame.symm_apply_apply_mk hz.2.2.1,
      B.frame.coe_linearMapAt_of_mem hz.2.2.2]
  have hlocal (u : 𝓢(X, EuclideanSpace ℂ (Fin G.rank))) (z : X) :
      T u z = B.localize hc (R (A.extend hc u)) z := by
    change matrixMultiplierCLM D hD' hcD (T₀ (matrixMultiplierCLM C hC hcC u)) z = _
    rw [matrixMultiplierCLM_apply]
    by_cases hz : z ∈ tsupport A.cutoff
    · have hzΩ := hAΩ hz
      have hzT := hzΩ.1
      have hcoord := coordinatePushforward_apply t ht hts χ A.cutoff hχ hcχ hχt
        A.smooth_cutoff A.compact_support (hAΩ.trans Set.inter_subset_left)
        P.coordinateOperator K₀ hK₀t P.hasOperatorSupport_coordinateOperator
        (fun w hw ↦ interior_subset (s := {z | A.cutoff z = 1}) (honeTarget hw))
        (matrixMultiplierCLM C hC hcC u) z hzT
      change T₀ (matrixMultiplierCLM C hC hcC u) z = _ at hcoord
      rw [hcoord, P.coordinateOperator_apply, hinput, P.operator_apply]
      have hf := houtputFrame (P.toLinearMap (J (A.extend hc u))) z hzΩ
      have hRf := hR (J (A.extend hc u)) (A.extend hc u) (hJmatch _) (x z)
      have hfinal : Bout z
          ((P.output.cutoff (t.symm z) : ℂ) •
            quantize P.symbol (P.input.localize P.chart_mem_atlas (J (A.extend hc u)))
              (t.symm z)) =
          (B.frame ⟨c.symm z, (R (A.extend hc u)).val (c.symm z)⟩).2 := by
        rw [← hxTarget z hzT, hRf]
        rw [P.toLinearMap_in_frame _ _ (hxSource z hzT) hzΩ.2.2.1, hxCoord] at hf
        exact hf
      change A.cutoff z • Bout z
        (P.output.cutoff (t.symm z) •
          quantize P.symbol (P.input.localize P.chart_mem_atlas (J (A.extend hc u)))
            (t.symm z)) = B.localizedFunction (R (A.extend hc u)) z
      simp only [BundleChartCutoff.localizedFunction, sectionInChart,
        (A.support_subset hz).1, ↓reduceIte, ← hAB, Complex.coe_smul]
      simpa only [Complex.coe_smul] using congrArg (fun w ↦ A.cutoff z • w) hfinal
    · have hAz := image_eq_zero_of_notMem_tsupport hz
      have hBz : B.cutoff z = 0 := by rwa [← hAB]
      simp [D, cutoffMatrix, hAz, hBz, BundleChartCutoff.localize,
        BundleChartCutoff.localizedFunction]
  -- The same target cutoff is one near L, so its input round trip preserves the supported action.
  have hinputRoundtrip (u : smoothSections (n := n) (r := G.rank) G.Fiber) :
      R (A.extend hc (A.localize hc u)) = R u := by
    apply hRsupport.eq_of_eventuallyEq
    apply eventually_nhdsSet_iff_forall.mpr
    intro y hy
    have hyc := (hbase hy).1.1
    have hyf := (hbase hy).1.2
    have hn := (c.continuousAt hyc).preimage_mem_nhds
      (isOpen_interior.mem_nhds (hone ⟨y, hy, rfl⟩))
    filter_upwards [(c.open_source.inter A.frame.open_baseSet).mem_nhds ⟨hyc, hyf⟩, hn]
      with z hz honez
    have hχz : A.cutoff (c z) = 1 := interior_subset (s := {w | A.cutoff w = 1}) honez
    change A.extendedFunction (A.localize hc u) z = u.val z
    simp only [BundleChartCutoff.extendedFunction, hz.1, ↓reduceIte]
    change (A.cutoff (c z) : ℂ) • A.frame.symmL ℂ z (A.localizedFunction u (c z)) = _
    rw [hχz, Complex.ofReal_one, one_smul]
    simp only [BundleChartCutoff.localizedFunction, c.map_source hz.1, ↓reduceIte,
      sectionInChart]
    rw [c.left_inv hz.1, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ hz.2]
    rw [hχz, Complex.ofReal_one, one_smul, A.frame.symmL_continuousLinearMapAt hz.2]
  have houtputRoundtrip (u : smoothSections (n := n) (r := G.rank) G.Fiber) :
      B.extend hc (B.localize hc (R u)) = R u := by
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ L
    · have hyc := (hbase hy).1.1
      have hyf := (hbase hy).2
      have hχy : B.cutoff (c y) = 1 := by
        rw [← hAB]
        exact interior_subset (s := {w | A.cutoff w = 1}) (hone ⟨y, hy, rfl⟩)
      change B.extendedFunction (B.localize hc (R u)) y = (R u).val y
      simp only [BundleChartCutoff.extendedFunction, hyc, ↓reduceIte]
      change (B.cutoff (c y) : ℂ) • B.frame.symmL ℂ y (B.localizedFunction (R u) (c y)) = _
      rw [hχy, Complex.ofReal_one, one_smul]
      simp only [BundleChartCutoff.localizedFunction, c.map_source hyc, ↓reduceIte,
        sectionInChart]
      rw [c.left_inv hyc, ← B.frame.continuousLinearMapAt_apply_of_mem ℂ hyf]
      rw [hχy, Complex.ofReal_one, one_smul, B.frame.symmL_continuousLinearMapAt hyf]
    · have hz : (R u).val y = 0 := by
        by_contra hne
        exact hy (hRsupport.1 u (subset_closure hne))
      change B.extendedFunction (B.localize hc (R u)) y = (R u).val y
      by_cases hyc : y ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, hyc, ↓reduceIte]
        change (B.cutoff (c y) : ℂ) • B.frame.symmL ℂ y (B.localizedFunction (R u) (c y)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hyc, ↓reduceIte,
          sectionInChart]
        rw [c.left_inv hyc, hz]
        by_cases hyf : y ∈ B.frame.baseSet
        · rw [show (B.frame ⟨y, (0 : H.Fiber y)⟩).2 = 0 from (B.frame.linear ℂ hyf).map_zero]
          simp
        · rw [B.frame.symmL_apply_of_notMem (R := ℂ) hyf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hyc, hz]
  refine ⟨Q, ?_, rfl, rfl, rfl, rfl, rfl, hprincipal⟩
  apply LinearMap.ext
  intro u
  have hTu : T (A.localize hc u) = B.localize hc (R (A.extend hc (A.localize hc u))) :=
    SchwartzMap.ext (hlocal (A.localize hc u))
  change B.extend hc (T (A.localize hc u)) = R u
  rw [hTu, hinputRoundtrip]
  exact houtputRoundtrip u


end NativePiece

end AtiyahSinger
