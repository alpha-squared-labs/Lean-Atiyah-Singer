/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ExteriorBundleExtension
public import AtiyahSinger.Geometry.RelativeMetricDensity

/-!
# Simultaneous relative geometric data for excision

Public module ID: M1351.

E01/D02/UL03/P02: on a second-countable Hausdorff smooth manifold, extend
the two bundles and the specified exterior identity
from SG III.13.4, (13.9), pp.248--249, using one coherent set of witnesses.
The same bundle identifications transport prescribed Hermitian metrics, and a
positive density is preserved on one neighborhood of a larger compact control.
The relative metric and density refinement is a project supplement.

The fixed-rank model requires an explicit equality of the two ranks. Common
frames on an empty exterior do not imply this equality. The theorem therefore
does not cover unequal-rank classes on compact open components; such classes
need a separate componentwise or locally varying-rank treatment. No compactness
or connectedness of the ambient manifold is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [MeasurableSpace M] [hBorel : BorelSpace M]

include hM hT hSC hBorel

/-- Extend an exterior identity and retain the given local geometry in the same witnesses. -/
theorem exists_relative_excision_data
    (U : Opens M) (K L : Set M) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ (U : Set M))
    (E F : SmoothFiniteComplexBundle (n := n) U) (hEF : E.rank = F.rank)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure U) [hν : IsSmoothPositiveMeasure (n := n) ν]
    (c : ∀ x : U, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap)) :
    let V : Opens U := ⟨(Subtype.val : U → M) ⁻¹' Kᶜ,
      hK.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
    let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
    ∀ (τE : ∀ x : V, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
      (τF : ∀ x : V, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
      IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := V)
        (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ E.Fiber))
        (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τE x).toLinearMap) →
      IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank) (M := V)
        (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ F.Fiber))
        (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τF x).toLinearMap) →
      (∀ (x : V) (v : E.Fiber x.val), τF x (c x.val v) = τE x v) →
      ∃ G H : SmoothFiniteComplexBundle (n := n) M,
        G.rank = E.rank ∧ H.rank = F.rank ∧
        ∃ (eE : ∀ x : U, E.Fiber x ≃ₗ[ℂ] G.Fiber x.val)
          (eF : ∀ x : U, F.Fiber x ≃ₗ[ℂ] H.Fiber x.val),
          IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := U)
            (E := E.Fiber)
            (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
            (fun x ↦ (eE x).toLinearMap) ∧
          IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank) (M := U)
            (E := F.Fiber)
            (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ H.Fiber))
            (fun x ↦ (eF x).toLinearMap) ∧
          ∃ (σE : ∀ x : W, G.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
            (σF : ∀ x : W, H.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
            IsSmoothBundleMap (n := n) (r := G.rank) (q := E.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ G.Fiber))
              (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
              (fun x ↦ (σE x).toLinearMap) ∧
            IsSmoothBundleMap (n := n) (r := H.rank) (q := E.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
              (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
              (fun x ↦ (σF x).toLinearMap) ∧
            (∀ (x : V) (v : E.Fiber x.val),
              σE ⟨x.val.val, x.property⟩ (eE x.val v) = τE x v) ∧
            (∀ (x : V) (v : F.Fiber x.val),
              σF ⟨x.val.val, x.property⟩ (eF x.val v) = τF x v) ∧
            ∃ d : ∀ x : M, G.Fiber x →L[ℂ] H.Fiber x,
              IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
                (fun x ↦ (d x).toLinearMap) ∧
              (∀ (x : U) (v : E.Fiber x), d x.val (eE x v) = eF x (c x v)) ∧
              (∀ (x : W) (v : G.Fiber x.val), σF x (d x.val v) = σE x v) ∧
              (∀ x : M, x ∉ K → Function.Bijective (d x)) ∧
              ∃ (g : SmoothHermitianMetric (n := n) (r := G.rank) G.Fiber)
                (l : SmoothHermitianMetric (n := n) (r := H.rank) H.Fiber)
                (μ : Measure M),
                IsSmoothPositiveMeasure (n := n) μ ∧
                ∃ O : Opens M, L ⊆ (O : Set M) ∧ O ≤ U ∧
                  (∀ (x : U), x.val ∈ O → ∀ v w : E.Fiber x,
                    g.pairing x.val (eE x v) (eE x w) = h.pairing x v w) ∧
                  (∀ (x : U), x.val ∈ O → ∀ v w : F.Fiber x,
                    l.pairing x.val (eF x v) (eF x w) = k.pairing x v w) ∧
                  (μ.comap (Subtype.val : U → M)).restrict
                      ((Subtype.val : U → M) ⁻¹' (O : Set M)) =
                    ν.restrict ((Subtype.val : U → M) ⁻¹' (O : Set M)) := by
  /- Stage 1: apply exterior bundle gluing to E and F on the same cover
  U and W=M\K. The rank equality permits the target frame to use the same
  model as the source even when U\K is empty. Retain the two actual overlap
  equations for eE, eF, σE and σF; do not choose new bundle identifications later.
  Stage 2: on U transport c by eF and the inverse of eE; on W use σF inverse
  followed by σE. The input frame identity and both overlap equations make
  these maps agree on U intersect W. Smooth inverse and composition in local
  matrices give one smooth bundle map d. Fiberwise finite dimensionality gives
  continuity for the original fiber norms. Its exterior expression is bijective.
  Stage 3: transport h and k to the pullbacks of these same G and H via the
  inverses of eE and eF. Smooth local matrix expressions show the transported
  pairings are smooth metrics. Use the relative metric extension for both and
  the relative density extension for ν, each with the larger compact set L.
  Intersect their three agreement neighborhoods inside U to obtain one O.
  Stage 4: evaluate the transported pairings on eE(v) and eF(v). Restrict the
  density equality to O. These are the displayed metric and actual measure
  equalities, using precisely the bundle witnesses already fixed in Stage 1.
  No exterior isometry is asserted: exterior invertibility suffices for kernel
  support, while adjoint comparisons use the preserved geometry near L.
  Empty opens and zero-rank fibers need no nonzero-vector or nonempty-base
  choice. Unequal ranks are deliberately excluded, even if the exterior is empty. -/
  classical
  -- Local coordinate facts retain native atlases and the original fiber norms.
  -- Assemble the actual local operator from its prescribed finite columns.
  have matrix_smooth {r q : ℕ}
      {X : Type _} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      {E F : X → Type}
      [∀ x, NormedAddCommGroup (E x)]
      [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
      [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
      [∀ x, NormedAddCommGroup (F x)]
      [∀ x, NormedSpace ℂ (F x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
      [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
      (a : ∀ x, E x →ₗ[ℂ] F x)
      (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun y ↦ ((f.linearMapAt ℂ y).comp
          ((a y).comp (e.symmL ℂ y).toLinearMap)).toContinuousLinearMap)
        (e.baseSet ∩ f.baseSet) := by
    classical
    have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun y ↦ ∑ k : Fin r,
          ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
            (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) k)
            ((f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single k 1))⟩).2))
        (e.baseSet ∩ f.baseSet) := by
      apply contMDiffOn_finsetSum
      intro k _
      exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) k)).restrictScalars
          ℝ).contMDiff.comp_contMDiffOn (ha e f k)
    -- The finite basis identifies this sum with the same coordinate operator.
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    let L := ((f.linearMapAt ℂ y).comp
      ((a y).comp (e.symmL ℂ y).toLinearMap)).toContinuousLinearMap
    have hexpand := congrArg L ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
    simpa [L, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2] using hexpand.symm
  -- Compose in one intermediate frame valid near the point.
  have comp_smooth {r q s : ℕ}
      {X : Type _} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      {E F G : X → Type}
      [∀ x, NormedAddCommGroup (E x)]
      [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
      [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
      [∀ x, NormedAddCommGroup (F x)]
      [∀ x, NormedSpace ℂ (F x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
      [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
      [∀ x, NormedAddCommGroup (G x)]
      [∀ x, NormedSpace ℂ (G x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) G)]
      [FiberBundle (EuclideanSpace ℂ (Fin s)) G]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) G]
      (a : ∀ x, E x →ₗ[ℂ] F x)
      (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a)
      (b : ∀ x, F x →ₗ[ℂ] G x)
      (hb : IsSmoothBundleMap (n := n) (r := q) (q := s) b) :
      IsSmoothBundleMap (n := n) (r := r) (q := s) (fun x ↦ (b x).comp (a x)) := by
    classical
    intro e he g hg j x hx
    let := he
    let := hg
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hfx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    let LA (y : X) := ((f.linearMapAt ℂ y).comp
      ((a y).comp (e.symmL ℂ y).toLinearMap)).toContinuousLinearMap
    let LB (y : X) := ((g.linearMapAt ℂ y).comp
      ((b y).comp (f.symmL ℂ y).toLinearMap)).toContinuousLinearMap
    have hLA := matrix_smooth a ha e f
    have hLB := matrix_smooth b hb f g
    let O := e.baseSet ∩ f.baseSet ∩ g.baseSet
    have hA : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ LA O :=
      hLA.mono (fun _ hy ↦ hy.1)
    have hB : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin s)) ∞ LB O :=
      hLB.mono (fun _ hy ↦ ⟨hy.1.2, hy.2⟩)
    have hcompose : ContDiff ℝ ∞ (fun p :
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin s)) ×
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ p.1.comp p.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    have hC := hcompose.contMDiff.comp_contMDiffOn (hB.prodMk_space hA)
    have hcol := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin s))
      (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn hC
    have hactual := hcol.congr (f₁ := fun y ↦
      (g ⟨y, (b y) ((a y) (e.symmL ℂ y (EuclideanSpace.single j 1)))⟩).2) (by
        intro y hy
        change (g ⟨y, (b y) ((a y) (e.symmL ℂ y (EuclideanSpace.single j 1)))⟩).2 =
          g.continuousLinearMapAt ℂ y ((b y) (f.symmL ℂ y
            (f.continuousLinearMapAt ℂ y ((a y) (e.symmL ℂ y
              (EuclideanSpace.single j 1))))))
        rw [f.symmL_continuousLinearMapAt hy.1.2,
          g.continuousLinearMapAt_apply_of_mem ℂ hy.2])
    exact (hactual.contMDiffAt
      (((e.open_baseSet.inter f.open_baseSet).inter g.open_baseSet).mem_nhds
        ⟨⟨hx.1, hfx⟩, hx.2⟩)).contMDiffWithinAt
  -- A fixed model change is smooth in the native trivial atlas.
  have constant_smooth {r q : ℕ}
      {X : Type _} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      (A : EuclideanSpace ℂ (Fin r) →L[ℂ]
      EuclideanSpace ℂ (Fin q)) :
      IsSmoothBundleMap (n := n) (M := X) (r := r) (q := q)
        (E := Bundle.Trivial X (EuclideanSpace ℂ (Fin r)))
        (F := Bundle.Trivial X (EuclideanSpace ℂ (Fin q)))
        (fun _ ↦ A.toLinearMap) := by
    rintro _ ⟨rfl⟩ _ ⟨rfl⟩ j
    have hc := (contMDiff_const.contMDiffOn : ContMDiffOn
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
        (fun _ : X ↦ A (EuclideanSpace.single j 1)) (Set.univ ∩ Set.univ))
    apply hc.congr
    intro x _
    rw [(Bundle.Trivial.trivialization X (EuclideanSpace ℂ (Fin r))).symmL_apply
      (Set.mem_univ x)]
    rw [Bundle.Trivial.trivialization_symm_apply]
    rfl
  -- Use native pulled-back frames to descend smoothness from the open cover.
  have glue_smooth {r q : ℕ}
      {X : Type _} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      {E F : X → Type}
      [∀ x, NormedAddCommGroup (E x)]
      [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
      [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
      [∀ x, NormedAddCommGroup (F x)]
      [∀ x, NormedSpace ℂ (F x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
      [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
      (U W : Opens X) (hcover : ∀ x : X, x ∈ U ∨ x ∈ W)
      (a : ∀ x, E x →ₗ[ℂ] F x)
      (hU : IsSmoothBundleMap (n := n) (M := U) (r := r) (q := q)
        (E := ((ContinuousMap.subtypeVal (U : Set X) : U → X) *ᵖ E))
        (F := ((ContinuousMap.subtypeVal (U : Set X) : U → X) *ᵖ F))
        (fun x ↦ a x.val))
      (hW : IsSmoothBundleMap (n := n) (M := W) (r := r) (q := q)
        (E := ((ContinuousMap.subtypeVal (W : Set X) : W → X) *ᵖ E))
        (F := ((ContinuousMap.subtypeVal (W : Set X) : W → X) *ᵖ F))
        (fun x ↦ a x.val)) :
      IsSmoothBundleMap (n := n) (r := r) (q := q) a := by
    intro e he f hf j x hx
    let := he
    let := hf
    have hlocal (O : Opens X)
        (hO : IsSmoothBundleMap (n := n) (M := O) (r := r) (q := q)
          (E := ((ContinuousMap.subtypeVal (O : Set X) : O → X) *ᵖ E))
          (F := ((ContinuousMap.subtypeVal (O : Set X) : O → X) *ᵖ F))
          (fun x ↦ a x.val)) (hxO : x ∈ O) :
        ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
          (fun y ↦ (f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2) x := by
      let incl : C(O, X) := ContinuousMap.subtypeVal (O : Set X)
      let : MemTrivializationAtlas (e.pullback incl) := ⟨e, he, rfl⟩
      let : MemTrivializationAtlas (f.pullback incl) := ⟨f, hf, rfl⟩
      have hc := hO (e.pullback incl) (f.pullback incl) j
      have hactual := hc.congr (f₁ := fun y : O ↦
        (f ⟨y.val, a y.val (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2) (by
          intro y hy
          change (f ⟨y.val, a y.val (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2 =
            (f ⟨y.val, a y.val ((e.pullback incl).symmL ℂ y
              (EuclideanSpace.single j 1))⟩).2
          rw [(e.pullback incl).symmL_apply hy.1]
          erw [e.symmL_apply hy.1, (e.pullback incl).symm_apply hy.1]
          rfl)
      have hm := hactual.contMDiffAt
        (((e.open_baseSet.inter f.open_baseSet).preimage
          continuous_subtype_val).mem_nhds (show (⟨x, hxO⟩ : O).val ∈
            e.baseSet ∩ f.baseSet from hx))
      exact (contMDiffAt_subtype_iff (U := O) (x := ⟨x, hxO⟩)).mp hm
    rcases hcover x with hxU | hxW
    · exact (hlocal U hU hxU).contMDiffWithinAt
    · exact (hlocal W hW hxW).contMDiffWithinAt
  -- Transport the original positive forms without changing any fiber norm.
  have transport_metric {r q : ℕ}
      {X : Type _} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X]
      {E F : X → Type}
      [∀ x, NormedAddCommGroup (E x)]
      [∀ x, NormedSpace ℂ (E x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
      [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
      [∀ x, NormedAddCommGroup (F x)]
      [∀ x, NormedSpace ℂ (F x)]
      [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
      [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
      [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
      [hSmoothF : IsSmoothComplexBundle (n := n) (r := q) F]
      (h : SmoothHermitianMetric (n := n) (r := r) E)
      (e : ∀ x, E x ≃ₗ[ℂ] F x)
      (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
      ∃ k : SmoothHermitianMetric (n := n) (r := q) F,
        ∀ (x : X) (v w : E x), k.pairing x (e x v) (e x w) = h.pairing x v w := by
    classical
    let core (x : X) : InnerProductSpace.Core ℂ (F x) :=
      { inner := fun u v ↦ h.pairing x ((e x).symm u) ((e x).symm v)
        conj_inner_symm := fun u v ↦ (h.toCore x).conj_inner_symm _ _
        re_inner_nonneg := fun v ↦ (h.toCore x).re_inner_nonneg _
        add_left := by
          intro u v w
          rw [map_add]
          exact (h.toCore x).add_left _ _ _
        smul_left := by
          intro u v c
          rw [map_smul]
          exact (h.toCore x).smul_left _ _ _
        definite := by
          intro v hv
          apply (e x).symm.injective
          rw [map_zero]
          exact (h.toCore x).definite _ hv }
    -- Smooth inverse columns compare Gram entries in the two original atlases.
    have hinv := he.symm e
    have hgram (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f] (i j : Fin q) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ (core y).inner (f.symmL ℂ y (EuclideanSpace.single i 1))
            (f.symmL ℂ y (EuclideanSpace.single j 1))) f.baseSet := by
      intro x hx
      let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      have hdx : x ∈ d.baseSet := mem_baseSet_trivializationAt _ _ x
      let coord (a : Fin q) (y : X) :=
        (d ⟨y, (e y).symm (f.symmL ℂ y (EuclideanSpace.single a 1))⟩).2
      have hcoord (a : Fin q) (b : Fin r) :
          ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
            (fun y ↦ coord a y b) (f.baseSet ∩ d.baseSet) :=
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) b).restrictScalars
          ℝ).contMDiff.comp_contMDiffOn (hinv f d a)
      have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ ∑ a, ∑ b,
            (starRingEnd ℂ) (coord i y a) * h.gramMatrix d y a b * coord j y b)
          (f.baseSet ∩ d.baseSet) := by
        apply contMDiffOn_finsetSum
        intro a _
        apply contMDiffOn_finsetSum
        intro b _
        have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i a)
        have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
        exact hmul.contMDiff.comp_contMDiffOn
          ((hmul.contMDiff.comp_contMDiffOn
            (hconj.prodMk_space ((h.contMDiffOn_gram d a b).mono
              (fun _ hy ↦ hy.2)))).prodMk_space (hcoord j b))
      have hactual := hsum.congr (f₁ := fun y ↦ (core y).inner
        (f.symmL ℂ y (EuclideanSpace.single i 1))
        (f.symmL ℂ y (EuclideanSpace.single j 1))) (by
          intro y hy
          exact h.pairing_eq_gramMatrix d y hy.2 _ _)
      exact (hactual.contMDiffAt ((f.open_baseSet.inter d.open_baseSet).mem_nhds
        ⟨hx, hdx⟩)).contMDiffWithinAt
    refine ⟨⟨core, hgram, hSmoothF⟩, ?_⟩
    intro x v w
    change h.pairing x ((e x).symm (e x v)) ((e x).symm (e x w)) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  let V : Opens U := ⟨(Subtype.val : U → M) ⁻¹' Kᶜ,
    hK.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
  let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  dsimp only
  intro τE τF hτE hτF hidentity
  -- Keep one common exterior model using the given rank equality, including empty exteriors.
  let A : EuclideanSpace ℂ (Fin E.rank) ≃L[ℂ] EuclideanSpace ℂ (Fin F.rank) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr hEF)).toContinuousLinearEquiv
  let τF' (x : V) := (τF x).trans A.toLinearEquiv
  have hτF' : IsSmoothBundleMap (n := n) (r := F.rank) (q := F.rank) (M := V)
      (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ F.Fiber))
      (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin F.rank)))
      (fun x ↦ (τF' x).toLinearMap) :=
    comp_smooth (X := V)
      (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ F.Fiber))
      (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
      (G := Bundle.Trivial V (EuclideanSpace ℂ (Fin F.rank)))
      (fun x ↦ (τF x).toLinearMap) hτF
      (fun _ ↦ A.toLinearMap)
      (constant_smooth (X := V) A.toContinuousLinearMap)
  obtain ⟨G, hG, eE, heE, σE, hσE, hσEeq⟩ :=
    exists_smoothBundle_extension_of_exterior_trivialization U K hK
      (hKL.trans hLU) E τE hτE
  obtain ⟨H, hH, eF, heF, σF', hσF', hσF'eq⟩ :=
    exists_smoothBundle_extension_of_exterior_trivialization U K hK
      (hKL.trans hLU) F τF' hτF'
  let σF (x : W) := (σF' x).trans A.symm.toLinearEquiv
  have hσF : IsSmoothBundleMap (n := n) (r := H.rank) (q := E.rank) (M := W)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      (fun x ↦ (σF x).toLinearMap) :=
    comp_smooth (X := W)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin F.rank)))
      (G := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      (fun x ↦ (σF' x).toLinearMap) hσF'
      (fun _ ↦ A.symm.toLinearMap)
      (constant_smooth (X := W) A.symm.toContinuousLinearMap)
  have hσFeq (x : V) (v : F.Fiber x.val) :
      σF ⟨x.val.val, x.property⟩ (eF x.val v) = τF x v := by
    dsimp only [σF, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [hσF'eq]
    exact A.symm_apply_apply (τF x v)
  -- Transport the original map on U and glue its prescribed identity on the exterior W.
  let : ∀ x, FiniteDimensional ℂ (G.Fiber x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin G.rank)) G.Fiber x
  let d (x : M) : G.Fiber x →L[ℂ] H.Fiber x :=
    if hx : x ∈ U then
      ((eF ⟨x, hx⟩).toLinearMap.comp
        ((c ⟨x, hx⟩).toLinearMap.comp (eE ⟨x, hx⟩).symm.toLinearMap)).toContinuousLinearMap
    else
      (((σF ⟨x, fun hxK ↦ hx (hLU (hKL hxK))⟩).symm.toLinearMap).comp
        (σE ⟨x, fun hxK ↦ hx (hLU (hKL hxK))⟩).toLinearMap).toContinuousLinearMap
  have hdU (x : U) (v : G.Fiber x.val) :
      d x.val v = eF x (c x ((eE x).symm v)) := by
    dsimp only [d]
    rw [dite_eq_left x.property]
    rfl
  have hdW (x : W) (v : G.Fiber x.val) :
      d x.val v = (σF x).symm (σE x v) := by
    by_cases hxU : x.val ∈ U
    · let y : V := ⟨⟨x.val, hxU⟩, x.property⟩
      rw [hdU ⟨x.val, hxU⟩ v]
      apply (σF x).injective
      rw [LinearEquiv.apply_symm_apply, hσFeq y, hidentity y]
      simpa only [LinearEquiv.apply_symm_apply] using
        (hσEeq y ((eE y.val).symm v)).symm
    · dsimp only [d]
      rw [dite_eq_right hxU]
      rfl
  have hdUsmooth : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ H.Fiber))
      (fun x ↦ (d x.val).toLinearMap) := by
    have ha := comp_smooth (X := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (F := E.Fiber) (G := F.Fiber) (fun x ↦ (eE x).symm.toLinearMap)
      (IsSmoothBundleMap.symm (M := U) (E := E.Fiber)
        (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber)) eE heE)
      (fun x ↦ (c x).toLinearMap) hc
    have hb := comp_smooth (X := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (F := F.Fiber)
      (G := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ H.Fiber))
      _ ha (fun x ↦ (eF x).toLinearMap) heF
    intro e he f hf j
    let := he
    let := hf
    exact (@hb e he f hf j).congr (fun y _ ↦ congrArg
      (fun v ↦ (f ⟨y, v⟩).2) (hdU y _))
  have hdWsmooth : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank) (M := W)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ G.Fiber))
      (F := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
      (fun x ↦ (d x.val).toLinearMap) := by
    have ha := comp_smooth (X := W)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ G.Fiber))
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
      (G := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
      (fun x ↦ (σE x).toLinearMap) hσE
      (fun x ↦ (σF x).symm.toLinearMap)
      (IsSmoothBundleMap.symm (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ H.Fiber))
        (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank))) σF hσF)
    intro e he f hf j
    let := he
    let := hf
    exact (@ha e he f hf j).congr (fun y _ ↦ congrArg
      (fun v ↦ (f ⟨y, v⟩).2) (hdW y _))
  have hdsmooth : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
      (fun x ↦ (d x).toLinearMap) :=
    glue_smooth (E := G.Fiber) (F := H.Fiber) U W (fun x ↦ by
      by_cases hx : x ∈ U
      · exact Or.inl hx
      · exact Or.inr (fun hxK ↦ hx (hLU (hKL hxK))))
      (fun x ↦ (d x).toLinearMap) hdUsmooth hdWsmooth
  -- Restrict the original G and H atlases once along the same inclusion from U to M.
  let inclU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let hGpullback : IsSmoothComplexBundle (n := n) (r := G.rank) (M := U)
      ((inclU : U → M) *ᵖ G.Fiber) :=
    isSmoothComplexBundle_pullback (n := n) (m := n) (M := M) (N := U)
      G.Fiber inclU (contMDiff_subtype_val (U := U))
  let hHpullback : IsSmoothComplexBundle (n := n) (r := H.rank) (M := U)
      ((inclU : U → M) *ᵖ H.Fiber) :=
    isSmoothComplexBundle_pullback (n := n) (m := n) (M := M) (N := U)
      H.Fiber inclU (contMDiff_subtype_val (U := U))
  -- Pass each same-atlas proof explicitly with the fixed source and target model ranks.
  obtain ⟨hGlocal, hGlocalEq⟩ :=
    transport_metric (r := E.rank) (q := G.rank) (X := U)
      (E := E.Fiber)
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (hSmoothF := hGpullback) h eE heE
  obtain ⟨hHlocal, hHlocalEq⟩ :=
    transport_metric (r := F.rank) (q := H.rank) (X := U)
      (E := F.Fiber)
      (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ H.Fiber))
      (hSmoothF := hHpullback) k eF heF
  obtain ⟨g, Og, hLOg, hOgU, hg⟩ :=
    exists_smoothHermitianMetric_extension G.Fiber U L hL hLU hGlocal
  obtain ⟨l, Ol, hLOl, hOlU, hl⟩ :=
    exists_smoothHermitianMetric_extension H.Fiber U L hL hLU hHlocal
  obtain ⟨μ, hμ, Oμ, hLOμ, hOμU, hμEq⟩ :=
    exists_smoothPositiveMeasure_extension (n := n) U L hL hLU ν
  -- One common neighborhood retains both pairings and the same actual local measure.
  let O : Opens M := Og ⊓ Ol ⊓ Oμ
  refine ⟨G, H, hG, hH, eE, eF, heE, heF, σE, σF, hσE, hσF,
    hσEeq, hσFeq, d, hdsmooth, ?_, ?_, ?_, g, l, μ, hμ, O, ?_, ?_, ?_, ?_, ?_⟩
  · intro x v
    rw [hdU, LinearEquiv.symm_apply_apply]
  · intro x v
    rw [hdW, LinearEquiv.apply_symm_apply]
  · intro x hx
    have heq : (d x : G.Fiber x → H.Fiber x) =
        (fun v ↦ (σF ⟨x, hx⟩).symm (σE ⟨x, hx⟩ v)) := funext (hdW ⟨x, hx⟩)
    rw [heq]
    exact (σF ⟨x, hx⟩).symm.bijective.comp (σE ⟨x, hx⟩).bijective
  · intro x hx
    exact ⟨⟨hLOg hx, hLOl hx⟩, hLOμ hx⟩
  · intro x hx
    exact hOgU hx.1.1
  · intro x hx v w
    exact (hg x hx.1.1 _ _).trans (hGlocalEq x v w)
  · intro x hx v w
    exact (hl x hx.1.2 _ _).trans (hHlocalEq x v w)
  · have hOmeas : MeasurableSet ((Subtype.val : U → M) ⁻¹' (O : Set M)) :=
      O.isOpen.measurableSet.preimage measurable_subtype_coe
    have hsmall : ((Subtype.val : U → M) ⁻¹' (O : Set M)) ⊆
        ((Subtype.val : U → M) ⁻¹' (Oμ : Set M)) := fun _ hx ↦ hx.2
    have hrestrict := congrArg
      (fun θ : Measure U ↦ θ.restrict ((Subtype.val : U → M) ⁻¹' (O : Set M))) hμEq
    simpa only [Measure.restrict_restrict hOmeas, Set.inter_eq_left.mpr hsmall] using
      hrestrict

end AtiyahSinger
