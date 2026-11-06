/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedMetricL2KernelCokernel
public import AtiyahSinger.Analysis.EquivariantFredholmCoordinates
public import AtiyahSinger.Analysis.SmoothEquivariantIndex

/-!
# The smooth index on an exact invariant domain realization

Public module ID: M0501.

An injective domain embedding with the original elliptic closed graph
identifies the actual kernel and range quotient. If it intertwines the
specified integral action, the bounded realization computes the original
smooth representation-valued index. The domain norm is retained throughout;
it can be the fixed Hilbert graph norm used before cutoff averaging.
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
  [hG : LieGroup IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Keep the arbitrary domain and both original quotient maps explicit in the finite coordinates.
/-- The same exact closed graph computes the full smooth index in any equivariant domain norm. -/
theorem smoothEquivariantAnalyticIndex_eq_of_graph_realization
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (γ : ContRepresentation ℂ G X)
    (hγ : Continuous (fun p : G × X ↦ γ p.1 p.2))
    (J : X →L[ℂ] h.L2SectionSpace μ) (hJ : Function.Injective J)
    (hJg : ∀ g x, J (γ g x) =
      h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g (J x))
    (T : X →L[ℂ] k.L2SectionSpace μ)
    (hgraph : (P.metricL2ClosedRealization h k).graph = (J.prod T).toLinearMap.range)
    (hTg : ∀ g, T.comp (γ g) =
      (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant g).comp T)
    (hT : T.IsFredholm) :
    P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
      equivariantFredholmIndex γ
        (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant) hγ
        (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
        T hTg hT := by
  classical
  let L := P.metricL2ClosedRealization h k
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  obtain ⟨κ, χ, e, f, he, hf⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  obtain ⟨eS, fS, heS, hfS⟩ :=
    P.exists_metricL2ClosedRealization_kernel_cokernel_equiv h k hP
  -- The domain embedding sends kernel vectors to their original zero-output graph points.
  have hker (x : h.L2SectionSpace μ) : x ∈ L.ker ↔ (x, 0) ∈ L.graph := by
    constructor
    · intro hx
      obtain ⟨u, rfl, hu⟩ := L.mem_ker_iff.mp hx
      exact L.mem_graph_iff'.mpr ⟨u, Prod.ext rfl hu⟩
    · intro hx
      obtain ⟨u, hu⟩ := L.mem_graph_iff'.mp hx
      exact L.mem_ker_iff.mpr ⟨u, (congrArg Prod.fst hu).symm, congrArg Prod.snd hu⟩
  let i₀ : T.ker →ₗ[ℂ] L.ker :=
    (J.toLinearMap.comp T.ker.subtype).codRestrict L.ker (by
      intro v
      apply (hker _).mpr
      rw [hgraph]
      exact ⟨v.val, Prod.ext rfl v.property⟩)
  have hi₀ : Function.Bijective i₀ := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hJ (congrArg Subtype.val hxy))
    · intro x
      have hx := (hker x.val).mp x.property
      rw [hgraph] at hx
      obtain ⟨v, hv⟩ := hx
      refine ⟨⟨v, congrArg Prod.snd hv⟩, ?_⟩
      exact Subtype.ext (congrArg Prod.fst hv)
  let i := LinearEquiv.ofBijective i₀ hi₀
  have hR : T.range = L.toFun.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (J x, T x) ∈ L.graph := by
        rw [hgraph]
        exact ⟨x, rfl⟩
      obtain ⟨u, hu⟩ := L.mem_graph_iff'.mp hx
      exact ⟨u, congrArg Prod.snd hu⟩
    · rintro ⟨u, rfl⟩
      have hu : (u.val, L u) ∈ L.graph := L.mem_graph_iff'.mpr ⟨u, rfl⟩
      rw [hgraph] at hu
      obtain ⟨x, hx⟩ := hu
      exact ⟨x, congrArg Prod.snd hx⟩
  let cQ := Submodule.quotEquivOfEq L.toFun.range T.range hR.symm
  have hq (v : k.L2SectionSpace μ) : cQ (L.toFun.range.mkQ v) = T.range.mkQ v := rfl
  let eT := (e.trans eS).trans i.symm
  let fT := (f.trans fS).trans cQ
  have heT (v : Fin κ.dimension → ℂ) :
      J (eT v).val = h.smoothToL2 μ (e v).val := by
    change J (i.symm (eS (e v))).val = _
    calc
      J (i.symm (eS (e v))).val = (i (i.symm (eS (e v)))).val := rfl
      _ = (eS (e v)).val := congrArg Subtype.val (i.apply_symm_apply _)
      _ = h.smoothToL2 μ (e v).val := heS (e v)
  have hfT (v : smoothSections (n := n) (r := q) F) :
      fT (f.symm (P.toLinearMap.range.mkQ v)) = T.range.mkQ (k.smoothToL2 μ v) := by
    change cQ (fS (f (f.symm (P.toLinearMap.range.mkQ v)))) = _
    rw [f.apply_symm_apply, hfS, hq]
  -- Both finite actions are compared on the same original smooth representative.
  rw [P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP κ χ e f he hf]
  symm
  apply equivariantFredholmIndex_eq_of_coordinates γ τ hγ
    (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
    T hTg hT κ χ eT fT
  · intro g v
    apply hJ
    rw [hJg, heT, heT, he]
    exact (h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE
      hInvariant hμInvariant g (e v).val).symm
  · let RC := equivariantCokernelRepresentation γ τ T hTg
    have hfinite (g : G) (v : Fin χ.dimension → ℂ) :
        fT (χ.representation g v) = RC g (fT v) := by
      obtain ⟨w, hw⟩ := P.toLinearMap.range.mkQ_surjective (f v)
      have hv : v = f.symm (P.toLinearMap.range.mkQ w) := by
        rw [hw, f.symm_apply_apply]
      have hfw := hf g w
      have hfv : f (χ.representation g v) =
          P.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF g w) := by
        rw [hv]
        exact hfw
      change cQ (fS (f (χ.representation g v))) = RC g (fT v)
      rw [hfv, hfS, hq, hv, hfT]
      change T.range.mkQ (k.smoothToL2 μ
          (σF.smoothSectionRepresentation IG hσF g w)) =
        T.range.mkQ (τ g (k.smoothToL2 μ w))
      exact congrArg T.range.mkQ (k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF
        kInvariant hμInvariant g w).symm
    intro g v
    rw [hfinite, fT.apply_symm_apply]
    rfl

end AtiyahSinger.PseudodifferentialOperator
