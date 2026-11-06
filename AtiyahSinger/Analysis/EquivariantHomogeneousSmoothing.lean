/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.EquivariantBoundarySmoothing
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

/-!
# Smooth equivariant homogeneous boundaries on original pullback bundles

Public module ID: M0523.

A continuous equivariant isomorphism off the zero section, on the pullbacks
of two specified smooth equivariant bundles over a compact manifold, has a
smooth degree-zero homogeneous representative. The same original bundles and
actions are retained. The output is exactly the existing ellipticSymbolTriple
of the selected homogeneous function, connected to the original triple by an
actual equivariant boundary homotopy with the zero section as its control.
Their equality is in the original equivariant support group, before forgetting.

The compact group has the given finite-dimensional smooth model; the base
is Hausdorff and second countable. The supplied smooth cotangent metric is
invariant for the original inverse
differential lift. Its unit sphere is compact, but the punctured cotangent
bundle is not assumed compact. No global bound for the original inverse on
that punctured bundle is required. Neither equal ranks nor positive dimension
is assumed, and the original boundary need not already be homogeneous.

SG III.13 Lemma 13.3 and the paragraph preceding (13.7), pp.245--246, give
the ordinary homogeneous representative route; SG Appendix A, Remark A.1,
supplies ordinary smooth bundle classification; SG III.9 supplies averaging.
The equivariant homogeneous smoothing statement, fine approximation and
boundary smoothing arguments are project supplements to these sources.
This is a fixed-bundle theorem, not realization of every equivariant K class
on one pair of globally fixed-rank smooth bundles. The proof smooths the original
boundary, extends its restriction to the invariant unit cosphere, and constructs
a positive radial cylinder on the same pullback fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle IsManifold
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hV : FiniteDimensional ℝ V] [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type}
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
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hV hG hGC hGT hM hT hSC hC hAction hE hF hσE hσF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Original pullback topologies, model change and the two boundary cylinders remain explicit.
set_option linter.unusedSectionVars false in

/-- Smooth homogeneous realization of the original equivariant boundary, with zero control. -/
theorem CompactSupportTriple.exists_equivariant_homogeneous_smooth_boundary
    (h : SmoothCotangentMetric (n := n) (M := M))
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
          (cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ)
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
    (hControl : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.control = cotangentZeroSet)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := IG)
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      a.IsEquivariant
        (σE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
        (σF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let ρE := σE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl)
    let ρF := σF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl)
    ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0,
      ∃ hi : IsEllipticGlobalSymbol E F s.val,
        (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
          equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ) ∧
        let b := ellipticSymbolTriple s.val s.property.1.continuous hi
        ∃ hb : b.IsEquivariant ρE ρF,
          (∃ H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b,
            H.control = cotangentZeroSet) ∧
          (EquivariantSupportBundleTriple.ofBoundary
            (FiniteBundle.ofFamily
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E))
            (FiniteBundle.ofFamily
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
            a ρE ρF ha).kZeroClass =
          (EquivariantSupportBundleTriple.ofBoundary
            (FiniteBundle.ofFamily
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E))
            (FiniteBundle.ofFamily
              ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
            b ρE ρF hb).kZeroClass := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  rcases a with ⟨K, hK, α⟩
  dsimp only at hControl
  subst K
  let a : CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
    ⟨cotangentZeroSet, hK, α⟩
  -- Keep the original cotangent topology while choosing a Euclidean smooth model.
  -- A countable cover of actual bundle charts supplies second countability.
  let CT := CotangentTotalSpace (n := n) (M := M)
  let V₀ := EuclideanSpace ℝ (Fin n)
  let W₀ := V₀ × CotangentModel n
  let I₀ := 𝓘(ℝ, V₀).prod 𝓘(ℝ, CotangentModel n)
  let : SecondCountableTopology CT := by
    let U (x : M) : Set M :=
      (trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x).baseSet ∩
        (chartAt V₀ x).source
    have hU (x : M) : U x ∈ nhds x := by
      let e := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
      exact Filter.inter_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x))
        (chart_source_mem_nhds V₀ x)
    obtain ⟨s, hsc, hs⟩ := countable_cover_nhds_of_sigmaCompact hU
    let : SecondCountableTopology (ModelProd V₀ (CotangentModel n)) :=
      inferInstanceAs (SecondCountableTopology (V₀ × CotangentModel n))
    apply ChartedSpace.secondCountable_of_countable_cover
      (ModelProd V₀ (CotangentModel n)) (s := cotangentZeroSection '' s) ?_
      (hsc.image cotangentZeroSection)
    apply Set.eq_univ_of_forall
    intro z
    have hz : z.proj ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hx, hz⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr ⟨cotangentZeroSection x, ?_⟩
    apply Set.mem_iUnion.mpr ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [FiberBundle.chartedSpace_chartAt]
    change z.proj ∈
        (trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x).baseSet ∧
      (((trivializationAt (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) x) z).1 ∈ (chartAt V₀ x).source ∧ _)
    refine ⟨hz.1, ?_, Set.mem_univ _⟩
    rw [Trivialization.coe_fst' _ hz.1]
    exact hz.2
  have hCT : IsManifold I₀ ∞ CT := inferInstance
  let : ChartedSpace W₀ CT := inferInstanceAs (ChartedSpace
    (ModelProd V₀ (CotangentModel n)) CT)
  let : IsManifold 𝓘(ℝ, W₀) ∞ CT := by
    rw [modelWithCornersSelf_prod]
    exact hCT
  let R : CotangentModel n ≃L[ℝ] V₀ :=
    (InnerProductSpace.toDual ℝ V₀).symm.toContinuousLinearEquiv
  let e : W₀ ≃L[ℝ] EuclideanSpace ℝ (Fin (n + n)) :=
    ((ContinuousLinearEquiv.refl ℝ V₀).prodCongr R).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)).symm
  let := linearModelChartedSpace e CT
  let := isManifold_linearModelChartedSpace e CT
  let d := linearModelDiffeomorph e CT
  have hπ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n)))
      𝓘(ℝ, V₀) ∞ (cotangentProjection (n := n) (M := M)) := by
    have hp : ContMDiff I₀ 𝓘(ℝ, V₀) ∞
        (cotangentProjection (n := n) (M := M)) :=
      contMDiff_proj (CotangentFiber (n := n) (M := M))
    have hi : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) I₀ ∞
        (id : CT → CT) := by
      dsimp only [I₀]
      rw [← modelWithCornersSelf_prod]
      exact d.contMDiff_invFun
    exact hp.comp hi
  have hforward : ContMDiff I₀ 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞
      (id : CT → CT) := by
    dsimp only [I₀]
    rw [← modelWithCornersSelf_prod]
    exact d.contMDiff_toFun
  have hreverse : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) I₀ ∞
      (id : CT → CT) := by
    dsimp only [I₀]
    rw [← modelWithCornersSelf_prod]
    exact d.contMDiff_invFun
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ G CT := by
    constructor
    have hact : ContMDiff (IG.prod I₀) I₀ ∞ (fun z : G × CT ↦ z.1 • z.2) :=
      contMDiff_smul
    exact hforward.comp (hact.comp
      (contMDiff_fst.prodMk (hreverse.comp contMDiff_snd)))
  -- Pull back the original frames and actions through the same smooth projection.
  -- The explicit topology equalities allow boundary smoothing on those exact bundles.
  let p : C(CT, M) := cotangentProjection (n := n) (M := M)
  let E' := (p : CT → M) *ᵖ E
  let F' := (p : CT → M) *ᵖ F
  let : IsSmoothComplexBundle (n := n + n) (r := r) E' :=
    isSmoothComplexBundle_pullback E p hπ
  let : IsSmoothComplexBundle (n := n + n) (r := q) F' :=
    isSmoothComplexBundle_pullback F p hπ
  let tE' : TopologicalSpace (TotalSpace Unit E') :=
    @Pullback.TotalSpace.topologicalSpace M Unit E CT (p : CT → M) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  let tF' : TopologicalSpace (TotalSpace Unit F') :=
    @Pullback.TotalSpace.topologicalSpace M Unit F CT (p : CT → M) _
      (modelTopology (EuclideanSpace ℂ (Fin q)) F)
  have hEtop : modelTopology (EuclideanSpace ℂ (Fin r)) E' = tE' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tE', modelTopology]
    rfl
  have hFtop : modelTopology (EuclideanSpace ℂ (Fin q)) F' = tF' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tF', modelTopology]
    rfl
  let PE (L : ∀ (g : G) (z : CT), E' z →ₗ[ℂ] E' (g • z)) : Prop :=
    ∀ (e₀ f₀ : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀], ∀ j : Fin r,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun z : G × CT ↦
          (f₀ ⟨z.1 • z.2, L z.1 z.2
            (e₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2)
        {z : G × CT | z.2 ∈ e₀.baseSet ∧ z.1 • z.2 ∈ f₀.baseSet}
  let PF (L : ∀ (g : G) (z : CT), F' z →ₗ[ℂ] F' (g • z)) : Prop :=
    ∀ (e₀ f₀ : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀], ∀ j : Fin q,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
        (fun z : G × CT ↦
          (f₀ ⟨z.1 • z.2, L z.1 z.2
            (e₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2)
        {z : G × CT | z.2 ∈ e₀.baseSet ∧ z.1 • z.2 ∈ f₀.baseSet}
  let ρE := σE.pullback p (fun _ _ ↦ rfl)
  let ρF := σF.pullback p (fun _ _ ↦ rfl)
  have hρE : PE ρE.linearMap := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × CT ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hπ.comp contMDiff_snd)
    apply ((hσE e₀ f₀ j).comp hi.contMDiffOn (fun z hz ↦ hz)).congr
    intro z hz
    have heq : (e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1) =
        e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1) := by
      rw [(e₀.pullback p).symmL_apply (R := ℂ) hz.1,
        e₀.symmL_apply (R := ℂ) hz.1, (e₀.pullback p).symm_apply hz.1]
      rfl
    change (f₀ ⟨z.1 • p z.2, σE.linearMap z.1 (p z.2)
      ((e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 =
        (f₀ ⟨z.1 • p z.2, σE.linearMap z.1 (p z.2)
          (e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  have hρF : PF ρF.linearMap := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × CT ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hπ.comp contMDiff_snd)
    apply ((hσF e₀ f₀ j).comp hi.contMDiffOn (fun z hz ↦ hz)).congr
    intro z hz
    have heq : (e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1) =
        e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1) := by
      rw [(e₀.pullback p).symmL_apply (R := ℂ) hz.1,
        e₀.symmL_apply (R := ℂ) hz.1, (e₀.pullback p).symm_apply hz.1]
      rfl
    change (f₀ ⟨z.1 • p z.2, σF.linearMap z.1 (p z.2)
      ((e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 =
        (f₀ ⟨z.1 • p z.2, σF.linearMap z.1 (p z.2)
          (e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  let Φ (tE : TopologicalSpace (TotalSpace Unit E'))
      (tF : TopologicalSpace (TotalSpace Unit F')) : Prop :=
    letI := tE
    letI := tF
    ∀ (τE : EquivariantStructure G E') (τF : EquivariantStructure G F'),
      PE τE.linearMap → PF τF.linearMap →
      ∀ (c : CompactSupportTriple E' F'), c.IsEquivariant τE τF →
      let W : TopologicalSpace.Opens CT :=
        ⟨c.controlᶜ, c.isCompact_control.isClosed.isOpen_compl⟩
      ∃ β : RelativeTriple E' F' c.controlᶜ,
        IsSmoothBundleMap (n := n + n) (r := r) (q := q) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set CT) : W → CT) *ᵖ E'))
          (F := ((ContinuousMap.subtypeVal (W : Set CT) : W → CT) *ᵖ F'))
          (fun z ↦ (β.linearEquiv z).toLinearMap) ∧
        let b : CompactSupportTriple E' F' :=
          { control := c.control
            isCompact_control := c.isCompact_control
            boundary := β }
        b.IsEquivariant τE τF ∧
          ∃ H : CompactSupportTriple.EquivariantHomotopy τE τF c b,
            H.control = c.control
  have hsmooth : Φ tE' tF' := by
    let hE' : IsSmoothComplexBundle (n := n + n) (r := r) E' := inferInstance
    let hF' : IsSmoothComplexBundle (n := n + n) (r := q) F' := inferInstance
    rw [← hEtop, ← hFtop]
    intro τE τF hτE hτF c hc
    let := hE'
    let := hF'
    exact c.exists_equivariant_smooth_boundary_homotopy (n := n + n) (r := r) (q := q)
      (E := E') (F := F') (hE := hE') (hF := hF') IG τE τF hτE hτF hc
  obtain ⟨β, hβsmooth, hβeq, Hβ, hHβ⟩ := hsmooth ρE ρF hρE hρF a ha
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let W : TopologicalSpace.Opens CT :=
    ⟨cotangentZeroSetᶜ, isClosed_cotangentZeroSet.isOpen_compl⟩
  let incl : C(W, CT) := ⟨Subtype.val, continuous_subtype_val⟩
  have hβcongr (x : M) (ξ η : CotangentFiber (n := n) x)
      (hξ : ξ ≠ 0) (hη : η ≠ 0) (heq : ξ = η) (v : E x) :
      β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v = β.linearEquiv ⟨⟨x, η⟩, hη⟩ v := by
    subst η
    rfl
  let b₀ : GlobalSymbolFunction (n := n) E F := fun x ξ ↦
    if hξ : ξ ≠ 0 then
      LinearMap.toContinuousLinearMap
        (show E x →ₗ[ℂ] F x from (β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩).toLinearMap)
    else 0
  have hb₀ (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) (v : E x) :
      b₀ x ξ v = β.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v := by
    simp only [b₀, dite_eq_left hξ]
    rfl
  -- Evaluate the smooth boundary in the original symbol charts; both pullback frames
  -- preserve their fiber vectors, so chart smoothness concerns the same boundary.
  have hb₀smooth : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F b₀ := by
    intro c hc e₀ f₀ _ _ z hz
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let U : TopologicalSpace.Opens (X × X) :=
      ⟨symbolChartDomain E F c e₀ f₀ ×ˢ {ξ | ξ ≠ 0},
        (isOpen_symbolChartDomain E F c e₀ f₀).prod isClosed_singleton.isOpen_compl⟩
    have hne (y : U) : covectorFromChart c (c.symm y.val.1) y.val.2 ≠ 0 := by
      intro hzero
      have hi := covectorInChart_covectorFromChart c hc (c.symm y.val.1)
        (c.map_target y.property.1.1.1) y.val.2
      rw [hzero] at hi
      have hzcoord : covectorInChart c (c.symm y.val.1) 0 = 0 := by ext j; rfl
      exact y.property.2 (hi.symm.trans hzcoord)
    let j : U → W := fun y ↦
      ⟨⟨c.symm y.val.1, covectorFromChart c (c.symm y.val.1) y.val.2⟩, hne y⟩
    have hj : ContMDiff 𝓘(ℝ, X × X) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ j := by
      intro y
      have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
      have hbase : ContMDiffAt 𝓘(ℝ, X × X) I ∞
          (fun y : X × X ↦ c.symm y.1) y.val :=
        (contMDiffAt_symm_of_mem_maximalAtlas hcm y.property.1.1.1).comp y.val
          contDiffAt_fst.contMDiffAt
      have hd := ((contMDiffAt_of_mem_maximalAtlas hcm
        (c.map_target y.property.1.1.1)).mfderiv_const
          (m := (∞ : WithTop ℕ∞)) (by simp)).comp y.val hbase
      have hinner : ContMDiffAt 𝓘(ℝ, X × X) 𝓘(ℝ, CotangentModel n) ∞
          (fun y : X × X ↦ innerSL ℝ y.2) y.val :=
        (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp y.val contDiffAt_snd.contMDiffAt
      have hmap : ContMDiffAt 𝓘(ℝ, X × X) I₀ ∞
          (fun y : X × X ↦ (⟨c.symm y.1, covectorFromChart c (c.symm y.1) y.2⟩ : CT))
          y.val := by
        apply (contMDiffAt_hom_bundle _).mpr
        refine ⟨hbase, ?_⟩
        apply (hinner.clm_comp hd).congr_of_eventuallyEq
        filter_upwards with y'
        ext v
        simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          Function.id_def, ContinuousLinearMap.comp_apply, I]
        rfl
      apply (ContMDiffAt.subtypeVal_comp_iff W j y).mp
      exact hforward.contMDiffAt.comp y (contMDiffAt_subtype_iff.mpr hmap)
    let e' := (e₀.pullback p).pullback incl
    let f' := (f₀.pullback p).pullback incl
    let : MemTrivializationAtlas (e₀.pullback p) := ⟨⟨e₀, inferInstance, rfl⟩⟩
    let : MemTrivializationAtlas (f₀.pullback p) := ⟨⟨f₀, inferInstance, rfl⟩⟩
    let : MemTrivializationAtlas e' := ⟨⟨e₀.pullback p, inferInstance, rfl⟩⟩
    let : MemTrivializationAtlas f' := ⟨⟨f₀.pullback p, inferInstance, rfl⟩⟩
    have hmatrix := IsSmoothBundleMap.contMDiffOn_matrix (M := W)
      (n := n + n) (r := r) (q := q) (E := (incl : W → CT) *ᵖ E')
      (F := (incl : W → CT) *ᵖ F')
      (fun x ↦ (β.linearEquiv x).toLinearMap) hβsmooth e' f'
    have hcoords := hmatrix.comp hj.contMDiffOn (fun y (_ : y ∈ Set.univ) ↦
      (show j y ∈ e'.baseSet ∩ f'.baseSet from ⟨y.property.1.1.2, y.property.1.2⟩))
    have hfull := contMDiffOn_univ.mp hcoords
    have hraw : ContMDiff 𝓘(ℝ, X × X)
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun y : U ↦ globalSymbolInChart E F b₀ c e₀ f₀ y.val.1 y.val.2) := by
      apply hfull.congr
      intro y
      apply ContinuousLinearMap.ext
      intro v
      simp only [globalSymbolInChart, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
        ContinuousLinearMap.comp_apply]
      have he : (e'.symmL ℂ (j y)) v = e₀.symmL ℂ (c.symm y.val.1) v := by
        rw [e'.symmL_apply y.property.1.1.2,
          e₀.symmL_apply y.property.1.1.2]
        change ((e₀.pullback p).pullback incl).symm (j y) v =
          e₀.symm (c.symm y.val.1) v
        rw [((e₀.pullback p).pullback incl).symm_apply y.property.1.1.2]
        change (e₀.pullback p).symm (incl (j y)) v = e₀.symm (c.symm y.val.1) v
        rw [(e₀.pullback p).symm_apply y.property.1.1.2]
        rfl
      change (f₀.continuousLinearMapAt ℂ (c.symm y.val.1))
        (b₀ (c.symm y.val.1) (covectorFromChart c (c.symm y.val.1) y.val.2)
          (e₀.symmL ℂ (c.symm y.val.1) v)) =
        f'.linearMapAt ℂ (j y) (β.linearEquiv (j y) (e'.symmL ℂ (j y) v))
      rw [he, hb₀ _ _ (hne y)]
      rw [f'.coe_linearMapAt_of_mem y.property.1.2]
      exact f₀.continuousLinearMapAt_apply_of_mem ℂ y.property.1.2 _
    have hrawAt : ContMDiffAt 𝓘(ℝ, X × X)
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (Function.uncurry (globalSymbolInChart E F b₀ c e₀ f₀)) z :=
      (contMDiffAt_subtype_iff (U := U)
        (f := Function.uncurry (globalSymbolInChart E F b₀ c e₀ f₀))
        (x := (⟨z, hz⟩ : U))).mp (by
          simpa only [Function.uncurry] using (hraw.contMDiffAt (x := (⟨z, hz⟩ : U))))
    exact hrawAt.contDiffAt.contDiffWithinAt
  -- Radial extension uses this same smooth boundary on the invariant unit cosphere.
  let cs : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) h :=
    ⟨cosphereRestriction h b₀, isSmoothCosphereSymbol_restriction h b₀ hb₀smooth⟩
  let s := smoothCosphereExtension h 0 cs
  have hs (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) (v : E x) :
      s.val x ξ v = β.linearEquiv
        ⟨⟨x, h.normalize x ξ⟩, h.normalize_ne_zero x ξ hξ⟩ v := by
    change cosphereExtension h 0 (cosphereRestriction h b₀) x ξ v = _
    rw [cosphereExtension_of_ne_zero h 0 _ x ξ hξ]
    simpa only [Real.rpow_zero, Complex.ofReal_one, one_smul, cosphereRestriction,
      SmoothCotangentMetric.radial] using hb₀ x (h.normalize x ξ)
        (h.normalize_ne_zero x ξ hξ) v
  have hi : IsEllipticGlobalSymbol E F s.val := by
    intro x ξ hξ
    have hf : (s.val x ξ : E x → F x) = fun v ↦ β.linearEquiv
        ⟨⟨x, h.normalize x ξ⟩, h.normalize_ne_zero x ξ hξ⟩ v := funext (hs x ξ hξ)
    rw [hf]
    exact (β.linearEquiv _).bijective
  have hnorm (g : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      h.normalize (g • x) (g • (⟨x, ξ⟩ : CT)).snd =
        (g • (⟨x, h.normalize x ξ⟩ : CT)).snd := by
    have hlen : h.length (g • x) (g • (⟨x, ξ⟩ : CT)).snd = h.length x ξ := hInv g x ξ
    simp only [SmoothCotangentMetric.normalize, hlen]
    rfl
  let TS := TotalSpace Unit E'
  let : MulAction G TS := ρE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let T : TS → TotalSpace Unit F := fun w ↦
    ⟨w.proj.proj, s.val w.proj.proj w.proj.snd w.snd⟩
  have hcov (g : G) (w : TS) (hw : w.proj.snd ≠ 0) : T (g • w) = g • T w := by
    rcases w with ⟨⟨x, ξ⟩, v⟩
    have hgne : (g • (⟨x, ξ⟩ : CT)).snd ≠ 0 := fun hz ↦
      hw ((ha.1 g ⟨x, ξ⟩).mp hz)
    change (⟨g • x, s.val (g • x) (g • (⟨x, ξ⟩ : CT)).snd
      (σE.linearMap g x v)⟩ : TotalSpace Unit F) =
        ⟨g • x, σF.linearMap g x (s.val x ξ v)⟩
    congr 1
    erw [hs (g • x) _ hgne, hs x ξ hw]
    have hgne' : (g • (⟨x, h.normalize x ξ⟩ : CT)).snd ≠ 0 := fun hz ↦
      h.normalize_ne_zero x ξ hw ((ha.1 g ⟨x, h.normalize x ξ⟩).mp hz)
    exact (hβcongr (g • x) _ _ (h.normalize_ne_zero (g • x) _ hgne)
      hgne' (hnorm g x ξ) (σE.linearMap g x v)).trans
        (hβeq.2 g ⟨⟨x, h.normalize x ξ⟩, h.normalize_ne_zero x ξ hw⟩ v)
  -- Conjugation and moving-fiber equivariance are compared in the original total space.
  let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} hx ↦ by
    subst y
    exact ContinuousLinearMap.id ℂ (F x)
  have htransport {x y : M} (hx : x = y) (v : F x) :
      (⟨y, transport hx v⟩ : TotalSpace Unit F) = ⟨x, v⟩ := by
    subst y
    rfl
  have hconj (g : G) (w : TS) :
      (⟨w.proj.proj,
        equivariantGlobalSymbolLinearMap IG σE σF g s.val w.proj.proj w.proj.snd w.snd⟩ :
          TotalSpace Unit F) = g • T (g⁻¹ • w) := by
    change (⟨w.proj.proj,
      transport (smul_inv_smul g w.proj.proj)
      (σF.linearMap g (g⁻¹ • w.proj.proj)
        (s.val (g⁻¹ • w.proj.proj)
          ((cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm)
              w.proj).snd (σE.linearMap g⁻¹ w.proj.proj w.snd)))⟩ :
        TotalSpace Unit F) = _
    rw [htransport]
    erw [Diffeomorph.smul_symm]
    rfl
  have heq : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ := by
    intro g x ξ hξ
    ext v
    apply TotalSpace.mk_injective x
    rw [hconj g (⟨⟨x, ξ⟩, v⟩ : TS), hcov g⁻¹ (⟨⟨x, ξ⟩, v⟩ : TS) hξ,
      smul_inv_smul]
  let b := ellipticSymbolTriple s.val s.property.1.continuous hi
  have hb : b.IsEquivariant ρE ρF :=
    ellipticSymbolTriple_isEquivariant IG σE σF s.val s.property.1.continuous hi heq
  -- Positive radial rescaling is continuous at every nonzero covector and fixes its base.
  let scale (z : unitInterval × W) : ℝ :=
    (1 - (z.1 : ℝ)) + (z.1 : ℝ) * (h.length z.2.val.proj z.2.val.snd)⁻¹
  have hscale : Continuous scale := by
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (((h.continuous_length.comp continuous_subtype_val).comp continuous_snd).inv₀
          (fun z ↦ (h.length_pos _ _ z.2.property).ne')))
  have hpos (z : unitInterval × W) : 0 < scale z := by
    have hlen := inv_pos.mpr (h.length_pos _ _ z.2.property)
    have ht0 := z.1.property.1
    have ht1 := z.1.property.2
    by_cases hz : (z.1 : ℝ) = 0
    · simp only [scale, hz, sub_zero, zero_mul, add_zero, zero_lt_one]
    · have ht : 0 < (z.1 : ℝ) := lt_of_le_of_ne ht0 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1) (mul_pos ht hlen)
  let j : unitInterval × W → W := fun z ↦
    ⟨⟨z.2.val.proj, scale z • z.2.val.snd⟩, smul_ne_zero (hpos z).ne' z.2.property⟩
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let e₀ := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M))
      z₀.2.val.proj
    have hz := (FiberBundle.continuousAt_totalSpace (CotangentModel n)
      (fun z : unitInterval × W ↦ z.2.val) (x₀ := z₀)).mp
        (continuous_subtype_val.comp continuous_snd).continuousAt
    apply (FiberBundle.continuousAt_totalSpace (CotangentModel n) _).mpr
    refine ⟨hz.1, ?_⟩
    apply (hscale.continuousAt.smul hz.2).congr_of_eventuallyEq
    filter_upwards [hz.1.preimage_mem_nhds
      (e₀.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with z hz'
    change (e₀ ⟨z.2.val.proj, scale z • z.2.val.snd⟩).2 = scale z • (e₀ z.2.val).2
    rw [← e₀.continuousLinearMapAt_apply_of_mem ℝ hz',
      ← e₀.continuousLinearMapAt_apply_of_mem ℝ hz']
    exact map_smul (e₀.continuousLinearMapAt ℝ z.2.val.proj) _ _
  let RE := (incl : W → CT) *ᵖ E'
  let RF := (incl : W → CT) *ᵖ F'
  let πW : C(unitInterval × W, W) := ⟨Prod.snd, continuous_snd⟩
  let CE := (πW : unitInterval × W → W) *ᵖ RE
  let CF := (πW : unitInterval × W → W) *ᵖ RF
  -- The three pullback topologies track the same original fiber throughout the cylinder.
  have hinput : Continuous (fun w : TotalSpace Unit CE ↦
      (⟨j w.proj, w.snd⟩ : TotalSpace Unit RE)) := by
    have hp := Pullback.continuous_proj Unit RE πW
    have he := (Pullback.continuous_lift Unit E p).comp
      ((Pullback.continuous_lift Unit E' incl).comp (Pullback.continuous_lift Unit RE πW))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E' incl).continuous_iff]
    refine (hj.comp hp).prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact (continuous_subtype_val.comp (hj.comp hp)).prodMk he
  have hout := β.continuous_total.comp hinput
  have hf := (Pullback.continuous_lift Unit F p).comp
    ((Pullback.continuous_lift Unit F' incl).comp hout)
  let f : Hom CE CF := {
    linearMap z := (β.linearEquiv (j z)).toLinearMap
    continuous_total := by
      have hp := Pullback.continuous_proj Unit RE πW
      rw [(inducing_pullbackTotalSpaceEmbedding Unit RF πW).continuous_iff]
      refine hp.prodMk ?_
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F' incl).continuous_iff]
      refine (continuous_snd.comp hp).prodMk ?_
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact ((continuous_subtype_val.comp continuous_snd).comp hp).prodMk hf }
  let J : Iso CE CF := f.toIso (fun z ↦ (β.linearEquiv (j z)).bijective)
  have hJ (z : unitInterval × W) (v : E z.2.val.proj) :
      J.linearEquiv z v = β.linearEquiv (j z) v := rfl
  have hJzero (z : W) (v : E z.val.proj) : J.linearEquiv (0, z) v = β.linearEquiv z v := by
    rw [hJ]
    apply hβcongr z.val.proj _ _ (j (0, z)).property z.property _ v
    change (1 - (0 : ℝ) + 0 * (h.length z.val.proj z.val.snd)⁻¹) • z.val.snd = _
    simp only [sub_zero, zero_mul, add_zero, one_smul]
  have hJone (z : W) (v : E z.val.proj) :
      J.linearEquiv (1, z) v = b.boundary.linearEquiv z v := by
    rw [hJ, ellipticSymbolTriple_boundary_apply, hs _ _ z.property]
    apply hβcongr z.val.proj _ _ (j (1, z)).property
      (h.normalize_ne_zero _ _ z.property) _ v
    change (1 - (1 : ℝ) + 1 * (h.length z.val.proj z.val.snd)⁻¹) • z.val.snd = _
    simp only [sub_self, one_mul, zero_add, SmoothCotangentMetric.normalize]
  have hJinter (t : unitInterval) (g : G) (z : W) (v : E' z.val) :
      J.linearEquiv (t, ⟨g • z.val, fun hz ↦ z.property ((ha.1 g z.val).mp hz)⟩)
        (ρE.linearMap g z.val v) = ρF.linearMap g z.val (J.linearEquiv (t, z) v) := by
    let gz : W := ⟨g • z.val, fun hz ↦ z.property ((ha.1 g z.val).mp hz)⟩
    have hlen : h.length (g • z.val).proj (g • z.val).snd =
        h.length z.val.proj z.val.snd := hInv g z.val.proj z.val.snd
    have hsc : scale (t, gz) = scale (t, z) := by
      dsimp only [scale, gz]
      rw [hlen]
    have hcovector : scale (t, gz) • (g • z.val).snd =
        (g • (⟨z.val.proj, scale (t, z) • z.val.snd⟩ : CT)).snd := by
      rw [hsc]
      rfl
    rw [hJ, hJ]
    change β.linearEquiv ⟨⟨(g • z.val).proj, scale (t, gz) • (g • z.val).snd⟩, _⟩
      (σE.linearMap g z.val.proj v) =
        σF.linearMap g z.val.proj (β.linearEquiv (j (t, z)) v)
    have hgne : (g • (⟨z.val.proj, scale (t, z) • z.val.snd⟩ : CT)).snd ≠ 0 :=
      fun hz ↦ (j (t, z)).property ((ha.1 g (j (t, z)).val).mp hz)
    exact (hβcongr (g • z.val.proj) _ _ (j (t, gz)).property hgne hcovector
      (σE.linearMap g z.val.proj v)).trans (hβeq.2 g (j (t, z)) v)
  -- Combine the given smoothing path with radial rescaling using its exact middle boundary.
  rcases Hβ with ⟨L, hL, hLI, haL, hbL, H₀, hH₀⟩
  dsimp only at hHβ
  change L = cotangentZeroSet at hHβ
  subst L
  let C := β.symm.pullback πW
  let Q := H₀.iso.trans (C.trans J)
  have hH : ∃ H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b,
      H.control = cotangentZeroSet := by
    refine ⟨{ control := cotangentZeroSet
              isCompact_control := hK
              invariant_control := ha.1
              left_control := Set.Subset.refl _
              right_control := Set.Subset.refl _
              homotopy := { iso := Q, map_zero := ?_, map_one := ?_ }
              intertwines := ?_ }, rfl⟩
    · intro z v
      change J.linearEquiv (0, z) ((β.linearEquiv z).symm
        (H₀.iso.linearEquiv (0, z) v)) = _
      rw [hJzero, H₀.map_zero, LinearEquiv.apply_symm_apply]
    · intro z v
      change J.linearEquiv (1, z) ((β.linearEquiv z).symm
        (H₀.iso.linearEquiv (1, z) v)) = _
      rw [H₀.map_one, CompactSupportTriple.enlarge_apply]
      change J.linearEquiv (1, z) ((β.linearEquiv z).symm (β.linearEquiv z v)) = _
      rw [LinearEquiv.symm_apply_apply, hJone, CompactSupportTriple.enlarge_apply]
      rfl
    · intro t g z v
      let gz : W := ⟨g • z.val, fun hz ↦ z.property ((ha.1 g z.val).mp hz)⟩
      change J.linearEquiv (t, gz) ((β.linearEquiv gz).symm
        (H₀.iso.linearEquiv (t, gz) (ρE.linearMap g z.val v))) =
          ρF.linearMap g z.val (J.linearEquiv (t, z)
            ((β.linearEquiv z).symm (H₀.iso.linearEquiv (t, z) v)))
      rw [hH₀ t g z v]
      have hinv := hβeq.inverse.2 g z (H₀.iso.linearEquiv (t, z) v)
      change (β.linearEquiv gz).symm (ρF.linearMap g z.val
        (H₀.iso.linearEquiv (t, z) v)) = ρE.linearMap g z.val
          ((β.linearEquiv z).symm (H₀.iso.linearEquiv (t, z) v)) at hinv
      rw [hinv]
      exact hJinter t g z _
  refine ⟨s, hi, heq, hb, hH, ?_⟩
  exact equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (FiniteBundle.ofFamily E') (FiniteBundle.ofFamily F') ρE ρF a b ha hb ⟨hH.choose⟩

end AtiyahSinger.ComplexBundle
