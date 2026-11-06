/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantFineApproximation
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTriple

/-!
# Smooth equivariant boundary maps with the original compact control

Public module ID: M1173.

On two already smooth equivariant bundles, an original continuous exterior
isomorphism is equivariantly homotopic to a smooth exterior isomorphism.
The original bundles, their actions and their one specified compact control
remain fixed. The result supplies the actual new boundary and a continuous
equivariant isomorphism homotopy whose control is exactly the original set.
It neither enlarges that control nor discards the boundary data at infinity.

The exterior of a compact set need not be compact, even when the base is
compact. Fine approximation with a positive continuous pointwise tolerance
replaces a uniform invertibility margin. Smoothness refers to the native
pullback atlases on this exact open exterior. The original base need not be
compact, and both fixed model ranks may be zero.

SG I.9.23--9.26 and ASI I Section 2 give the underlying equivariant support
framework. SG Appendix A, Remark A.1, states ordinary smooth classification;
SG III.9 supplies compact-group averaging. The same-control smooth boundary
homotopy is a project supplement to those source statements.
The proof retains the original exterior and control throughout the actual affine
homotopy.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace Topology
open scoped Manifold ContDiff unitInterval

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
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

variable
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hE hF hG hGC hGT hAction hσE hσF

/-- Smooth the original equivariant exterior isomorphism with exactly the same compact control. -/
theorem CompactSupportTriple.exists_equivariant_smooth_boundary_homotopy
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      CompactSupportTriple E F)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.IsEquivariant σE σF) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    let W : Opens M := ⟨a.controlᶜ, a.isCompact_control.isClosed.isOpen_compl⟩
    ∃ β : RelativeTriple E F a.controlᶜ,
      IsSmoothBundleMap (n := n) (r := r) (q := q) (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E))
        (F := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F))
        (fun x ↦ (β.linearEquiv x).toLinearMap) ∧
      let b : CompactSupportTriple E F :=
        { control := a.control
          isCompact_control := a.isCompact_control
          boundary := β }
      b.IsEquivariant σE σF ∧
        ∃ H : CompactSupportTriple.EquivariantHomotopy σE σF a b,
          H.control = a.control := by
  /- Stage 1: retain W as the complement of the original compact control K.
  Hausdorffness makes W open. Pull back the original smooth bundle atlases
  along its inclusion and compare the native modeled pullback topology with
  the original Unit-tagged restriction topology, preserving all vectors.
  Invariance restricts the original base and bundle actions to this same W;
  their joint smoothness restricts to its native open-submanifold atlas.
  Stage 2: choose smooth Hermitian metrics on these restricted bundles.
  In a local frame, the compact model unit sphere gives a positive lower
  bound for the original boundary map on a neighborhood of each point.
  The argument also covers empty spheres at rank zero. Combine these
  local bounds by a locally finite smooth partition of unity to obtain
  a positive continuous margin d(x). No global positive lower bound on
  the noncompact exterior, or invariance of the metrics, is required.
  Stage 3: apply equivariant fine approximation with tolerance d(x)/2.
  Its metric error estimate and the original map's lower bound show
  that every affine map for t in I is injective. Compose with the
  original inverse and use finite-dimensional injectivity/surjectivity
  to obtain bijectivity without comparing global ranks on empty W.
  Stage 4: prove continuity of this same affine cylinder in the original
  frames. Hom.toIso supplies its continuous inverse from fiberwise
  bijectivity; the endpoint at t=1 gives the new smooth boundary map.
  Both endpoints intertwine the same restricted actions, so each affine
  slice does too. The initial map is continuous; no smooth cylinder is
  asserted. Restore the original restriction topology for these same maps.
  Stage 5: form b and its EquivariantHomotopy with the original K, its
  compactness and invariance certificates, and reflexive control inclusions.
  Same-set restriction identities give the exact cylinder endpoints.
  Consequently H.control=K, also when W is empty. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let W : Opens M := ⟨a.controlᶜ, a.isCompact_control.isClosed.isOpen_compl⟩
  let i : C(W, M) := ContinuousMap.subtypeVal (W : Set M)
  let E' := (i : W → M) *ᵖ E
  let F' := (i : W → M) *ᵖ F
  -- The native modeled pullback and the old Unit restriction preserve the same total topology.
  let tE' : TopologicalSpace (TotalSpace Unit E') :=
    @Pullback.TotalSpace.topologicalSpace M Unit E W (i : W → M) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  let tF' : TopologicalSpace (TotalSpace Unit F') :=
    @Pullback.TotalSpace.topologicalSpace M Unit F W (i : W → M) _
      (modelTopology (EuclideanSpace ℂ (Fin q)) F)
  have hEtop : modelTopology (EuclideanSpace ℂ (Fin r)) E' = tE' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tE', modelTopology]
    rfl
  have hFtop : modelTopology (EuclideanSpace ℂ (Fin q)) F' = tF' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tF', modelTopology]
    rfl
  let : TopologicalSpace (TotalSpace Unit E') := modelTopology (EuclideanSpace ℂ (Fin r)) E'
  let : TopologicalSpace (TotalSpace Unit F') := modelTopology (EuclideanSpace ℂ (Fin q)) F'
  let hEsmooth : IsSmoothComplexBundle (n := n) (r := r) E' :=
    isSmoothComplexBundle_pullback E i contMDiff_subtype_val
  let hFsmooth : IsSmoothComplexBundle (n := n) (r := q) F' :=
    isSmoothComplexBundle_pullback F i contMDiff_subtype_val
  -- Invariance restricts the actual base action to this exact open exterior.
  let : MulAction G W :=
    { smul g x := ⟨g • x.val, fun hx ↦ x.property ((ha.invariant_control g x.val).mp hx)⟩
      one_smul x := Subtype.ext (one_smul G x.val)
      mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let : ContinuousSMul G W :=
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G W :=
    ⟨(ContMDiff.subtypeVal_comp_iff W (fun p : G × W ↦ p.1 • p.2)).mp
      (contMDiff_fst.smul (contMDiff_subtype_val.comp contMDiff_snd))⟩
  have hElift : Function.Injective (fun z : TotalSpace Unit E' ↦
      (⟨z.proj.val, z.snd⟩ : TotalSpace Unit E)) := by
    rintro ⟨x, u⟩ ⟨y, v⟩ huv
    have hxy : x = y := Subtype.ext (congrArg TotalSpace.proj huv)
    subst y
    exact congrArg (fun w : E x.val ↦ (⟨x, w⟩ : TotalSpace Unit E'))
      (TotalSpace.mk_injective x.val huv)
  -- The restricted action on E retains each original moving-fiber linear map.
  let ρE : EquivariantStructure G E' :=
    { linearMap g x := σE.linearMap g x.val
      one_map x v := hElift (σE.one_map x.val v)
      mul_map g h x v := hElift (σE.mul_map g h x.val v)
      continuous_action := by
        change @Continuous _ _
          (@instTopologicalSpaceProd G (TotalSpace Unit E') _
            (modelTopology (EuclideanSpace ℂ (Fin r)) E'))
          (modelTopology (EuclideanSpace ℂ (Fin r)) E') _
        rw [hEtop]
        let : TopologicalSpace (TotalSpace Unit E') := tE'
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E i).continuous_iff]
        have hb : Continuous (fun p : G × TotalSpace Unit E' ↦ p.1 • p.2.proj) :=
          continuous_fst.smul ((Pullback.continuous_proj Unit E i).comp continuous_snd)
        have hv := σE.continuous_action.comp (continuous_fst.prodMk
          ((Pullback.continuous_lift Unit E i).comp continuous_snd))
        exact hb.prodMk hv }
  have hρE : ρE.IsSmooth (n := n) (r := r) IG := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : G × W ↦ (p.1, (p.2 : M))) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    apply ((hσE e f j).comp hi.contMDiffOn (fun p hp ↦ hp)).congr
    intro p hp
    have heq : (e.pullback i).symmL ℂ p.2 (EuclideanSpace.single j 1) =
        e.symmL ℂ p.2.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hp.1, e.symmL_apply (R := ℂ) hp.1,
        (e.pullback i).symm_apply hp.1]
      rfl
    change (f ⟨p.1 • p.2.val, σE.linearMap p.1 p.2.val
      ((e.pullback i).symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2 =
        (f ⟨p.1 • p.2.val, σE.linearMap p.1 p.2.val
          (e.symmL ℂ p.2.val (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  have hFlift : Function.Injective (fun z : TotalSpace Unit F' ↦
      (⟨z.proj.val, z.snd⟩ : TotalSpace Unit F)) := by
    rintro ⟨x, u⟩ ⟨y, v⟩ huv
    have hxy : x = y := Subtype.ext (congrArg TotalSpace.proj huv)
    subst y
    exact congrArg (fun w : F x.val ↦ (⟨x, w⟩ : TotalSpace Unit F'))
      (TotalSpace.mk_injective x.val huv)
  -- The restricted action on F retains each original moving-fiber linear map.
  let ρF : EquivariantStructure G F' :=
    { linearMap g x := σF.linearMap g x.val
      one_map x v := hFlift (σF.one_map x.val v)
      mul_map g h x v := hFlift (σF.mul_map g h x.val v)
      continuous_action := by
        change @Continuous _ _
          (@instTopologicalSpaceProd G (TotalSpace Unit F') _
            (modelTopology (EuclideanSpace ℂ (Fin q)) F'))
          (modelTopology (EuclideanSpace ℂ (Fin q)) F') _
        rw [hFtop]
        let : TopologicalSpace (TotalSpace Unit F') := tF'
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F i).continuous_iff]
        have hb : Continuous (fun p : G × TotalSpace Unit F' ↦ p.1 • p.2.proj) :=
          continuous_fst.smul ((Pullback.continuous_proj Unit F i).comp continuous_snd)
        have hv := σF.continuous_action.comp (continuous_fst.prodMk
          ((Pullback.continuous_lift Unit F i).comp continuous_snd))
        exact hb.prodMk hv }
  have hρF : ρF.IsSmooth (n := n) (r := q) IG := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : G × W ↦ (p.1, (p.2 : M))) :=
      contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    apply ((hσF e f j).comp hi.contMDiffOn (fun p hp ↦ hp)).congr
    intro p hp
    have heq : (e.pullback i).symmL ℂ p.2 (EuclideanSpace.single j 1) =
        e.symmL ℂ p.2.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hp.1, e.symmL_apply (R := ℂ) hp.1,
        (e.pullback i).symm_apply hp.1]
      rfl
    change (f ⟨p.1 • p.2.val, σF.linearMap p.1 p.2.val
      ((e.pullback i).symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2 =
        (f ⟨p.1 • p.2.val, σF.linearMap p.1 p.2.val
          (e.symmL ℂ p.2.val (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  let α : Iso E' F' :=
    { linearEquiv x := a.boundary.linearEquiv x
      continuous_total := by
        change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) E')
          (modelTopology (EuclideanSpace ℂ (Fin q)) F') _
        rw [hEtop, hFtop]
        exact a.boundary.continuous_total
      continuous_symm := by
        change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) F')
          (modelTopology (EuclideanSpace ℂ (Fin r)) E') _
        rw [hEtop, hFtop]
        exact a.boundary.continuous_symm }
  have hα : α.IsEquivariant ρE ρF := fun g x v ↦ ha.boundary_intertwines g x v
  let : ∀ x, FiniteDimensional ℂ (E' x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E' x
  let : ∀ x, FiniteDimensional ℂ (F' x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F' x
  let : IsFiniteRank E' := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E'
  let : IsFiniteRank F' := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F'
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) (hE := hEsmooth) E'
  obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := q) (hE := hFsmooth) F'
  -- The original smooth Gram matrices give continuity without replacing any fiber norm.
  have hHquad : Continuous (fun z : TotalSpace Unit E' ↦
      (h.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin r)) E'
    have hb : Continuous (fun z : TotalSpace Unit E' ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin r)) E'
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E' z.proj
    let U : Set (TotalSpace Unit E') := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit E' ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E').continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin r) : ContinuousOn
        (fun w : TotalSpace Unit E' ↦ h.gramMatrix e w.proj i j) U :=
      (h.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit E' ↦
        (∑ i : Fin r, ∑ j : Fin r,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * h.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (h.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  have hKquad : Continuous (fun z : TotalSpace Unit F' ↦
      (k.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin q)) F'
    have hb : Continuous (fun z : TotalSpace Unit F' ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin q)) F'
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F' z.proj
    let U : Set (TotalSpace Unit F') := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit F' ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F').continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin q) : ContinuousOn
        (fun w : TotalSpace Unit F' ↦ k.gramMatrix e w.proj i j) U :=
      (k.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit F' ↦
        (∑ i : Fin q, ∑ j : Fin q,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * k.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (k.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  let H (x : W) : Seminorm ℂ (E' x) := by
    let : InnerProductSpace.Core ℂ (E' x) := h.toCore x
    exact @normSeminorm ℂ (E' x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  let K (x : W) : Seminorm ℂ (F' x) := by
    let : InnerProductSpace.Core ℂ (F' x) := k.toCore x
    exact @normSeminorm ℂ (F' x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  have hH (x : W) (v : E' x) : H x v = Real.sqrt (h.pairing x v v).re := rfl
  have hK (x : W) (v : F' x) : K x v = Real.sqrt (k.pairing x v v).re := rfl
  have hHc : Continuous (fun z : TotalSpace Unit E' ↦ H z.proj z.snd) :=
    hHquad.sqrt
  have hKc : Continuous (fun z : TotalSpace Unit F' ↦ K z.proj z.snd) :=
    hKquad.sqrt
  -- A compact model sphere gives α positive local lower bound, including empty spheres.
  let e (x : W) := trivializationAt (EuclideanSpace ℂ (Fin r)) E' x
  have hlocal (x : W) : ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set W,
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ v : E' y,
        δ * H y v ≤ K y (α.linearEquiv y v) := by
    let O : Set W := (e x).baseSet
    have hW : IsOpen O := (e x).open_baseSet
    have hx : x ∈ O := mem_baseSet_trivializationAt _ _ _
    let x₀ : O := ⟨x, hx⟩
    let T := O × EuclideanSpace ℂ (Fin r)
    let v (p : T) : E' p.1.val := (e x).symmL ℂ p.1.val p.2
    have hv : Continuous (fun p : T ↦ (⟨p.1.val, v p⟩ : TotalSpace Unit E')) := by
      apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin r)) E' _).mpr
      have hc := (e x).continuousOn_symm.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p : T ↦ ⟨p.1.property, Set.mem_univ _⟩)
      apply hc.congr
      intro p
      change (⟨p.1.val, (e x).symm p.1.val p.2⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E') = ⟨p.1.val, v p⟩
      exact congrArg (fun w : E' p.1.val ↦
        (⟨p.1.val, w⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E'))
        ((e x).symmL_apply p.1.property p.2).symm
    have hH₀ : Continuous (fun u : EuclideanSpace ℂ (Fin r) ↦ H x (v (x₀, u))) :=
      (hHc.comp hv).comp (continuous_const.prodMk continuous_id)
    have hK₀ : Continuous (fun u : EuclideanSpace ℂ (Fin r) ↦
        K x (α.linearEquiv x (v (x₀, u)))) :=
      (hKc.comp (α.continuous_total.comp hv)).comp
        ((continuous_const (y := x₀)).prodMk continuous_id)
    have hvpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) : v (x₀, u) ≠ 0 := by
      have hu₀ : u ≠ 0 := by
        intro hz
        simp [hz] at hu
      intro hz
      apply hu₀
      have he := (e x).continuousLinearMapAt_symmL (R := ℂ) hx u
      rw [show (e x).symmL ℂ x u = 0 from hz, map_zero] at he
      exact he.symm
    have hHpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) :
        0 < H x (v (x₀, u)) := by
      rw [hH, Real.sqrt_pos]
      exact h.pairing_self_pos _ _ (hvpos u hu)
    have hKpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) :
        0 < K x (α.linearEquiv x (v (x₀, u))) := by
      rw [hK, Real.sqrt_pos]
      apply k.pairing_self_pos
      simpa only [map_zero] using (α.linearEquiv x).injective.ne_iff.mpr (hvpos u hu)
    obtain ⟨c, hc, hcBound⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1).exists_forall_le'
        (hK₀.continuousOn.div hH₀.continuousOn (fun u hu ↦ (hHpos u hu).ne'))
        (fun u hu ↦ div_pos (hKpos u hu) (hHpos u hu))
    let δ := c / 2
    have hδ : 0 < δ := half_pos hc
    let d (p : T) : ℝ := K p.1.val (α.linearEquiv p.1.val (v p)) - δ * H p.1.val (v p)
    have hd : Continuous d := (hKc.comp (α.continuous_total.comp hv)).sub
      (continuous_const.mul (hHc.comp hv))
    have hpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) : 0 < d (x₀, u) := by
      have hb := (le_div_iff₀ (hHpos u hu)).mp (hcBound u hu)
      have hp := hHpos u hu
      change 0 < K x (α.linearEquiv x (v (x₀, u))) - δ * H x (v (x₀, u))
      dsimp only [δ]
      nlinarith
    have hevent : ∀ᶠ y : O in 𝓝 x₀,
        ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1, 0 < d (y, u) :=
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1).eventually_forall_of_forall_eventually
          (fun u hu ↦ (hd.continuousAt (x := (x₀, u))).eventually
            (Ioi_mem_nhds (hpos u hu)))
    obtain ⟨V, hsub, hV, hxV⟩ := mem_nhds_iff.mp hevent
    have hVo : IsOpen ((Subtype.val : O → W) '' V) := hW.isOpenMap_subtype_val _ hV
    refine ⟨δ, hδ, Subtype.val '' V, hVo, ⟨x₀, hxV, rfl⟩, ?_⟩
    rintro y ⟨y', hy', rfl⟩ w
    by_cases hw : w = 0
    · simp [hw]
    let u := (e x) ⟨y'.val, w⟩ |>.2
    have hu : u ≠ 0 := by
      intro hz
      apply hw
      have he := (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property w
      rw [(e x).continuousLinearMapAt_apply_of_mem ℂ y'.property] at he
      change (e x).symmL ℂ y'.val u = w at he
      rw [hz, map_zero] at he
      exact he.symm
    let u₀ := (‖u‖⁻¹ : ℂ) • u
    have hu₀ : u₀ ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1 := by
      simpa [u₀, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hu
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hrecover : (‖u‖ : ℂ) • v (y', u₀) = w := by
      dsimp only [v, u₀]
      rw [map_smul, smul_smul]
      rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu_norm.ne'), one_smul]
      dsimp only [u]
      rw [← (e x).continuousLinearMapAt_apply_of_mem ℂ y'.property]
      exact (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property w
    have hbound := le_of_lt (sub_pos.mp (hsub hy' u₀ hu₀))
    conv_lhs => rw [← hrecover]
    conv_rhs => rw [← hrecover]
    simp only [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu_norm.le]
    nlinarith [mul_le_mul_of_nonneg_left hbound hu_norm.le]
  choose δ hδ U hUopen hxU hUbound using hlocal
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  -- Locally finite convex averaging gives a positive continuous pointwise margin.
  let : LocallyCompactSpace W :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) W
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ U hUopen hcover
  let d (x : W) : ℝ := ∑ᶠ j : W, ρ j x * δ j
  have hdsum (x : W) : d x = ∑ j ∈ ρ.finsupport x, ρ j x * δ j := by
    exact (ρ.sum_finsupport_smul_eq_finsum x (fun j _ ↦ δ j)).symm
  have hdc : Continuous d := by
    exact (ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (fun j _ _ ↦ contMDiffAt_const)).continuous
  have hd (x : W) : 0 < d x := by
    rw [hdsum]
    obtain ⟨j, hj⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (ρ.nonneg j x) (hδ j).le
    · exact ⟨j, (ρ.mem_finsupport x).mpr hj.ne', mul_pos hj (hδ j)⟩
  have hmargin (x : W) (v : E' x) : d x * H x v ≤ K x (α.linearEquiv x v) := by
    rw [hdsum, Finset.sum_mul]
    calc
      (∑ j ∈ ρ.finsupport x, ρ j x * δ j * H x v) ≤
          ∑ j ∈ ρ.finsupport x, ρ j x * K x (α.linearEquiv x v) := by
        apply Finset.sum_le_sum
        intro j hj
        have hnz : ρ j x ≠ 0 := (ρ.mem_finsupport x).mp hj
        have hxU := hρ j (subset_tsupport (ρ j) hnz)
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hUbound j x hxU v) (ρ.nonneg j x)
      _ = K x (α.linearEquiv x v) := by
        rw [← Finset.sum_mul, ρ.sum_finsupport x (Set.mem_univ x), one_mul]
  -- Approximate the same original exterior map within half this actual local margin.
  let ε : C(W, ℝ) := ⟨fun x ↦ d x / 2, hdc.div_const 2⟩
  obtain ⟨b, hbsmooth, hbequiv, hbclose⟩ :=
    α.toHom.exists_equivariant_smooth_fine_approximation (hE := hEsmooth) (hF := hFsmooth)
      IG ρE ρF hρE hρF hα h k ε
      (fun x ↦ half_pos (hd x))
  have herror (x : W) (v : E' x) :
      K x (b.linearMap x v - α.linearEquiv x v) ≤ d x / 2 * H x v := by
    apply (sq_le_sq₀ (apply_nonneg (K x) _) (mul_nonneg (half_pos (hd x)).le
      (apply_nonneg (H x) v))).mp
    have hkpos : 0 ≤ (k.pairing x (b.linearMap x v - α.linearEquiv x v)
        (b.linearMap x v - α.linearEquiv x v)).re := (k.toCore x).re_inner_nonneg _
    have hhpos : 0 ≤ (h.pairing x v v).re := (h.toCore x).re_inner_nonneg _
    rw [hK, hH, mul_pow, Real.sq_sqrt hkpos, Real.sq_sqrt hhpos]
    exact hbclose x v
  let L (t : I) (x : W) : E' x →ₗ[ℂ] F' x :=
    α.toHom.linearMap x + (((t : ℝ) : ℂ) • (b.linearMap x - α.toHom.linearMap x))
  have hLzero (x : W) (v : E' x) : L 0 x v = α.linearEquiv x v := by
    simp [L, Iso.toHom]
  have hLone (x : W) (v : E' x) : L 1 x v = b.linearMap x v := by
    simp [L]
  have hLinj (t : I) (x : W) : Function.Injective (L t x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hv₀
    have hHpos : 0 < H x v := by
      rw [hH, Real.sqrt_pos]
      exact h.pairing_self_pos x v hv₀
    have hav : α.linearEquiv x v = -(((t : ℝ) : ℂ) •
        (b.linearMap x v - α.linearEquiv x v)) := by
      change α.linearEquiv x v + (((t : ℝ) : ℂ) •
        (b.linearMap x v - α.linearEquiv x v)) = 0 at hv
      exact eq_neg_of_add_eq_zero_left hv
    have hupper : K x (α.linearEquiv x v) ≤ d x / 2 * H x v := by
      calc
        K x (α.linearEquiv x v) = (t : ℝ) *
            K x (b.linearMap x v - α.linearEquiv x v) := by
          conv_lhs => rw [hav]
          rw [map_neg_eq_map, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg t.property.1]
        _ ≤ K x (b.linearMap x v - α.linearEquiv x v) :=
          mul_le_of_le_one_left (apply_nonneg (K x) _) t.property.2
        _ ≤ d x / 2 * H x v := herror x v
    have hlower := hmargin x v
    have hdpos := hd x
    nlinarith
  have hLbij (t : I) (x : W) : Function.Bijective (L t x) := by
    refine ⟨hLinj t x, ?_⟩
    let A : E' x →ₗ[ℂ] E' x := (α.linearEquiv x).symm.toLinearMap.comp (L t x)
    have hAinj : Function.Injective A := (α.linearEquiv x).symm.injective.comp (hLinj t x)
    have hAsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hAinj
    intro w
    obtain ⟨v, hv⟩ := hAsurj ((α.linearEquiv x).symm w)
    refine ⟨v, (α.linearEquiv x).symm.injective hv⟩
  -- Keep the actual affine cylinder, and test its joint continuity in original frames.
  let p : I × W → W := Prod.snd
  let : IsFiniteRank (p *ᵖ E') := isFiniteRank_pullback (E := E') ⟨p, continuous_snd⟩
  let : IsFiniteRank (p *ᵖ F') := isFiniteRank_pullback (E := F') ⟨p, continuous_snd⟩
  have hLcontinuous : Continuous (fun z : TotalSpace Unit (p *ᵖ E') ↦
      (⟨z.proj.2, L z.proj.1 z.proj.2 z.snd⟩ : TotalSpace Unit F')) := by
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F' _).mpr
    apply continuous_iff_continuousAt.mpr
    intro z
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F' z.proj.2
    have hz : z.proj.2 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hbase : Continuous (fun w : TotalSpace Unit (p *ᵖ E') ↦ w.proj.2) :=
      (Pullback.continuous_proj Unit E' p).snd
    apply f.continuousAt_of_comp_left hbase.continuousAt hz
    have hac := ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F').comp
      (α.continuous_total.comp (Pullback.continuous_lift Unit E' p))).continuousAt (x := z)
    have hbc := ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F').comp
      (b.continuous_total.comp (Pullback.continuous_lift Unit E' p))).continuousAt (x := z)
    have hca := ((f.continuousAt (f.mem_source.mpr hz)).comp hac).snd
    have hcb := ((f.continuousAt (f.mem_source.mpr hz)).comp hbc).snd
    have htime : Continuous (fun w : TotalSpace Unit (p *ᵖ E') ↦ ((w.proj.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp (Pullback.continuous_proj Unit E' p).fst)
    have hcoord := hca.add (htime.continuousAt.smul (hcb.sub hca))
    apply (hbase.continuousAt.prodMk hcoord).congr_of_eventuallyEq
    filter_upwards [(f.open_baseSet.preimage hbase).mem_nhds hz] with w hw
    refine Prod.ext (f.proj_toFun _ (f.mem_source.mpr hw)) ?_
    change (f ⟨w.proj.2, α.linearEquiv w.proj.2 w.snd + ((w.proj.1 : ℝ) : ℂ) •
        (b.linearMap w.proj.2 w.snd - α.linearEquiv w.proj.2 w.snd)⟩).2 =
      (f ⟨w.proj.2, α.linearEquiv w.proj.2 w.snd⟩).2 + ((w.proj.1 : ℝ) : ℂ) •
        ((f ⟨w.proj.2, b.linearMap w.proj.2 w.snd⟩).2 -
          (f ⟨w.proj.2, α.linearEquiv w.proj.2 w.snd⟩).2)
    simp only [← f.continuousLinearMapAt_apply_of_mem ℂ hw]
    rw [map_add, map_smul, map_sub]
  let c : Hom (p *ᵖ E') (p *ᵖ F') :=
    { linearMap y := L y.1 y.2
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F' p).continuous_iff]
        exact (Pullback.continuous_proj Unit E' p).prodMk hLcontinuous }
  let B : Iso E' F' := b.toIso (fun x ↦ by
    have heq : L 1 x = b.linearMap x := LinearMap.ext (hLone x)
    have hi := hLbij 1 x
    rwa [heq] at hi)
  let Hpath : IsoHomotopy α B :=
    { iso := c.toIso (fun y ↦ hLbij y.1 y.2)
      map_zero := hLzero
      map_one := hLone }
  -- Restore the original Unit restriction topology while retaining the very same maps.
  let β : RelativeTriple E F a.controlᶜ :=
    { linearEquiv x := B.linearEquiv x
      continuous_total := by
        have hc := B.continuous_total
        change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) E')
          (modelTopology (EuclideanSpace ℂ (Fin q)) F') _ at hc
        rw [hEtop, hFtop] at hc
        exact hc
      continuous_symm := by
        have hc := B.continuous_symm
        change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) F')
          (modelTopology (EuclideanSpace ℂ (Fin r)) E') _ at hc
        rw [hEtop, hFtop] at hc
        exact hc }
  refine ⟨β, hbsmooth, ?_, ?_⟩
  · exact ⟨ha.invariant_control, fun g x v ↦ hbequiv g x v⟩
  · let T : CompactSupportTriple E F :=
      { control := a.control
        isCompact_control := a.isCompact_control
        boundary := β }
    let Horiginal : IsoHomotopy
        (a.enlarge a.control a.isCompact_control (Set.Subset.refl _)).boundary
        (T.enlarge a.control a.isCompact_control (Set.Subset.refl _)).boundary :=
      { iso :=
          { linearEquiv y := Hpath.iso.linearEquiv y
            continuous_total := by
              have hc := Hpath.iso.continuous_total
              change @Continuous _ _
                (@Pullback.TotalSpace.topologicalSpace W Unit E' (I × W) p _
                  (modelTopology (EuclideanSpace ℂ (Fin r)) E'))
                (@Pullback.TotalSpace.topologicalSpace W Unit F' (I × W) p _
                  (modelTopology (EuclideanSpace ℂ (Fin q)) F')) _ at hc
              rw [hEtop, hFtop] at hc
              exact hc
            continuous_symm := by
              have hc := Hpath.iso.continuous_symm
              change @Continuous _ _
                (@Pullback.TotalSpace.topologicalSpace W Unit F' (I × W) p _
                  (modelTopology (EuclideanSpace ℂ (Fin q)) F'))
                (@Pullback.TotalSpace.topologicalSpace W Unit E' (I × W) p _
                  (modelTopology (EuclideanSpace ℂ (Fin r)) E')) _ at hc
              rw [hEtop, hFtop] at hc
              exact hc }
        map_zero := by
          intro x v
          exact (Hpath.map_zero x v).trans
            (a.enlarge_apply a.control a.isCompact_control (Set.Subset.refl _) x v).symm
        map_one := by
          intro x v
          exact (Hpath.map_one x v).trans
            (T.enlarge_apply a.control a.isCompact_control (Set.Subset.refl _) x v).symm }
    -- Copy the exact original compact control and verify every time slice's same-action square.
    refine ⟨{ control := a.control
              isCompact_control := a.isCompact_control
              invariant_control := ha.invariant_control
              left_control := Set.Subset.refl _
              right_control := Set.Subset.refl _
              homotopy := Horiginal
              intertwines := ?_ }, rfl⟩
    intro t g x v
    change L t (g • x) (ρE.linearMap g x v) = ρF.linearMap g x (L t x v)
    change α.toHom.linearMap (g • x) (ρE.linearMap g x v) + ((t : ℝ) : ℂ) •
        (b.linearMap (g • x) (ρE.linearMap g x v) -
          α.toHom.linearMap (g • x) (ρE.linearMap g x v)) =
      ρF.linearMap g x (α.toHom.linearMap x v + ((t : ℝ) : ℂ) •
        (b.linearMap x v - α.toHom.linearMap x v))
    rw [hα g x v, hbequiv g x v, map_add, map_smul, map_sub]

end AtiyahSinger.ComplexBundle
