/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereContinuousTopology
public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Analysis.PuncturedSymbol
public import AtiyahSinger.Geometry.EquivariantBundleMapAverageFamily
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Topology.EquivariantBundlePullback

/-!
# Equivariant projection in the original cosphere section topology

Public module ID: M0496.

An invariant smooth cotangent metric makes radial extension compatible with the
specified cotangent and bundle actions. The actual normalized Haar average on
those original punctured pullback bundles therefore induces a continuous map
on the original compact-open space of continuous cosphere symbols. Its image
is equivariant, it fixes equivariant symbols, and it preserves smooth symbols.

The construction retains arbitrary source and target fiber universes and ranks.
Only spatial variables are differentiated, so the group model need not be finite
dimensional. The smooth cosphere topology is not identified with the continuous
one. This is the averaging projection used with ordinary smooth density to control
elliptic relative paths, supplementing SG III.7.10--7.11 and III.9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle IsManifold MeasureTheory Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
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
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hG hGC hGT hM hT hE hF hσE hσF

attribute [local instance] t2Space_cotangent

set_option maxHeartbeats 2400000 in
-- Native model transport, both Hom-frame bridges and the same average elaborate together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
/-- Continuous Haar projection onto equivariant cosphere sections preserves smooth sections. -/
theorem exists_continuous_equivariant_cosphere_projection
    (h : SmoothCotangentMetric (n := n) (M := M))
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
          (cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
            ⟨x, ξ⟩).snd = h.length x ξ)
    : ∃ A : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) h →
        ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) h,
      @Continuous _ _ (continuousCosphereSymbolTopology h) (continuousCosphereSymbolTopology h) A ∧
      (∀ a, ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF g
          (cosphereExtension h 0 (A a).val) x ξ = cosphereExtension h 0 (A a).val x ξ) ∧
      (∀ a, (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE σF g (cosphereExtension h 0 a.val) x ξ =
          cosphereExtension h 0 a.val x ξ) → A a = a) ∧
      (∀ a, IsSmoothCosphereSymbol (r := r) (q := q) h a.val →
        IsSmoothCosphereSymbol (r := r) (q := q) h (A a).val) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let CT := CotangentTotalSpace (n := n) (M := M)
  let V₀ := EuclideanSpace ℝ (Fin n)
  let W₀ := V₀ × CotangentModel n
  let I₀ := 𝓘(ℝ, V₀).prod 𝓘(ℝ, CotangentModel n)
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
  let W : TopologicalSpace.Opens CT :=
    ⟨cotangentZeroSetᶜ, isClosed_cotangentZeroSet.isOpen_compl⟩
  have hne (g : G) (z : W) : (g • z.val).snd ≠ 0 := by
    intro hz
    have hn : 0 < h.length z.val.proj z.val.snd := h.length_pos _ _ z.property
    exact hn.ne' ((hInv g z.val.proj z.val.snd).symm.trans
      ((h.length_eq_zero_iff _ _).mpr hz))
  let : MulAction G W :=
    { smul g z := ⟨g • z.val, hne g z⟩
      one_smul z := Subtype.ext (one_smul G z.val)
      mul_smul g k z := Subtype.ext (mul_smul g k z.val) }
  let : ContinuousSMul G W :=
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ G W :=
    ⟨(ContMDiff.subtypeVal_comp_iff W (fun p : G × W ↦ p.1 • p.2)).mp
      (contMDiff_fst.smul (contMDiff_subtype_val.comp contMDiff_snd))⟩
  let p : C(W, M) := (cotangentProjection (n := n) (M := M)).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  have hp : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n)))
      𝓘(ℝ, V₀) ∞ p := hπ.comp contMDiff_subtype_val
  let E' := (p : W → M) *ᵖ E
  let F' := (p : W → M) *ᵖ F
  let : IsSmoothComplexBundle (n := n + n) (r := r) E' :=
    isSmoothComplexBundle_pullback E p hp
  let : IsSmoothComplexBundle (n := n + n) (r := q) F' :=
    isSmoothComplexBundle_pullback F p hp
  let tE' : TopologicalSpace (TotalSpace Unit E') :=
    @Pullback.TotalSpace.topologicalSpace M Unit E W (p : W → M) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  let tF' : TopologicalSpace (TotalSpace Unit F') :=
    @Pullback.TotalSpace.topologicalSpace M Unit F W (p : W → M) _
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
  have extE {u v : TotalSpace Unit E'} (hbase : u.proj = v.proj)
      (hvec : (⟨p u.proj, u.snd⟩ : TotalSpace Unit E) = ⟨p v.proj, v.snd⟩) : u = v := by
    rcases u with ⟨u, x⟩
    rcases v with ⟨v, y⟩
    dsimp only at hbase
    subst v
    exact congrArg (fun w ↦ (⟨u, w⟩ : TotalSpace Unit E'))
      (TotalSpace.mk_injective (p u) hvec)
  have extF {u v : TotalSpace Unit F'} (hbase : u.proj = v.proj)
      (hvec : (⟨p u.proj, u.snd⟩ : TotalSpace Unit F) = ⟨p v.proj, v.snd⟩) : u = v := by
    rcases u with ⟨u, x⟩
    rcases v with ⟨v, y⟩
    dsimp only at hbase
    subst v
    exact congrArg (fun w ↦ (⟨u, w⟩ : TotalSpace Unit F'))
      (TotalSpace.mk_injective (p u) hvec)
  let ρE : EquivariantStructure G E' :=
    { linearMap g z := σE.linearMap g (p z)
      one_map z v := extE (one_smul G z) (σE.one_map (p z) v)
      mul_map g k z v := extE (mul_smul g k z) (σE.mul_map g k (p z) v)
      continuous_action := by
        change @Continuous _ _
          (@instTopologicalSpaceProd G (TotalSpace Unit E') _
            (modelTopology (EuclideanSpace ℂ (Fin r)) E'))
          (modelTopology (EuclideanSpace ℂ (Fin r)) E') _
        rw [hEtop]
        let : TopologicalSpace (TotalSpace Unit E') := tE'
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
        exact (continuous_fst.smul ((Pullback.continuous_proj Unit E p).comp
          continuous_snd)).prodMk (σE.continuous_action.comp (continuous_fst.prodMk
            ((Pullback.continuous_lift Unit E p).comp continuous_snd))) }
  let ρF : EquivariantStructure G F' :=
    { linearMap g z := σF.linearMap g (p z)
      one_map z v := extF (one_smul G z) (σF.one_map (p z) v)
      mul_map g k z v := extF (mul_smul g k z) (σF.mul_map g k (p z) v)
      continuous_action := by
        change @Continuous _ _
          (@instTopologicalSpaceProd G (TotalSpace Unit F') _
            (modelTopology (EuclideanSpace ℂ (Fin q)) F'))
          (modelTopology (EuclideanSpace ℂ (Fin q)) F') _
        rw [hFtop]
        let : TopologicalSpace (TotalSpace Unit F') := tF'
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
        exact (continuous_fst.smul ((Pullback.continuous_proj Unit F p).comp
          continuous_snd)).prodMk (σF.continuous_action.comp (continuous_fst.prodMk
            ((Pullback.continuous_lift Unit F p).comp continuous_snd))) }
  have hρE : ρE.IsSmooth (n := n + n) (r := r) IG := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × W ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hp.comp contMDiff_snd)
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
  have hρF : ρF.IsSmooth (n := n + n) (r := q) IG := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × W ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hp.comp contMDiff_snd)
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
  let C := ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) h
  let : TopologicalSpace C := continuousCosphereSymbolTopology h
  have hradial : Continuous (fun z : W ↦ h.radial
      (⟨z.val, z.property⟩ : PuncturedCotangentBundle (n := n) (M := M))) :=
    h.continuous_radial
  have hprojE : Continuous (fun z : TotalSpace Unit E' ↦ z.proj) :=
    continuous_model_proj (EuclideanSpace ℂ (Fin r)) E'
  have hliftE : Continuous (fun z : TotalSpace Unit E' ↦
      (⟨p z.proj, z.snd⟩ : TotalSpace Unit E)) := by
    change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) E') _ _
    rw [hEtop]
    exact Pullback.continuous_lift Unit E p
  have joint := (continuous_cosphere_iff h (id : C → C)).mp continuous_id
  have hInput : Continuous (fun z : C × TotalSpace Unit E' ↦
      (⟨p z.2.proj, z.1.val (h.radial ⟨z.2.proj.val, z.2.proj.property⟩) z.2.snd⟩ :
        TotalSpace Unit F)) := by
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    exact (Continuous.comp joint (continuous_fst.prodMk
      (hradial.comp (hprojE.comp continuous_snd)))).clm_bundle_apply
        ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).comp
          (hliftE.comp continuous_snd))
  have hL : Continuous (fun z : C × TotalSpace Unit E' ↦
      (⟨z.2.proj, z.1.val (h.radial ⟨z.2.proj.val, z.2.proj.property⟩) z.2.snd⟩ :
        TotalSpace Unit F')) := by
    change @Continuous _ _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) F') _
    rw [hFtop]
    let : TopologicalSpace (TotalSpace Unit F') := tF'
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact (hprojE.comp continuous_snd).prodMk hInput
  let L (a : C) : Hom E' F' :=
    { linearMap z := (a.val (h.radial ⟨z.val, z.property⟩)).toLinearMap
      continuous_total := hL.comp (continuous_const.prodMk continuous_id) }
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let B (a : C) : Hom E' F' := (L a).equivariantAverage ρE ρF
  have hB : Continuous (fun z : C × TotalSpace Unit E' ↦ (B z.1).totalMap z.2) :=
    Hom.continuous_equivariantAverage_family ρE ρF L hL
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let b₀ (a : C) : GlobalSymbolFunction (n := n) E F := fun x ξ ↦
    if hξ : ξ ≠ 0 then
      LinearMap.toContinuousLinearMap
        (show E x →ₗ[ℂ] F x from (B a).linearMap ⟨⟨x, ξ⟩, hξ⟩)
    else 0
  have hb₀ (a : C) (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0)
      (v : E x) : b₀ a x ξ v = (B a).linearMap ⟨⟨x, ξ⟩, hξ⟩ v := by
    simp only [b₀, dite_eq_left hξ]
    rfl
  -- Recover the actual Hom-section continuity from continuous evaluation on every vector.
  have hsymbol : IsContinuousOffZeroSymbolFamily (r := r) (q := q) b₀ := by
    let Y := C × W
    have hf : Continuous (fun y : Y ↦ p y.2) := p.continuous.comp continuous_snd
    apply continuous_iff_continuousAt.mpr
    intro y₀
    apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
    refine ⟨hf.continuousAt, ?_⟩
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p y₀.2)
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F (p y₀.2)
    have he₀ : p y₀.2 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hf₀ : p y₀.2 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hevent : ∀ᶠ y : Y in 𝓝 y₀, p y.2 ∈ e.baseSet :=
      hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he₀)
    have hfevent : ∀ᶠ y : Y in 𝓝 y₀, p y.2 ∈ f.baseSet :=
      hf.continuousAt.preimage_mem_nhds (f.open_baseSet.mem_nhds hf₀)
    apply continuousAt_clm_apply.mpr
    intro v
    have hsection : ContinuousAt (fun y : Y ↦
        (⟨p y.2, e.symm (p y.2) v⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) y₀ := by
      have hlocal := e.continuousOn_symm.comp (hf.prodMk continuous_const).continuousOn
        (fun y (hy : p y.2 ∈ e.baseSet) ↦ ⟨hy, Set.mem_univ v⟩)
      exact hlocal.continuousAt hevent
    have hpull : ContinuousAt (fun y : Y ↦
        (⟨y.2, e.symm (p y.2) v⟩ : TotalSpace Unit E')) y₀ := by
      change @ContinuousAt _ _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) E') _ _
      rw [hEtop]
      let : TopologicalSpace (TotalSpace Unit E') := tE'
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuousAt_iff]
      exact continuousAt_snd.prodMk
        ((continuous_unitTotalEquiv_symm (EuclideanSpace ℂ (Fin r)) E).continuousAt.comp
          hsection)
    have hout := hB.continuousAt.comp (continuousAt_fst.prodMk hpull)
    have hliftF : Continuous (fun z : TotalSpace Unit F' ↦
        (⟨p z.proj, z.snd⟩ : TotalSpace Unit F)) := by
      change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) F') _ _
      rw [hFtop]
      exact Pullback.continuous_lift Unit F p
    have hcoord := (f.continuousAt (f.mem_source.mpr hf₀)).snd.comp
      ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).continuousAt.comp
        (hliftF.continuousAt.comp hout))
    apply hcoord.congr_of_eventuallyEq
    filter_upwards [hevent, hfevent] with y hey hfy
    change (f.continuousLinearMapAt ℂ (p y.2))
      (b₀ y.1 y.2.val.proj y.2.val.snd ((e.symmL ℂ (p y.2)) v)) =
        (f ⟨p y.2, (B y.1).linearMap y.2 (e.symm (p y.2) v)⟩).2
    rw [e.symmL_apply hey, hb₀ _ _ _ y.2.property]
    exact f.continuousLinearMapAt_apply_of_mem ℂ hfy _
  let A (a : C) : C :=
    ⟨cosphereRestriction h (b₀ a), (hsymbol.slice a).cosphereRestriction h⟩
  have hA : Continuous A := (continuous_cosphere_iff h A).mpr
    (Continuous.comp hsymbol (continuous_fst.prodMk
      (h.continuous_cosphereInclusion.comp continuous_snd)))
  have heqv (a : C) : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g (b₀ a) x ξ = b₀ a x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF (b₀ a)).mpr
    intro g x ξ hξ v
    have he := (L a).isEquivariant_equivariantAverage ρE ρF g
      (⟨⟨x, ξ⟩, hξ⟩ : W) v
    change b₀ a (g • (⟨x, ξ⟩ : CT)).proj (g • (⟨x, ξ⟩ : CT)).snd
      (σE.linearMap g x v) = σF.linearMap g x (b₀ a x ξ v)
    rw [hb₀ a _ _ (hne g ⟨⟨x, ξ⟩, hξ⟩), hb₀ a _ _ hξ]
    exact he
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro a
    exact equivariant_cosphereExtension_restriction IG σE σF h hInv 0 (b₀ a) (heqv a)
  · intro a ha
    have hc := (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF
      (cosphereExtension h 0 a.val)).mp ha
    have hLa : (L a).IsEquivariant ρE ρF := by
      intro g z v
      change a.val (h.radial ⟨g • z.val, hne g z⟩) (σE.linearMap g (p z) v) =
        σF.linearMap g (p z) (a.val (h.radial ⟨z.val, z.property⟩) v)
      have hh := hc g z.val.proj z.val.snd z.property v
      change cosphereExtension h 0 a.val (g • z.val).proj (g • z.val).snd
        (σE.linearMap g (p z) v) = σF.linearMap g (p z)
          (cosphereExtension h 0 a.val z.val.proj z.val.snd v) at hh
      rw [cosphereExtension_of_ne_zero h 0 a.val _ _ (hne g z),
        cosphereExtension_of_ne_zero h 0 a.val _ _ z.property] at hh
      simpa only [Real.rpow_zero, Complex.ofReal_one, one_smul,
        SmoothCotangentMetric.radial] using hh
    have hBa : B a = L a :=
      (L a).equivariantAverage_eq_of_isEquivariant ρE ρF hLa
    apply Subtype.ext
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change b₀ a z.val.proj z.val.snd v = a.val z v
    rw [hb₀ _ _ _ (h.cosphere_ne_zero z), hBa]
    change a.val (h.radial (h.cosphereInclusion z)) v = a.val z v
    have he := congrArg (cosphereSymbolTotal (r := r) (q := q) h a.val)
      (h.radial_cosphereInclusion z)
    exact DFunLike.congr_fun (TotalSpace.mk_injective z.val.proj he) v
  · intro a ha
    have hLsm : IsSmoothBundleMap (n := n + n) (r := r) (q := q) (L a).linearMap := by
      rintro _ ⟨e₀, he, rfl⟩ _ ⟨f₀, hf, rfl⟩ j z₀ hz₀
      change p z₀ ∈ e₀.baseSet ∩ f₀.baseSet at hz₀
      let := he
      let := hf
      let I := 𝓘(ℝ, V₀)
      let IW := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n)))
      let c := chartAt V₀ (p z₀)
      let t := trivializationAt V₀ (TangentSpace I) (p z₀)
      have hc : c ∈ atlas V₀ M := chart_mem_atlas _ _
      have hx₀ : p z₀ ∈ c.source := mem_chart_source _ _
      have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
      have hnative : ContMDiff IW I₀ ∞ (fun z : W ↦ z.val) :=
        hreverse.comp contMDiff_subtype_val
      have hsource := (contMDiffAt_hom_bundle _).mp (hnative.contMDiffAt (x := z₀))
      have hbase := hp.contMDiffAt (x := z₀)
      have hchart : ContMDiffAt IW I ∞ (fun z : W ↦ c (p z)) z₀ :=
        (contMDiffAt_of_mem_maximalAtlas hcm hx₀).comp z₀ hbase
      have hξ : ContMDiffAt IW 𝓘(ℝ, V₀ →L[ℝ] ℝ) ∞
          (fun z : W ↦ z.val.snd.comp (t.symmL ℝ (p z))) z₀ := by
        have hh := hsource.2
        change ContMDiffAt IW 𝓘(ℝ, V₀ →L[ℝ] ℝ) ∞
          (fun z : W ↦ ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ
            (p z)).comp (z.val.snd.comp (t.symmL ℝ (p z)))) z₀ at hh
        simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_comp] using hh
      have hd₀ := (contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx₀)).mfderiv_const
        (m := (∞ : WithTop ℕ∞)) (by simp)
      unfold inTangentCoordinates at hd₀
      simp only [c.left_inv hx₀] at hd₀
      have hd := hd₀.comp z₀ hchart
      have hdual (v : V₀) : ContMDiffAt IW 𝓘(ℝ, ℝ) ∞
          (fun z : W ↦ z.val.snd ((mfderiv I I c.symm (c (p z))) v)) z₀ := by
        apply (hξ.clm_apply (hd.clm_apply (contMDiffAt_const (c := v)))).congr_of_eventuallyEq
        filter_upwards [hbase.continuousAt.preimage_mem_nhds
          (c.open_source.mem_nhds hx₀)] with z hz
        dsimp only [Function.comp_apply, ContinuousLinearMap.inCoordinates, Function.id_def]
        simp only [TangentBundle.symmL_model_space]
        erw [c.left_inv hz]
        change z.val.snd ((mfderiv I I c.symm (c (p z))) v) =
          z.val.snd (t.symmL ℝ (p z) (t.continuousLinearMapAt ℝ (p z)
            ((mfderiv I I c.symm (c (p z))) v)))
        exact congrArg z.val.snd
          (t.symmL_continuousLinearMapAt (R := ℝ) hz
            ((mfderiv I I c.symm (c (p z))) v)).symm
      have hcoord : ContMDiffAt IW I ∞
          (fun z : W ↦ covectorInChart c (p z) z.val.snd) z₀ := by
        apply PiLp.contDiff_toLp.contMDiff.contMDiffAt.comp z₀
        apply contMDiffAt_pi_space.mpr
        intro i
        exact hdual (EuclideanSpace.single i 1)
      have hnz : covectorInChart c (p z₀) z₀.val.snd ≠ 0 := by
        intro hzero
        have hi := covectorFromChart_covectorInChart c hc (p z₀) hx₀ z₀.val.snd
        rw [hzero] at hi
        have hz : covectorFromChart c (p z₀) 0 = 0 := by
          ext v
          simp [covectorFromChart]
        exact z₀.property (hi.symm.trans hz)
      have hdomain : (c (p z₀), covectorInChart c (p z₀) z₀.val.snd) ∈
          symbolChartDomain E F c e₀ f₀ ×ˢ {ξ | ξ ≠ 0} := by
        refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, hnz⟩
        · simpa only [Set.mem_preimage, c.left_inv hx₀] using hz₀.1
        · simpa only [Set.mem_preimage, c.left_inv hx₀] using hz₀.2
      have hvalue := ((ha c hc e₀ f₀).contDiffAt
        (((isOpen_symbolChartDomain E F c e₀ f₀).prod isOpen_ne).mem_nhds hdomain)).contMDiffAt
          |>.comp z₀ (hchart.prodMk_space hcoord)
      have happly : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
            EuclideanSpace ℂ (Fin r) ↦ z.1 z.2) :=
        (isBoundedBilinearMap_apply (𝕜 := ℂ)).contDiff.restrict_scalars ℝ
      apply ((happly.comp_contMDiffAt (hvalue.prodMk_space
        (contMDiffAt_const (c := EuclideanSpace.single j (1 : ℂ))))).congr_of_eventuallyEq
          ?_).contMDiffWithinAt
      filter_upwards [hbase.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx₀),
        hbase.continuousAt.preimage_mem_nhds
          ((e₀.open_baseSet.inter f₀.open_baseSet).mem_nhds hz₀)] with z hcz hframes
      change (f₀ ⟨p z, (L a).linearMap z
        ((e₀.pullback p).symmL ℂ z (EuclideanSpace.single j 1))⟩).2 =
          globalSymbolInChart E F (cosphereExtension h 0 a.val) c e₀ f₀ (c (p z))
            (covectorInChart c (p z) z.val.snd) (EuclideanSpace.single j 1)
      rw [globalSymbolInChart_covectorInChart E F _ c hc e₀ f₀ (p z) hcz]
      simp only [ContinuousLinearMap.comp_apply]
      rw [cosphereExtension_of_ne_zero h 0 a.val (p z) z.val.snd z.property]
      simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
      have heq : (e₀.pullback p).symmL ℂ z (EuclideanSpace.single j 1) =
          e₀.symmL ℂ (p z) (EuclideanSpace.single j 1) := by
        rw [(e₀.pullback p).symmL_apply hframes.1, e₀.symmL_apply hframes.1,
          (e₀.pullback p).symm_apply hframes.1]
        rfl
      rw [heq]
      exact (f₀.continuousLinearMapAt_apply_of_mem ℂ hframes.2 _).symm
    have hBsm : IsSmoothBundleMap (n := n + n) (r := r) (q := q) (B a).linearMap :=
      (L a).isSmoothBundleMap_equivariantAverage ρE ρF IG hρE hρF hLsm
    have hb₀smooth : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F (b₀ a) := by
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
      let e' := e₀.pullback p
      let f' := f₀.pullback p
      let : MemTrivializationAtlas e' := ⟨⟨e₀, inferInstance, rfl⟩⟩
      let : MemTrivializationAtlas f' := ⟨⟨f₀, inferInstance, rfl⟩⟩
      have hmatrix := IsSmoothBundleMap.contMDiffOn_matrix (M := W)
        (n := n + n) (r := r) (q := q) (E := E')
        (F := F')
        (B a).linearMap hBsm e' f'
      have hcoords := hmatrix.comp hj.contMDiffOn (fun y (_ : y ∈ Set.univ) ↦
        (show j y ∈ e'.baseSet ∩ f'.baseSet from ⟨y.property.1.1.2, y.property.1.2⟩))
      have hfull := contMDiffOn_univ.mp hcoords
      have hraw : ContMDiff 𝓘(ℝ, X × X)
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (fun y : U ↦ globalSymbolInChart E F (b₀ a) c e₀ f₀ y.val.1 y.val.2) := by
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
          change (e₀.pullback p).symm (j y) v = e₀.symm (c.symm y.val.1) v
          rw [(e₀.pullback p).symm_apply y.property.1.1.2]
          rfl
        change (f₀.continuousLinearMapAt ℂ (c.symm y.val.1))
          (b₀ a (c.symm y.val.1) (covectorFromChart c (c.symm y.val.1) y.val.2)
            (e₀.symmL ℂ (c.symm y.val.1) v)) =
          f'.linearMapAt ℂ (j y) ((B a).linearMap (j y) (e'.symmL ℂ (j y) v))
        rw [he, hb₀ a _ _ (hne y)]
        rw [f'.coe_linearMapAt_of_mem y.property.1.2]
        exact f₀.continuousLinearMapAt_apply_of_mem ℂ y.property.1.2 _
      have hrawAt : ContMDiffAt 𝓘(ℝ, X × X)
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (Function.uncurry (globalSymbolInChart E F (b₀ a) c e₀ f₀)) z :=
        (contMDiffAt_subtype_iff (U := U)
          (f := Function.uncurry (globalSymbolInChart E F (b₀ a) c e₀ f₀))
          (x := (⟨z, hz⟩ : U))).mp (by
            simpa only [Function.uncurry] using (hraw.contMDiffAt (x := (⟨z, hz⟩ : U))))
      exact hrawAt.contDiffAt.contDiffWithinAt
    exact isSmoothCosphereSymbol_restriction h (b₀ a) hb₀smooth

end AtiyahSinger
