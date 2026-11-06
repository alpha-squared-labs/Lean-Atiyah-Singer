/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Analysis.EllipticSymbolTriple
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Geometry.EquivariantRelativeBundleSmoothing
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.SmoothBundleMapPullback
public import AtiyahSinger.Topology.RealBundleSupport

/-!
# Equivariant relative homogeneous smoothing

Public module ID: M0563.

Smooth the actual homogeneous boundary using its original group actions and
one prescribed invariant cutoff. The radial homotopy fixes the prescribed
exterior at every time and intertwines the original pulled fiber actions.

This is the equivariant relative refinement of SG III.13.3, using invariant
metrics and fine approximation. The base need not be compact or have finite
CW type. The buffer and invariant cutoff remain explicit data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
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

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hE hF hG hGC hGT hAction hσE hσF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- The native model comparison retains three dependent pullback atlases and one fixed cylinder.
/-- Relative homogeneous smoothing retains the same exterior map and an actual fixed homotopy. -/
theorem exists_equivariant_smooth_homogeneous_boundary_relative
    (h : SmoothCotangentMetric (n := n) (M := M))
    (hInv : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd = h.length x ξ)
    (K L : Set M) (hK : IsCompact K) (hKL : K ⊆ interior L)
    (c : ∀ x, E x →L[ℂ] F x)
    (hc : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (c x).toLinearMap))
    (α : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      RelativeTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)
        cotangentZeroSetᶜ)
    (hα : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0)
      (t : ℝ) (ht : 0 < t) (v : E x),
      α.linearEquiv ⟨⟨x, t • ξ⟩, smul_ne_zero ht.ne' hξ⟩ v =
        α.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v)
    (hαc : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (x : M), x ∉ K → ∀ (ξ : CotangentFiber (n := n) x)
      (hξ : ξ ≠ 0) (v : E x), α.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v = c x v)
    (hαEq : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := M))
        (hz : z.snd ≠ 0) (hgz : (g • z).snd ≠ 0) (v : E z.proj),
        α.linearEquiv ⟨g • z, hgz⟩ (σE.linearMap g z.proj v) =
          σF.linearMap g z.proj (α.linearEquiv ⟨z, hz⟩ v))
    (χ : M → ℝ)
    (hχsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχK : tsupport χ ⊆ Kᶜ) (hχL : ∀ x ∉ L, χ x = 1)
    (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχinv : ∀ (g : G) (x : M), χ (g • x) = χ x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0,
      IsEllipticGlobalSymbol E F s.val ∧
      (∀ (x : M), x ∉ L → ∀ ξ : CotangentFiber (n := n) x, s.val x ξ = c x) ∧
      ∃ β : RelativeTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)
        cotangentZeroSetᶜ,
        (∀ (z : (cotangentZeroSetᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
          (v : E z.val.proj), β.linearEquiv z v = s.val z.val.proj z.val.snd v) ∧
        ∃ H : IsoHomotopy α β,
          (∀ (t : unitInterval) (z : (cotangentZeroSetᶜ :
              Set (CotangentTotalSpace (n := n) (M := M)))), z.val.proj ∉ L →
            ∀ v : E z.val.proj, H.iso.linearEquiv (t, z) v = c z.val.proj v) ∧
          (∀ (t : unitInterval) (g : G) (z : CotangentTotalSpace (n := n) (M := M))
            (hz : z.snd ≠ 0) (hgz : (g • z).snd ≠ 0) (v : E z.proj),
            H.iso.linearEquiv (t, ⟨g • z, hgz⟩) (σE.linearMap g z.proj v) =
              σF.linearMap g z.proj (H.iso.linearEquiv (t, ⟨z, hz⟩) v)) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let CT := CotangentTotalSpace (n := n) (M := M)
  let V₀ := EuclideanSpace ℝ (Fin n)
  let W₀ := V₀ × CotangentModel n
  let I₀ := 𝓘(ℝ, V₀).prod 𝓘(ℝ, CotangentModel n)
  -- The original total topology is second countable without a compact base.
  let : RealBundle.IsFiniteRank (CotangentModel n) (CotangentFiber (n := n) (M := M)) :=
    RealBundle.isFiniteRank_of_vectorBundle _ _
  let : SecondCountableTopology CT :=
    RealBundle.secondCountableTopology_totalSpace (CotangentModel n) (CotangentFiber (M := M))
  -- Change only the finite-dimensional smooth model, retaining all base points and covectors.
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
  let p : C(CT, M) := cotangentProjection (n := n) (M := M)
  let E' := (p : CT → M) *ᵖ E
  let F' := (p : CT → M) *ᵖ F
  let hE' : IsSmoothComplexBundle (n := n + n) (r := r) E' :=
    isSmoothComplexBundle_pullback E p hπ
  let hF' : IsSmoothComplexBundle (n := n + n) (r := q) F' :=
    isSmoothComplexBundle_pullback F p hπ
  let W : Opens CT := ⟨cotangentZeroSetᶜ, isClosed_cotangentZeroSet.isOpen_compl⟩
  have hzero (g : G) (z : CT) : (g • z).snd = 0 ↔ z.snd = 0 := by
    rw [← h.length_eq_zero_iff (g • z).proj (g • z).snd,
      ← h.length_eq_zero_iff z.proj z.snd]
    exact congrArg (fun r : ℝ ↦ r = 0) (hInv g z.proj z.snd) ▸ Iff.rfl
  let : MulAction G W :=
    { smul g z := ⟨g • z.val, fun hz ↦ z.property ((hzero g z.val).mp hz)⟩
      one_smul z := Subtype.ext (one_smul G z.val)
      mul_smul g k z := Subtype.ext (mul_smul g k z.val) }
  let : ContinuousSMul G W :=
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ G W :=
    ⟨(ContMDiff.subtypeVal_comp_iff W (fun p : G × W ↦ p.1 • p.2)).mp
      (contMDiff_fst.smul (contMDiff_subtype_val.comp contMDiff_snd))⟩
  let incl : C(W, CT) := ⟨Subtype.val, continuous_subtype_val⟩
  let RE := (incl : W → CT) *ᵖ E'
  let RF := (incl : W → CT) *ᵖ F'
  let hRE : IsSmoothComplexBundle (n := n + n) (r := r) RE :=
    isSmoothComplexBundle_pullback E' incl contMDiff_subtype_val
  let hRF : IsSmoothComplexBundle (n := n + n) (r := q) RF :=
    isSmoothComplexBundle_pullback F' incl contMDiff_subtype_val
  let proj : C(W, M) := p.comp incl
  let A : Set W := proj ⁻¹' Lᶜ
  let U : Opens W := ⟨proj ⁻¹' Kᶜ, hK.isClosed.isOpen_compl.preimage proj.continuous⟩
  let tRE : TopologicalSpace (TotalSpace Unit RE) :=
    @Pullback.TotalSpace.topologicalSpace CT Unit E' W (incl : W → CT) _
      (@Pullback.TotalSpace.topologicalSpace M Unit E CT (p : CT → M) _
        (modelTopology (EuclideanSpace ℂ (Fin r)) E))
  let tRF : TopologicalSpace (TotalSpace Unit RF) :=
    @Pullback.TotalSpace.topologicalSpace CT Unit F' W (incl : W → CT) _
      (@Pullback.TotalSpace.topologicalSpace M Unit F CT (p : CT → M) _
        (modelTopology (EuclideanSpace ℂ (Fin q)) F))
  have hREtop : modelTopology (EuclideanSpace ℂ (Fin r)) RE = tRE := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tRE, modelTopology]
    rfl
  have hRFtop : modelTopology (EuclideanSpace ℂ (Fin q)) RF = tRF := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tRF, modelTopology]
    rfl
  -- Pulling back the exterior map proves smoothness in the same three nested native atlases.
  have hrestricted : IsSmoothBundleMap (n := n + n) (r := r) (q := q) (M := U)
      (E := (ContinuousMap.subtypeVal (U : Set W) : U → W) *ᵖ RE)
      (F := (ContinuousMap.subtypeVal (U : Set W) : U → W) *ᵖ RF)
      (fun z ↦ (α.linearEquiv z.val).toLinearMap) := by
    have hs := ((hc.pullback p hπ).pullback incl contMDiff_subtype_val).pullback
      (N := U) (m := n + n) (ContinuousMap.subtypeVal (U : Set W)) contMDiff_subtype_val
    have hmaps : (fun z : U ↦ (α.linearEquiv z.val).toLinearMap) =
        (fun z : U ↦ (c (p (incl z.val))).toLinearMap) := by
      funext z
      apply LinearMap.ext
      intro v
      exact hαc z.val.val.proj z.property z.val.val.snd z.val.property v
    rw [hmaps]
    exact hs
  -- The native modeled pullbacks preserve the original moving-fiber maps.
  let ρE := σE.modelPullback p (fun _ _ ↦ rfl)
  let ρF := σF.modelPullback p (fun _ _ ↦ rfl)
  let ρRE := ρE.modelPullback incl (fun _ _ ↦ rfl)
  let ρRF := ρF.modelPullback incl (fun _ _ ↦ rfl)
  have hρE := σE.modelPullback_isSmooth IG hσE p (fun _ _ ↦ rfl) hπ
  have hρF := σF.modelPullback_isSmooth IG hσF p (fun _ _ ↦ rfl) hπ
  have hρRE := ρE.modelPullback_isSmooth IG hρE incl (fun _ _ ↦ rfl)
    contMDiff_subtype_val
  have hρRF := ρF.modelPullback_isSmooth IG hρF incl (fun _ _ ↦ rfl)
    contMDiff_subtype_val
  let αlin : ∀ z : W, RE z ≃ₗ[ℂ] RF z := α.linearEquiv
  have hαcont := α.continuous_total
  have hαsymm := α.continuous_symm
  let : TopologicalSpace (TotalSpace Unit RE) := modelTopology (EuclideanSpace ℂ (Fin r)) RE
  let : TopologicalSpace (TotalSpace Unit RF) := modelTopology (EuclideanSpace ℂ (Fin q)) RF
  let αm : Iso RE RF := {
    linearEquiv := αlin
    continuous_total := by
      change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) RE)
        (modelTopology (EuclideanSpace ℂ (Fin q)) RF) _
      rw [hREtop, hRFtop]
      exact hαcont
    continuous_symm := by
      change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) RF)
        (modelTopology (EuclideanSpace ℂ (Fin r)) RE) _
      rw [hREtop, hRFtop]
      exact hαsymm }
  have hαm : αm.IsEquivariant ρRE ρRF := by
    intro g z v
    exact hαEq g z.val z.property (g • z).property v
  let χW : W → ℝ := fun z ↦ χ (proj z)
  have hχW : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) 𝓘(ℝ, ℝ) ∞ χW :=
    hχsmooth.comp (hπ.comp contMDiff_subtype_val)
  have hχWU : tsupport χW ⊆ (U : Set W) := by
    apply (tsupport_comp_subset_preimage _ proj.continuous).trans
    exact Set.preimage_mono hχK
  obtain ⟨βm, hβsmooth, _hβEq, Hm, hHmEq, hHmFixed⟩ :=
    αm.exists_equivariant_smooth_homotopy_relative (hE := hRE) (hF := hRF)
      IG ρRE ρRF hρRE hρRF hαm A U χW hχW hχWU
      (fun z hz ↦ hχL (proj z) hz) (fun z ↦ hχbounds (proj z))
      (fun g z ↦ hχinv g (proj z)) hrestricted
  let βlin : ∀ z : W, RE z ≃ₗ[ℂ] RF z := βm.linearEquiv
  let Hlin : ∀ z : unitInterval × W, RE z.2 ≃ₗ[ℂ] RF z.2 := Hm.iso.linearEquiv
  have hβcont := βm.continuous_total
  have hβsymm := βm.continuous_symm
  have hHcont := Hm.iso.continuous_total
  have hHsymm := Hm.iso.continuous_symm
  change Continuous (fun z : TotalSpace Unit RE ↦
    (⟨z.proj, βlin z.proj z.snd⟩ : TotalSpace Unit RF)) at hβcont
  change Continuous (fun z : TotalSpace Unit RF ↦
    (⟨z.proj, (βlin z.proj).symm z.snd⟩ : TotalSpace Unit RE)) at hβsymm
  change Continuous (fun z : TotalSpace Unit ((Prod.snd : unitInterval × W → W) *ᵖ RE) ↦
    (⟨z.proj, Hlin z.proj z.snd⟩ :
      TotalSpace Unit ((Prod.snd : unitInterval × W → W) *ᵖ RF))) at hHcont
  change Continuous (fun z : TotalSpace Unit ((Prod.snd : unitInterval × W → W) *ᵖ RF) ↦
    (⟨z.proj, (Hlin z.proj).symm z.snd⟩ :
      TotalSpace Unit ((Prod.snd : unitInterval × W → W) *ᵖ RE))) at hHsymm
  have hHzero (z : W) (v : RE z) : Hlin (0, z) v = αlin z v := Hm.map_zero z v
  have hHone (z : W) (v : RE z) : Hlin (1, z) v = βlin z v := Hm.map_one z v
  have hHfixed (t : unitInterval) (z : W) (hz : z ∈ A) (v : RE z) :
      Hlin (t, z) v = αlin z v := hHmFixed t z hz v
  have hHlinEq (t : unitInterval) (g : G) (z : W) (v : E z.val.proj) :
      Hlin (t, g • z) (σE.linearMap g z.val.proj v) =
        σF.linearMap g z.val.proj (Hlin (t, z) v) := hHmEq t g z v
  change IsSmoothBundleMap (n := n + n) (r := r) (q := q)
    (fun z ↦ (βlin z).toLinearMap) at hβsmooth
  -- Restore the original restriction topology without changing any fiber map.
  let : TopologicalSpace (TotalSpace Unit RE) := tRE
  let : TopologicalSpace (TotalSpace Unit RF) := tRF
  let β : RelativeTriple E' F' cotangentZeroSetᶜ := {
    linearEquiv := βlin
    continuous_total := by
      change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin r)) RE)
        (modelTopology (EuclideanSpace ℂ (Fin q)) RF) _ at hβcont
      rw [hREtop, hRFtop] at hβcont
      exact hβcont
    continuous_symm := by
      change @Continuous _ _ (modelTopology (EuclideanSpace ℂ (Fin q)) RF)
        (modelTopology (EuclideanSpace ℂ (Fin r)) RE) _ at hβsymm
      rw [hREtop, hRFtop] at hβsymm
      exact hβsymm }
  let Hβ : IsoHomotopy α β := {
    iso := {
      linearEquiv := Hlin
      continuous_total := by
        change @Continuous _ _
          (@Pullback.TotalSpace.topologicalSpace W Unit RE (unitInterval × W) Prod.snd _
            (modelTopology (EuclideanSpace ℂ (Fin r)) RE))
          (@Pullback.TotalSpace.topologicalSpace W Unit RF (unitInterval × W) Prod.snd _
            (modelTopology (EuclideanSpace ℂ (Fin q)) RF)) _ at hHcont
        rw [hREtop, hRFtop] at hHcont
        exact hHcont
      continuous_symm := by
        change @Continuous _ _
          (@Pullback.TotalSpace.topologicalSpace W Unit RF (unitInterval × W) Prod.snd _
            (modelTopology (EuclideanSpace ℂ (Fin q)) RF))
          (@Pullback.TotalSpace.topologicalSpace W Unit RE (unitInterval × W) Prod.snd _
            (modelTopology (EuclideanSpace ℂ (Fin r)) RE)) _ at hHsymm
        rw [hREtop, hRFtop] at hHsymm
        exact hHsymm }
    map_zero := hHzero
    map_one := hHone }
  have hHβ (t : unitInterval) (z : W) (hz : z ∈ A) (v : E z.val.proj) :
      Hβ.iso.linearEquiv (t, z) v = α.linearEquiv z v := hHfixed t z hz v
  have hHβEq (t : unitInterval) (g : G) (z : W) (v : E z.val.proj) :
      Hβ.iso.linearEquiv (t, g • z) (σE.linearMap g z.val.proj v) =
        σF.linearMap g z.val.proj (Hβ.iso.linearEquiv (t, z) v) := hHlinEq t g z v
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
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
    let IM := 𝓘(ℝ, X)
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
      have hcm : c ∈ maximalAtlas IM ∞ M := subset_maximalAtlas (I := IM) hc
      have hbase : ContMDiffAt 𝓘(ℝ, X × X) IM ∞
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
          Function.id_def, ContinuousLinearMap.comp_apply, IM]
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
  -- Radial extension uses this same smooth boundary on the specified unit cosphere.
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
  -- The zero value is unconstrained by punctured smoothness and positive homogeneity.
  -- Choose the prescribed exterior map there, including all exterior zero covectors.
  let a : GlobalSymbolFunction (n := n) E F := fun x ξ ↦ if ξ = 0 then c x else s.val x ξ
  have has : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a := by
    intro d hd e₀ f₀ _ _
    apply (s.property.1 d hd e₀ f₀).congr
    intro z hz
    have hne : covectorFromChart d (d.symm z.1) z.2 ≠ 0 := by
      intro hzero
      have hi := covectorInChart_covectorFromChart d hd (d.symm z.1)
        (d.map_target hz.1.1.1) z.2
      rw [hzero] at hi
      have hzcoord : covectorInChart d (d.symm z.1) 0 = 0 := by ext j; rfl
      exact hz.2 (hi.symm.trans hzcoord)
    simp only [Function.uncurry, globalSymbolInChart, a, ite_eq_right hne]
  have hah : IsHomogeneousGlobalSymbol E F 0 a := by
    intro x ξ hξ t ht
    simp only [a, ite_eq_right hξ, ite_eq_right (smul_ne_zero ht.ne' hξ)]
    exact s.property.2 x ξ hξ t ht
  let s' : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
    ⟨a, has, hah⟩
  have hs' (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      s'.val x ξ = s.val x ξ := ite_eq_right hξ
  have hi' : IsEllipticGlobalSymbol E F s'.val := by
    intro x ξ hξ
    rw [hs' x ξ hξ]
    exact hi x ξ hξ
  have hext (x : M) (hx : x ∉ L) (ξ : CotangentFiber (n := n) x) :
      s'.val x ξ = c x := by
    by_cases hξ : ξ = 0
    · change a x ξ = c x
      simp only [a, ite_eq_left hξ]
    · rw [hs' x ξ hξ]
      ext v
      rw [hs x ξ hξ]
      let z : W := ⟨⟨x, h.normalize x ξ⟩, h.normalize_ne_zero x ξ hξ⟩
      have hzA : z ∈ A := hx
      have hxK : x ∉ K := fun hin ↦ hx (interior_subset (hKL hin))
      exact (Hβ.map_one z v).symm.trans
        ((hHβ 1 z hzA v).trans (hαc x hxK _ z.property v))
  -- Normalize the entire fixed homotopy. Its starting boundary is unchanged by hα.
  let j : W → W := fun z ↦ h.cosphereInclusion (h.radial z)
  have hj : Continuous j := h.continuous_cosphereInclusion.comp h.continuous_radial
  let πW : C(unitInterval × W, W) := ⟨Prod.snd, continuous_snd⟩
  let CE := (πW : unitInterval × W → W) *ᵖ RE
  let CF := (πW : unitInterval × W → W) *ᵖ RF
  let Jbase : unitInterval × W → unitInterval × W := fun z ↦ (z.1, j z.2)
  have hJbase : Continuous Jbase := continuous_fst.prodMk (hj.comp continuous_snd)
  have hp : Continuous (π Unit CE) := Pullback.continuous_proj Unit RE πW
  have hinput : Continuous (fun w : TotalSpace Unit CE ↦
      (⟨Jbase w.proj, w.snd⟩ : TotalSpace Unit CE)) := by
    have he := (Pullback.continuous_lift Unit E p).comp
      ((Pullback.continuous_lift Unit E' incl).comp (Pullback.continuous_lift Unit RE πW))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit RE πW).continuous_iff]
    refine (hJbase.comp hp).prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E' incl).continuous_iff]
    refine ((hj.comp continuous_snd).comp hp).prodMk ?_
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact ((continuous_subtype_val.comp hj).comp (continuous_snd.comp hp)).prodMk he
  have hout := Hβ.iso.continuous_total.comp hinput
  have hf := (Pullback.continuous_lift Unit F p).comp
    ((Pullback.continuous_lift Unit F' incl).comp
      ((Pullback.continuous_lift Unit RF πW).comp hout))
  let f : Hom CE CF :=
    { linearMap z := (Hβ.iso.linearEquiv (Jbase z)).toLinearMap
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit RF πW).continuous_iff]
        refine hp.prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F' incl).continuous_iff]
        refine (continuous_snd.comp hp).prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
        exact ((continuous_subtype_val.comp continuous_snd).comp hp).prodMk hf }
  let J : Iso CE CF := f.toIso (fun z ↦ (Hβ.iso.linearEquiv (Jbase z)).bijective)
  let γ := ellipticSymbolBoundary s.val s.property.1.continuous hi
  have hγ (z : W) (v : E z.val.proj) : γ.linearEquiv z v =
      s'.val z.val.proj z.val.snd v := by
    rw [hs' _ _ z.property]
    exact ellipticSymbolBoundary_apply s.val s.property.1.continuous hi z v
  have hJzero (z : W) (v : E z.val.proj) : J.linearEquiv (0, z) v = α.linearEquiv z v := by
    change Hβ.iso.linearEquiv (0, j z) v = _
    rw [Hβ.map_zero]
    exact hα z.val.proj z.val.snd z.property (h.length z.val.proj z.val.snd)⁻¹
      (inv_pos.mpr (h.length_pos _ _ z.property)) v
  have hJone (z : W) (v : E z.val.proj) : J.linearEquiv (1, z) v = γ.linearEquiv z v := by
    change Hβ.iso.linearEquiv (1, j z) v = _
    rw [Hβ.map_one, ellipticSymbolBoundary_apply, hs _ _ z.property]
    rfl
  let H : IsoHomotopy α γ :=
    { iso := J
      map_zero := hJzero
      map_one := hJone }
  refine ⟨s', hi', hext, γ, hγ, H, ?_, ?_⟩
  · intro t z hz v
    change Hβ.iso.linearEquiv (t, j z) v = _
    have hzA : j z ∈ A := hz
    rw [hHβ t (j z) hzA v]
    exact hαc z.val.proj (fun hin ↦ hz (interior_subset (hKL hin)))
      _ (j z).property v
  · -- Invariant length makes the full radial cylinder equivariant.
    intro t g z hz hgz v
    have hnorm : h.normalize (g • z).proj (g • z).snd =
        (g • (⟨z.proj, h.normalize z.proj z.snd⟩ : CT)).snd := by
      have hlen : h.length (g • z).proj (g • z).snd = h.length z.proj z.snd :=
        hInv g z.proj z.snd
      simp only [SmoothCotangentMetric.normalize, hlen]
      rfl
    have hsame (x : M) (ξ η : CotangentFiber (n := n) x)
        (hξ : ξ ≠ 0) (hη : η ≠ 0) (heq : ξ = η) (u : E x) :
        Hβ.iso.linearEquiv (t, ⟨⟨x, ξ⟩, hξ⟩) u =
          Hβ.iso.linearEquiv (t, ⟨⟨x, η⟩, hη⟩) u := by
      subst η
      rfl
    have hgne : (g • (⟨z.proj, h.normalize z.proj z.snd⟩ : CT)).snd ≠ 0 :=
      fun hzero' ↦ h.normalize_ne_zero z.proj z.snd hz
        ((hzero g ⟨z.proj, h.normalize z.proj z.snd⟩).mp hzero')
    change Hβ.iso.linearEquiv (t, j ⟨g • z, hgz⟩) (σE.linearMap g z.proj v) =
      σF.linearMap g z.proj (Hβ.iso.linearEquiv (t, j ⟨z, hz⟩) v)
    exact (hsame (g • z).proj _ _ (h.normalize_ne_zero _ _ hgz) hgne hnorm
      (σE.linearMap g z.proj v)).trans (hHβEq t g (j ⟨z, hz⟩) v)

end AtiyahSinger.ComplexBundle
