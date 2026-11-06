/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantContinuousSymbolHomotopy
public import AtiyahSinger.Analysis.EquivariantSymbolIndexBundle
public import AtiyahSinger.Analysis.PuncturedSymbolFamilyEvaluation
public import AtiyahSinger.Geometry.EquivariantBundleMapApproximation

/-!
# Original cotangent germ isomorphisms preserve the equivariant analytic index

Public module ID: M0589.

Two actual equivariant isomorphisms of original cotangent pullbacks intertwining
homogeneous elliptic symbols outside a specified compact set preserve their full
canonical equivariant indices. The compact set, fiber maps, and their covariance
are explicit; no support-triple wrapper or K-index descent assumption is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Topology
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 30

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
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
  {E' : M → Type*}
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) E']
  {F' : M → Type*}
  [∀ x, NormedAddCommGroup (F' x)] [∀ x, NormedSpace ℂ (F' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) F']
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := r') E']
  [IsSmoothComplexBundle (n := n) (r := q') F']

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (hσE' : σE'.IsSmooth (n := n) (r := r') IG)
  (hσF' : σF'.IsSmooth (n := n) (r := q') IG)

set_option maxHeartbeats 2000000 in
-- The original pullback maps and native fiber contraction are retained.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual equivariant cotangent germ square preserves the full analytic symbol index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_cotangent_germ_iso
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol E' F' t.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (ht : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE' σF' g t.val x ξ = t.val x ξ)
    (K : Set (CotangentTotalSpace (n := n) (M := M))) (hK : IsCompact K)
    (U : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E'))
    (hU : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := IG)
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      U.IsEquivariant
        (σE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
        (σE'.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl)))
    (V : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F'))
    (hV : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := IG)
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      V.IsEquivariant
        (σF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
        (σF'.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl)))
    (hst : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) ∉ K → ∀ u : E x,
          V.linearEquiv ⟨x, ξ⟩ (s.val x ξ u) =
            t.val x ξ (U.linearEquiv ⟨x, ξ⟩ u)) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
      equivariantHomogeneousAnalyticIndex IG σE' σF' hσE' hσF' t hj ht := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  have hzeroE : Continuous (fun z : TotalSpace Unit E ↦
      (⟨cotangentZeroSection z.proj, z.snd⟩ : TotalSpace Unit ((p : _ → M) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact (continuous_cotangentZeroSection.comp
      (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E)).prodMk continuous_id
  have hzeroEprime : Continuous (fun z : TotalSpace Unit E' ↦
      (⟨cotangentZeroSection z.proj, z.snd⟩ : TotalSpace Unit ((p : _ → M) *ᵖ E'))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E' p).continuous_iff]
    exact (continuous_cotangentZeroSection.comp
      (continuous_model_proj (EuclideanSpace ℂ (Fin r')) E')).prodMk continuous_id
  have hzeroF : Continuous (fun z : TotalSpace Unit F ↦
      (⟨cotangentZeroSection z.proj, z.snd⟩ : TotalSpace Unit ((p : _ → M) *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact (continuous_cotangentZeroSection.comp
      (continuous_model_proj (EuclideanSpace ℂ (Fin q)) F)).prodMk continuous_id
  have hzeroFprime : Continuous (fun z : TotalSpace Unit F' ↦
      (⟨cotangentZeroSection z.proj, z.snd⟩ : TotalSpace Unit ((p : _ → M) *ᵖ F'))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' p).continuous_iff]
    exact (continuous_cotangentZeroSection.comp
      (continuous_model_proj (EuclideanSpace ℂ (Fin q')) F')).prodMk continuous_id
  let e₀ : Iso E E' :=
    { linearEquiv x := U.linearEquiv (cotangentZeroSection x)
      continuous_total := (Pullback.continuous_lift Unit E' p).comp
        (U.continuous_total.comp hzeroE)
      continuous_symm := (Pullback.continuous_lift Unit E p).comp
        (U.continuous_symm.comp hzeroEprime) }
  let f₀ : Iso F F' :=
    { linearEquiv x := V.linearEquiv (cotangentZeroSection x)
      continuous_total := (Pullback.continuous_lift Unit F' p).comp
        (V.continuous_total.comp hzeroF)
      continuous_symm := (Pullback.continuous_lift Unit F p).comp
        (V.continuous_symm.comp hzeroFprime) }
  have hEvalU (x : M) (ξ η : CotangentFiber (n := n) x) (hξη : ξ = η)
      (v : E x) : U.linearEquiv (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) v =
        U.linearEquiv (⟨x, η⟩ : CotangentTotalSpace (n := n) (M := M)) v := by
    subst η
    rfl
  have hEvalV (x : M) (ξ η : CotangentFiber (n := n) x) (hξη : ξ = η)
      (v : F x) : V.linearEquiv (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) v =
        V.linearEquiv (⟨x, η⟩ : CotangentTotalSpace (n := n) (M := M)) v := by
    subst η
    rfl
  have he₀ : e₀.IsEquivariant σE σE' := by
    intro g x v
    have hh := hU g (cotangentZeroSection x) v
    exact (hEvalU (g • x) 0 _ (ContinuousLinearMap.zero_comp _).symm
      (σE.linearMap g x v)).trans hh
  have hf₀ : f₀.IsEquivariant σF σF' := by
    intro g x v
    have hh := hV g (cotangentZeroSection x) v
    exact (hEvalV (g • x) 0 _ (ContinuousLinearMap.zero_comp _).symm
      (σF.linearMap g x v)).trans hh
  obtain ⟨e, he, heg, He, hHe⟩ :=
    e₀.exists_equivariant_smooth_homotopy IG σE σE' hσE hσE' he₀
  obtain ⟨f, hf, hfg, Hf, hHf⟩ :=
    f₀.exists_equivariant_smooth_homotopy IG σF σF' hσF hσF' hf₀
  -- The invariant original metric places a whole cosphere beyond the given compact germ control.
  obtain ⟨h, hInv⟩ := exists_invariant_smoothCotangentMetric_of_compact_action
    (n := n) (M := M) (G := G) IG
  let Z := CotangentTotalSpace (n := n) (M := M)
  let W := PuncturedCotangentBundle (n := n) (M := M)
  let pc : C(W, M) := p.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hlength (g : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      h.length (g • x) (g • (⟨x, ξ⟩ : Z)).snd = h.length x ξ :=
    congrArg Real.sqrt (hInv g x ξ ξ)
  obtain ⟨B, hB⟩ := hK.bddAbove_image h.continuous_length.continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hbound (z : Z) (hz : z ∈ K) : h.length z.proj z.snd < R := by
    have hb := hB (Set.mem_image_of_mem _ hz)
    dsimp only [R]
    linarith [le_max_left B 0]
  let radialPoint (t : unitInterval) (x : M) (ξ : CotangentFiber (n := n) x) : Z :=
    ⟨x, ((1 - (t : ℝ)) * R) • h.normalize x ξ⟩
  have radial_continuous : Continuous (fun z : unitInterval × W ↦
      radialPoint z.1 z.2.val.proj z.2.val.snd) := by
    have hnorm : Continuous (fun z : unitInterval × W ↦ (h.radial z.2).val) :=
      continuous_subtype_val.comp (h.continuous_radial.comp continuous_snd)
    have hfactor : Continuous (fun z : unitInterval × W ↦ (1 - (z.1 : ℝ)) * R) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_const
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let C := CotangentModel n
    let T := CotangentFiber (n := n) (M := M)
    let a := trivializationAt C T z₀.2.val.proj
    have hn := (FiberBundle.continuousAt_totalSpace C _ (x₀ := z₀)).mp hnorm.continuousAt
    apply (FiberBundle.continuousAt_totalSpace C _).mpr
    refine ⟨hn.1, ?_⟩
    apply (hfactor.continuousAt.smul hn.2).congr_of_eventuallyEq
    filter_upwards [hn.1.preimage_mem_nhds
      (a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt C T z₀.2.val.proj))] with z hz
    change (a (radialPoint z.1 z.2.val.proj z.2.val.snd)).2 =
      ((1 - (z.1 : ℝ)) * R) • (a (h.radial z.2).val).2
    dsimp only [radialPoint, SmoothCotangentMetric.radial]
    change z.2.val.proj ∈ a.baseSet at hz
    rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz,
      ← a.continuousLinearMapAt_apply_of_mem ℝ hz]
    exact map_smul (a.continuousLinearMapAt ℝ z.2.val.proj) _ _
  have radial_cov (t : unitInterval) (g : G) (x : M)
      (ξ : CotangentFiber (n := n) x) :
      (radialPoint t (g • x) (g • (⟨x, ξ⟩ : Z)).snd).snd =
        (g • radialPoint t x ξ).snd := by
    dsimp only [radialPoint, SmoothCotangentMetric.normalize]
    rw [hlength]
    rfl
  have radial_outside (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      radialPoint 0 x ξ ∉ K := by
    have hnorm : h.length x (radialPoint 0 x ξ).snd = R := by
      change h.length x (((1 - (0 : ℝ)) * R) • h.normalize x ξ) = R
      simp only [sub_zero, one_mul]
      rw [h.length_smul, abs_of_pos hR, h.length_normalize x ξ hξ, mul_one]
    intro hz
    exact (lt_irrefl R) (hnorm ▸ hbound _ hz)
  -- Smooth terminal bundle maps give an actual smooth homogeneous conjugate symbol.
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨a, ha, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (e.linearEquiv x).symm.toLinearMap) (he.symm e.linearEquiv)
  obtain ⟨b, hb, _⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ) f.toHom.linearMap hf
  have hsah : IsHomogeneousGlobalSymbol E' F 0 (globalSymbolComp s.val a.val) := by
    simpa only [add_zero] using s.property.2.globalSymbolComp a.property.2
  let sa : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q) E' F 0 :=
    ⟨globalSymbolComp s.val a.val, s.property.1.globalSymbolComp a.property.1, hsah⟩
  have hcH : IsHomogeneousGlobalSymbol E' F' 0 (globalSymbolComp b.val sa.val) := by
    simpa only [add_zero] using b.property.2.globalSymbolComp sa.property.2
  let c : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' 0 :=
    ⟨globalSymbolComp b.val sa.val, b.property.1.globalSymbolComp sa.property.1, hcH⟩
  have hc (x : M) (ξ : CotangentFiber (n := n) x) (v : E' x) :
      c.val x ξ v = f.linearEquiv x (s.val x ξ ((e.linearEquiv x).symm v)) := by
    change b.val x ξ (s.val x ξ (a.val x ξ v)) = _
    rw [hb, ha]
    rfl
  -- Adjust the contraction by the specified zero-section homotopies at the same time.
  let : ∀ x, FiniteDimensional ℂ (E x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : ∀ x, FiniteDimensional ℂ (F x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, FiniteDimensional ℂ (E' x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r')) E' x
  let : ∀ x, FiniteDimensional ℂ (F' x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q')) F' x
  let A (τ : unitInterval) (x : M) (ξ : CotangentFiber (n := n) x) : E x ≃ₗ[ℂ] E' x :=
    (U.linearEquiv (radialPoint τ x ξ)).trans
      ((e₀.linearEquiv x).symm.trans (He.iso.linearEquiv (τ, x)))
  let B (τ : unitInterval) (x : M) (ξ : CotangentFiber (n := n) x) : F x ≃ₗ[ℂ] F' x :=
    (V.linearEquiv (radialPoint τ x ξ)).trans
      ((f₀.linearEquiv x).symm.trans (Hf.iso.linearEquiv (τ, x)))
  let H : unitInterval → GlobalSymbolFunction (n := n) E' F' := fun τ x ξ ↦
    ((B τ x ξ).toLinearMap.toContinuousLinearMap).comp
      ((s.val x ξ).comp ((A τ x ξ).symm.toLinearMap.toContinuousLinearMap))
  have hHEll : ∀ τ, IsEllipticGlobalSymbol E' F' (H τ) := by
    intro τ x ξ hξ
    exact ((B τ x ξ).bijective.comp (hi x ξ hξ)).comp (A τ x ξ).symm.bijective
  have hH : IsContinuousOffZeroSymbolFamily (r := r') (q := q') H := by
    apply (isContinuousOffZeroSymbolFamily_iff_continuous_total H).mpr
    let D := unitInterval × TotalSpace Unit ((pc : W → M) *ᵖ E')
    have hp : Continuous (fun z : D ↦ z.2.proj) :=
      (Pullback.continuous_proj Unit E' pc).comp continuous_snd
    have hx : Continuous (fun z : D ↦ z.2.proj.val.proj) := pc.continuous.comp hp
    have hr : Continuous (fun z : D ↦ radialPoint z.1 z.2.proj.val.proj z.2.proj.val.snd) :=
      radial_continuous.comp (continuous_fst.prodMk hp)
    -- Follow the actual inverse adjusted source map through the original total spaces.
    let v₀ (z : D) : TotalSpace Unit ((Prod.snd : unitInterval × M → M) *ᵖ E') :=
      ⟨(z.1, z.2.proj.val.proj), z.2.snd⟩
    have hv₀ : Continuous v₀ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E' Prod.snd).continuous_iff]
      exact (continuous_fst.prodMk hx).prodMk
        ((Pullback.continuous_lift Unit E' pc).comp continuous_snd)
    let v₁ (z : D) : TotalSpace Unit E :=
      ⟨z.2.proj.val.proj, (He.iso.linearEquiv (z.1, z.2.proj.val.proj)).symm z.2.snd⟩
    have hv₁ : Continuous v₁ := (Pullback.continuous_lift Unit E Prod.snd).comp
      (He.iso.continuous_symm.comp hv₀)
    let v₂ (z : D) : TotalSpace Unit E' :=
      ⟨z.2.proj.val.proj, e₀.linearEquiv z.2.proj.val.proj (v₁ z).snd⟩
    have hv₂ : Continuous v₂ := e₀.continuous_total.comp hv₁
    let v₃ (z : D) : TotalSpace Unit ((p : Z → M) *ᵖ E') :=
      ⟨radialPoint z.1 z.2.proj.val.proj z.2.proj.val.snd, (v₂ z).snd⟩
    have hv₃ : Continuous v₃ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E' p).continuous_iff]
      exact hr.prodMk hv₂
    let v₄ (z : D) : TotalSpace Unit E :=
      ⟨z.2.proj.val.proj,
        (U.linearEquiv (radialPoint z.1 z.2.proj.val.proj z.2.proj.val.snd)).symm (v₂ z).snd⟩
    have hv₄ : Continuous v₄ := (Pullback.continuous_lift Unit E p).comp
      (U.continuous_symm.comp hv₃)
    -- The original symbol is evaluated on that same vector, then the adjusted target is applied.
    let v₅ (z : D) : TotalSpace Unit F :=
      ⟨z.2.proj.val.proj, s.val z.2.proj.val.proj z.2.proj.val.snd (v₄ z).snd⟩
    have hv₅ : Continuous v₅ := by
      apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
      exact (s.property.1.continuous.comp hp).clm_bundle_apply
        ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).comp hv₄)
    let v₆ (z : D) : TotalSpace Unit ((p : Z → M) *ᵖ F) :=
      ⟨radialPoint z.1 z.2.proj.val.proj z.2.proj.val.snd, (v₅ z).snd⟩
    have hv₆ : Continuous v₆ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact hr.prodMk hv₅
    let v₇ (z : D) : TotalSpace Unit F' :=
      ⟨z.2.proj.val.proj,
        V.linearEquiv (radialPoint z.1 z.2.proj.val.proj z.2.proj.val.snd) (v₅ z).snd⟩
    have hv₇ : Continuous v₇ := (Pullback.continuous_lift Unit F' p).comp
      (V.continuous_total.comp hv₆)
    let v₈ (z : D) : TotalSpace Unit F :=
      ⟨z.2.proj.val.proj, (f₀.linearEquiv z.2.proj.val.proj).symm (v₇ z).snd⟩
    have hv₈ : Continuous v₈ := f₀.continuous_symm.comp hv₇
    let v₉ (z : D) : TotalSpace Unit ((Prod.snd : unitInterval × M → M) *ᵖ F) :=
      ⟨(z.1, z.2.proj.val.proj), (v₈ z).snd⟩
    have hv₉ : Continuous v₉ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F Prod.snd).continuous_iff]
      exact (continuous_fst.prodMk hx).prodMk hv₈
    have hout : Continuous (fun z : D ↦
        (⟨z.2.proj.val.proj, H z.1 z.2.proj.val.proj z.2.proj.val.snd z.2.snd⟩ :
          TotalSpace Unit F')) := (Pullback.continuous_lift Unit F' Prod.snd).comp
      (Hf.iso.continuous_total.comp hv₉)
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' pc).continuous_iff]
    exact hp.prodMk hout
  -- Every adjusted isomorphism intertwines the same moving-fiber actions.
  have he₀Inv (g : G) (x : M) (v : E' x) :
      (e₀.linearEquiv (g • x)).symm (σE'.linearMap g x v) =
        σE.linearMap g x ((e₀.linearEquiv x).symm v) := by
    apply (e₀.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((he₀ g x ((e₀.linearEquiv x).symm v)).trans
      (congrArg (σE'.linearMap g x) ((e₀.linearEquiv x).apply_symm_apply v))).symm
  have hf₀Inv (g : G) (x : M) (v : F' x) :
      (f₀.linearEquiv (g • x)).symm (σF'.linearMap g x v) =
        σF.linearMap g x ((f₀.linearEquiv x).symm v) := by
    apply (f₀.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((hf₀ g x ((f₀.linearEquiv x).symm v)).trans
      (congrArg (σF'.linearMap g x) ((f₀.linearEquiv x).apply_symm_apply v))).symm
  have hAcov (τ : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x)
      (v : E x) : A τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd (σE.linearMap g x v) =
        σE'.linearMap g x (A τ x ξ v) := by
    have hUr : U.linearEquiv (radialPoint τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd)
        (σE.linearMap g x v) =
        σE'.linearMap g x (U.linearEquiv (radialPoint τ x ξ) v) :=
      (hEvalU (g • x) _ _ (radial_cov τ g x ξ) (σE.linearMap g x v)).trans
        (hU g (radialPoint τ x ξ) v)
    change He.iso.linearEquiv (τ, g • x)
      ((e₀.linearEquiv (g • x)).symm
        (U.linearEquiv (radialPoint τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd)
          (σE.linearMap g x v))) = _
    rw [hUr, he₀Inv, hHe]
    rfl
  have hBcov (τ : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x)
      (v : F x) : B τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd (σF.linearMap g x v) =
        σF'.linearMap g x (B τ x ξ v) := by
    have hVr : V.linearEquiv (radialPoint τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd)
        (σF.linearMap g x v) =
        σF'.linearMap g x (V.linearEquiv (radialPoint τ x ξ) v) :=
      (hEvalV (g • x) _ _ (radial_cov τ g x ξ) (σF.linearMap g x v)).trans
        (hV g (radialPoint τ x ξ) v)
    change Hf.iso.linearEquiv (τ, g • x)
      ((f₀.linearEquiv (g • x)).symm
        (V.linearEquiv (radialPoint τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd)
          (σF.linearMap g x v))) = _
    rw [hVr, hf₀Inv, hHf]
    rfl
  have hAcovInv (τ : unitInterval) (g : G) (x : M)
      (ξ : CotangentFiber (n := n) x) (v : E' x) :
      (A τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd).symm (σE'.linearMap g x v) =
        σE.linearMap g x ((A τ x ξ).symm v) := by
    apply (A τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd).injective
    rw [LinearEquiv.apply_symm_apply, hAcov, LinearEquiv.apply_symm_apply]
  have hHg (τ : unitInterval) :
      ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σE' σF' g (H τ) x ξ = H τ x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE' σF' (H τ)).mpr
    intro g x ξ hξ v
    change B τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd
      (s.val (g • x) (g • (⟨x, ξ⟩ : Z)).snd
        ((A τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd).symm (σE'.linearMap g x v))) = _
    have hscov : s.val (g • x) (g • (⟨x, ξ⟩ : Z)).snd
        (σE.linearMap g x ((A τ x ξ).symm v)) =
        σF.linearMap g x (s.val x ξ ((A τ x ξ).symm v)) :=
      (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF s.val).mp hs g x ξ hξ _
    rw [hAcovInv]
    exact (congrArg (B τ (g • x) (g • (⟨x, ξ⟩ : Z)).snd) hscov).trans
      (hBcov τ g x ξ (s.val x ξ ((A τ x ξ).symm v)))
  -- The adjusted maps begin at the exterior germ and end at the chosen smooth base maps.
  have hA₀ (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) :
      A 0 x ξ v = U.linearEquiv (radialPoint 0 x ξ) v := by
    change He.iso.linearEquiv (0, x)
      ((e₀.linearEquiv x).symm (U.linearEquiv (radialPoint 0 x ξ) v)) = _
    rw [He.map_zero, LinearEquiv.apply_symm_apply]
  have hB₀ (x : M) (ξ : CotangentFiber (n := n) x) (v : F x) :
      B 0 x ξ v = V.linearEquiv (radialPoint 0 x ξ) v := by
    change Hf.iso.linearEquiv (0, x)
      ((f₀.linearEquiv x).symm (V.linearEquiv (radialPoint 0 x ξ) v)) = _
    rw [Hf.map_zero, LinearEquiv.apply_symm_apply]
  have hA₁ (x : M) (ξ : CotangentFiber (n := n) x) (v : E x) :
      A 1 x ξ v = e.linearEquiv x v := by
    have hu : U.linearEquiv (radialPoint 1 x ξ) v = e₀.linearEquiv x v :=
      hEvalU x _ 0 (by dsimp [radialPoint]; simp) v
    change He.iso.linearEquiv (1, x)
      ((e₀.linearEquiv x).symm (U.linearEquiv (radialPoint 1 x ξ) v)) = _
    rw [hu, LinearEquiv.symm_apply_apply, He.map_one]
  have hB₁ (x : M) (ξ : CotangentFiber (n := n) x) (v : F x) :
      B 1 x ξ v = f.linearEquiv x v := by
    have hv : V.linearEquiv (radialPoint 1 x ξ) v = f₀.linearEquiv x v :=
      hEvalV x _ 0 (by dsimp [radialPoint]; simp) v
    change Hf.iso.linearEquiv (1, x)
      ((f₀.linearEquiv x).symm (V.linearEquiv (radialPoint 1 x ξ) v)) = _
    rw [hv, LinearEquiv.symm_apply_apply, Hf.map_one]
  have hA₀Inv (x : M) (ξ : CotangentFiber (n := n) x) (v : E' x) :
      (A 0 x ξ).symm v = (U.linearEquiv (radialPoint 0 x ξ)).symm v := by
    apply (A 0 x ξ).injective
    rw [LinearEquiv.apply_symm_apply, hA₀, LinearEquiv.apply_symm_apply]
  have hA₁Inv (x : M) (ξ : CotangentFiber (n := n) x) (v : E' x) :
      (A 1 x ξ).symm v = (e.linearEquiv x).symm v := by
    apply (A 1 x ξ).injective
    rw [LinearEquiv.apply_symm_apply, hA₁, LinearEquiv.apply_symm_apply]
  have hradialFactor (x : M) (ξ : CotangentFiber (n := n) x) :
      (radialPoint 0 x ξ).snd = (R * (h.length x ξ)⁻¹) • ξ := by
    change ((1 - (0 : ℝ)) * R) • ((h.length x ξ)⁻¹ • ξ) = _
    rw [sub_zero, one_mul, smul_smul]
  have h0 (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      H 0 x ξ = t.val x ξ := by
    have hpos : 0 < R * (h.length x ξ)⁻¹ := mul_pos hR (inv_pos.mpr (h.length_pos x ξ hξ))
    have hradne : (radialPoint 0 x ξ).snd ≠ 0 := by
      rw [hradialFactor]
      exact smul_ne_zero hpos.ne' hξ
    have hsrad : s.val x (radialPoint 0 x ξ).snd = s.val x ξ := by
      rw [hradialFactor, s.property.2 x ξ hξ _ hpos]
      simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
    have htrad : t.val x (radialPoint 0 x ξ).snd = t.val x ξ := by
      rw [hradialFactor, t.property.2 x ξ hξ _ hpos]
      simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
    apply ContinuousLinearMap.ext
    intro v
    change B 0 x ξ (s.val x ξ ((A 0 x ξ).symm v)) = _
    rw [hB₀, hA₀Inv]
    have hsquare := hst x (radialPoint 0 x ξ).snd hradne (radial_outside x ξ hξ)
      ((U.linearEquiv (radialPoint 0 x ξ)).symm v)
    change V.linearEquiv (radialPoint 0 x ξ)
      (s.val x (radialPoint 0 x ξ).snd ((U.linearEquiv (radialPoint 0 x ξ)).symm v)) =
        t.val x (radialPoint 0 x ξ).snd
          (U.linearEquiv (radialPoint 0 x ξ) ((U.linearEquiv (radialPoint 0 x ξ)).symm v))
      at hsquare
    rw [hsrad, htrad, LinearEquiv.apply_symm_apply] at hsquare
    exact hsquare
  have h1 (x : M) (ξ : CotangentFiber (n := n) x) (_ : ξ ≠ 0) :
      H 1 x ξ = c.val x ξ := by
    apply ContinuousLinearMap.ext
    intro v
    change B 1 x ξ (s.val x ξ ((A 1 x ξ).symm v)) = _
    rw [hB₁, hA₁Inv, hc]
  have hce : IsEllipticGlobalSymbol E' F' c.val := by
    intro x ξ hξ
    rw [← h1 x ξ hξ]
    exact hHEll 1 x ξ hξ
  have hcg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE' σF' g c.val x ξ = c.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE' σF' c.val).mpr
    intro g x ξ hξ v
    have hgne : (g • (⟨x, ξ⟩ : Z)).snd ≠ 0 := by
      intro hz
      exact (h.length_pos x ξ hξ).ne' ((hlength g x ξ).symm.trans
        ((h.length_eq_zero_iff _ _).mpr hz))
    have hcov := (equivariantGlobalSymbolLinearMap_eq_iff IG σE' σF' (H 1)).mp
      (hHg 1) g x ξ hξ v
    change H 1 (g • x) (g • (⟨x, ξ⟩ : Z)).snd (σE'.linearMap g x v) =
      σF'.linearMap g x (H 1 x ξ v) at hcov
    rw [h1 (g • x) _ hgne, h1 x ξ hξ] at hcov
    exact hcov
  -- Both comparisons use the actual endpoint symbols and the same smooth base isomorphisms.
  have hsc := equivariantHomogeneousAnalyticIndex_eq_of_bundleIso
    IG σE σF σE' σF' hσE hσF hσE' hσF' e f he hf heg hfg s c hi hce hs hcg
    (fun x ξ _ v ↦ by rw [hc, LinearEquiv.symm_apply_apply])
  have htc := equivariantHomogeneousAnalyticIndex_eq_of_continuous_homotopy
    IG σE' σF' hσE' hσF' t c hj hce ht hcg H hH hHEll hHg h0 h1
  exact hsc.trans htc.symm

end AtiyahSinger
