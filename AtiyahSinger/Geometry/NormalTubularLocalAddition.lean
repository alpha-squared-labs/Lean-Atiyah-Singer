/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ManifoldLocalAddition
public import AtiyahSinger.Geometry.NormalTubularLocalSubtraction
public import AtiyahSinger.Geometry.NormalTubularShrinking
public import AtiyahSinger.Geometry.TangentNormalBundle

/-!
# A normalized smooth local addition

Public module ID: M1311.

A second-countable Hausdorff finite-dimensional real manifold without boundary has a smooth
local addition. We construct a partial diffeomorphism from a neighborhood of the zero section
in its actual tangent bundle to a neighborhood of the diagonal in the product manifold.
Its first component is the original bundle projection, it takes each zero vector to the
corresponding diagonal point, and its second component has identity fiber derivative at zero.

The construction inverts the normalized local subtraction supplied by a partition of unity.
In native product and tangent charts its differential preserves the first component and acts
identically in the vertical direction, so it is invertible. The noncompact shrinking theorem
then selects a single inverse branch along the entire zero section. The inverse is smooth
because it agrees locally with the same inverse-function charts. Differentiating the local
subtraction identity retains the exact fiber normalization.

This supplementary construction uses the original tangent topology and smooth atlas. It needs
neither a metric nor a geodesic exponential, compactness, or a constant tubular radius.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- A normalized smooth local addition, expressed as a partial diffeomorphism from a neighborhood
of the zero section to a neighborhood of the diagonal in the original product manifold. -/
theorem exists_smooth_localAddition :
    ∃ Φ : PartialDiffeomorph ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (TangentBundle (𝓘(ℝ, E)) M) (M × M) ∞,
      (∀ x, (⟨x, 0⟩ : TangentBundle (𝓘(ℝ, E)) M) ∈ Φ.source) ∧
      (∀ p ∈ Φ.source, (Φ p).1 = p.proj) ∧
      (∀ x, Φ (⟨x, 0⟩ : TangentBundle (𝓘(ℝ, E)) M) = (x, x)) ∧
      ∀ x, HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (fun v : E ↦ (Φ (⟨x, v⟩ : TangentBundle (𝓘(ℝ, E)) M)).2)
        0 (ContinuousLinearMap.id ℝ E) := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨Ω, d, hΩ, hdiag, hs, hzero, hd⟩ :=
    exists_smooth_localSubtraction (E := E) (M := M)
  -- Invert the subtraction near each diagonal point, retaining the original model types.
  have hlocalInverse : ∀ x : M,
      ∃ Φ : PartialDiffeomorph ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
          ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M) (TangentBundle (𝓘(ℝ, E)) M) ∞,
        (x, x) ∈ Φ.source ∧ Φ.source ⊆ Ω ∧
          (Φ : M × M → TangentBundle (𝓘(ℝ, E)) M) =
            (fun z ↦ ⟨z.1, d z.1 z.2⟩) := by
    intro x
    have hx := hdiag x
    let D : M × M → TangentBundle (𝓘(ℝ, E)) M := fun z ↦ ⟨z.1, d z.1 z.2⟩
    let κ := chartAt E x
    let a : E := κ x
    let φ := extChartAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (x, x)
    let ψ := extChartAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (D (x, x))
    let g : E × E → E × E := ψ ∘ D ∘ φ.symm
    have hD : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ D (x, x) := hs.contMDiffAt (hΩ.mem_nhds hx)
    have hga : ContDiffAt ℝ ∞ g (a, a) := by
      simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using!
        (contMDiffAt_iff.mp hD).2
    have hdd : HasFDerivAt (d x ∘ κ.symm) (ContinuousLinearMap.id ℝ E) a := by
      simpa only [writtenInExtChartAt, mfld_simps, hasFDerivWithinAt_univ] using! (hd x).2
    have hself (v w : E) :
        extChartAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
          (⟨x, v⟩ : TangentBundle (𝓘(ℝ, E)) M) ⟨x, w⟩ = (a, w) := by
      change (κ x, tangentCoordChange (𝓘(ℝ, E)) x x x w) = (a, w)
      rw [tangentCoordChange_self (by simp)]
    have hfirst : (fun p : E × E ↦ (g p).1) =ᶠ[𝓝 (a, a)] Prod.fst := by
      have ha : a ∈ κ.target := κ.map_source (mem_chart_source E x)
      filter_upwards [continuous_fst.continuousAt (κ.open_target.mem_nhds ha)] with p hp
      change κ (κ.symm p.1) = p.1
      exact κ.right_inv hp
    have hvertical (u : E) : g (a, u) = (a, d x (κ.symm u)) := by
      change extChartAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (⟨x, d x x⟩ : TangentBundle (𝓘(ℝ, E)) M)
        ⟨κ.symm (κ x), d (κ.symm (κ x)) (κ.symm u)⟩ = _
      rw [κ.left_inv (mem_chart_source E x)]
      exact hself _ _
    -- The derivative has identity first component and identity vertical block.
    let A : (E × E) →L[ℝ] (E × E) := fderiv ℝ g (a, a)
    have hA : HasFDerivAt g A (a, a) := (hga.differentiableAt (by simp)).hasFDerivAt
    have hAfirst : ∀ v : E × E, (A v).1 = v.1 := by
      have h := ((hasFDerivAt_fst (p := g (a, a))).comp (a, a) hA).congr_of_eventuallyEq
        hfirst.symm
      have heq := h.unique (hasFDerivAt_fst (p := (a, a)))
      intro v
      exact congrArg (fun L : (E × E) →L[ℝ] E ↦ L v) heq
    have hAvertical : ∀ v : E, A (0, v) = (0, v) := by
      have h := (hA.comp a (hasFDerivAt_prodMk_right a a)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u ↦ (hvertical u).symm)
      have heq := h.unique ((hasFDerivAt_const a a).prodMk hdd)
      intro v
      exact congrArg (fun L : E →L[ℝ] (E × E) ↦ L v) heq
    -- These two block identities give injectivity, hence invertibility in finite dimension.
    have hker : ∀ v, A v = 0 → v = 0 := by
      intro v hv
      have hv₁ : v.1 = 0 := by simpa only [hAfirst, Prod.fst_zero] using congrArg Prod.fst hv
      have hsplit : v = (0, v.2) := Prod.ext hv₁ rfl
      rw [hsplit, hAvertical] at hv
      exact hsplit.trans hv
    have hinj : Function.Injective A := by
      intro v w hvw
      apply sub_eq_zero.mp
      apply hker
      rw [map_sub, hvw, sub_self]
    let e : (E × E) ≃L[ℝ] (E × E) :=
      (LinearEquiv.ofBijective A.toLinearMap
        ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
    have hginv : A.IsInvertible := ⟨e, rfl⟩
    have hmd : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) D (x, x) := hD.mdifferentiableAt (by simp)
    have hm : mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) D (x, x) = A := by
      simpa only [ModelWithCorners.range_eq_univ, fderivWithin_univ] using! hmd.mfderiv_abuse
    apply AtiyahSinger.exists_partialDiffeomorph_of_isInvertible_mfderiv hs hΩ hx
    rw [hm]
    exact hginv
  -- Regard the diagonal as a closed embedded subspace of the union of local inverse domains.
  let TM := TangentBundle (𝓘(ℝ, E)) M
  let : T2Space TM := (AtiyahSinger.tangentBundle_topology E M).1
  let : ParacompactSpace TM := (AtiyahSinger.tangentBundle_topology E M).2.2
  let D : M × M → TM := fun z ↦ ⟨z.1, d z.1 z.2⟩
  choose Ψ hmem hsub heq using hlocalInverse
  change ∀ x, (Ψ x : M × M → TM) = D at heq
  let V : TopologicalSpace.Opens (M × M) :=
    ⟨⋃ x, (Ψ x).source, isOpen_iUnion fun x ↦ (Ψ x).open_source⟩
  have hVΩ : (V : Set (M × M)) ⊆ Ω := by
    intro p hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp hp
    exact hsub x hx
  have hdiagV (x : M) : (x, x) ∈ V := mem_iUnion_of_mem x (hmem x)
  let s : Set V := {p | p.val.1 = p.val.2}
  let e : s ≃ₜ M :=
    { toFun := fun p ↦ p.val.val.1
      invFun := fun x ↦ ⟨⟨(x, x), hdiagV x⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨x, y⟩, hp⟩, hxy⟩
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext rfl hxy
      right_inv := fun x ↦ rfl
      continuous_toFun := continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
      continuous_invFun := by fun_prop }
  have hzemb : IsClosedEmbedding (zeroSection E (TangentSpace (𝓘(ℝ, E)) : M → Type _)) :=
    (show Function.LeftInverse (fun p : TM ↦ p.proj)
      (zeroSection E (TangentSpace (𝓘(ℝ, E)))) from fun x ↦ rfl).isClosedEmbedding
        (FiberBundle.continuous_proj E _)
        (contMDiff_zeroSection (IB := 𝓘(ℝ, E)) (n := ∞)
          ℝ (TangentSpace (𝓘(ℝ, E)))).continuous
  have hrestricted : IsClosedEmbedding (fun p : s ↦ D p.val.val) := by
    have hfun : (fun p : s ↦ D p.val.val) =
        (zeroSection E (TangentSpace (𝓘(ℝ, E)))) ∘ e := by
      funext p
      change (⟨p.val.val.1, d p.val.val.1 p.val.val.2⟩ : TM) = ⟨p.val.val.1, 0⟩
      rw [← p.property, hzero]
      rfl
    rw [hfun]
    exact hzemb.comp e.isClosedEmbedding
  have hDV : Continuous (fun p : V ↦ D p.val) :=
    hs.continuousOn.comp_continuous continuous_subtype_val fun p ↦ hVΩ p.property
  have hloc : ∀ p ∈ s, ∃ u : Set V, IsOpen u ∧ p ∈ u ∧ InjOn (fun q : V ↦ D q.val) u := by
    intro p hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp p.property
    refine ⟨Subtype.val ⁻¹' (Ψ x).source,
      (Ψ x).open_source.preimage continuous_subtype_val, hx, ?_⟩
    intro q hq r hr hqr
    apply Subtype.ext
    apply (Ψ x).toPartialEquiv.injOn hq hr
    simpa only [heq] using hqr
  -- Shrink once along the full noncompact diagonal to make the subtraction globally injective.
  obtain ⟨u, hu, hsu, hinu⟩ :=
    AtiyahSinger.exists_isOpen_superset_injOn_of_isClosedEmbedding hDV hrestricted hloc
  let U : Set (M × M) := Subtype.val '' u
  have hU : IsOpen U := V.2.isOpenEmbedding_subtypeVal.isOpenMap _ hu
  have hUV : U ⊆ V := by rintro p ⟨q, hq, rfl⟩; exact q.property
  have hdiagU (x : M) : (x, x) ∈ U :=
    ⟨⟨(x, x), hdiagV x⟩, hsu rfl, rfl⟩
  have hDU : InjOn D U := by
    rintro p ⟨p', hp, rfl⟩ q ⟨q', hq, rfl⟩ hpq
    exact congrArg Subtype.val (hinu hp hq hpq)
  have hlocal (p : M × M) (hp : p ∈ U) : ∃ x, p ∈ (Ψ x).source :=
    mem_iUnion.mp (hUV hp)
  let T : Set TM := D '' U
  have hT : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨x, hpx⟩ := hlocal p hp
    have h := (Ψ x).toOpenPartialHomeomorph.image_mem_nhds hpx (hU.mem_nhds hp)
    simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, heq] using h
  -- Select the unique inverse on the image; the diagonal fallback also handles empty M.
  let G : TM → M × M := fun z ↦ if hz : z ∈ T then hz.choose else (z.proj, z.proj)
  have hG (z : TM) (hz : z ∈ T) : G z ∈ U ∧ D (G z) = z := by
    dsimp only [G]
    rw [dite_eq_left hz]
    exact hz.choose_spec
  have hleft (p : M × M) (hp : p ∈ U) : G (D p) = p :=
    hDU (hG _ ⟨p, hp, rfl⟩).1 hp (hG _ ⟨p, hp, rfl⟩).2
  -- The selected inverse agrees near each image point with an already smooth inverse chart.
  have hGsmooth : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ G T := by
    intro z hz
    have hp := (hG z hz).1
    obtain ⟨x, hpx⟩ := hlocal (G z) hp
    let K := (Ψ x).toOpenPartialHomeomorph
    have hDz : K (G z) = z := by
      change (Ψ x) (G z) = z
      rw [heq x]
      exact (hG z hz).2
    have hzK : z ∈ K.target := hDz ▸ K.map_source hpx
    let W : Set TM := K.target ∩ K.symm ⁻¹' U
    have hW : IsOpen W := K.symm.isOpen_inter_preimage hU
    have hzW : z ∈ W := by
      refine ⟨hzK, ?_⟩
      have hInv : K.symm z = G z := by
        simpa only [hDz] using K.left_inv hpx
      change K.symm z ∈ U
      rw [hInv]
      exact hp
    apply ContMDiffAt.contMDiffWithinAt
    have hlocalSmooth := (Ψ x).contMDiffOn_invFun.contMDiffAt (K.open_target.mem_nhds hzK)
    apply hlocalSmooth.congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hzW] with y hy
    have hyU : K.symm y ∈ U := hy.2
    have hDy : D (K.symm y) = y := by
      rw [← heq x]
      exact K.right_inv hy.1
    have hyT : y ∈ T := ⟨K.symm y, hyU, hDy⟩
    exact hDU (hG y hyT).1 hyU ((hG y hyT).2.trans hDy.symm)
  let Φ : PartialDiffeomorph ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M) TM ∞ :=
    { toFun := D
      invFun := G
      source := U
      target := T
      map_source' := fun p hp ↦ ⟨p, hp, rfl⟩
      map_target' := fun z hz ↦ (hG z hz).1
      left_inv' := hleft
      right_inv' := fun z hz ↦ (hG z hz).2
      open_source := hU
      open_target := hT
      contMDiffOn_toFun := hs.mono (hUV.trans hVΩ)
      contMDiffOn_invFun := hGsmooth }
  have hDzero (x : M) : D (x, x) = ⟨x, 0⟩ := by
    simp [D, hzero]
    rfl
  have hzeroT (x : M) : (⟨x, 0⟩ : TM) ∈ T :=
    ⟨(x, x), hdiagU x, hDzero x⟩
  have hGbase (p : TM) (hp : p ∈ T) : (G p).1 = p.proj :=
    congrArg (fun q : TM ↦ q.proj) (hG p hp).2
  have hGzero (x : M) : G (⟨x, 0⟩ : TM) = (x, x) := by
    rw [← hDzero x]
    exact hleft _ (hdiagU x)
  -- The fiber derivative is fixed by differentiating the inverse subtraction identity.
  have hincl (x : M) : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun v : E ↦ (⟨x, v⟩ : TM)) := by
    intro v
    let e := trivializationAt E (TangentSpace (𝓘(ℝ, E))) x
    rw [e.contMDiffAt_iff (e.mem_source.mpr (mem_baseSet_trivializationAt _ _ _))]
    refine ⟨contMDiffAt_const, ?_⟩
    apply contMDiffAt_id.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro w
    change tangentCoordChange (𝓘(ℝ, E)) x x x w = w
    exact tangentCoordChange_self (by simp)
  have hderivAdd (x : M) : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (fun v : E ↦ (G (⟨x, v⟩ : TM)).2) 0 (ContinuousLinearMap.id ℝ E) := by
    let incl : E → TM := fun v ↦ ⟨x, v⟩
    have hci : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞ incl := hincl x
    let a : E → M := fun v ↦ (G (⟨x, v⟩ : TM)).2
    have ha0 : a 0 = x := congrArg Prod.snd (hGzero x)
    have ha : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ a 0 :=
      contMDiffAt_snd.comp (0 : E)
        ((hGsmooth.contMDiffAt (hT.mem_nhds (hzeroT x))).comp (0 : E) hci.contMDiffAt)
    have hright : (d x ∘ a) =ᶠ[𝓝 (0 : E)] id := by
      have hnear := hci.continuous.continuousAt (hT.mem_nhds (hzeroT x))
      filter_upwards [hnear] with v hv
      have heq := congrArg (fun q : TM ↦ (q.snd : E)) (hG ⟨x, v⟩ hv).2
      change d (G ⟨x, v⟩).1 (G ⟨x, v⟩).2 = v at heq
      rw [hGbase ⟨x, v⟩ hv] at heq
      exact heq
    let A : E →L[ℝ] E := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) a 0
    have hda : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) a 0 A :=
      (ha.mdifferentiableAt (by simp)).hasMFDerivAt
    have hdc : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (d x) (a 0)
        (ContinuousLinearMap.id ℝ E) := by
      rw [ha0]
      exact hd x
    have hchain : HasFDerivAt (d x ∘ a) ((ContinuousLinearMap.id ℝ E).comp A) (0 : E) :=
      (hdc.comp (0 : E) hda).hasFDerivAt
    have heq := (hchain.congr_of_eventuallyEq hright.symm).unique (hasFDerivAt_id (0 : E))
    have hAeq : A = ContinuousLinearMap.id ℝ E := by
      simpa only [ContinuousLinearMap.id_comp] using! heq
    exact hAeq ▸ hda
  exact ⟨Φ.symm, hzeroT, hGbase, hGzero, hderivAdd⟩

end AtiyahSinger
