/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalTubularLocalAddition

/-!
# Normalized tubular germs of the actual quotient normal bundle

Public module ID: M1310.

For second-countable Hausdorff finite-dimensional real manifolds, a proper smooth
embedding admits a normalized diffeomorphism from an open neighborhood of the entire
zero section in its actual quotient normal bundle to an open subset of the ambient
manifold. The smooth splitting uses the original selected quotient atlas, and the
normal derivative is the identity in that same atlas.

We combine a smooth right inverse of the normal quotient with an ambient local addition.
At zero the total differential has the original immersion differential in the horizontal
block and the chosen splitting in the vertical block. The quotient separates these blocks,
so the differential is bijective. Local inverse charts then glue after noncompact shrinking
along the closed embedded zero section; their inverses prove smoothness of the common inverse.

This is the local-addition proof of the tubular neighborhood theorem, supplementing MS 11.1
in the noncompact case. No compactness or constant radius is assumed. Compression of whole
fibers into this germ is a separate step. The nonempty-base assumption only supplies a value
for the total inverse function away from its open target; the empty-base theorem is immediate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [Nonempty M]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

omit [T2Space M] [SecondCountableTopology M] in
/-- A smooth normal map with the normalized fiber derivative has a tubular germ with the
same forward function. Thus additional identities of the given map survive shrinking. -/
theorem exists_normalTubeGerm_of_normalizedMap (he : IsEmbedding f) (hp : IsProperMap f) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∀ (Ω : Set (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)))
      (g : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) → N)
      (s : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x →L[ℝ] TangentSpace 𝓘(ℝ, F) (f x)),
      IsOpen Ω → (∀ x, (⟨x, 0⟩ : TotalSpace _ _) ∈ Ω) →
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F) ∞ g Ω →
      (∀ x, g ⟨x, 0⟩ = f x) →
      (∀ x, Function.RightInverse (s x)
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ) →
      (∀ x : M,
        let e := (trivializationAt (NormalModel E F)
          (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x).continuousLinearEquivAt ℝ x
          (mem_baseSet_trivializationAt (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x)
        HasMFDerivAt 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F)
          (fun w ↦ g ⟨x, e.symm w⟩) 0 ((s x).comp e.symm.toContinuousLinearMap)) →
      ∃ Φ : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F)
          (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) N ∞,
        Φ.source ⊆ Ω ∧ (Φ : TotalSpace _ _ → N) = g ∧
        (∀ x, (⟨x, 0⟩ : TotalSpace _ _) ∈ Φ.source) ∧
        (∀ x, Φ ⟨x, 0⟩ = f x) ∧
        ∀ x : M,
          let e := (trivializationAt (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x).continuousLinearEquivAt ℝ x
            (mem_baseSet_trivializationAt (NormalModel E F)
              (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x)
          ∀ v : NormalModel E F,
            (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
              (mfderiv 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F)
                (fun w ↦ Φ ⟨x, e.symm w⟩) 0
                  ((NormedSpace.fromTangentSpace (0 : NormalModel E F)).symm v)) = e.symm v := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace F N
  let : ParacompactSpace N := inferInstance
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  intro Ω g s hΩ hmem hg hzero hright hder
  have hnormal : ∀ x : M,
      let e := (trivializationAt G V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt G V x)
      ∀ v : G, (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) (fun w ↦ g ⟨x, e.symm w⟩) 0
          ((NormedSpace.fromTangentSpace (0 : G)).symm v)) = e.symm v := by
    intro x
    dsimp only
    intro v
    rw [(hder x).mfderiv]
    exact hright x _
  -- The horizontal differential is df, and the quotient detects the normal block.
  have hlocalInverse : ∀ x : M, ∃ Ψ : PartialDiffeomorph
      (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) NB N ∞,
      (⟨x, 0⟩ : NB) ∈ Ψ.source ∧ Ψ.source ⊆ Ω ∧ (Ψ : NB → N) = g := by
    intro x
    let z₀ : NB := ⟨x, 0⟩
    let κ := chartAt E x
    let a : E := κ x
    let t := trivializationAt G V x
    have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt G V x
    let e := t.continuousLinearEquivAt ℝ x hx
    let φ := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z₀
    let ψ := chartAt F (f x)
    let C : E × G → F := ψ ∘ g ∘ φ.symm
    have hφzero : φ z₀ = (a, 0) := by
      dsimp only [φ]
      rw [FiberBundle.extChartAt]
      change (κ (t ⟨x, 0⟩).1, (t ⟨x, 0⟩).2) = (a, 0)
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx, map_zero]
    have hφvertical (w : G) : φ.symm (a, w) = (⟨x, e.symm w⟩ : NB) := by
      dsimp only [φ]
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm (κ x), w) = _
      rw [κ.left_inv (mem_chart_source E x)]
      exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x hx w
    have hφhorizontal : (fun u : E ↦ φ.symm (u, 0)) =ᶠ[𝓝 a]
        (fun u : E ↦ (⟨κ.symm u, 0⟩ : NB)) := by
      have hκ : ContinuousAt κ.symm a := κ.continuousAt_symm
        (κ.map_source (mem_chart_source E x))
      have hκx : κ.symm a = x := κ.left_inv (mem_chart_source E x)
      filter_upwards [hκ (hκx ▸ t.open_baseSet.mem_nhds hx)] with u hu
      dsimp only [φ]
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm u, 0) = _
      rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hu, map_zero]
    have hgx : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞ g z₀ :=
      hg.contMDiffAt (hΩ.mem_nhds (hmem x))
    have hC : ContDiffAt ℝ ∞ C (a, 0) := by
      have h := (contMDiffAt_iff.mp hgx).2
      change ContDiffWithinAt ℝ ∞ (extChartAt 𝓘(ℝ, F) (g z₀) ∘ g ∘ φ.symm)
        (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, G))) (φ z₀) at h
      rw [hφzero, hzero x] at h
      simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
    let A : (E × G) →L[ℝ] F := fderiv ℝ C (a, 0)
    have hA : HasFDerivAt C A (a, 0) := (hC.differentiableAt (by simp)).hasFDerivAt
    let B : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
    have hB : HasFDerivAt (ψ ∘ f ∘ κ.symm) B a := by
      simpa only [writtenInExtChartAt, mfld_simps, hasFDerivWithinAt_univ] using!
        (f.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.2
    have hhorizontal : ∀ v : E, A (v, 0) = B v := by
      have heq : (fun u : E ↦ C (u, 0)) =ᶠ[𝓝 a] (ψ ∘ f ∘ κ.symm) := by
        filter_upwards [hφhorizontal] with u hu
        change ψ (g (φ.symm (u, 0))) = ψ (f (κ.symm u))
        rw [hu, hzero]
      have hc : HasFDerivAt (fun u : E ↦ C (u, 0))
          (A.comp (ContinuousLinearMap.inl ℝ E G)) a := by
        simpa only [Function.comp_def] using!
          HasFDerivAt.comp a hA (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : G))
      have h := hc.congr_of_eventuallyEq heq.symm
      intro v
      exact congrArg (fun L : E →L[ℝ] F ↦ L v) (h.unique hB)
    let L : G →L[ℝ] F := (s x).comp e.symm.toContinuousLinearMap
    have hvertical : ∀ w : G, A (0, w) = L w := by
      have hd := hder x
      have hL : HasFDerivAt (fun w : G ↦ ψ (g ⟨x, e.symm w⟩)) L 0 := by
        have h := hd.2
        simpa only [writtenInExtChartAt, mfld_simps, map_zero, hzero,
          hasFDerivWithinAt_univ] using! h
      have heq : (fun w : G ↦ C (a, w)) =ᶠ[𝓝 (0 : G)]
          (fun w : G ↦ ψ (g ⟨x, e.symm w⟩)) :=
        Filter.Eventually.of_forall fun w ↦ congrArg (ψ ∘ g) (hφvertical w)
      have h := (hA.comp 0 (hasFDerivAt_prodMk_right a (0 : G))).congr_of_eventuallyEq
        heq.symm
      intro w
      exact congrArg (fun L : G →L[ℝ] F ↦ L w) (h.unique hL)
    -- The original quotient splits the two blocks, proving bijectivity without a rank shortcut.
    have hAblock (v : E × G) : A v = B v.1 + L v.2 := by
      calc
        A v = A ((v.1, 0) + (0, v.2)) := by
          congr 1
          ext <;> simp
        _ = A (v.1, 0) + A (0, v.2) := A.map_add _ _
        _ = B v.1 + L v.2 := by rw [hhorizontal, hvertical]
    let Q : F →ₗ[ℝ] V x :=
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    have hQB (v : E) : Q (B v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    have hQL (w : G) : Q (L w) = e.symm w := hright x (e.symm w)
    have hker (v : E × G) (hv : A v = 0) : v = 0 := by
      have hw : e.symm v.2 = 0 := by
        have h := congrArg Q hv
        change Q (A v) = Q 0 at h
        rw [hAblock, map_add, hQB, hQL, Q.map_zero, zero_add] at h
        exact h
      have hv₂ : v.2 = 0 := e.symm.injective (hw.trans (e.symm.map_zero).symm)
      have hv₁ : v.1 = 0 := by
        have hBv : B v.1 = B 0 := by
          simpa only [hAblock, hv₂, map_zero, add_zero] using hv
        exact hf.mfderiv_injective (by simp) x hBv
      exact Prod.ext hv₁ hv₂
    have hinj : Function.Injective A := by
      intro v w hvw
      apply sub_eq_zero.mp
      apply hker
      rw [map_sub, hvw, sub_self]
    have hsurj : Function.Surjective A := by
      intro u
      let w : G := e (Q u)
      have hker : u - L w ∈ LinearMap.range
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        change Q (u - L w) = 0
        rw [map_sub, hQL, show e.symm w = Q u from e.symm_apply_apply (Q u), sub_self]
      obtain ⟨v, hv⟩ := hker
      refine ⟨(v, w), ?_⟩
      rw [hAblock]
      change B v + L w = u
      change B v = u - L w at hv
      rw [hv, sub_add_cancel]
    let Aequiv : (E × G) ≃L[ℝ] F :=
      (LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
    have hm : mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) g z₀ = A := by
      have h := (hgx.mdifferentiableAt (by simp)).mfderiv_abuse
      change mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) g z₀ =
        fderivWithin ℝ (extChartAt 𝓘(ℝ, F) (g z₀) ∘ g ∘ φ.symm)
          (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, G))) (φ z₀) at h
      rw [hφzero, hzero x] at h
      simpa only [ModelWithCorners.range_eq_univ, fderivWithin_univ] using! h
    apply exists_partialDiffeomorph_of_isInvertible_mfderiv hg hΩ (hmem x)
    rw [hm]
    exact ⟨Aequiv, rfl⟩
  -- Shrink along the whole closed embedded zero section to make the map one-to-one.
  choose Ψ hΨmem hΨsub hΨeq using hlocalInverse
  let W : TopologicalSpace.Opens NB :=
    ⟨⋃ x, (Ψ x).source, isOpen_iUnion fun x ↦ (Ψ x).open_source⟩
  have hWΩ : (W : Set NB) ⊆ Ω := by
    intro p hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp hp
    exact hΨsub x hx
  have hzeroW (x : M) : (⟨x, 0⟩ : NB) ∈ W := mem_iUnion_of_mem x (hΨmem x)
  let Z : Set W := {p | p.val.snd = 0}
  have hzcont : Continuous (zeroSection G V) :=
    Bundle.Trivialization.continuous_zeroSection ℝ
  let e : Z ≃ₜ M :=
    { toFun := fun p ↦ p.val.val.proj
      invFun := fun x ↦ ⟨⟨⟨x, 0⟩, hzeroW x⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨x, v⟩, hp⟩, hv⟩
        change v = (0 : V x) at hv
        subst v
        rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (FiberBundle.continuous_proj G V).comp
        (continuous_subtype_val.comp continuous_subtype_val)
      continuous_invFun := (hzcont.subtype_mk hzeroW).subtype_mk (fun _ ↦ rfl) }
  have hfclosed : IsClosedEmbedding (f : M → N) := ⟨he, hp.isClosedMap.isClosed_range⟩
  have hrestricted : IsClosedEmbedding (fun p : Z ↦ g p.val.val) := by
    have hfun : (fun p : Z ↦ g p.val.val) = f ∘ e := by
      funext p
      rcases p with ⟨⟨⟨x, v⟩, hp⟩, hv⟩
      change v = (0 : V x) at hv
      subst v
      exact hzero x
    rw [hfun]
    exact hfclosed.comp e.isClosedEmbedding
  have hgW : Continuous (fun p : W ↦ g p.val) :=
    hg.continuousOn.comp_continuous continuous_subtype_val (fun p ↦ hWΩ p.property)
  have hloc : ∀ p ∈ Z, ∃ u : Set W, IsOpen u ∧ p ∈ u ∧
      InjOn (fun q : W ↦ g q.val) u := by
    intro p hp
    obtain ⟨x, hx⟩ := mem_iUnion.mp p.property
    refine ⟨Subtype.val ⁻¹' (Ψ x).source,
      (Ψ x).open_source.preimage continuous_subtype_val, hx, ?_⟩
    intro q hq r hr hqr
    apply Subtype.ext
    apply (Ψ x).toPartialEquiv.injOn hq hr
    simpa only [hΨeq] using hqr
  obtain ⟨u, hu, hZu, hinu⟩ :=
    exists_isOpen_superset_injOn_of_isClosedEmbedding hgW hrestricted hloc
  let U : Set NB := Subtype.val '' u
  have hU : IsOpen U := W.2.isOpenEmbedding_subtypeVal.isOpenMap _ hu
  have hUW : U ⊆ W := by
    rintro p ⟨q, hq, rfl⟩
    exact q.property
  have hzeroU (x : M) : (⟨x, 0⟩ : NB) ∈ U :=
    ⟨⟨⟨x, 0⟩, hzeroW x⟩, hZu rfl, rfl⟩
  have hgU : InjOn g U := by
    rintro p ⟨p', hp, rfl⟩ q ⟨q', hq, rfl⟩ hpq
    exact congrArg Subtype.val (hinu hp hq hpq)
  have hlocal (p : NB) (hp : p ∈ U) : ∃ x, p ∈ (Ψ x).source :=
    mem_iUnion.mp (hUW hp)
  -- Each point of the image has the same smooth inverse as one original local chart.
  let T : Set N := g '' U
  have hT : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨x, hpx⟩ := hlocal p hp
    have h := (Ψ x).toOpenPartialHomeomorph.image_mem_nhds hpx (hU.mem_nhds hp)
    simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hΨeq] using h
  let p₀ : NB := ⟨Classical.choice inferInstance, 0⟩
  let j : N → NB := fun y ↦ if hy : y ∈ T then hy.choose else p₀
  have hj (y : N) (hy : y ∈ T) : j y ∈ U ∧ g (j y) = y := by
    dsimp only [j]
    rw [dite_eq_left hy]
    exact hy.choose_spec
  have hleft (p : NB) (hp : p ∈ U) : j (g p) = p :=
    hgU (hj _ ⟨p, hp, rfl⟩).1 hp (hj _ ⟨p, hp, rfl⟩).2
  have hjsmooth : ContMDiffOn 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ j T := by
    intro y hy
    have hp := (hj y hy).1
    obtain ⟨x, hpx⟩ := hlocal (j y) hp
    let K := (Ψ x).toOpenPartialHomeomorph
    have hgy : K (j y) = y := by
      change (Ψ x) (j y) = y
      rw [hΨeq x]
      exact (hj y hy).2
    have hyK : y ∈ K.target := hgy ▸ K.map_source hpx
    let O : Set N := K.target ∩ K.symm ⁻¹' U
    have hO : IsOpen O := K.symm.isOpen_inter_preimage hU
    have hyO : y ∈ O := by
      refine ⟨hyK, ?_⟩
      have hinv : K.symm y = j y := by
        simpa only [hgy] using K.left_inv hpx
      change K.symm y ∈ U
      rw [hinv]
      exact hp
    apply ContMDiffAt.contMDiffWithinAt
    have hlocalSmooth := (Ψ x).contMDiffOn_invFun.contMDiffAt (K.open_target.mem_nhds hyK)
    apply hlocalSmooth.congr_of_eventuallyEq
    filter_upwards [hO.mem_nhds hyO] with z hz
    have hzU : K.symm z ∈ U := hz.2
    have hgz : g (K.symm z) = z := by
      rw [← hΨeq x]
      exact K.right_inv hz.1
    have hzT : z ∈ T := ⟨K.symm z, hzU, hgz⟩
    exact hgU (hj z hzT).1 hzU ((hj z hzT).2.trans hgz.symm)
  let Φ : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) NB N ∞ :=
    { toFun := g
      invFun := j
      source := U
      target := T
      map_source' := fun p hp ↦ ⟨p, hp, rfl⟩
      map_target' := fun y hy ↦ (hj y hy).1
      left_inv' := hleft
      right_inv' := fun y hy ↦ (hj y hy).2
      open_source := hU
      open_target := hT
      contMDiffOn_toFun := hg.mono (hUW.trans hWΩ)
      contMDiffOn_invFun := hjsmooth }
  exact ⟨Φ, hUW.trans hWΩ, rfl, hzeroU, hzero, hnormal⟩

/-- A normalized tubular germ for a proper embedding, on the original quotient bundle. -/
theorem exists_normalTubeGerm (he : IsEmbedding f) (hp : IsProperMap f) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ Φ : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F)
        (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) N ∞,
      (∀ x, (⟨x, 0⟩ : TotalSpace _ _) ∈ Φ.source) ∧
      (∀ x, Φ ⟨x, 0⟩ = f x) ∧
      ∀ x : M,
        let e := (trivializationAt (NormalModel E F)
          (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x).continuousLinearEquivAt ℝ x
          (mem_baseSet_trivializationAt (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x)
        ∀ v : NormalModel E F,
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F)
              (fun w ↦ Φ ⟨x, e.symm w⟩) 0
                ((NormedSpace.fromTangentSpace (0 : NormalModel E F)).symm v)) = e.symm v := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : ParacompactSpace M := inferInstance
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  -- Lift the actual quotient bundle into the ambient tangent bundle by its smooth splitting.
  obtain ⟨s, hs, hright⟩ := exists_smooth_normal_rightInverse f hf
  obtain ⟨Φ, hΦsource, hΦproj, hΦzero, hΦderiv⟩ :=
    exists_smooth_localAddition (E := F) (M := N)
  let S : NB → TangentBundle 𝓘(ℝ, F) N := fun z ↦ ⟨f z.proj, s z.proj z.snd⟩
  have hS : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞ S := by
    have hLift : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
        (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace F ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) ↦
          (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      constructor
      · exact f.contMDiff.contMDiffAt.comp z
          (Bundle.contMDiffAt_proj ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))
      · exact (Bundle.contMDiffAt_totalSpace.mp
          (show ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, F))
            (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ id z from contMDiffAt_id)).2
    exact hLift.comp hs
  let Ω := S ⁻¹' Φ.source
  let g : NB → N := fun z ↦ (Φ (S z)).2
  have hΩ : IsOpen Ω := Φ.open_source.preimage hS.continuous
  have hzero (x : M) : g ⟨x, 0⟩ = f x := by
    simpa only [g, S, map_zero] using congrArg Prod.snd (hΦzero (f x))
  have hmem (x : M) : (⟨x, 0⟩ : NB) ∈ Ω := by
    simpa only [Ω, S, mem_preimage, map_zero] using hΦsource (f x)
  have hg : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞ g Ω := by
    intro z hz
    exact ((Φ.contMDiffOn.comp hS.contMDiffOn (fun _ h ↦ h)) z hz).snd
  obtain ⟨Ψ, _, _, hΨmem, hΨzero, hΨnormal⟩ :=
    exists_normalTubeGerm_of_normalizedMap f hf he hp Ω g s hΩ hmem hg hzero hright (by
      intro x
      dsimp only
      let e := (trivializationAt G V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt G V x)
      let L : G →L[ℝ] F := (s x).comp e.symm.toContinuousLinearMap
      have hd : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, F)
          (fun w : G ↦ g ⟨x, e.symm w⟩) 0 L := by
        have hΦL : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, F)
            (fun v : F ↦ (Φ ⟨f x, v⟩).2) (L 0) (ContinuousLinearMap.id ℝ F) := by
          rw [L.map_zero]
          exact hΦderiv (f x)
        have h := hΦL.comp 0 L.hasMFDerivAt
        simpa only [Function.comp_def, map_zero, ContinuousLinearMap.id_comp] using! h
      exact hd)
  exact ⟨Ψ, hΨmem, hΨzero, hΨnormal⟩

end AtiyahSinger
