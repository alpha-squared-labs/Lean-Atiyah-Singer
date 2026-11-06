/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenNormalPullback
public import AtiyahSinger.Geometry.TangentNormalPullback
public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# Open transport of the original normal and tubular data

Public module ID: M1326.

The derivative of a smooth local diffeomorphism has a smooth local inverse,
obtained by differentiating the same base inverse. This permits the original
normal-quotient comparison to be applied to the tangent square as well as the
base square. All models and normal quotient atlases remain the original ones.

Sources: the chain rule and the tubular naturality argument of SG III.12 and
Karoubi IV.5.21--5.22. These explicit geometric adapters implement that argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology

section Tangent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
/-- The actual tangent map of a smooth local diffeomorphism is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_smoothTangentMap
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    IsLocalDiffeomorph 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) ∞ (smoothTangentMap f) := by
  intro z
  let h := hf z.proj
  let g := h.localInverse
  let T := tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let S := tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g
  have hfmem (x : M) (hx : x ∈ g.target) : f x ∈ g.source := by
    have ht := g.map_target hx
    have hr := h.localInverse_right_inv ht
    rw [g.right_inv hx] at hr
    rw [hr]
    exact ht
  have hleft (x : TangentBundle 𝓘(ℝ, E) M) (hx : x.proj ∈ g.target) :
      S (T x) = x := by
    -- The base inverse identity holds on an open neighborhood of this same vector's base.
    have hfx : f x.proj ∈ g.source := hfmem x.proj hx
    have hgs := g.contMDiffOn.contMDiffAt (g.open_source.mem_nhds hfx)
    dsimp only [S, T]
    rw [← tangentMap_comp_at x (hgs.mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiable (by simp) x.proj)]
    apply TotalSpace.ext (h.localInverse_left_inv hx)
    apply heq_of_eq
    have heq : (g : N → M) ∘ f =ᶠ[𝓝 x.proj] id :=
      Filter.eventuallyEq_of_mem (g.open_target.mem_nhds hx) h.localInverse_eqOn_left
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    have hv := congrArg (fun L ↦ L x.snd) hd
    rw [mfderiv_id] at hv
    exact hv
  have hright (y : TangentBundle 𝓘(ℝ, F) N) (hy : y.proj ∈ g.source) :
      T (S y) = y := by
    have hgs := g.contMDiffOn.contMDiffAt (g.open_source.mem_nhds hy)
    dsimp only [S, T]
    rw [← tangentMap_comp_at y
      (f.contMDiff.mdifferentiable (by simp) (g y.proj))
      (hgs.mdifferentiableAt (by simp))]
    apply TotalSpace.ext (h.localInverse_right_inv hy)
    apply heq_of_eq
    have heq : (f : M → N) ∘ g =ᶠ[𝓝 y.proj] id :=
      Filter.eventuallyEq_of_mem (g.open_source.mem_nhds hy) h.localInverse_eqOn_right
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F))
    have hv := congrArg (fun L ↦ L y.snd) hd
    rw [mfderiv_id] at hv
    exact hv
  -- Differentiate the original partial inverse on the full tangent fibers over its open sets.
  let Φ : PartialDiffeomorph 𝓘(ℝ, E × E) 𝓘(ℝ, F × F)
      (TangentBundle 𝓘(ℝ, E) M) (TangentBundle 𝓘(ℝ, F) N) ∞ :=
    { toFun := T
      invFun := S
      source := TotalSpace.proj ⁻¹' g.target
      target := TotalSpace.proj ⁻¹' g.source
      map_source' := by
        intro x hx
        change f x.proj ∈ g.source
        exact hfmem x.proj hx
      map_target' := fun y hy ↦ g.map_source hy
      left_inv' := hleft
      right_inv' := hright
      open_source := g.open_target.preimage (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E)))
      open_target := g.open_source.preimage (FiberBundle.continuous_proj F (TangentSpace 𝓘(ℝ, F)))
      contMDiffOn_toFun := (smoothTangentMap f).contMDiff.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        exact ((g.contMDiffOn.contMDiffAt (g.open_source.mem_nhds hy)).contMDiffAt_tangentMap
          (X := y) (m := ∞) (by simp)).contMDiffWithinAt }
  exact Φ.isLocalDiffeomorphAt _ _ _ h.localInverse_mem_target

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- An injective local diffeomorphism identifies its domain with its actual open image. -/
theorem exists_diffeomorph_openRange
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hinj : Function.Injective f) :
    ∃ e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M hf.image ∞,
      ∀ x : M, (e x).val = f x := by
  let he : IsOpenEmbedding f :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap f.contMDiff.continuous hinj hf.isOpenMap
  let e : M ≃ₜ hf.image := he.isEmbedding.toHomeomorph
  have hinverse : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm := by
    intro y
    -- The inverse onto the image agrees locally with the original specified smooth inverse.
    let h := hf (e.symm y)
    have hbase : f (e.symm y) = y.val := congrArg Subtype.val (e.apply_symm_apply y)
    have hy : y.val ∈ h.localInverse.source := hbase ▸ h.localInverse_mem_source
    have hs := (h.contMDiffOn_localInverse.contMDiffAt
      (h.localInverse.open_source.mem_nhds hy)).comp y
        (contMDiff_subtype_val (I := 𝓘(ℝ, F)) (U := hf.image)).contMDiffAt
    apply hs.congr_of_eventuallyEq
    filter_upwards [(h.localInverse.open_source.preimage continuous_subtype_val).mem_nhds hy]
      with y' hy'
    apply hinj
    exact (congrArg Subtype.val (e.apply_symm_apply y')).trans
      (h.localInverse_right_inv hy').symm
  refine ⟨{
    toEquiv := e.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := hinverse }, fun _ ↦ rfl⟩
  exact (ContMDiff.subtypeVal_comp_iff hf.image e).mp f.contMDiff

end Tangent

section Source

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the source through an open parametrization transports the same whole normal tube. -/
theorem exists_tubularNeighborhood_openSource
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, G) 𝓘(ℝ, F) P N ∞)
    (i : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ g)
    (hi : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ i)
    (hinj : Function.Injective i) (hcomm : ∀ x, f x = g (i x))
    (e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
      NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, F) g (i x))
    (he : ∀ (x : M) (v : F),
      e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) g (i x)).toLinearMap).mkQ v)
    (T : TubularNeighborhood g hg) :
    ∃ S : TubularNeighborhood f hf,
      ∀ z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f),
        S.totalMap f hf z = T.totalMap g hg ⟨i z.proj, e z.proj z.snd⟩ := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let Vf := NormalModel E F
  let Vg := NormalModel G F
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, G) 𝓘(ℝ, F) g
  let NBf := TotalSpace Vf νf
  let NBg := TotalSpace Vg νg
  -- The supplied representative formula identifies the canonical smooth quotient comparison.
  obtain ⟨e₀, he₀, hes, heis⟩ := exists_normalPullback_equiv_of_localDiffeomorph
    f g i (ContMDiffMap.id (I := 𝓘(ℝ, F)) (M := N)) hf hg hi
      (Diffeomorph.refl 𝓘(ℝ, F) N ∞).isLocalDiffeomorph hcomm
  have heq : e = e₀ := by
    funext x
    apply ContinuousLinearEquiv.ext
    funext v
    obtain ⟨w, rfl⟩ :=
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ_surjective v
    have h := he₀ x w
    have hder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F)
        (ContMDiffMap.id (I := 𝓘(ℝ, F)) (M := N) (n := ∞)) (f x) =
        ContinuousLinearMap.id ℝ F := by
      change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (id : N → N) (f x) = _
      rw [mfderiv_id]
      rfl
    rw [hder] at h
    exact (he x w).trans h.symm
  subst e₀
  obtain ⟨d, hd⟩ := exists_diffeomorph_openRange i hi hinj
  let L (z : NBf) : NBg := ⟨i z.proj, e z.proj z.snd⟩
  have hL : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, G).prod 𝓘(ℝ, Vg)) ∞ L := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨i.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj νf),
      (Bundle.contMDiffAt_totalSpace.mp (hes z)).2⟩
  have hT : ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, Vg)) 𝓘(ℝ, F) ∞ (T.totalMap g hg) :=
    contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  have hTopen : IsOpenEmbedding (T.totalMap g hg) :=
    T.target.isOpen.isOpenEmbedding_subtypeVal.comp T.diffeomorph.toHomeomorph.isOpenEmbedding
  let τ (z : NBf) : N := T.totalMap g hg (L z)
  have hτ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) 𝓘(ℝ, F) ∞ τ := hT.comp hL
  let U : TopologicalSpace.Opens N :=
    ⟨T.totalMap g hg '' {w : NBg | w.proj ∈ Set.range i},
      hTopen.isOpenMap _ (hi.isOpen_range.preimage (FiberBundle.continuous_proj Vg νg))⟩
  have hτmem (z : NBf) : τ z ∈ U := ⟨L z, ⟨z.proj, rfl⟩, rfl⟩
  let a (y : U) : T.target := ⟨y.val, by
    obtain ⟨w, _, hw⟩ := y.property
    rw [← hw]
    exact (T.diffeomorph w).property⟩
  have ha : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff T.target a).mp contMDiff_subtype_val
  let w (y : U) : NBg := T.diffeomorph.symm (a y)
  have hw : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, G).prod 𝓘(ℝ, Vg)) ∞ w :=
    T.diffeomorph.symm.contMDiff.comp ha
  have hwbase (y : U) : (w y).proj ∈ Set.range i := by
    obtain ⟨v, hv, hval⟩ := y.property
    have heq : w y = v := by
      apply T.diffeomorph.injective
      change T.diffeomorph (T.diffeomorph.symm (a y)) = T.diffeomorph v
      rw [Diffeomorph.apply_symm_apply]
      exact Subtype.ext hval.symm
    exact heq ▸ hv
  let b (y : U) : M := d.symm ⟨(w y).proj, hwbase y⟩
  have hb : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ b := by
    apply d.symm.contMDiff.comp
    exact (ContMDiff.subtypeVal_comp_iff hi.image _).mp ((contMDiff_proj νg).comp hw)
  have hib (y : U) : i (b y) = (w y).proj := by
    rw [← hd]
    exact congrArg Subtype.val (d.apply_symm_apply ⟨(w y).proj, hwbase y⟩)
  let v (y : U) : νg (i (b y)) := (congrArg νg (hib y).symm).mp (w y).snd
  have hv (y : U) : (⟨i (b y), v y⟩ : NBg) = w y :=
    TotalSpace.ext (hib y) (by simp [v])
  let R (y : U) : TotalSpace Vg ((i : M → P) *ᵖ νg) := ⟨b y, v y⟩
  have hR : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞ R := by
    have hlift := hw.congr hv
    intro y
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨hb y, (Bundle.contMDiffAt_totalSpace.mp (hlift y)).2⟩
  let r (y : U) : NBf := ⟨b y, (e (b y)).symm (v y)⟩
  have hr : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞ r := heis.comp hR
  have hLr (y : U) : L (r y) = w y := by
    change (⟨i (b y), e (b y) ((e (b y)).symm (v y))⟩ : NBg) = w y
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hv y
  have hright (y : U) : τ (r y) = y.val := by
    change T.totalMap g hg (L (r y)) = y.val
    rw [hLr]
    exact congrArg Subtype.val (T.diffeomorph.apply_symm_apply (a y))
  have hLinj : Function.Injective L := by
    rintro ⟨x, v⟩ ⟨y, u⟩ h
    have hxy : x = y := hinj (congrArg TotalSpace.proj h)
    subst y
    apply congrArg (TotalSpace.mk x)
    apply (e x).injective
    exact eq_of_heq (TotalSpace.mk.inj h).2
  have hleft (z : NBf) : r ⟨τ z, hτmem z⟩ = z :=
    hLinj (hTopen.injective (hright ⟨τ z, hτmem z⟩))
  let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) 𝓘(ℝ, F) NBf U ∞ :=
    { toFun z := ⟨τ z, hτmem z⟩
      invFun := r
      left_inv := hleft
      right_inv y := Subtype.ext (hright y)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp hτ
      contMDiff_invFun := hr }
  have hzero (x : M) : (D ⟨x, 0⟩ : N) = f x := by
    change T.totalMap g hg ⟨i x, e x 0⟩ = f x
    rw [map_zero]
    exact (T.map_zero (i x)).trans (hcomm x).symm
  refine ⟨{ target := U, diffeomorph := D, map_zero := hzero, normal_deriv := ?_ },
    fun _ ↦ rfl⟩
  intro x
  dsimp only
  let cf := (trivializationAt Vf νf x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt Vf νf x)
  let cg := (trivializationAt Vg νg (i x)).continuousLinearEquivAt ℝ (i x)
    (mem_baseSet_trivializationAt Vg νg (i x))
  let A : Vf →L[ℝ] Vg := cg.toContinuousLinearMap.comp
    ((e x).toContinuousLinearMap.comp cf.symm.toContinuousLinearMap)
  let γ (u : Vg) : N := T.totalMap g hg ⟨i x, cg.symm u⟩
  let δ (u : Vf) : N := τ ⟨x, cf.symm u⟩
  have hγ : ContMDiff 𝓘(ℝ, Vg) 𝓘(ℝ, F) ∞ γ := by
    apply hT.comp
    intro u
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have hc (v : Vg) : (trivializationAt Vg νg (i x) ⟨i x, cg.symm v⟩).2 = v := by
      have hh := cg.apply_symm_apply v
      rw [Trivialization.continuousLinearEquivAt_apply] at hh
      exact hh
    simpa only [hc] using!
      (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, Vg) 𝓘(ℝ, Vg) ∞ id u)
  have hcurve : γ ∘ A = δ := by
    funext u
    change T.totalMap g hg ⟨i x, cg.symm (cg (e x (cf.symm u)))⟩ = _
    rw [cg.symm_apply_apply]
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, Vf)) (I' := 𝓘(ℝ, Vg)) (I'' := 𝓘(ℝ, F)) 0
    (show MDifferentiableAt 𝓘(ℝ, Vg) 𝓘(ℝ, F) γ (A 0) from by
      simpa only [map_zero] using hγ.mdifferentiable (by simp) 0)
    ((A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
  have hAder : mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, Vg) A 0 = A := by
    rw [mfderiv_eq_fderiv]
    exact A.fderiv
  rw [hcurve, hAder, map_zero] at hcomp
  intro u
  change (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) δ 0 u) = cf.symm u
  apply (e x).injective
  rw [he]
  have hd := congrArg (fun C : Vf →L[ℝ] F ↦ C u) hcomp
  change mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) δ 0 u =
    mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, F) γ 0 (A u) at hd
  rw [hd]
  have hn := T.normal_deriv (i x) (A u)
  change (LinearMap.range (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) g (i x)).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, F) γ 0 (A u)) = cg.symm (A u) at hn
  exact hn.trans (cg.symm_apply_apply (e x (cf.symm u)))

end Source

section Ambient

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An ambient open parametrization transports a normalized tube through its actual normal map. -/
theorem exists_tubularNeighborhood_openAmbient
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, G) M P ∞)
    (j : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ g)
    (hj : IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ j)
    (hinj : Function.Injective j) (hcomm : ∀ x, j (f x) = g x)
    (e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
      NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) g x)
    (he : ∀ (x : M) (v : F),
      e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) g x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) j (f x) v))
    (T : TubularNeighborhood f hf) :
    ∃ S : TubularNeighborhood g hg,
      ∀ z : TotalSpace (NormalModel E G) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) g),
        S.totalMap g hg z = j (T.totalMap f hf ⟨z.proj, (e z.proj).symm z.snd⟩) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let Vf := NormalModel E F
  let Vg := NormalModel E G
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) g
  let NBf := TotalSpace Vf νf
  let NBg := TotalSpace Vg νg
  -- The normal map is fixed by the original derivative before constructing any tube.
  obtain ⟨e₀, he₀, hes, heis⟩ := exists_normalPullback_equiv_of_localDiffeomorph
    f g (ContMDiffMap.id (I := 𝓘(ℝ, E)) (M := M)) j hf hg
      (Diffeomorph.refl 𝓘(ℝ, E) M ∞).isLocalDiffeomorph hj hcomm
  have heq : e = e₀ := by
    funext x
    apply ContinuousLinearEquiv.ext
    funext v
    obtain ⟨w, rfl⟩ :=
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ_surjective v
    exact (he x w).trans (he₀ x w).symm
  subst e₀
  have hc : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞
      (fun z : NBf ↦ (⟨z.proj, e z.proj z.snd⟩ : NBg)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj νf, (Bundle.contMDiffAt_totalSpace.mp (hes z)).2⟩
  have hci : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞
      (fun z : NBg ↦ (⟨z.proj, (e z.proj).symm z.snd⟩ : NBf)) := by
    apply heis.comp
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨Bundle.contMDiffAt_proj νg,
      (Bundle.contMDiffAt_totalSpace.mp (contMDiffAt_id (x := z))).2⟩
  let c : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) NBf NBg ∞ :=
    { toFun z := ⟨z.proj, e z.proj z.snd⟩
      invFun z := ⟨z.proj, (e z.proj).symm z.snd⟩
      left_inv z := congrArg (TotalSpace.mk z.proj) ((e z.proj).symm_apply_apply z.snd)
      right_inv z := congrArg (TotalSpace.mk z.proj) ((e z.proj).apply_symm_apply z.snd)
      contMDiff_toFun := hc
      contMDiff_invFun := hci }
  obtain ⟨d, hd⟩ := exists_diffeomorph_openRange j hj hinj
  have hT : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) 𝓘(ℝ, F) ∞ (T.totalMap f hf) :=
    contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  have hTopen : IsOpenEmbedding (T.totalMap f hf) :=
    T.target.isOpen.isOpenEmbedding_subtypeVal.comp T.diffeomorph.toHomeomorph.isOpenEmbedding
  let τ (z : NBg) : P := j (T.totalMap f hf (c.symm z))
  have hτ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) 𝓘(ℝ, G) ∞ τ :=
    j.contMDiff.comp (hT.comp c.symm.contMDiff)
  let U : TopologicalSpace.Opens P := ⟨j '' T.target, hj.isOpenMap _ T.target.isOpen⟩
  have hτmem (z : NBg) : τ z ∈ U :=
    ⟨T.totalMap f hf (c.symm z), (T.diffeomorph (c.symm z)).property, rfl⟩
  let yj (y : U) : hj.image := ⟨y.val, by
    obtain ⟨x, _, hx⟩ := y.property
    exact ⟨x, hx⟩⟩
  have hyj : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, G) ∞ yj :=
    (ContMDiff.subtypeVal_comp_iff hj.image yj).mp contMDiff_subtype_val
  let b (y : U) : N := d.symm (yj y)
  have hb : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ b := d.symm.contMDiff.comp hyj
  have hjb (y : U) : j (b y) = y.val := by
    rw [← hd]
    exact congrArg Subtype.val (d.apply_symm_apply (yj y))
  have hbmem (y : U) : b y ∈ T.target := by
    obtain ⟨x, hx, heq⟩ := y.property
    have hbx : b y = x := hinj ((hjb y).trans heq.symm)
    exact hbx ▸ hx
  let a (y : U) : T.target := ⟨b y, hbmem y⟩
  have ha : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff T.target a).mp hb
  let r (y : U) : NBg := c (T.diffeomorph.symm (a y))
  have hr : ContMDiff 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞ r :=
    c.contMDiff.comp (T.diffeomorph.symm.contMDiff.comp ha)
  have hright (y : U) : τ (r y) = y.val := by
    change j (T.totalMap f hf (c.symm (c (T.diffeomorph.symm (a y))))) = y.val
    rw [c.symm_apply_apply]
    change j ((T.diffeomorph (T.diffeomorph.symm (a y))).val) = y.val
    rw [T.diffeomorph.apply_symm_apply]
    exact hjb y
  have hτinj : Function.Injective τ := by
    intro z w heq
    exact c.symm.injective (hTopen.injective (hinj heq))
  let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) 𝓘(ℝ, G) NBg U ∞ :=
    { toFun z := ⟨τ z, hτmem z⟩
      invFun := r
      left_inv z := hτinj (hright ⟨τ z, hτmem z⟩)
      right_inv y := Subtype.ext (hright y)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp hτ
      contMDiff_invFun := hr }
  have hzero (x : M) : (D ⟨x, 0⟩ : P) = g x := by
    change j (T.totalMap f hf ⟨x, (e x).symm 0⟩) = g x
    rw [map_zero]
    exact (congrArg j (T.map_zero x)).trans (hcomm x)
  refine ⟨{ target := U, diffeomorph := D, map_zero := hzero, normal_deriv := ?_ },
    fun _ ↦ rfl⟩
  -- The original chart derivative conjugates the normal derivative by exactly e.
  intro x
  dsimp only
  let cf := (trivializationAt Vf νf x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt Vf νf x)
  let cg := (trivializationAt Vg νg x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt Vg νg x)
  let A : Vg →L[ℝ] Vf := cf.toContinuousLinearMap.comp
    ((e x).symm.toContinuousLinearMap.comp cg.symm.toContinuousLinearMap)
  let γ (u : Vf) : N := T.totalMap f hf ⟨x, cf.symm u⟩
  let δ (u : Vg) : P := τ ⟨x, cg.symm u⟩
  have hγ : ContMDiff 𝓘(ℝ, Vf) 𝓘(ℝ, F) ∞ γ := by
    apply hT.comp
    intro u
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have hc (v : Vf) : (trivializationAt Vf νf x ⟨x, cf.symm v⟩).2 = v := by
      have hh := cf.apply_symm_apply v
      rw [Trivialization.continuousLinearEquivAt_apply] at hh
      exact hh
    simpa only [hc] using!
      (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, Vf) 𝓘(ℝ, Vf) ∞ id u)
  have hcurve : (j : N → P) ∘ γ ∘ A = δ := by
    funext u
    change j (T.totalMap f hf ⟨x, cf.symm (cf ((e x).symm (cg.symm u)))⟩) = _
    rw [cf.symm_apply_apply]
    rfl
  have hγzero : γ (A 0) = f x := by
    change T.totalMap f hf ⟨x, cf.symm (A 0)⟩ = f x
    rw [map_zero, map_zero]
    exact T.map_zero x
  have hAder : mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, Vf) A 0 = A := by
    rw [mfderiv_eq_fderiv]
    exact A.fderiv
  have hγA := mfderiv_comp (I := 𝓘(ℝ, Vg)) (I' := 𝓘(ℝ, Vf)) (I'' := 𝓘(ℝ, F)) 0
    (show MDifferentiableAt 𝓘(ℝ, Vf) 𝓘(ℝ, F) γ (A 0) from by
      simpa only [map_zero] using hγ.mdifferentiable (by simp) 0)
    ((A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
  have hδ := mfderiv_comp (I := 𝓘(ℝ, Vg)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, G)) 0
    (j.contMDiff.mdifferentiable (by simp) (γ (A 0)))
    ((hγ.comp (A.contDiff (n := ∞)).contMDiff).mdifferentiable (by simp) 0)
  rw [hcurve, hγA, hAder] at hδ
  have hbase : (γ ∘ A) 0 = f x := hγzero
  rw [hbase, map_zero] at hδ
  intro u
  change (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) g x).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, G) δ 0 u) = cg.symm u
  have hd := congrArg (fun C : Vg →L[ℝ] G ↦ C u) hδ
  change mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, G) δ 0 u =
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) j (f x) (mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) γ 0 (A u)) at hd
  rw [hd, ← he]
  have hn := T.normal_deriv x (A u)
  change (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) γ 0 (A u)) = cf.symm (A u) at hn
  rw [hn]
  change e x (cf.symm (cf ((e x).symm (cg.symm u)))) = cg.symm u
  rw [cf.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

end Ambient

end AtiyahSinger
