/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedNormalBundle

/-!
# Restricting a parameter-preserving tube to a time slice

Public module ID: M1343.

A normalized tube retaining time restricts to a normalized tube of the original
slice immersion. The slice uses the prescribed normal quotient comparison
`[v] ↦ [(0,v)]`, so its total map is exactly the corresponding slice of the
original tube. This retains the endpoint witnesses needed by isotopy invariance.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped ContDiff

attribute [local instance] productFullChartedSpace product_full_isManifold normalBundleTopology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same parameter-preserving normalized tube restricts to the original slice normal. -/
theorem exists_tubularNeighborhood_parameterSlice
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ g)
    (htime : ∀ p, (g p).1 = p.1)
    (t : ℝ) (hslice : ∀ x, g (t, x) = (t, f x))
    (e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
      NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x))
    (he : ∀ (x : M) (v : F),
      e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
        (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x)).toLinearMap).mkQ
          (0, v))
    (T : TubularNeighborhood g hg)
    (hTtime : ∀ z, (T.totalMap g hg z).1 = z.proj.1) :
    ∃ S : TubularNeighborhood f hf,
      ∀ z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f),
        S.totalMap f hf z = (T.totalMap g hg ⟨(t, z.proj), e z.proj z.snd⟩).2 := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := normalBundleFiberBundle g hg
  let := normalBundleVectorBundle g hg
  let := normalBundleContMDiffVectorBundle g hg
  let Vf := NormalModel E F
  let Vg := NormalModel (ℝ × E) (ℝ × F)
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g
  let NBf := TotalSpace Vf νf
  let NBg := TotalSpace Vg νg
  -- The representative formula uniquely specifies the canonical smooth normal comparison.
  obtain ⟨e₀, he₀, hes, heis⟩ := exists_parameterSlice_normalEquiv f g hf hg htime t hslice
  have heq : e = e₀ := by
    funext x
    apply ContinuousLinearEquiv.ext
    funext v
    obtain ⟨w, rfl⟩ :=
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ_surjective v
    exact (he x w).trans (he₀ x w).symm
  subst e₀
  let inc := smoothParameterSlice E M t
  let L (z : NBf) : NBg := ⟨(t, z.proj), e z.proj z.snd⟩
  have hL : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
      (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, Vg)) ∞ L := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨inc.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj νf),
      (Bundle.contMDiffAt_totalSpace.mp (hes z)).2⟩
  have hT : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, Vg)) 𝓘(ℝ, ℝ × F) ∞
      (T.totalMap g hg) := contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  let τ (z : NBf) : N := (T.totalMap g hg (L z)).2
  have hτ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) 𝓘(ℝ, F) ∞ τ := by
    have h : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, Vf))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ (T.totalMap g hg ∘ L) := by
      simpa only [modelWithCornersSelf_prod] using hT.comp hL
    exact h.snd
  have hτtime (z : NBf) : T.totalMap g hg (L z) = (t, τ z) :=
    Prod.ext (hTtime (L z)) rfl
  let U : TopologicalSpace.Opens N :=
    ⟨{y | (t, y) ∈ T.target}, T.target.isOpen.preimage
      (continuous_const.prodMk continuous_id)⟩
  have hτmem (z : NBf) : τ z ∈ U := by
    change (t, τ z) ∈ T.target
    rw [← hτtime]
    exact (T.diffeomorph (L z)).property
  let a (y : U) : T.target := ⟨(t, y.val), y.property⟩
  have ha : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) ∞ a := by
    apply (ContMDiff.subtypeVal_comp_iff T.target a).mp
    have h : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
        (fun y : U ↦ (t, y.val)) :=
      contMDiff_const.prodMk (contMDiff_subtype_val (I := 𝓘(ℝ, F)) (U := U))
    simpa only [modelWithCornersSelf_prod] using! h
  let w (y : U) : NBg := T.diffeomorph.symm (a y)
  have hw : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, Vg)) ∞ w :=
    T.diffeomorph.symm.contMDiff.comp ha
  have hwtime (y : U) : (w y).proj.1 = t := by
    rw [← hTtime (w y)]
    change (T.diffeomorph (T.diffeomorph.symm (a y))).val.1 = t
    rw [T.diffeomorph.apply_symm_apply]
  let v (y : U) : νg (t, (w y).proj.2) :=
    (congrArg νg (show (w y).proj = (t, (w y).proj.2) from
      Prod.ext (hwtime y) rfl)).mp (w y).snd
  have hv (y : U) : (⟨(t, (w y).proj.2), v y⟩ : NBg) = w y := by
    exact TotalSpace.ext (Prod.ext (hwtime y).symm rfl) (by simp [v])
  let R (y : U) : TotalSpace Vg ((inc : M → ℝ × M) *ᵖ νg) :=
    ⟨(w y).proj.2, v y⟩
  have hR : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, Vg)) ∞ R := by
    have hbase : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (fun y : U ↦ (w y).proj.2) := by
      have h : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
          (fun y : U ↦ (w y).proj) := by
        simpa only [modelWithCornersSelf_prod] using! (contMDiff_proj νg).comp hw
      exact h.snd
    have hlift : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, Vg)) ∞
        (fun y : U ↦ (⟨(t, (w y).proj.2), v y⟩ : NBg)) := hw.congr hv
    intro y
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨hbase y, (Bundle.contMDiffAt_totalSpace.mp (hlift y)).2⟩
  let ι (y : U) : NBf := ⟨(w y).proj.2, (e (w y).proj.2).symm (v y)⟩
  have hι : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) ∞ ι := heis.comp hR
  have hLι (y : U) : L (ι y) = w y := by
    change (⟨(t, (w y).proj.2), e (w y).proj.2 ((e (w y).proj.2).symm (v y))⟩ : NBg) = w y
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hv y
  have hright (y : U) : τ (ι y) = y.val := by
    change (T.totalMap g hg (L (ι y))).2 = y.val
    rw [hLι]
    change (T.diffeomorph (T.diffeomorph.symm (a y))).val.2 = y.val
    rw [T.diffeomorph.apply_symm_apply]
  have hLinj : Function.Injective L := by
    rintro ⟨x, v⟩ ⟨y, u⟩ h
    have hxy : x = y := congrArg (fun z : NBg ↦ z.proj.2) h
    subst y
    apply congrArg (TotalSpace.mk x)
    apply (e x).injective
    exact eq_of_heq (TotalSpace.mk.inj h).2
  have hleft (z : NBf) : ι ⟨τ z, hτmem z⟩ = z := by
    apply hLinj
    rw [hLι]
    apply T.diffeomorph.injective
    change T.diffeomorph (T.diffeomorph.symm (a ⟨τ z, hτmem z⟩)) = T.diffeomorph (L z)
    rw [T.diffeomorph.apply_symm_apply]
    apply Subtype.ext
    exact (hτtime z).symm
  let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, Vf)) 𝓘(ℝ, F) NBf U ∞ := {
    toFun z := ⟨τ z, hτmem z⟩
    invFun := ι
    left_inv := hleft
    right_inv y := Subtype.ext (hright y)
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp hτ
    contMDiff_invFun := hι }
  have hzero (x : M) : (D ⟨x, 0⟩ : N) = f x := by
    change (T.totalMap g hg ⟨(t, x), e x 0⟩).2 = f x
    rw [(e x).map_zero]
    change (T.diffeomorph ⟨(t, x), 0⟩).val.2 = f x
    rw [T.map_zero, hslice]
  refine ⟨{ target := U, diffeomorph := D, map_zero := hzero, normal_deriv := ?_ },
    fun _ ↦ rfl⟩
  intro x
  dsimp only
  let cf := (trivializationAt Vf νf x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt Vf νf x)
  let cg := (trivializationAt Vg νg (t, x)).continuousLinearEquivAt ℝ (t, x)
    (mem_baseSet_trivializationAt Vg νg (t, x))
  let A : Vf →L[ℝ] Vg := cg.toContinuousLinearMap.comp
    ((e x).toContinuousLinearMap.comp cf.symm.toContinuousLinearMap)
  let γ (u : Vg) : ℝ × N := T.totalMap g hg ⟨(t, x), cg.symm u⟩
  let δ (u : Vf) : N := τ ⟨x, cf.symm u⟩
  have hγ : ContMDiff 𝓘(ℝ, Vg) 𝓘(ℝ, ℝ × F) ∞ γ := by
    apply hT.comp
    intro u
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have hc (v : Vg) :
        (trivializationAt Vg νg (t, x) ⟨(t, x), cg.symm v⟩).2 = v := by
      have hh := cg.apply_symm_apply v
      rw [Trivialization.continuousLinearEquivAt_apply] at hh
      exact hh
    simpa only [hc] using!
      (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, Vg) 𝓘(ℝ, Vg) ∞ id u)
  have hδ : ContMDiff 𝓘(ℝ, Vf) 𝓘(ℝ, F) ∞ δ := by
    apply hτ.comp
    intro u
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have hc (v : Vf) : (trivializationAt Vf νf x ⟨x, cf.symm v⟩).2 = v := by
      have hh := cf.apply_symm_apply v
      rw [Trivialization.continuousLinearEquivAt_apply] at hh
      exact hh
    simpa only [hc] using!
      (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, Vf) 𝓘(ℝ, Vf) ∞ id u)
  have hcurve : γ ∘ A = fun u : Vf ↦ (t, δ u) := by
    funext u
    change T.totalMap g hg ⟨(t, x), cg.symm (cg (e x (cf.symm u)))⟩ = (t, δ u)
    rw [cg.symm_apply_apply]
    exact hτtime ⟨x, cf.symm u⟩
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, Vf)) (I' := 𝓘(ℝ, Vg))
    (I'' := 𝓘(ℝ, ℝ × F)) 0
    (show MDifferentiableAt 𝓘(ℝ, Vg) 𝓘(ℝ, ℝ × F) γ (A 0) from by
      simpa only [map_zero] using hγ.mdifferentiable (by simp) 0)
    ((A.contDiff (n := ∞)).contMDiff.mdifferentiable (by simp) 0)
  have hAder : mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, Vg) A 0 = A := by
    rw [mfderiv_eq_fderiv]
    exact A.fderiv
  have hcurveDer : mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, ℝ × F) (fun u : Vf ↦ (t, δ u)) 0 =
      (ContinuousLinearMap.inr ℝ ℝ F).comp (mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) δ 0) := by
    have h := mfderiv_prodMk (I := 𝓘(ℝ, Vf)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, F))
      (f := fun _ : Vf ↦ t) (g := δ) (x := 0)
      mdifferentiableAt_const (hδ.mdifferentiable (by simp) 0)
    rw [mfderiv_const] at h
    simpa only [modelWithCornersSelf_prod] using! h
  rw [hcurve, hcurveDer, hAder, map_zero] at hcomp
  intro u
  change (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) δ 0 u) = cf.symm u
  apply (e x).injective
  rw [he]
  have hd := congrArg (fun C : Vf →L[ℝ] (ℝ × F) ↦ C u) hcomp
  change (0, mfderiv 𝓘(ℝ, Vf) 𝓘(ℝ, F) δ 0 u) =
    mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, ℝ × F) γ 0 (A u) at hd
  rw [hd]
  have hn := T.normal_deriv (t, x) (A u)
  change (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x)).toLinearMap).mkQ
    (mfderiv 𝓘(ℝ, Vg) 𝓘(ℝ, ℝ × F) γ 0 (A u)) = cg.symm (A u) at hn
  exact hn.trans (cg.symm_apply_apply (e x (cf.symm u)))

end AtiyahSinger
