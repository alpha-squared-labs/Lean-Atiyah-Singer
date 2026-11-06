/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedTangentEmbedding
public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# Tubular neighborhoods preserving a real parameter

Public module ID: M1342.

For second-countable Hausdorff finite-dimensional real manifolds, a proper
embedding of parameter cylinders that retains the parameter admits a
normalized tubular neighborhood retaining it as well. Correct the actual
normal quotient splitting by its time tangent component, apply local addition
only in the ambient manifold, then shrink and compress within each normal
fiber. All quotient normal fibers and their selected smooth atlases are unchanged.

This is the parameter tubular construction needed for SG III.13 isotopy
invariance. Properness is required for the whole cylinder, whose source may
be noncompact. No properness of the resulting open tubular map is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

section FullProduct

variable (E F M N : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

/-- The original product charts, with the full product model type tag explicit. -/
@[reducible]
def productFullChartedSpace : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))

attribute [local instance] productFullChartedSpace

/-- The native product manifold under the equal full real model. -/
theorem product_full_isManifold [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] :
    IsManifold 𝓘(ℝ, E × F) ∞ (M × N) := by
  simpa only [modelWithCornersSelf_prod] using
    (inferInstance : IsManifold (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ (M × N))

end FullProduct

attribute [local instance] productFullChartedSpace product_full_isManifold normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]

set_option backward.isDefEq.respectTransparency false in
/-- A proper parameter-preserving embedding has a parameter-preserving normalized tube. -/
theorem exists_parameterTubularNeighborhood
    (f : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
    (hf : IsImmersion 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ f)
    (he : IsEmbedding f) (hp : IsProperMap f)
    (htime : ∀ p, (f p).1 = p.1) :
    ∃ T : TubularNeighborhood f hf,
      ∀ z : TotalSpace (NormalModel (ℝ × E) (ℝ × F))
          (NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) f),
        (T.totalMap f hf z).1 = z.proj.1 := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let G := NormalModel (ℝ × E) (ℝ × F)
  let V := NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) f
  let NB := TotalSpace G V
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
    let := hEmpty
    obtain ⟨T⟩ := nonempty_tubularNeighborhood f hf he hp
    exact ⟨T, fun z ↦ isEmptyElim z.proj.2⟩
  | inr hNonempty =>
    let := hNonempty
    let : LocallyCompactSpace (ℝ × M) := ChartedSpace.locallyCompactSpace (ℝ × E) (ℝ × M)
    let : ParacompactSpace (ℝ × M) := inferInstance
    -- The derivative of the retained time coordinate is exactly the first projection.
    let B (p : ℝ × M) : (ℝ × E) →L[ℝ] (ℝ × F) :=
      mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) f p
    have hBtime (p : ℝ × M) (v : ℝ × E) : (B p v).1 = v.1 := by
      have hfst : ContMDiff 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) ∞ (@Prod.fst ℝ N) := by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
            (@Prod.fst ℝ N))
      have hcomp := mfderiv_comp p (hfst.mdifferentiable (by simp) (f p))
        (f.contMDiff.mdifferentiable (by simp) p)
      have heq : (@Prod.fst ℝ N) ∘ f = @Prod.fst ℝ M := funext htime
      rw [heq] at hcomp
      have hdM : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (@Prod.fst ℝ M) p =
          ContinuousLinearMap.fst ℝ ℝ E := by
        simpa only [modelWithCornersSelf_prod] using!
          (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (x := p))
      have hdN : mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (@Prod.fst ℝ N) (f p) =
          ContinuousLinearMap.fst ℝ ℝ F := by
        simpa only [modelWithCornersSelf_prod] using!
          (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) (x := f p))
      rw [hdM, hdN] at hcomp
      have h := congrArg (fun L : (ℝ × E) →L[ℝ] ℝ ↦ L v) hcomp
      exact h.symm
    obtain ⟨s₀, hs, hright⟩ := exists_smooth_normal_rightInverse f hf
    let s (p : ℝ × M) : V p →L[ℝ] (ℝ × F) := s₀ p
    let r (p : ℝ × M) : V p →L[ℝ] (ℝ × F) :=
      s p - (B p).comp ((ContinuousLinearMap.inl ℝ ℝ E).comp
        ((ContinuousLinearMap.fst ℝ ℝ F).comp (s p)))
    have hrtime (p : ℝ × M) (v : V p) : (r p v).1 = 0 := by
      change (s p v).1 - (B p ((s p v).1, 0)).1 = 0
      rw [hBtime, sub_self]
    have hrright (p : ℝ × M) : Function.RightInverse (r p)
        (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) f p).toLinearMap).mkQ := by
      intro v
      change (LinearMap.range (B p).toLinearMap).mkQ
        (s p v - B p ((s p v).1, 0)) = v
      have hsright : (LinearMap.range (B p).toLinearMap).mkQ (s p v) = v := hright p v
      rw [map_sub, hsright]
      have hzero : (LinearMap.range (B p).toLinearMap).mkQ
          (B p ((s p v).1, 0)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨((s p v).1, 0), rfl⟩
      rw [hzero, sub_zero]
    -- Realize the given quotient splitting in the actual ambient tangent bundle.
    let S : NB → TangentBundle 𝓘(ℝ, ℝ × F) (ℝ × N) :=
      fun z ↦ ⟨f z.proj, s z.proj z.snd⟩
    have hS : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) (𝓘(ℝ, ℝ × F)).tangent ∞ S := by
      have hLift : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, ℝ × F))
          (𝓘(ℝ, ℝ × F)).tangent ∞
          (fun z : TotalSpace (ℝ × F) ((f : ℝ × M → ℝ × N) *ᵖ
              (TangentSpace 𝓘(ℝ, ℝ × F))) ↦
            (⟨f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, ℝ × F) (ℝ × N))) := by
        intro z
        apply Bundle.contMDiffAt_totalSpace.mpr
        constructor
        · exact f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj _)
        · exact (Bundle.contMDiffAt_totalSpace.mp
            (show ContMDiffAt (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, ℝ × F))
              (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, ℝ × F)) ∞ id z from contMDiffAt_id)).2
      exact hLift.comp hs
    have hsplit : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
        ((𝓘(ℝ, ℝ)).tangent.prod (𝓘(ℝ, F)).tangent) ∞
        (fun z : NB ↦
          ((⟨(f z.proj).1, (s z.proj z.snd).1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ),
            (⟨(f z.proj).2, (s z.proj z.snd).2⟩ : TangentBundle 𝓘(ℝ, F) N))) := by
      have hS' : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)).tangent ∞
          (fun z : NB ↦ (⟨f z.proj, s z.proj z.snd⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × N))) := by
        simpa only [modelWithCornersSelf_prod] using! hS
      exact contMDiff_equivTangentBundleProd.comp hS'
    let a (z : NB) : ℝ := (s z.proj z.snd).1
    have ha : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ) ∞ a :=
      (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hsplit.fst
    let J : NB → TangentBundle 𝓘(ℝ, ℝ × E) (ℝ × M) :=
      fun z ↦ ⟨z.proj, (a z, 0)⟩
    have hJ : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
        (𝓘(ℝ, ℝ × E)).tangent ∞ J := by
      have hproj : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ × E) ∞
          (fun z : NB ↦ z.proj) := contMDiff_proj V
      have hprojp : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun z : NB ↦ z.proj) := by
        simpa only [modelWithCornersSelf_prod] using hproj
      have ht : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) (𝓘(ℝ, ℝ)).tangent ∞
          (fun z : NB ↦ (⟨z.proj.1, a z⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
        intro z
        apply Bundle.contMDiffAt_totalSpace.mpr
        refine ⟨hprojp.fst z, ?_⟩
        simpa using ha z
      have hz : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E)).tangent ∞
          (fun z : NB ↦ (⟨z.proj.2, 0⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
        (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E))).comp hprojp.snd
      have h : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)).tangent ∞
          (fun z : NB ↦ (⟨z.proj, (a z, 0)⟩ :
            TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (ℝ × M))) :=
        contMDiff_equivTangentBundleProd_symm.comp (ht.prodMk hz)
      simpa only [modelWithCornersSelf_prod] using! h
    have hf₂ : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) ∞ (fun p ↦ (f p).2) := by
      have h : ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞ f := by
        simpa only [modelWithCornersSelf_prod] using f.contMDiff
      exact h.snd
    let C : NB → TangentBundle 𝓘(ℝ, F) N :=
      fun z ↦ ⟨(f z.proj).2, (B z.proj (a z, 0)).2⟩
    have hC : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F)).tangent ∞ C := by
      have h := (hf₂.contMDiff_tangentMap (m := ∞) (by simp)).comp hJ
      convert h using 1
      funext z
      simp only [Function.comp_def, C, J, tangentMap]
      have hfst : ContMDiff 𝓘(ℝ, ℝ × F) 𝓘(ℝ, F) ∞ (@Prod.snd ℝ N) := by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiff_snd : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
            (@Prod.snd ℝ N))
      have hcomp := mfderiv_comp z.proj (hfst.mdifferentiable (by simp) (f z.proj))
        (f.contMDiff.mdifferentiable (by simp) z.proj)
      have hdN : mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, F) (@Prod.snd ℝ N) (f z.proj) =
          ContinuousLinearMap.snd ℝ ℝ F := by
        simpa only [modelWithCornersSelf_prod] using!
          (mfderiv_snd (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) (x := f z.proj))
      rw [hdN] at hcomp
      have hd := congrArg (fun L : (ℝ × E) →L[ℝ] F ↦ L (a z, 0)) hcomp
      have hd' : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) (fun p ↦ (f p).2) z.proj (a z, 0) =
          (B z.proj (a z, 0)).2 := by
        exact hd
      rw [hd']
    let R : NB → TangentBundle 𝓘(ℝ, F) N :=
      fun z ↦ ⟨(f z.proj).2, (r z.proj z.snd).2⟩
    have hR : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) (𝓘(ℝ, F)).tangent ∞ R := by
      intro z
      have h₁ := Bundle.contMDiffAt_totalSpace.mp (hsplit.snd z)
      have h₂ := Bundle.contMDiffAt_totalSpace.mp (hC z)
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨h₁.1, ?_⟩
      apply (h₁.2.sub h₂.2).congr_of_eventuallyEq
      let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) (f z.proj).2
      have hnear : ∀ᶠ w in 𝓝 z, (f w.proj).2 ∈ t.baseSet :=
        h₁.1.continuousAt (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
      filter_upwards [hnear] with w hw
      change (t ⟨(f w.proj).2, (s w.proj w.snd).2 - (B w.proj (a w, 0)).2⟩).2 =
        (t ⟨(f w.proj).2, (s w.proj w.snd).2⟩).2 -
          (t ⟨(f w.proj).2, (B w.proj (a w, 0)).2⟩).2
      simpa only [t.coe_linearMapAt_of_mem (R := ℝ) hw] using
        (t.linearMapAt ℝ (f w.proj).2).map_sub
          ((s w.proj w.snd).2) ((B w.proj (a w, 0)).2)
    obtain ⟨Φ, hΦsource, _, hΦzero, hΦderiv⟩ := exists_smooth_localAddition (E := F) (M := N)
    let Ω : Set NB := R ⁻¹' Φ.source
    let g : NB → ℝ × N := fun z ↦ (z.proj.1, (Φ (R z)).2)
    have hΩ : IsOpen Ω := Φ.open_source.preimage hR.continuous
    have hmem (p : ℝ × M) : (⟨p, 0⟩ : NB) ∈ Ω := by
      change (⟨(f p).2, (r p 0).2⟩ : TangentBundle 𝓘(ℝ, F) N) ∈ Φ.source
      rw [(r p).map_zero]
      exact hΦsource (f p).2
    have hzero (p : ℝ × M) : g ⟨p, 0⟩ = f p := by
      apply Prod.ext (htime p).symm
      change (Φ (⟨(f p).2, (r p 0).2⟩ : TangentBundle 𝓘(ℝ, F) N)).2 = (f p).2
      rw [(r p).map_zero]
      exact congrArg Prod.snd (hΦzero (f p).2)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ × F) ∞ g Ω := by
      have hproj : ContMDiff (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G))
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun z : NB ↦ z.proj) := by
        simpa only [modelWithCornersSelf_prod] using (contMDiff_proj V (n := ∞))
      have hsecond : ContMDiffOn (𝓘(ℝ, ℝ × E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞
          (fun z ↦ (Φ (R z)).2) Ω := by
        intro z hz
        exact ((Φ.contMDiffOn.comp hR.contMDiffOn (fun _ h ↦ h)) z hz).snd
      have h := hproj.fst.contMDiffOn.prodMk hsecond
      simpa only [modelWithCornersSelf_prod] using h
    have hder : ∀ p : ℝ × M,
        let e := (trivializationAt G V p).continuousLinearEquivAt ℝ p
          (mem_baseSet_trivializationAt G V p)
        HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ × F)
          (fun w ↦ g ⟨p, e.symm w⟩) 0 ((r p).comp e.symm.toContinuousLinearMap) := by
      intro p
      dsimp only
      let e := (trivializationAt G V p).continuousLinearEquivAt ℝ p
        (mem_baseSet_trivializationAt G V p)
      let L : G →L[ℝ] (ℝ × F) := (r p).comp e.symm.toContinuousLinearMap
      let L₂ : G →L[ℝ] F := (ContinuousLinearMap.snd ℝ ℝ F).comp L
      have hΦL : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, F)
          (fun v : F ↦ (Φ ⟨(f p).2, v⟩).2) (L₂ 0) (ContinuousLinearMap.id ℝ F) := by
        rw [L₂.map_zero]
        exact hΦderiv (f p).2
      have hsecond := hΦL.comp 0 L₂.hasMFDerivAt
      have h := (hasMFDerivAt_const (I := 𝓘(ℝ, G)) (I' := 𝓘(ℝ, ℝ))
        (x := (0 : G)) p.1).prodMk hsecond
      have hL : (0 : G →L[ℝ] ℝ).prod
          ((ContinuousLinearMap.id ℝ F).comp L₂) = L := by
        apply ContinuousLinearMap.ext
        intro v
        exact Prod.ext (hrtime p (e.symm v)).symm rfl
      rw [hL] at h
      simpa only [modelWithCornersSelf_prod, Function.comp_def] using! h
    -- Shrinking retains g itself; compression changes only the normal fiber coordinate.
    obtain ⟨Ψ, _, hΨg, hΨzero, hΨmap, hΨnormal⟩ :=
      exists_normalTubeGerm_of_normalizedMap f hf he hp Ω g r hΩ hmem hg hzero hrright hder
    obtain ⟨T, hT⟩ := exists_tubularNeighborhood_of_normalTubeGerm f hf Ψ
      hΨzero hΨmap hΨnormal
    refine ⟨T, fun z ↦ ?_⟩
    obtain ⟨w, _, hwbase, hw⟩ := hT z
    rw [hw, hΨg]
    exact congrArg Prod.fst hwbase

end AtiyahSinger
