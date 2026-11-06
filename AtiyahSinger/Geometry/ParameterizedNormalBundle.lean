/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedTubularNeighborhood
public import AtiyahSinger.Geometry.TransverseNormalPullback

/-!
# Normal bundles of parameter slices

Public module ID: M1339.

The normal quotient of a parameter-preserving immersion restricts to the
original normal quotient of every immersed slice. The comparison sends the
class of an ambient vector `v` to the class of `(0,v)`. Its inverse removes
the time-direction shear of the cylinder derivative. Both maps are smooth
for the original quotient atlases and the native pullback topology.

This is the transverse-slice comparison used in the isotopy construction of
SG III.13, with the actual quotient representative and its sign made explicit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] productFullChartedSpace product_full_isManifold normalBundleTopology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- The original inclusion of a time slice, bundled for the native pullback atlas. -/
def smoothParameterSlice (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (t : ℝ) :
    ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) M (ℝ × M) ∞ :=
  ⟨fun x ↦ (t, x), by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_const.prodMk contMDiff_id : ContMDiff 𝓘(ℝ, E)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞ (fun x : M ↦ (t, x)))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual quotient normal of a time-preserving immersion restricts to its slice normal. -/
theorem exists_parameterSlice_normalEquiv
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsImmersion 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ g)
    (htime : ∀ p, (g p).1 = p.1)
    (t : ℝ) (hslice : ∀ x, g (t, x) = (t, f x)) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    letI := normalBundleFiberBundle g hg
    letI := normalBundleVectorBundle g hg
    letI := normalBundleContMDiffVectorBundle g hg
    ∃ e : ∀ x, NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f x ≃L[ℝ]
        NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x),
      (∀ (x : M) (v : F),
        e x ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ v) =
          (LinearMap.range (mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x)).toLinearMap).mkQ
            (0, v)) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel (ℝ × E) (ℝ × F))) ∞
        (fun z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) ↦
          (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (NormalModel (ℝ × E) (ℝ × F))
            ((smoothParameterSlice E M t : M → ℝ × M) *ᵖ
              (NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g)))) ∧
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel (ℝ × E) (ℝ × F)))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) ∞
        (fun z : TotalSpace (NormalModel (ℝ × E) (ℝ × F))
            ((smoothParameterSlice E M t : M → ℝ × M) *ᵖ
              (NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g)) ↦
          (⟨z.proj, (e z.proj).symm z.snd⟩ :
            TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))) := by
  classical
  let i := smoothParameterSlice E M t
  let j := smoothParameterSlice F N t
  let A (x : M) : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let B (x : M) : (ℝ × E) →L[ℝ] (ℝ × F) :=
    mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) g (t, x)
  have hi (x : M) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) i x =
      ContinuousLinearMap.inr ℝ ℝ E := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) (fun x : M ↦ (t, x)) x = _
    have h := mfderiv_prodMk (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, E))
      (f := fun _ : M ↦ t) (g := id) (x := x)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [mfderiv_const, mfderiv_id] at h
    simpa only [modelWithCornersSelf_prod] using! h
  have hj (y : N) : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) j y =
      ContinuousLinearMap.inr ℝ ℝ F := by
    change mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) (fun y : N ↦ (t, y)) y = _
    have h := mfderiv_prodMk (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, F))
      (f := fun _ : N ↦ t) (g := id) (x := y)
      mdifferentiableAt_const mdifferentiableAt_id
    rw [mfderiv_const, mfderiv_id] at h
    simpa only [modelWithCornersSelf_prod] using! h
  -- Differentiating the commuting slice square identifies its vertical derivative.
  have hBvertical (x : M) (v : E) : B x (0, v) = (0, A x v) := by
    have heq : (g : ℝ × M → ℝ × N) ∘ i = (j : N → ℝ × N) ∘ f := funext hslice
    have hleft := mfderiv_comp x (g.contMDiff.mdifferentiable (by simp) (i x))
      (i.contMDiff.mdifferentiable (by simp) x)
    have hright := mfderiv_comp x (j.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)
    rw [heq, hright, hi, hj] at hleft
    exact (congrArg (fun L : E →L[ℝ] (ℝ × F) ↦ L v) hleft).symm
  have hBtime (x : M) (v : ℝ × E) : (B x v).1 = v.1 := by
    have hfst : ContMDiff 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) ∞ (@Prod.fst ℝ N) := by
      simpa only [modelWithCornersSelf_prod] using
        (contMDiff_fst : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
          (@Prod.fst ℝ N))
    have hcomp := mfderiv_comp (t, x) (hfst.mdifferentiable (by simp) (g (t, x)))
      (g.contMDiff.mdifferentiable (by simp) (t, x))
    have heq : (@Prod.fst ℝ N) ∘ g = @Prod.fst ℝ M := funext htime
    rw [heq] at hcomp
    have hdM : mfderiv 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) (@Prod.fst ℝ M) (t, x) =
        ContinuousLinearMap.fst ℝ ℝ E := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (x := (t, x)))
    have hdN : mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ) (@Prod.fst ℝ N) (g (t, x)) =
        ContinuousLinearMap.fst ℝ ℝ F := by
      simpa only [modelWithCornersSelf_prod] using!
        (mfderiv_fst (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F)) (x := g (t, x)))
    rw [hdM, hdN] at hcomp
    exact (congrArg (fun L : (ℝ × E) →L[ℝ] ℝ ↦ L v) hcomp).symm
  -- Time retention proves both transversality conditions in the actual tangent spaces.
  have hpreimage (x : M) (v : F) :
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ × F) j (f x) v ∈ LinearMap.range (B x).toLinearMap ↔
        v ∈ LinearMap.range (A x).toLinearMap := by
    rw [hj]
    constructor
    · rintro ⟨u, hu⟩
      change B x u = (0, v) at hu
      have ht : u.1 = 0 := by
        rw [← hBtime x u]
        exact congrArg Prod.fst hu
      refine ⟨u.2, ?_⟩
      have hbu := hBvertical x u.2
      have hu' : u = (0, u.2) := Prod.ext ht rfl
      rw [hu', hbu] at hu
      exact congrArg Prod.snd hu
    · rintro ⟨u, rfl⟩
      exact ⟨(0, u), hBvertical x u⟩
  have hspan (x : M) (w : ℝ × F) : ∃ (v : F) (u : ℝ × E),
      w = (ContinuousLinearMap.inr ℝ ℝ F) v + B x u := by
    refine ⟨w.2 - (B x (w.1, 0)).2, (w.1, 0), ?_⟩
    apply Prod.ext
    · change w.1 = 0 + (B x (w.1, 0)).1
      rw [zero_add, hBtime]
    · change w.2 = (w.2 - (B x (w.1, 0)).2) + (B x (w.1, 0)).2
      exact (sub_add_cancel _ _).symm
  obtain ⟨e, he, hs, his⟩ := exists_transverse_normalPullback_equiv f g i j hf hg
    (fun x ↦ (hslice x).symm) hpreimage (by
      intro x
      dsimp only
      intro w
      simpa only [hj] using! hspan x w)
  refine ⟨e, ?_, hs, his⟩
  intro x v
  have h := he x v
  rw [hj] at h
  exact h

end AtiyahSinger
