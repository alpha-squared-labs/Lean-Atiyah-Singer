/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalBundle
public import Mathlib.Topology.Homotopy.Basic

/-!
# Affine comparison of smooth tangent-normal splittings

Public module ID: M1493.

Two splittings of the same canonical tangent-normal exact sequence have inverse
maps that differ by a vertical shear. Their affine interpolation is therefore
a bundle isomorphism at every time, with a jointly continuous inverse. This
gives an open embedding of the whole parameter cylinder, with the two original
inverse total homeomorphisms as endpoints.

The source is the ordered product of two native pullbacks of the original real
normal bundle. Both splittings use the same canonical projection and vertical
inclusion; the result is not convex interpolation of arbitrary isomorphisms.
No paracompactness or separation assumption is needed for comparison of two
already supplied splittings. Such assumptions enter their existence theorem.

Source: the standard affine-space argument for splittings of an exact sequence,
used here as an explicit project supplement to SG III.12, printed p.241, and
HU III.9.6. Those passages do not separately state this whole-total open-cylinder
formulation. The proof uses the same two supplied splittings throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.TangentNormalSplitting

open Bundle Manifold Topology
open scoped ContDiff unitInterval

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νT" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "V" => NormalModel E F
local notation "VT" => NormalModel (E × E) (F × F)
local notation "πM" => smoothTangentBundleProjection E M
local notation "νP" => ((πM : TangentBundle 𝓘(ℝ, E) M → M) *ᵖ ν)

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse splittings admit their affine homotopy with an open total cylinder. -/
theorem exists_inverseAffineHomotopy (S₀ S₁ : TangentNormalSplitting f hf) :
    ∃ H : ContinuousMap.Homotopy
        (⟨(S₀.totalHomeomorph f hf).symm, (S₀.totalHomeomorph f hf).symm.continuous⟩ :
          C(TotalSpace (V × V) (νP ×ᵇ νP), TotalSpace VT νT))
        (⟨(S₁.totalHomeomorph f hf).symm, (S₁.totalHomeomorph f hf).symm.continuous⟩ :
          C(TotalSpace (V × V) (νP ×ᵇ νP), TotalSpace VT νT)),
      IsOpenEmbedding (fun p : I × TotalSpace (V × V) (νP ×ᵇ νP) ↦ (p.1, H p)) ∧
        ∀ (t : I) (z : TotalSpace (V × V) (νP ×ᵇ νP)),
          H (t, z) = (⟨z.proj,
            (1 - (t : ℝ)) • (S₀.equiv z.proj).symm z.snd +
              (t : ℝ) • (S₁.equiv z.proj).symm z.snd⟩ : TotalSpace VT νT) := by
  classical
  -- Stage 1: work in the original quotient atlases and native pullback-product topology.
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  have continuous_fiberwise_combination {B X F₀ : Type _} [TopologicalSpace B] [TopologicalSpace X]
      [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
      {V₀ : B → Type _} [∀ b, AddCommGroup (V₀ b)] [∀ b, Module ℝ (V₀ b)]
      [∀ b, TopologicalSpace (V₀ b)] [TopologicalSpace (TotalSpace F₀ V₀)]
      [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
      (b : X → B) (u v : ∀ x, V₀ (b x)) (a c : X → ℝ)
      (hu : Continuous (fun x ↦ (⟨b x, u x⟩ : TotalSpace F₀ V₀)))
      (hv : Continuous (fun x ↦ (⟨b x, v x⟩ : TotalSpace F₀ V₀)))
      (ha : Continuous a) (hc : Continuous c) :
      Continuous (fun x ↦ (⟨b x, a x • u x + c x • v x⟩ : TotalSpace F₀ V₀)) := by
    have hb : Continuous b := (FiberBundle.continuous_proj F₀ V₀).comp hu
    rw [continuous_iff_continuousAt]
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt F₀ V₀ (b x)
    have hu' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hu.continuousAt).2
    have hv' := ((FiberBundle.continuousAt_totalSpace F₀ _ (x₀ := x)).mp hv.continuousAt).2
    have hn : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
      hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F₀ V₀ (b x)))
    apply ((ha.continuousAt.smul hu').add (hc.continuousAt.smul hv')).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    change (e ⟨b y, a y • u y + c y • v y⟩).2 =
      a y • (e ⟨b y, u y⟩).2 + c y • (e ⟨b y, v y⟩).2
    simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]
  -- Stage 2: the shared projection and vertical inclusion make the difference a shear.
  let L (z : TangentBundle 𝓘(ℝ, E) M) : (ν z.proj × ν z.proj) →ₗ[ℝ]
      (ν z.proj × ν z.proj) :=
    (S₀.equiv z).toLinearMap.comp (S₁.equiv z).symm.toLinearMap
  have hLfirst (z : TangentBundle 𝓘(ℝ, E) M) (v : ν z.proj × ν z.proj) :
      (L z v).1 = v.1 := by
    change (S₀.equiv z ((S₁.equiv z).symm v)).1 = v.1
    rw [S₀.fst_equiv, ← S₁.fst_equiv]
    simp
  have hLvertical (z : TangentBundle 𝓘(ℝ, E) M) (v : ν z.proj) :
      L z (0, v) = (0, v) := by
    have hsame : (S₁.equiv z).symm (0, v) = tangentNormalVerticalMap f hf z v := by
      apply (S₁.equiv z).injective
      simpa using (S₁.equiv_vertical z v).symm
    change S₀.equiv z ((S₁.equiv z).symm (0, v)) = (0, v)
    rw [hsame, S₀.equiv_vertical]
  have hLsquare (z : TangentBundle 𝓘(ℝ, E) M) (v : ν z.proj × ν z.proj) :
      L z (L z v) = 2 • L z v - v := by
    have hdiff : L z (L z v - v) = L z v - v := by
      have hvertical : L z v - v = (0, (L z v).2 - v.2) := by
        apply Prod.ext
        · simp [hLfirst]
        · rfl
      rw [hvertical, hLvertical]
    calc
      L z (L z v) = (L z v - v) + L z v :=
        sub_eq_iff_eq_add.mp (by simpa only [map_sub] using hdiff)
      _ = 2 • L z v - v := by module
  have hcoordinates (z : TangentBundle 𝓘(ℝ, E) M) (t : ℝ)
      (v : ν z.proj × ν z.proj) :
      S₀.equiv z ((1 - t) • (S₀.equiv z).symm v + t • (S₁.equiv z).symm v) =
        (1 - t) • v + t • L z v := by
    simp [L]
  -- Stage 3: the inverse is the opposite shear, with the parameter kept explicit.
  let A : I × TotalSpace (V × V) (νP ×ᵇ νP) → TotalSpace VT νT := fun p ↦
    ⟨p.2.proj, (1 - (p.1 : ℝ)) • (S₀.equiv p.2.proj).symm p.2.snd +
      (p.1 : ℝ) • (S₁.equiv p.2.proj).symm p.2.snd⟩
  let B : I × TotalSpace VT νT → TotalSpace (V × V) (νP ×ᵇ νP) := fun p ↦
    ⟨p.2.proj, (1 + (p.1 : ℝ)) • S₀.equiv p.2.proj p.2.snd +
      (-(p.1 : ℝ)) • L p.2.proj (S₀.equiv p.2.proj p.2.snd)⟩
  have hBA (t : I) (z : TotalSpace (V × V) (νP ×ᵇ νP)) : B (t, A (t, z)) = z := by
    rcases z with ⟨z, v⟩
    apply congrArg (fun w : ν z.proj × ν z.proj ↦
      (⟨z, w⟩ : TotalSpace (V × V) (νP ×ᵇ νP)))
    change (1 + (t : ℝ)) • S₀.equiv z _ + (-(t : ℝ)) • L z (S₀.equiv z _) = v
    rw [hcoordinates]
    simp only [map_add, map_smul, hLsquare]
    module
  have hAB (t : I) (z : TotalSpace VT νT) : A (t, B (t, z)) = z := by
    rcases z with ⟨z, w⟩
    apply congrArg (fun v : νT z ↦ (⟨z, v⟩ : TotalSpace VT νT))
    apply (S₀.equiv z).injective
    change S₀.equiv z ((1 - (t : ℝ)) • (S₀.equiv z).symm _ +
      (t : ℝ) • (S₁.equiv z).symm _) = S₀.equiv z w
    rw [hcoordinates]
    change (1 - (t : ℝ)) • ((1 + (t : ℝ)) • S₀.equiv z w +
      (-(t : ℝ)) • L z (S₀.equiv z w)) +
      (t : ℝ) • L z ((1 + (t : ℝ)) • S₀.equiv z w +
        (-(t : ℝ)) • L z (S₀.equiv z w)) = S₀.equiv z w
    simp only [map_add, map_smul, hLsquare]
    module
  -- Stage 4: local linear bundle charts give joint continuity, including the inverse.
  have hA : Continuous A := by
    apply continuous_fiberwise_combination
      (fun p : I × TotalSpace (V × V) (νP ×ᵇ νP) ↦ p.2.proj)
    · exact (S₀.totalHomeomorph f hf).symm.continuous.comp continuous_snd
    · exact (S₁.totalHomeomorph f hf).symm.continuous.comp continuous_snd
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    · exact continuous_subtype_val.comp continuous_fst
  have hB : Continuous B := by
    let (z : TangentBundle 𝓘(ℝ, E) M) : AddCommGroup ((νP ×ᵇ νP) z) := by
      change AddCommGroup (ν z.proj × ν z.proj)
      infer_instance
    let (z : TangentBundle 𝓘(ℝ, E) M) : Module ℝ ((νP ×ᵇ νP) z) := by
      change Module ℝ (ν z.proj × ν z.proj)
      infer_instance
    let (z : TangentBundle 𝓘(ℝ, E) M) : TopologicalSpace ((νP ×ᵇ νP) z) := by
      change TopologicalSpace (ν z.proj × ν z.proj)
      infer_instance
    apply continuous_fiberwise_combination (F₀ := V × V) (V₀ := νP ×ᵇ νP)
      (fun p : I × TotalSpace VT νT ↦ p.2.proj)
    · exact (S₀.totalHomeomorph f hf).continuous.comp continuous_snd
    · exact (S₀.totalHomeomorph f hf).continuous.comp
        ((S₁.totalHomeomorph f hf).symm.continuous.comp
          ((S₀.totalHomeomorph f hf).continuous.comp continuous_snd))
    · exact continuous_const.add (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_subtype_val.comp continuous_fst).neg
  -- Stage 5: a homeomorphism of whole cylinders supplies openness and the exact endpoints.
  let cylinder : (I × TotalSpace (V × V) (νP ×ᵇ νP)) ≃ₜ (I × TotalSpace VT νT) :=
    { toFun := fun p ↦ (p.1, A p)
      invFun := fun p ↦ (p.1, B p)
      left_inv := fun p ↦ Prod.ext rfl (hBA p.1 p.2)
      right_inv := fun p ↦ Prod.ext rfl (hAB p.1 p.2)
      continuous_toFun := continuous_fst.prodMk hA
      continuous_invFun := continuous_fst.prodMk hB }
  let H : ContinuousMap.Homotopy
      (⟨(S₀.totalHomeomorph f hf).symm, (S₀.totalHomeomorph f hf).symm.continuous⟩ :
        C(TotalSpace (V × V) (νP ×ᵇ νP), TotalSpace VT νT))
      (⟨(S₁.totalHomeomorph f hf).symm, (S₁.totalHomeomorph f hf).symm.continuous⟩ :
        C(TotalSpace (V × V) (νP ×ᵇ νP), TotalSpace VT νT)) :=
    { toFun := A
      continuous_toFun := hA
      map_zero_left := fun z ↦ by
        change (⟨z.proj, (1 - (0 : ℝ)) • (S₀.equiv z.proj).symm z.snd +
          (0 : ℝ) • (S₁.equiv z.proj).symm z.snd⟩ : TotalSpace VT νT) = _
        simp only [sub_zero, one_smul, zero_smul, add_zero]
        rfl
      map_one_left := fun z ↦ by
        change (⟨z.proj, (1 - (1 : ℝ)) • (S₀.equiv z.proj).symm z.snd +
          (1 : ℝ) • (S₁.equiv z.proj).symm z.snd⟩ : TotalSpace VT νT) = _
        simp only [sub_self, zero_smul, one_smul, zero_add]
        rfl }
  exact ⟨H, cylinder.isOpenEmbedding, fun _ _ ↦ rfl⟩

end AtiyahSinger.TangentNormalSplitting
