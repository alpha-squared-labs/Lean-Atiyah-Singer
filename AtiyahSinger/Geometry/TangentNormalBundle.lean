/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Geometry.TangentEmbedding

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The normal exact sequence of a tangent embedding

Public module ID: M1490.

The normal bundle of the original tangent map has a canonical exact sequence
whose kernel and quotient are the pulled-back original normal bundle. Its
vertical inclusion and projection are fixed by the actual vertical derivative
and derivative of the tangent-bundle projection. A smooth splitting identifies
this normal bundle with the ordered double of that pullback; the first component
is the quotient and the second the vertical part. Such a splitting is a choice,
not a canonical coordinate equality.

The product-model adapters retain mathlib's original tangent bundle charts.
The chart adapter is enabled locally; the manifold certificate is a named
instance for that adapter and the equal full model. No fiber norms, connection
or substitute normal carrier are installed.
Sources: SG III.12, printed p.241, and the quotient and splitting constructions
in HU III.8.2, III.9.6 and XVIII.2.6. The smooth exact-sequence and partition-of-unity
arguments are explicit supplements to those source summaries. The original
tangent topology, normal exact sequence and normalized smooth splitting are proved
below. The splitting uses smooth weights on the source pulled back to its tangent bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold
open scoped ContDiff

section FullModel

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original tangent charts, with their product model type tag made explicit. -/
@[reducible]
def tangentBundleFullChartedSpace : ChartedSpace (E × E) (TangentBundle 𝓘(ℝ, E) M) :=
  inferInstanceAs (ChartedSpace (ModelProd E E) (TangentBundle 𝓘(ℝ, E) M))

attribute [local instance] tangentBundleFullChartedSpace

/-- The original tangent manifold under the equal full real product model. -/
instance tangentBundle_full_isManifold :
    IsManifold 𝓘(ℝ, E × E) ∞ (TangentBundle 𝓘(ℝ, E) M) := by
  simpa only [modelWithCornersSelf_prod] using
    (inferInstance : IsManifold (𝓘(ℝ, E)).tangent ∞ (TangentBundle 𝓘(ℝ, E) M))

attribute [local instance] tangentBundle_full_isManifold

/-- Standard separation and countability properties of the original finite-rank tangent bundle. -/
theorem tangentBundle_topology [FiniteDimensional ℝ E] [T2Space M]
    [SecondCountableTopology M] :
    T2Space (TangentBundle 𝓘(ℝ, E) M) ∧
      SecondCountableTopology (TangentBundle 𝓘(ℝ, E) M) ∧
      ParacompactSpace (TangentBundle 𝓘(ℝ, E) M) := by
  classical
  let TM := TangentBundle 𝓘(ℝ, E) M
  let e := fun x : M ↦ trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x
  have hproj : Continuous (fun z : TM ↦ z.proj) := FiberBundle.continuous_proj _ _
  -- Separate distinct base points by projection, or vectors in one common bundle chart.
  have hT2 : T2Space TM := by
    apply t2Space_iff_disjoint_nhds.mpr
    intro z w hzw
    by_cases hbase : z.proj = w.proj
    · have hz : z ∈ (e z.proj).source := (e z.proj).mem_source.mpr
        (mem_baseSet_trivializationAt _ _ _)
      have hw : w ∈ (e z.proj).source := (e z.proj).mem_source.mpr
        (hbase ▸ mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
      exact ((e z.proj).continuousAt hz).disjoint
        (disjoint_nhds_nhds.mpr (fun he ↦ hzw ((e z.proj).injOn hz hw he)))
        ((e z.proj).continuousAt hw)
    · exact hproj.continuousAt.disjoint (disjoint_nhds_nhds.mpr hbase) hproj.continuousAt
  let := hT2
  -- A countable family of base trivializations yields a countable open cover upstairs.
  obtain ⟨s, hsc, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M ↦ (e x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  let := hsc.toEncodable
  have hpatch (x : s) : SecondCountableTopology ((e x).source) :=
    (e x).toOpenPartialHomeomorph.secondCountableTopology_source
  have hcover' : ⋃ x : s, (e x).source = (Set.univ : Set TM) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hz : z.proj ∈ ⋃ x ∈ s, (e x).baseSet := hcover ▸ Set.mem_univ _
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨⟨x, hx⟩, (e x).mem_source.mpr hzx⟩
  have hsecond : SecondCountableTopology TM :=
    TopologicalSpace.secondCountableTopology_of_countable_cover
      (fun x : s ↦ (e x).open_source) hcover'
  let := hsecond
  -- Local compactness is inherited from the original finite-dimensional tangent charts.
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  exact ⟨hT2, hsecond, inferInstance⟩

/-- The original tangent-bundle projection as a smooth map in the full product model. -/
def smoothTangentBundleProjection :
    ContMDiffMap 𝓘(ℝ, E × E) 𝓘(ℝ, E) (TangentBundle 𝓘(ℝ, E) M) M ∞ :=
  ⟨Bundle.TotalSpace.proj, by
    simpa only [modelWithCornersSelf_prod] using
      (Bundle.contMDiff_proj (𝕜 := ℝ) (n := ∞) (TangentSpace 𝓘(ℝ, E) : M → Type _))⟩

/-- Canonical vertical lift, defined by differentiating the actual affine fiber inclusion. -/
def tangentVerticalLift (z : TangentBundle 𝓘(ℝ, E) M) :
    TangentSpace 𝓘(ℝ, E) z.proj →L[ℝ] TangentSpace 𝓘(ℝ, E × E) z :=
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj).continuousLinearEquivAt
    ℝ z.proj (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
  -- The affine map sends zero to z; chart coordinates only parameterize its derivative.
  ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E)
      (fun a : E ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, E) M)) 0).comp
    (NormedSpace.fromTangentSpace (0 : E)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap

end FullModel

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)

/-- The actual tangent map, packaged with smoothness in the full product models. -/
def smoothTangentMap :
    ContMDiffMap 𝓘(ℝ, E × E) 𝓘(ℝ, F × F)
      (TangentBundle 𝓘(ℝ, E) M) (TangentBundle 𝓘(ℝ, F) N) ∞ :=
  ⟨tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f, by
    simpa only [modelWithCornersSelf_prod] using
      f.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.defProp false in
/-- The existing tangent-embedding theorem, adapted to the same full product models. -/
def isImmersion_smoothTangentMap (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) ∞ (smoothTangentMap f) := by
  change IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) ∞ (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) f)
  simpa only [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] using
    (isSmoothEmbedding_tangentMap hf).isImmersion

variable (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
local notation "νT" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "V" => NormalModel E F
local notation "VT" => NormalModel (E × E) (F × F)
local notation "πM" => smoothTangentBundleProjection E M
local notation "νP" => ((πM : TangentBundle 𝓘(ℝ, E) M → M) *ᵖ ν)

open Function Set Topology in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in

/-- The canonical smooth normal exact sequence of the original tangent embedding. -/
theorem exists_tangentNormal_exactSequence :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ∃ i : ∀ z : TangentBundle 𝓘(ℝ, E) M, ν z.proj →L[ℝ] νT z,
      ∃ p : ∀ z : TangentBundle 𝓘(ℝ, E) M, νT z →L[ℝ] ν z.proj,
        ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V))
            (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
            (fun z : TotalSpace V νP ↦ (⟨z.proj, i z.proj z.snd⟩ : TotalSpace VT νT)) ∧
          ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT))
            (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
            (fun z : TotalSpace VT νT ↦ (⟨z.proj, p z.proj z.snd⟩ : TotalSpace V νP)) ∧
          (∀ (z : TangentBundle 𝓘(ℝ, E) M) (w : TangentSpace 𝓘(ℝ, F) (f z.proj)),
            i z ((LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ w) =
              (LinearMap.range
                (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ
                  (tangentVerticalLift F N (smoothTangentMap f z) w)) ∧
          (∀ (z : TangentBundle 𝓘(ℝ, E) M)
              (w : TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f z)),
            p z ((LinearMap.range
                (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ w) =
              (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ
                (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
                  (smoothTangentBundleProjection F N) (smoothTangentMap f z) w)) ∧
          ∀ z, Function.Injective (i z) ∧ Function.Surjective (p z) ∧
            LinearMap.range (i z).toLinearMap = LinearMap.ker (p z).toLinearMap := by
  classical
  -- Stage 1: descend the commuting vertical tangent sequences to their actual quotients.
  have quotient_exact
      {E F X Y : Type _}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
      (a : E →L[ℝ] F) (d : X →L[ℝ] Y)
      (vE : E →L[ℝ] X) (pE : X →L[ℝ] E)
      (vF : F →L[ℝ] Y) (pF : Y →L[ℝ] F)
      (ha : Injective a) (hvF : Injective vF)
      (hpE : Surjective pE) (hpF : Surjective pF)
      (heE : LinearMap.range vE.toLinearMap = LinearMap.ker pE.toLinearMap)
      (heF : LinearMap.range vF.toLinearMap = LinearMap.ker pF.toLinearMap)
      (hvertical : d.comp vE = vF.comp a)
      (hprojection : pF.comp d = a.comp pE) :
      ∃ i : (F ⧸ LinearMap.range a.toLinearMap) →L[ℝ]
          (Y ⧸ LinearMap.range d.toLinearMap),
        ∃ p : (Y ⧸ LinearMap.range d.toLinearMap) →L[ℝ]
            (F ⧸ LinearMap.range a.toLinearMap),
          (∀ w, i ((LinearMap.range a.toLinearMap).mkQ w) =
            (LinearMap.range d.toLinearMap).mkQ (vF w)) ∧
          (∀ w, p ((LinearMap.range d.toLinearMap).mkQ w) =
            (LinearMap.range a.toLinearMap).mkQ (pF w)) ∧
          Injective i ∧ Surjective p ∧
            LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap := by
    let qA := (LinearMap.range a.toLinearMap).mkQL
    let qD := (LinearMap.range d.toLinearMap).mkQL
    have hvert (e : E) : d (vE e) = vF (a e) :=
      DFunLike.congr_fun hvertical e
    have hproj (x : X) : pF (d x) = a (pE x) :=
      DFunLike.congr_fun hprojection x
    have hvEzero (e : E) : pE (vE e) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← heE]
      exact ⟨e, rfl⟩
    have hvFzero (f : F) : pF (vF f) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← heF]
      exact ⟨f, rfl⟩
    have hiwell : LinearMap.range a.toLinearMap ≤ (qD.comp vF).ker := by
      rintro _ ⟨e, rfl⟩
      change qD (vF (a e)) = 0
      rw [← hvert]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨vE e, rfl⟩
    have hpwell : LinearMap.range d.toLinearMap ≤ (qA.comp pF).ker := by
      rintro _ ⟨x, rfl⟩
      change qA (pF (d x)) = 0
      rw [hproj]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨pE x, rfl⟩
    let i := (LinearMap.range a.toLinearMap).liftQL (qD.comp vF) hiwell
    let p := (LinearMap.range d.toLinearMap).liftQL (qA.comp pF) hpwell
    have hi (f : F) : i (qA f) = qD (vF f) := rfl
    have hp (y : Y) : p (qD y) = qA (pF y) := rfl
    refine ⟨i, p, hi, hp, ?_, ?_, ?_⟩
    · apply (LinearMap.ker_eq_bot).mp
      apply le_antisymm ?_ bot_le
      intro u hu
      obtain ⟨f, rfl⟩ := (LinearMap.range a.toLinearMap).mkQ_surjective u
      have hzero : qD (vF f) = 0 := LinearMap.mem_ker.mp hu
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
      change d x = vF f at hx
      have hxzero : pE x = 0 := ha (by
        calc
          a (pE x) = pF (d x) := (hproj x).symm
          _ = pF (vF f) := congrArg pF hx
          _ = 0 := hvFzero f
          _ = a 0 := (map_zero a).symm)
      have hxrange : x ∈ LinearMap.range vE.toLinearMap := by
        rw [heE]
        exact hxzero
      obtain ⟨e, he⟩ := hxrange
      change vE e = x at he
      have hf : a e = f := hvF (by rw [← hvert, he]; exact hx)
      change qA f = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨e, hf⟩
    · intro u
      obtain ⟨f, rfl⟩ := (LinearMap.range a.toLinearMap).mkQ_surjective u
      obtain ⟨y, hy⟩ := hpF f
      exact ⟨qD y, by rw [hp, hy]; rfl⟩
    · apply le_antisymm
      · rintro _ ⟨u, rfl⟩
        obtain ⟨f, rfl⟩ := (LinearMap.range a.toLinearMap).mkQ_surjective u
        change p (i (qA f)) = 0
        rw [hi, hp, hvFzero, map_zero]
      · intro u hu
        obtain ⟨y, rfl⟩ := (LinearMap.range d.toLinearMap).mkQ_surjective u
        have hzero : qA (pF y) = 0 := LinearMap.mem_ker.mp hu
        obtain ⟨e, he⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
        change a e = pF y at he
        obtain ⟨x, hx⟩ := hpE e
        have hv : y - d x ∈ LinearMap.range vF.toLinearMap := by
          rw [heF]
          change pF (y - d x) = 0
          rw [map_sub, hproj, hx, he, sub_self]
        obtain ⟨f, hf⟩ := hv
        change vF f = y - d x at hf
        refine ⟨qA f, ?_⟩
        change i (qA f) = qD y
        rw [hi, hf, map_sub]
        have hdx : qD (d x) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
        rw [hdx, sub_zero]
  -- Smooth quotient descent uses local right inverses in the same native bundle charts.
  have local_smooth_rightInverse
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)] (Q : ∀ x, W x
      →L[ℝ] V₀ x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x)) (x : M) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∃ s : ∀ y, V₀ y →L[ℝ] W y,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
            (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
          ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
    classical
    let a := trivializationAt F W x
    let b := trivializationAt G V₀ x
    let A (y : M) : F →L[ℝ] G :=
      (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
    let U := a.baseSet ∩ b.baseSet
    have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
    have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
      intro y hy
      have heval (v : F) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
          (fun z ↦ A z v) U y := by
        have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
            (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace F W)) y := by
          apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
          filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
          rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
          exact a.continuousLinearMapAt_symmL hz v
        have hq := hQ.contMDiffAt.comp y hs
        have hb := (b.contMDiffAt_iff (b.mem_source.mpr hy.2)).mp hq
        apply hb.2.contMDiffWithinAt.congr
        · intro z hz
          change (b.continuousLinearMapAt ℝ z) (Q z (a.symmL ℝ z v)) = _
          exact b.continuousLinearMapAt_apply_of_mem ℝ hz.2 _
        · exact b.continuousLinearMapAt_apply_of_mem ℝ hy.2 _
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have hv := heval v
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
      exact hv
    -- Choose one right inverse at the center; nearby invertible corrections vary smoothly.
    have hsurj : Function.Surjective (A x) := by
      intro v
      obtain ⟨w, hw⟩ := hsurjective x (b.symmL ℝ x v)
      refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
      change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
        (a.continuousLinearMapAt ℝ x w))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
      rw [hw, b.continuousLinearMapAt_symmL hx.2]
    obtain ⟨R₀, hR₀⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
    let R : G →L[ℝ] F := R₀.toContinuousLinearMap
    let C (y : M) : G →L[ℝ] G := (A y).comp R
    have hCx : C x = ContinuousLinearMap.id ℝ G := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : G →ₗ[ℝ] G ↦ L v) hR₀
    have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞ C U :=
      hA.clm_comp contMDiffOn_const
    have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
    have hinv : (C x).IsInvertible := by
      rw [hCx]
      exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
    have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
      Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
    obtain ⟨U', hsub, hU'o, hx'⟩ := mem_nhds_iff.mp hevent
    let P (y : M) : G →L[ℝ] F := R.comp (C y).inverse
    have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
      intro y hy
      have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
      have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
      exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
    -- Transport this corrected matrix back through the same two original trivializations.
    let s (y : M) : V₀ y →L[ℝ] W y :=
      (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
    let c := b.continuousLinearMap (RingHom.id ℝ) a
    have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U' := by
      apply (c.contMDiffOn_section_iff hU'o (fun y hy ↦ (hsub hy).1.symm)).mpr
      apply hP.congr
      intro y hy
      ext v
      rw [show c = b.continuousLinearMap (RingHom.id ℝ) a from rfl,
        Trivialization.continuousLinearMap_apply]
      change (a.continuousLinearMapAt ℝ y)
        (a.symmL ℝ y (P y (b.continuousLinearMapAt ℝ y (b.symmL ℝ y v)))) = P y v
      rw [b.continuousLinearMapAt_symmL (hsub hy).1.2,
        a.continuousLinearMapAt_symmL (hsub hy).1.1]
    have hright (y : M) (hy : y ∈ U') (v : V₀ y) : Q y (s y v) = v := by
      have hinj : Function.Injective (b.continuousLinearMapAt ℝ y) := by
        intro u v huv
        have heq := congrArg (b.symmL ℝ y) huv
        exact (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 u).symm.trans
          (heq.trans (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 v))
      apply hinj
      change (A y) (R ((C y).inverse (b.continuousLinearMapAt ℝ y v))) =
        b.continuousLinearMapAt ℝ y v
      change (C y) ((C y).inverse (b.continuousLinearMapAt ℝ y v)) =
        b.continuousLinearMapAt ℝ y v
      obtain ⟨e, he⟩ := (hsub hy).2
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.apply_symm_apply _
    exact ⟨U', hU'o, hx', s, hs, hright⟩
  have smooth_descent
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)]
      {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]
      {Z : M → Type _} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
      [∀ x, TopologicalSpace (Z x)] [∀ x, IsTopologicalAddGroup (Z x)]
      [∀ x, ContinuousSMul ℝ (Z x)] [TopologicalSpace (TotalSpace H Z)]
      [FiberBundle H Z] [VectorBundle ℝ H Z] [ContMDiffVectorBundle ∞ H Z 𝓘(ℝ, E)]
      (Q : ∀ x, W x →L[ℝ] V₀ x) (D : ∀ x, V₀ x →L[ℝ] Z x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x))
      (hDQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, D z.proj (Q z.proj z.snd)⟩ : TotalSpace H Z))) :
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace G V₀ ↦ (⟨z.proj, D z.proj z.snd⟩ : TotalSpace H Z)) := by
    intro z
    obtain ⟨U, hU, hz, s, hs, hright⟩ := local_smooth_rightInverse Q hQ hsurjective z.proj
    have hsAt := (hs z.proj hz).contMDiffAt (hU.mem_nhds hz)
    have htotal : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun w : TotalSpace G V₀ ↦ (⟨w.proj, s w.proj w.snd⟩ : TotalSpace F W)) z := by
      exact (hsAt.comp z (Bundle.contMDiffAt_proj V₀)).clm_bundle_apply contMDiffAt_id
    apply (hDQ.contMDiffAt.comp z htotal).congr_of_eventuallyEq
    filter_upwards [((FiberBundle.continuous_proj G V₀).continuousAt).preimage_mem_nhds
      (hU.mem_nhds hz)] with w hw
    change (⟨w.proj, D w.proj w.snd⟩ : TotalSpace H Z) =
      ⟨w.proj, D w.proj (Q w.proj (s w.proj w.snd))⟩
    rw [hright w.proj hw]
  have smooth_pullback_map
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)]
      {D : Type _} [NormedAddCommGroup D] [NormedSpace ℝ D]
      {N : Type _} [TopologicalSpace N] [ChartedSpace D N]
      [IsManifold 𝓘(ℝ, D) ∞ N]
      (f : ContMDiffMap 𝓘(ℝ, D) 𝓘(ℝ, E) N M ∞)
      (Q : ∀ x, W x →L[ℝ] V₀ x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀))) :
      ContMDiff (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, D).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F ((f : N → M) *ᵖ W) ↦
          (⟨z.proj, Q (f z.proj) z.snd⟩ : TotalSpace G ((f : N → M) *ᵖ V₀))) := by
    have hLift : ContMDiff (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace F ((f : N → M) *ᵖ W) ↦
          (⟨f z.proj, z.snd⟩ : TotalSpace F W)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      constructor
      · exact f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj ((f : N → M) *ᵖ W))
      · exact (Bundle.contMDiffAt_totalSpace.mp
          (show ContMDiffAt (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, D).prod 𝓘(ℝ, F)) ∞
            id z from contMDiffAt_id)).2
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact Bundle.contMDiffAt_proj ((f : N → M) *ᵖ W)
    · exact (Bundle.contMDiffAt_totalSpace.mp ((hQ.comp hLift).contMDiffAt)).2
  -- Stage 2: compute the actual affine-fiber derivative and projection in native charts.
  have native_trivM (x : M) (w : TangentSpace 𝓘(ℝ, E) x) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) x) w = w := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source E x),
      mfderiv_extChartAt_self]
    rfl
  have native_chartM (z : TangentBundle 𝓘(ℝ, E) M) (w : E) :
      chartAt (E × E) z (⟨z.proj, w⟩ : TangentBundle 𝓘(ℝ, E) M) =
        (chartAt E z.proj z.proj, w) := by
    apply Prod.ext
    · rfl
    · change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, w⟩).2 = w
      exact native_trivM z.proj w
  have affine_smoothM (z : TangentBundle 𝓘(ℝ, E) M) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
    intro a
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_const
    · simp only [show ∀ b : E, (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from b)⟩).2 = (show E from z.snd)
            + b from fun b ↦ native_trivM _ _]
      change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a
      exact (contMDiffAt_const.add contMDiffAt_id :
          ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a)
  have affine_derivM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E)
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) 0 =
          ContinuousLinearMap.inr ℝ E E := by
    let g : E → TangentBundle 𝓘(ℝ, E) M := fun a ↦ ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E)
      z.proj from a)⟩
    have hg0 : g 0 = z := by simp [g]
    have hg := (affine_smoothM z 0).mdifferentiableAt (by simp)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) (g 0))
    have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
      (I'' := 𝓘(ℝ, E × E)) 0 hc hg
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    rw [← hd]
    have heq : (extChartAt 𝓘(ℝ, E × E) (g 0) ∘ g) =
        (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) := by
      funext a
      rw [hg0]
      exact native_chartM z _
    rw [heq, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) 0 = _
    convert! ((hasFDerivAt_const (chartAt E z.proj z.proj) (0 : E)).prodMk
      ((hasFDerivAt_const (show E from z.snd) (0 : E)).add (hasFDerivAt_id (0 : E)))).fderiv using 1
    · ext w <;> simp
    · infer_instance
    · infer_instance
  have vertical_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      tangentVerticalLift E M z = ContinuousLinearMap.inr ℝ E E := by
    let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
    have he (w : E) : e w = w := native_trivM z.proj w
    have hei (w : E) : e.symm w = w := by
      rw [← he (e.symm w), e.apply_symm_apply]
    have hg : (fun a : E ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, E) M)) =
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
      funext a
      rw [hei]
    change ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) _ 0).comp
      (NormedSpace.fromTangentSpace (0 : E)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap = _
    rw [hg, affine_derivM z]
    ext w
    change (0, e w) = (0, w)
    rw [he]
  have projection_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (smoothTangentBundleProjection E M) z =
        ContinuousLinearMap.fst ℝ E E := by
    let p := smoothTangentBundleProjection E M
    have hp := p.contMDiff.mdifferentiable (by simp) z
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
      (mem_chart_source E z.proj)
    have hd := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) z hc hp
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) =
        Prod.fst ∘ extChartAt 𝓘(ℝ, E × E) z := rfl
    change (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) z :
        (E × E) →L[ℝ] E) = (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
          (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M) z : (E × E) →L[ℝ] E) at hd
    have hf : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) Prod.fst
        (extChartAt 𝓘(ℝ, E × E) z z) := differentiableAt_fst.mdifferentiableAt
    rw [heq, mfderiv_comp z hf (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) z)), mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
    change fderiv ℝ (Prod.fst : E × E → E) _ = _ at hd
    rw [fderiv_fst] at hd
    exact hd.symm
  have native_trivN (x : N) (w : TangentSpace 𝓘(ℝ, F) x) :
      (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) x) w = w := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source F x),
      mfderiv_extChartAt_self]
    rfl
  have native_chartN (z : TangentBundle 𝓘(ℝ, F) N) (w : F) :
      chartAt (F × F) z (⟨z.proj, w⟩ : TangentBundle 𝓘(ℝ, F) N) =
        (chartAt F z.proj z.proj, w) := by
    apply Prod.ext
    · rfl
    · change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj
          ⟨z.proj, w⟩).2 = w
      exact native_trivN z.proj w
  have affine_smoothN (z : TangentBundle 𝓘(ℝ, F) N) :
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F) ∞
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) := by
    intro a
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_const
    · simp only [show ∀ b : F, (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj
          ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from b)⟩).2 = (show F from z.snd)
            + b from fun b ↦ native_trivN _ _]
      change ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun b : F ↦ (show F from z.snd) + b) a
      exact (contMDiffAt_const.add contMDiffAt_id :
          ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun b : F ↦ (show F from z.snd) + b) a)
  have affine_derivN (z : TangentBundle 𝓘(ℝ, F) N) :
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F)
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) 0 =
          ContinuousLinearMap.inr ℝ F F := by
    let g : F → TangentBundle 𝓘(ℝ, F) N := fun a ↦ ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F)
      z.proj from a)⟩
    have hg0 : g 0 = z := by simp [g]
    have hg := (affine_smoothN z 0).mdifferentiableAt (by simp)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F × F))
      (mem_chart_source (F × F) (g 0))
    have hd := mfderiv_comp (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F × F))
      (I'' := 𝓘(ℝ, F × F)) 0 hc hg
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    rw [← hd]
    have heq : (extChartAt 𝓘(ℝ, F × F) (g 0) ∘ g) =
        (fun a : F ↦ (chartAt F z.proj z.proj, (show F from z.snd) + a)) := by
      funext a
      rw [hg0]
      exact native_chartN z _
    rw [heq, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : F ↦ (chartAt F z.proj z.proj, (show F from z.snd) + a)) 0 = _
    convert! ((hasFDerivAt_const (chartAt F z.proj z.proj) (0 : F)).prodMk
      ((hasFDerivAt_const (show F from z.snd) (0 : F)).add (hasFDerivAt_id (0 : F)))).fderiv using 1
    · ext w <;> simp
    · infer_instance
    · infer_instance
  have vertical_formulaN (z : TangentBundle 𝓘(ℝ, F) N) :
      tangentVerticalLift F N z = ContinuousLinearMap.inr ℝ F F := by
    let e := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj)
    have he (w : F) : e w = w := native_trivN z.proj w
    have hei (w : F) : e.symm w = w := by
      rw [← he (e.symm w), e.apply_symm_apply]
    have hg : (fun a : F ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, F) N)) =
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) := by
      funext a
      rw [hei]
    change ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) _ 0).comp
      (NormedSpace.fromTangentSpace (0 : F)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap = _
    rw [hg, affine_derivN z]
    ext w
    change (0, e w) = (0, w)
    rw [he]
  have projection_formulaN (z : TangentBundle 𝓘(ℝ, F) N) :
      mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) z =
        ContinuousLinearMap.fst ℝ F F := by
    let p := smoothTangentBundleProjection F N
    have hp := p.contMDiff.mdifferentiable (by simp) z
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F))
      (mem_chart_source F z.proj)
    have hd := mfderiv_comp (I := 𝓘(ℝ, F × F)) (I' := 𝓘(ℝ, F))
      (I'' := 𝓘(ℝ, F)) z hc hp
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : (extChartAt 𝓘(ℝ, F) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N)) =
        Prod.fst ∘ extChartAt 𝓘(ℝ, F × F) z := rfl
    change (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
      (extChartAt 𝓘(ℝ, F) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N)) z :
        (F × F) →L[ℝ] F) = (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
          (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N) z : (F × F) →L[ℝ] F) at hd
    have hf : MDifferentiableAt 𝓘(ℝ, F × F) 𝓘(ℝ, F) Prod.fst
        (extChartAt 𝓘(ℝ, F × F) z z) := differentiableAt_fst.mdifferentiableAt
    rw [heq, mfderiv_comp z hf (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F × F))
      (mem_chart_source (F × F) z)), mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
    change fderiv ℝ (Prod.fst : F × F → F) _ = _ at hd
    rw [fderiv_fst] at hd
    exact hd.symm
  have hNat
      (z : TangentBundle 𝓘(ℝ, E) M) :
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).comp
          (tangentVerticalLift E M z) =
        (tangentVerticalLift F N (smoothTangentMap f z)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) := by
    let a : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
      ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from v)⟩
    let b : F → TangentBundle 𝓘(ℝ, F) N := fun v ↦
      ⟨f z.proj, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) z.snd +
        (show TangentSpace 𝓘(ℝ, F) (f z.proj) from v)⟩
    let L : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj
    have ha0 : a 0 = z := by simp [a]
    have hb0 : b 0 = smoothTangentMap f z := by simp [b, smoothTangentMap, tangentMap]
    have ha : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 :=
      (affine_smoothM z 0).mdifferentiableAt (by simp)
    have hb : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 :=
      (affine_smoothN (smoothTangentMap f z) 0).mdifferentiableAt (by simp)
    have heq : smoothTangentMap f ∘ a = b ∘ L := by
      funext v
      change (⟨f z.proj, L ((show E from z.snd) + v)⟩ : TangentBundle 𝓘(ℝ, F) N) =
        ⟨f z.proj, L z.snd + L v⟩
      exact congrArg (fun w ↦ (⟨f z.proj, w⟩ : TangentBundle 𝓘(ℝ, F) N))
        (map_add L (show E from z.snd) v)
    have hleft := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
      (I'' := 𝓘(ℝ, F × F)) 0
      (ha0 ▸ (smoothTangentMap f).contMDiff.mdifferentiable (by simp) z) ha
    have hright := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
      (I'' := 𝓘(ℝ, F × F)) 0
      (show MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F × F) b (L 0) from by simpa using hb)
      ((L.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
    have hLder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) L 0 = L := by
      rw [mfderiv_eq_fderiv]
      exact L.fderiv
    have hDa : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 = ContinuousLinearMap.inr ℝ E E :=
      affine_derivM z
    have hDb : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 = ContinuousLinearMap.inr ℝ F F :=
      affine_derivN (smoothTangentMap f z)
    rw [heq, hright, hDa, hLder] at hleft
    have hzder : mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) (a 0) =
        mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z := by
      congr 1
    rw [hzder] at hleft
    have hzero : L 0 = 0 := map_zero L
    have hbder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b (L 0) =
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 := by
      congr 1
    rw [hbder, hDb] at hleft
    rw [vertical_formulaM z, vertical_formulaN (smoothTangentMap f z)]
    exact hleft.symm
  have hVM := vertical_formulaM
  have hVN := vertical_formulaN
  have hPM := projection_formulaM
  have hPN := projection_formulaN
  -- Stage 3: differentiate the smooth affine family to obtain global vertical smoothness.
  have affine_family_smooth
      {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type _} [TopologicalSpace P] [ChartedSpace G P]
    [IsManifold 𝓘(ℝ, G) ∞ P]
      (b : P → TangentBundle 𝓘(ℝ, F) N)
      (w : ∀ x : P, TangentSpace 𝓘(ℝ, F) (b x).proj)
      (hb : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F) ∞ b)
      (hw : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F) ∞
        (fun x ↦ (⟨(b x).proj, w x⟩ : TangentBundle 𝓘(ℝ, F) N))) :
      ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F × F) ∞
        (fun x : P × ℝ ↦ (⟨(b x.1).proj, (b x.1).snd + x.2 • w x.1⟩ :
          TangentBundle 𝓘(ℝ, F) N)) := by
    intro x
    have h1 := (hb x.1).comp x (contMDiffAt_fst (I := 𝓘(ℝ, G)) (J := 𝓘(ℝ, ℝ)))
    have h2 := (hw x.1).comp x (contMDiffAt_fst (I := 𝓘(ℝ, G)) (J := 𝓘(ℝ, ℝ)))
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace] at h1 h2 ⊢
    refine ⟨h1.1, ?_⟩
    apply (h1.2.add (contMDiffAt_snd.smul h2.2)).congr_of_eventuallyEq
    let e := trivializationAt F (TangentSpace 𝓘(ℝ, F)) (b x.1).proj
    filter_upwards [h1.1.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with y hy
    change (b y.1).proj ∈ e.baseSet at hy
    change (e ⟨(b y.1).proj, (b y.1).snd + y.2 • w y.1⟩).2 =
      (e ⟨(b y.1).proj, (b y.1).snd⟩).2 + y.2 • (e ⟨(b y.1).proj, w y.1⟩).2
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hy,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hy,
      ← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]
  have vertical_smooth_of
      {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : Type _} [TopologicalSpace P] [ChartedSpace G P]
    [IsManifold 𝓘(ℝ, G) ∞ P]
      (b : P → TangentBundle 𝓘(ℝ, F) N)
      (w : ∀ x : P, TangentSpace 𝓘(ℝ, F) (b x).proj)
      (hb : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F) ∞ b)
      (hw : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F) ∞
        (fun x ↦ (⟨(b x).proj, w x⟩ : TangentBundle 𝓘(ℝ, F) N))) :
      ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F).tangent ∞
        (fun x ↦ (⟨b x, tangentVerticalLift F N (b x) (w x)⟩ :
          TangentBundle 𝓘(ℝ, F × F) (TangentBundle 𝓘(ℝ, F) N))) := by
    let family (x : P) (t : ℝ) : TangentBundle 𝓘(ℝ, F) N :=
      ⟨(b x).proj, (b x).snd + t • w x⟩
    have hfamily : ContMDiff (𝓘(ℝ, G).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F × F) ∞
        (Function.uncurry family) := affine_family_smooth b w hb hw
    have hzero (x : P) : family x 0 = b x := by simp [family]
    have hder (x : P) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F × F) (family x) 0
        (1 : ℝ) = tangentVerticalLift F N (b x) (w x) := by
      let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight (show F from w x)
      let a : F → TangentBundle 𝓘(ℝ, F) N := fun v ↦
        ⟨(b x).proj, (b x).snd + (show TangentSpace 𝓘(ℝ, F) (b x).proj from v)⟩
      have heq : family x = a ∘ L := rfl
      have hLder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) L 0 = L := by
        rw [mfderiv_eq_fderiv]
        exact L.fderiv
      have hAder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) a (L 0) =
          ContinuousLinearMap.inr ℝ F F := by
        have hz : L 0 = 0 := map_zero L
        have heq' : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) a (L 0) =
            mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) a 0 := by congr 1
        exact heq'.trans (affine_derivN (b x))
      have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, F))
        (I'' := 𝓘(ℝ, F × F)) 0
        ((affine_smoothN (b x) (L 0)).mdifferentiableAt (by simp))
        (((L.contDiff (n := ∞)).contMDiff).mdifferentiableAt (by simp))
      rw [hAder, hLder] at hd
      rw [heq, hd, vertical_formulaN]
      change (0, (1 : ℝ) • (show F from w x)) = (0, w x)
      rw [one_smul]
    have hbase : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, F × F) ∞ (fun x ↦ family x 0) :=
      hfamily.comp (contMDiff_id.prodMk contMDiff_const)
    intro x
    have hφ := (hfamily (x, 0)).mfderiv family (fun _ ↦ (0 : ℝ))
      (show ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ) ∞ (fun _ : P ↦ (0 : ℝ)) x from
        contMDiffAt_const) (m := ∞) (by simp)
    have hv : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, ℝ).tangent ∞
        (fun _ : P ↦ (⟨(0 : ℝ), (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) x :=
      contMDiffAt_const
    have heval : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, F × F).tangent ∞
        (fun y : P ↦ (⟨family y 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F × F) (family y) 0
          (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, F × F) (TangentBundle 𝓘(ℝ, F) N))) x :=
      ContMDiffAt.clm_apply_of_inCoordinates
        (IM := 𝓘(ℝ, G)) (IB₁ := 𝓘(ℝ, ℝ)) (IB₂ := 𝓘(ℝ, F × F))
        (F₁ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))
        (F₂ := F × F)
        (E₂ := TangentSpace 𝓘(ℝ, F × F) (M := TangentBundle 𝓘(ℝ, F) N))
        (b₁ := fun _ : P ↦ (0 : ℝ)) (b₂ := fun y : P ↦ family y 0)
        (ϕ := fun y : P ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F × F) (family y) 0)
        (v := fun _ : P ↦ (1 : ℝ)) hφ hv (hbase x)
    convert heval using 1
    funext y
    exact TotalSpace.ext (hzero y).symm (heq_of_eq (hder y).symm)
  have hVNsmooth :
      ContMDiff (𝓘(ℝ, F × F).prod 𝓘(ℝ, F)) 𝓘(ℝ, F × F).tangent ∞
        (fun z : TotalSpace F
            ((smoothTangentBundleProjection F N : TangentBundle 𝓘(ℝ, F) N → N) *ᵖ
              (TangentSpace 𝓘(ℝ, F) : N → Type _)) ↦
          (⟨z.proj, tangentVerticalLift F N z.proj z.snd⟩ :
            TangentBundle 𝓘(ℝ, F × F) (TangentBundle 𝓘(ℝ, F) N))) := by
    let πN₀ := smoothTangentBundleProjection F N
    let V₀ := ((πN₀ : TangentBundle 𝓘(ℝ, F) N → N) *ᵖ (TangentSpace 𝓘(ℝ, F) : N → Type _))
    let X := TotalSpace F V₀
    let : ChartedSpace ((F × F) × F) X :=
      inferInstanceAs (ChartedSpace (ModelProd (F × F) F) X)
    let : IsManifold 𝓘(ℝ, (F × F) × F) ∞ X := by
      simpa only [modelWithCornersSelf_prod] using
        (inferInstance : IsManifold (𝓘(ℝ, F × F).prod 𝓘(ℝ, F)) ∞ X)
    have hb : ContMDiff 𝓘(ℝ, (F × F) × F) 𝓘(ℝ, F × F) ∞
        (fun z : X ↦ z.proj) := by
      simpa only [modelWithCornersSelf_prod] using
        (Bundle.contMDiff_proj (𝕜 := ℝ) (n := ∞) V₀)
    have hw' : ContMDiff 𝓘(ℝ, (F × F) × F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) ∞
        (fun z : X ↦ (⟨πN₀ z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      refine ⟨πN₀.contMDiff.contMDiffAt.comp z (hb z), ?_⟩
      have hid : ContMDiffAt 𝓘(ℝ, (F × F) × F)
          (𝓘(ℝ, F × F).prod 𝓘(ℝ, F)) ∞ (id : X → X) z := by
        simpa only [modelWithCornersSelf_prod] using
          (contMDiffAt_id : ContMDiffAt 𝓘(ℝ, (F × F) × F)
            𝓘(ℝ, (F × F) × F) ∞ (id : X → X) z)
      exact (Bundle.contMDiffAt_totalSpace.mp hid).2
    have hw : ContMDiff 𝓘(ℝ, (F × F) × F) 𝓘(ℝ, F × F) ∞
        (fun z : X ↦ (⟨z.proj.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F) N)) := by
      convert! hw' using 1
      exact modelWithCornersSelf_prod
    simpa only [modelWithCornersSelf_prod] using
      (vertical_smooth_of (fun z : X ↦ z.proj) (fun z ↦ z.snd) hb hw)
  -- Stage 4: retain the selected normal atlases and construct both quotient maps jointly.
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let W := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  let WP := ((πM : TM → M) *ᵖ W)
  let WT := ((smoothTangentMap f : TM → TN) *ᵖ (TangentSpace 𝓘(ℝ, F × F)))
  let (x : M) : AddCommGroup (W x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : Module ℝ (W x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (W x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (W x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : TM) : AddCommGroup (WP x) := by
    change AddCommGroup (W x.proj)
    infer_instance
  let (x : TM) : Module ℝ (WP x) := by
    change Module ℝ (W x.proj)
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (WP x) := by
    change IsTopologicalAddGroup (W x.proj)
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (WP x) := by
    change ContinuousSMul ℝ (W x.proj)
    infer_instance
  let (x : TM) : AddCommGroup (WT x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : Module ℝ (WT x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (WT x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (WT x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : AddCommGroup (νP x) := by
    change AddCommGroup (ν x.proj)
    infer_instance
  let (x : TM) : Module ℝ (νP x) := by
    change Module ℝ (ν x.proj)
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (νP x) := by
    change IsTopologicalAddGroup (ν x.proj)
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (νP x) := by
    change ContinuousSMul ℝ (ν x.proj)
    infer_instance
  let q (x : M) := (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQL
  let qT (z : TM) :=
    (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQL
  let dπ (z : TN) :=
    mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) z
  have hproj (z : TM) :
      (dπ (smoothTangentMap f z)).comp
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).comp
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) πM z) := by
    have hleft := mfderiv_comp z
      ((smoothTangentBundleProjection F N).contMDiff.mdifferentiable (by simp) _)
      ((smoothTangentMap f).contMDiff.mdifferentiable (by simp) z)
    have hright := mfderiv_comp z (f.contMDiff.mdifferentiable (by simp) _)
      ((smoothTangentBundleProjection E M).contMDiff.mdifferentiable (by simp) z)
    exact hleft.symm.trans hright
  have hfib (z : TM) : ∃ i : ν z.proj →L[ℝ] νT z,
      ∃ p : νT z →L[ℝ] ν z.proj,
        (∀ w, i (q z.proj w) = qT z (tangentVerticalLift F N (smoothTangentMap f z) w)) ∧
        (∀ w, p (qT z w) = q z.proj (dπ (smoothTangentMap f z) w)) ∧
        Injective i ∧ Surjective p ∧
          LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap := by
    apply quotient_exact
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj)
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z)
      (tangentVerticalLift E M z) (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) πM z)
      (tangentVerticalLift F N (smoothTangentMap f z)) (dπ (smoothTangentMap f z))
    · exact hf.isImmersion.mfderiv_injective (by simp) z.proj
    · rw [hVN]
      intro u v h
      exact congrArg Prod.snd h
    · rw [hPM]
      exact fun v ↦ ⟨(v, 0), rfl⟩
    · change Surjective (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
        (smoothTangentBundleProjection F N) (smoothTangentMap f z))
      rw [hPN]
      exact fun v ↦ ⟨(v, 0), rfl⟩
    · rw [hVM, hPM]
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rfl
      · intro hw
        exact ⟨w.2, Prod.ext hw.symm rfl⟩
    · change LinearMap.range (tangentVerticalLift F N (smoothTangentMap f z)).toLinearMap =
        LinearMap.ker (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
          (smoothTangentBundleProjection F N) (smoothTangentMap f z)).toLinearMap
      rw [hVN, hPN]
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rfl
      · intro hw
        exact ⟨w.2, Prod.ext hw.symm rfl⟩
    · exact hNat z
    · exact hproj z
  choose i p hi hp hinj hsurj hexact using hfib
  have hq : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace F W ↦ (⟨z.proj, q z.proj z.snd⟩ : TotalSpace V ν)) :=
    (smoothNormalQuotientMap f hf.isImmersion).contMDiff
  have hqP : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace F WP ↦ (⟨z.proj, q z.proj.proj z.snd⟩ : TotalSpace V νP)) := by
    exact smooth_pullback_map (F := F) (G := V) (W := W) (V₀ := ν) πM q hq
  have hqT : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace (F × F) WT ↦ (⟨z.proj, qT z.proj z.snd⟩ : TotalSpace VT νT)) :=
    (smoothNormalQuotientMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)).contMDiff
  have hVLlift : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace F WP ↦
        (⟨smoothTangentMap f z.proj, z.snd⟩ : TotalSpace F
          ((smoothTangentBundleProjection F N : TN → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact (smoothTangentMap f).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj WP)
    · exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
          (𝓘(ℝ, E × E).prod 𝓘(ℝ, F)) ∞ id z from contMDiffAt_id)).2
  have hVpull : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F)) ∞
      (fun z : TotalSpace F WP ↦
        (⟨z.proj, tangentVerticalLift F N (smoothTangentMap f z.proj) z.snd⟩ :
          TotalSpace (F × F) WT)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact Bundle.contMDiffAt_proj WP
    · exact (Bundle.contMDiffAt_totalSpace.mp
        ((hVNsmooth.comp hVLlift).contMDiffAt)).2
  -- Stage 5: the representative formulas imply smoothness by local quotient descent.
  have hismooth : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace V νP ↦ (⟨z.proj, i z.proj z.snd⟩ : TotalSpace VT νT)) := by
    apply smooth_descent (F := F) (G := V) (H := VT) (W := WP) (V₀ := νP) (Z := νT)
      (fun z : TM ↦ q z.proj) i hqP
      (fun z ↦ (LinearMap.range
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ_surjective)
    exact (hqT.comp hVpull).congr (fun z ↦ by
      change (⟨z.proj, i z.proj _⟩ : TotalSpace VT νT) = ⟨z.proj, qT z.proj _⟩
      exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace VT νT)) (hi z.proj z.snd))
  have hWTlift : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F))
      (𝓘(ℝ, F × F)).tangent ∞
      (fun z : TotalSpace (F × F) WT ↦
        (⟨smoothTangentMap f z.proj, z.snd⟩ : TangentBundle 𝓘(ℝ, F × F) TN)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact (smoothTangentMap f).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj WT)
    · exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F))
          (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F)) ∞ id z from contMDiffAt_id)).2
  have hπtangent := (smoothTangentBundleProjection F N).contMDiff.contMDiff_tangentMap
    (m := ∞) (by simp)
  have hPpull : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace (F × F) WT ↦
        (⟨z.proj, dπ (smoothTangentMap f z.proj) z.snd⟩ : TotalSpace F WP)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact Bundle.contMDiffAt_proj WT
    · exact (Bundle.contMDiffAt_totalSpace.mp
        ((hπtangent.comp hWTlift).contMDiffAt)).2
  have hpsmooth : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace VT νT ↦ (⟨z.proj, p z.proj z.snd⟩ : TotalSpace V νP)) := by
    apply smooth_descent (F := F × F) (G := VT) (H := V)
      (W := WT) (V₀ := νT) (Z := νP) qT p hqT
      (fun z ↦ (LinearMap.range
        (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQ_surjective)
    exact (hqP.comp hPpull).congr (fun z ↦ by
      change (⟨z.proj, p z.proj _⟩ : TotalSpace V νP) = ⟨z.proj, q z.proj.proj _⟩
      exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace V νP)) (hp z.proj z.snd))
  exact ⟨i, p, hismooth, hpsmooth, hi, hp, fun z ↦ ⟨hinj z, hsurj z, hexact z⟩⟩

/-- The canonical vertical normal map selected with its companion projection. -/
def tangentNormalVerticalMap : ∀ z : TangentBundle 𝓘(ℝ, E) M, ν z.proj →L[ℝ] νT z :=
  (exists_tangentNormal_exactSequence f hf).choose

/-- The canonical projection selected from that same exact-sequence witness. -/
def tangentNormalProjection : ∀ z : TangentBundle 𝓘(ℝ, E) M, νT z →L[ℝ] ν z.proj :=
  (exists_tangentNormal_exactSequence f hf).choose_spec.choose

/-- A smooth splitting of the canonical normal exact sequence, with its ordered factors fixed. -/
structure TangentNormalSplitting where
  /-- The first factor is the normal quotient direction; the second is the vertical direction. -/
  equiv : ∀ z : TangentBundle 𝓘(ℝ, E) M, νT z ≃L[ℝ] (ν z.proj × ν z.proj)
  /-- The actual total map is smooth for the same selected normal atlases and native pullback. -/
  contMDiff_toFun :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞
      (fun z : TotalSpace VT νT ↦
        (⟨z.proj, equiv z.proj z.snd⟩ : TotalSpace (V × V) (νP ×ᵇ νP)))
  /-- The inverse total map is smooth for those same actual bundle topologies and atlases. -/
  contMDiff_invFun :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    letI := normalBundleContMDiffVectorBundle f hf.isImmersion
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj, (equiv z.proj).symm z.snd⟩ : TotalSpace VT νT))
  /-- The first component is the original canonical projection, not an arbitrary quotient map. -/
  fst_equiv : ∀ (z : TangentBundle 𝓘(ℝ, E) M) (w : νT z),
    (equiv z w).1 = tangentNormalProjection f hf z w
  /-- The canonical vertical inclusion is exactly the second ordered factor. -/
  equiv_vertical : ∀ (z : TangentBundle 𝓘(ℝ, E) M) (v : ν z.proj),
    equiv z (tangentNormalVerticalMap f hf z v) = (0, v)

open Function Set Topology in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in

/-- The canonical normal exact sequence has a smooth splitting over a paracompact source. -/
theorem nonempty_tangentNormalSplitting [T2Space M] [ParacompactSpace M] :
    Nonempty (TangentNormalSplitting f hf) := by
  classical
  -- Stage 1: local smooth descent and weighted gluing will use only the source M.
  have local_smooth_rightInverse
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)] (Q : ∀ x, W x
      →L[ℝ] V₀ x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x)) (x : M) :
      ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∃ s : ∀ y, V₀ y →L[ℝ] W y,
          ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
            (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U ∧
          ∀ y, y ∈ U → ∀ v, Q y (s y v) = v := by
    classical
    let a := trivializationAt F W x
    let b := trivializationAt G V₀ x
    let A (y : M) : F →L[ℝ] G :=
      (b.continuousLinearMapAt ℝ y).comp ((Q y).comp (a.symmL ℝ y))
    let U := a.baseSet ∩ b.baseSet
    have hU : IsOpen U := a.open_baseSet.inter b.open_baseSet
    have hx : x ∈ U := ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩
    have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] G) ∞ A U := by
      intro y hy
      have heval (v : F) : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
          (fun z ↦ A z v) U y := by
        have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
            (fun z ↦ (⟨z, a.symmL ℝ z v⟩ : TotalSpace F W)) y := by
          apply a.contMDiffAt_iff (a.mem_source.mpr hy.1) |>.mpr
          refine ⟨contMDiffAt_id, ?_⟩
          apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
          filter_upwards [a.open_baseSet.mem_nhds hy.1] with z hz
          rw [← a.continuousLinearMapAt_apply_of_mem ℝ hz]
          exact a.continuousLinearMapAt_symmL hz v
        have hq := hQ.contMDiffAt.comp y hs
        have hb := (b.contMDiffAt_iff (b.mem_source.mpr hy.2)).mp hq
        apply hb.2.contMDiffWithinAt.congr
        · intro z hz
          change (b.continuousLinearMapAt ℝ z) (Q z (a.symmL ℝ z v)) = _
          exact b.continuousLinearMapAt_apply_of_mem ℝ hz.2 _
        · exact b.continuousLinearMapAt_apply_of_mem ℝ hy.2 _
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
      apply contDiffWithinAt_clm_apply.mpr
      intro v
      have hv := heval v
      rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
      exact hv
    -- Choose one right inverse at the center; nearby invertible corrections vary smoothly.
    have hsurj : Function.Surjective (A x) := by
      intro v
      obtain ⟨w, hw⟩ := hsurjective x (b.symmL ℝ x v)
      refine ⟨a.continuousLinearMapAt ℝ x w, ?_⟩
      change (b.continuousLinearMapAt ℝ x) (Q x (a.symmL ℝ x
        (a.continuousLinearMapAt ℝ x w))) = v
      erw [a.symmL_continuousLinearMapAt (R := ℝ) hx.1]
      rw [hw, b.continuousLinearMapAt_symmL hx.2]
    obtain ⟨R₀, hR₀⟩ := (A x).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hsurj)
    let R : G →L[ℝ] F := R₀.toContinuousLinearMap
    let C (y : M) : G →L[ℝ] G := (A y).comp R
    have hCx : C x = ContinuousLinearMap.id ℝ G := by
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : G →ₗ[ℝ] G ↦ L v) hR₀
    have hC : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] G) ∞ C U :=
      hA.clm_comp contMDiffOn_const
    have hCAt := (hC x hx).contMDiffAt (hU.mem_nhds hx)
    have hinv : (C x).IsInvertible := by
      rw [hCx]
      exact ⟨ContinuousLinearEquiv.refl ℝ G, rfl⟩
    have hevent : ∀ᶠ y in 𝓝 x, y ∈ U ∧ (C y).IsInvertible :=
      Filter.inter_mem (hU.mem_nhds hx) (hCAt.continuousAt hinv.eventually_nhds)
    obtain ⟨U', hsub, hU'o, hx'⟩ := mem_nhds_iff.mp hevent
    let P (y : M) : G →L[ℝ] F := R.comp (C y).inverse
    have hP : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, G →L[ℝ] F) ∞ P U' := by
      intro y hy
      have hCy := (hC y (hsub hy).1).contMDiffAt (hU.mem_nhds (hsub hy).1)
      have hInv := ((hsub hy).2.contDiffAt_map_inverse (n := ∞)).contMDiffAt.comp y hCy
      exact (contMDiffAt_const.clm_comp hInv).contMDiffWithinAt
    -- Transport this corrected matrix back through the same two original trivializations.
    let s (y : M) : V₀ y →L[ℝ] W y :=
      (a.symmL ℝ y).comp ((P y).comp (b.continuousLinearMapAt ℝ y))
    let c := b.continuousLinearMap (RingHom.id ℝ) a
    have hs : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun y ↦ TotalSpace.mk' (G →L[ℝ] F) y (s y)) U' := by
      apply (c.contMDiffOn_section_iff hU'o (fun y hy ↦ (hsub hy).1.symm)).mpr
      apply hP.congr
      intro y hy
      ext v
      rw [show c = b.continuousLinearMap (RingHom.id ℝ) a from rfl,
        Trivialization.continuousLinearMap_apply]
      change (a.continuousLinearMapAt ℝ y)
        (a.symmL ℝ y (P y (b.continuousLinearMapAt ℝ y (b.symmL ℝ y v)))) = P y v
      rw [b.continuousLinearMapAt_symmL (hsub hy).1.2,
        a.continuousLinearMapAt_symmL (hsub hy).1.1]
    have hright (y : M) (hy : y ∈ U') (v : V₀ y) : Q y (s y v) = v := by
      have hinj : Function.Injective (b.continuousLinearMapAt ℝ y) := by
        intro u v huv
        have heq := congrArg (b.symmL ℝ y) huv
        exact (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 u).symm.trans
          (heq.trans (b.symmL_continuousLinearMapAt (R := ℝ) (hsub hy).1.2 v))
      apply hinj
      change (A y) (R ((C y).inverse (b.continuousLinearMapAt ℝ y v))) =
        b.continuousLinearMapAt ℝ y v
      change (C y) ((C y).inverse (b.continuousLinearMapAt ℝ y v)) =
        b.continuousLinearMapAt ℝ y v
      obtain ⟨e, he⟩ := (hsub hy).2
      rw [← he, ContinuousLinearMap.inverse_equiv]
      exact e.apply_symm_apply _
    exact ⟨U', hU'o, hx', s, hs, hright⟩
  have smooth_descent
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)]
      {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]
      {Z : M → Type _} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
      [∀ x, TopologicalSpace (Z x)] [∀ x, IsTopologicalAddGroup (Z x)]
      [∀ x, ContinuousSMul ℝ (Z x)] [TopologicalSpace (TotalSpace H Z)]
      [FiberBundle H Z] [VectorBundle ℝ H Z] [ContMDiffVectorBundle ∞ H Z 𝓘(ℝ, E)]
      (Q : ∀ x, W x →L[ℝ] V₀ x) (D : ∀ x, V₀ x →L[ℝ] Z x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀)))
      (hsurjective : ∀ x, Surjective (Q x))
      (hDQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, D z.proj (Q z.proj z.snd)⟩ : TotalSpace H Z))) :
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, H)) ∞
        (fun z : TotalSpace G V₀ ↦ (⟨z.proj, D z.proj z.snd⟩ : TotalSpace H Z)) := by
    intro z
    obtain ⟨U, hU, hz, s, hs, hright⟩ := local_smooth_rightInverse Q hQ hsurjective z.proj
    have hsAt := (hs z.proj hz).contMDiffAt (hU.mem_nhds hz)
    have htotal : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun w : TotalSpace G V₀ ↦ (⟨w.proj, s w.proj w.snd⟩ : TotalSpace F W)) z := by
      exact (hsAt.comp z (Bundle.contMDiffAt_proj V₀)).clm_bundle_apply contMDiffAt_id
    apply (hDQ.contMDiffAt.comp z htotal).congr_of_eventuallyEq
    filter_upwards [((FiberBundle.continuous_proj G V₀).continuousAt).preimage_mem_nhds
      (hU.mem_nhds hz)] with w hw
    change (⟨w.proj, D w.proj w.snd⟩ : TotalSpace H Z) =
      ⟨w.proj, D w.proj (Q w.proj (s w.proj w.snd))⟩
    rw [hright w.proj hw]
  have smooth_pullback_map
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)]
      {D : Type _} [NormedAddCommGroup D] [NormedSpace ℝ D]
      {N : Type _} [TopologicalSpace N] [ChartedSpace D N]
      [IsManifold 𝓘(ℝ, D) ∞ N]
      (f : ContMDiffMap 𝓘(ℝ, D) 𝓘(ℝ, E) N M ∞)
      (Q : ∀ x, W x →L[ℝ] V₀ x)
      (hQ : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀))) :
      ContMDiff (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, D).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F ((f : N → M) *ᵖ W) ↦
          (⟨z.proj, Q (f z.proj) z.snd⟩ : TotalSpace G ((f : N → M) *ᵖ V₀))) := by
    have hLift : ContMDiff (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
        (fun z : TotalSpace F ((f : N → M) *ᵖ W) ↦
          (⟨f z.proj, z.snd⟩ : TotalSpace F W)) := by
      intro z
      apply Bundle.contMDiffAt_totalSpace.mpr
      constructor
      · exact f.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj ((f : N → M) *ᵖ W))
      · exact (Bundle.contMDiffAt_totalSpace.mp
          (show ContMDiffAt (𝓘(ℝ, D).prod 𝓘(ℝ, F)) (𝓘(ℝ, D).prod 𝓘(ℝ, F)) ∞
            id z from contMDiffAt_id)).2
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact Bundle.contMDiffAt_proj ((f : N → M) *ᵖ W)
    · exact (Bundle.contMDiffAt_totalSpace.mp ((hQ.comp hLift).contMDiffAt)).2
  have smooth_total_to_hom
      {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {V₀ W : M → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, E)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, E)] (Q : ∀ x, W x
      →L[ℝ] V₀ x)
      (U : Set M) (hU : IsOpen U)
      (hQ : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, F)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (fun z : TotalSpace F W ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G V₀))
        {z | z.proj ∈ U}) :
      ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
        (fun y ↦ TotalSpace.mk' (F →L[ℝ] G) y (Q y)) U := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    let a := trivializationAt F W x
    let b := trivializationAt G V₀ x
    have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt _ _ _
    have hbx : x ∈ b.baseSet := mem_baseSet_trivializationAt _ _ _
    have heval (v : F) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞
        (fun y ↦ ContinuousLinearMap.inCoordinates F W G V₀ x y x y (Q y) v) x := by
      have hs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞
          (fun y ↦ (⟨y, a.symmL ℝ y v⟩ : TotalSpace F W)) x := by
        apply a.contMDiffAt_iff (a.mem_source.mpr hax) |>.mpr
        refine ⟨contMDiffAt_id, ?_⟩
        apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
        filter_upwards [a.open_baseSet.mem_nhds hax] with y hy
        rw [← a.continuousLinearMapAt_apply_of_mem ℝ hy]
        exact a.continuousLinearMapAt_symmL hy v
      have hq := (hQ (⟨x, a.symmL ℝ x v⟩ : TotalSpace F W) hx).contMDiffAt
        ((hU.preimage (FiberBundle.continuous_proj F W)).mem_nhds hx)
      have hb := (b.contMDiffAt_iff (b.mem_source.mpr hbx)).mp (hq.comp x hs)
      apply hb.2.congr_of_eventuallyEq
      filter_upwards [b.open_baseSet.mem_nhds hbx] with y hy
      exact b.continuousLinearMapAt_apply_of_mem ℝ hy _
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_clm_apply.mpr
    intro v
    have hv := heval v
    rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at hv
    exact hv
  -- Pull locally finite smooth weights back from M; no paracompactness of TM is needed.
  have smooth_rightInverse_over_base
      {E D : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    {M : Type _} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [ParacompactSpace M]
    {N : Type _} [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N]
    {F G : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V₀ W : N → Type _}
    [∀ x, AddCommGroup (V₀ x)] [∀ x, Module ℝ (V₀ x)] [∀ x, TopologicalSpace (V₀ x)]
    [∀ x, IsTopologicalAddGroup (V₀ x)] [∀ x, ContinuousSMul ℝ (V₀ x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
    [TopologicalSpace (TotalSpace G V₀)] [TopologicalSpace (TotalSpace F W)]
    [FiberBundle G V₀] [VectorBundle ℝ G V₀] [ContMDiffVectorBundle ∞ G V₀ 𝓘(ℝ, D)]
    [FiberBundle F W] [VectorBundle ℝ F W] [ContMDiffVectorBundle ∞ F W 𝓘(ℝ, D)]
      (f : ContMDiffMap 𝓘(ℝ, D) 𝓘(ℝ, E) N M ∞)
      (Q : ∀ x, W x →L[ℝ] V₀ x)
      (cover : M → Set M) (hcovero : ∀ x, IsOpen (cover x)) (hcover : ∀ x, x ∈ cover x)
      (s : M → ∀ z : N, V₀ z →L[ℝ] W z)
      (hs : ∀ i, ContMDiffOn 𝓘(ℝ, D) (𝓘(ℝ, D).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun z ↦ TotalSpace.mk' (G →L[ℝ] F) z (s i z)) ((f : N → M) ⁻¹' cover i))
      (hQs : ∀ i z, f z ∈ cover i → ∀ v, Q z (s i z v) = v) :
      ∃ a : ∀ z, V₀ z →L[ℝ] W z,
        ContMDiff 𝓘(ℝ, D) (𝓘(ℝ, D).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
          (fun z ↦ TotalSpace.mk' (G →L[ℝ] F) z (a z)) ∧
        ∀ z v, Q z (a z v) = v := by
    classical
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
    have hweights : ∃ φ : M → M → ℝ,
        (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ i)) ∧
        (∀ i x, 0 ≤ φ i x) ∧ (∀ x, ∃ i, 0 < φ i x) ∧
        LocallyFinite (fun i ↦ tsupport (φ i)) ∧
        ∀ i, tsupport (φ i) ⊆ cover i := by
      -- Start with compact smooth-bump supports contained in the fixed original frames.
      have hb (x : M) : ∃ b : SmoothBumpFunction 𝓘(ℝ, E) x,
          tsupport b ⊆ cover x :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp
          ((hcovero x).mem_nhds (hcover x)) |>.imp
            (fun b hb ↦ hb.2)
      choose b hb using hb
      obtain ⟨U, hUo, hUc, hUf, hUb⟩ := precise_refinement
        (fun x ↦ support (b x)) (fun x ↦ (b x).isOpen_support)
        (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, (b x).c_mem_support⟩)
      -- A continuous bump cover supplies compact closed pieces covering the whole base.
      obtain ⟨ρ, hρ⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite
        isClosed_univ U hUo hUf hUc.ge
      let K (i : M) : Set M := {x | ρ i x = 1}
      have hKclosed (i : M) : IsClosed (K i) := isClosed_eq (ρ i).continuous continuous_const
      have hKU (i : M) : K i ⊆ U i := by
        intro x hx
        apply hρ i
        apply subset_closure
        change ρ i x ≠ 0
        change ρ i x = 1 at hx
        simp [hx]
      have hKc : (univ : Set M) ⊆ ⋃ i, K i := by
        intro x hx
        exact mem_iUnion.mpr ⟨ρ.ind x hx, (ρ.eventuallyEq_one x hx).eq_of_nhds⟩
      have hKcompact (i : M) : IsCompact (K i) :=
        (b i).hasCompactSupport.of_isClosed_subset (hKclosed i)
          ((hKU i).trans ((hUb i).trans subset_closure))
      -- Smooth finitely many small bumps on each compact piece; their supports stay in U i.
      have hφ (i : M) : ∃ φ : M → ℝ,
          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ ∧ (∀ x, 0 ≤ φ x) ∧
          (∀ x ∈ K i, 0 < φ x) ∧ tsupport φ ⊆ U i := by
        have hb' (x : K i) : ∃ b' : SmoothBumpFunction 𝓘(ℝ, E) (x : M),
            tsupport b' ⊆ U i :=
          (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : M)).mem_iff.mp
            ((hUo i).mem_nhds (hKU i x.property)) |>.imp (fun b' hb' ↦ hb'.2)
        choose c hc using hb'
        obtain ⟨t, ht⟩ := (hKcompact i).elim_finite_subcover
          (fun x : K i ↦ support (c x)) (fun x ↦ (c x).isOpen_support)
          (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, (c ⟨x, hx⟩).c_mem_support⟩)
        refine ⟨fun x ↦ ∑ y ∈ t, c y x, ?_, ?_, ?_, ?_⟩
        · exact contMDiff_finsetSum fun y hy ↦ (c y).contMDiff
        · intro x
          exact Finset.sum_nonneg fun y hy ↦ (c y).nonneg
        · intro x hx
          obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
          exact Finset.sum_pos' (fun z hz ↦ (c z).nonneg)
            ⟨y, hy, lt_of_le_of_ne (c y).nonneg (Ne.symm hxy)⟩
        · apply subset_trans (b := ⋃ y ∈ t, tsupport (c y))
          · apply closure_minimal
            · intro x hx
              by_contra hn
              apply hx
              apply Finset.sum_eq_zero
              intro y hy
              apply image_eq_zero_of_notMem_tsupport
              exact fun hxy ↦ hn (mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
            · exact isClosed_biUnion_finset fun y hy ↦ isClosed_closure
          · exact iUnion₂_subset fun y hy ↦ hc y
      choose φ hφsmooth hφnonneg hφpos hφsupport using hφ
      refine ⟨φ, hφsmooth, hφnonneg, ?_, hUf.subset hφsupport, ?_⟩
      · intro x
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hKc (mem_univ x))
        exact ⟨i, hφpos i x hi⟩
      · intro i
        exact (hφsupport i).trans ((hUb i).trans (subset_closure.trans (hb i)))
    obtain ⟨φ, hφsmooth, hφnonneg, hφpos, hφfinite, hφsupport⟩ := hweights
    let ψ (i : M) (z : N) := φ i (f z)
    have hψsmooth (i : M) : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, ℝ) ∞ (ψ i) :=
      (hφsmooth i).comp f.contMDiff
    have hψsupport (i : M) : tsupport (ψ i) ⊆ (f : N → M) ⁻¹' tsupport (φ i) := by
      apply closure_minimal
      · intro z hz
        exact subset_closure hz
      · exact isClosed_closure.preimage f.contMDiff.continuous
    have hψfinite : LocallyFinite (fun i ↦ tsupport (ψ i)) :=
      (hφfinite.preimage_continuous f.contMDiff.continuous).subset hψsupport
    let t (z : N) : V₀ z →L[ℝ] W z := ∑ᶠ i, ψ i z • s i z
    have hterm (i : M) : ContMDiff 𝓘(ℝ, D)
        (𝓘(ℝ, D).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun z ↦ TotalSpace.mk' (G →L[ℝ] F) z (ψ i z • s i z)) :=
      ContMDiffOn.smul_section_of_tsupport (hψsmooth i).contMDiffOn
        ((hcovero i).preimage f.contMDiff.continuous)
        (fun z hz ↦ hφsupport i (hψsupport i hz)) (hs i)
    have ht : ContMDiff 𝓘(ℝ, D) (𝓘(ℝ, D).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun z ↦ TotalSpace.mk' (G →L[ℝ] F) z (t z)) := by
      apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
      apply hψfinite.subset
      intro i z hz
      exact subset_closure (show ψ i z ≠ 0 from fun h ↦ hz (by simp [h]))
    have hfinite (z : N) : (support (fun i ↦ ψ i z)).Finite :=
      (hψfinite.point_finite z).subset (fun i hi ↦ subset_closure hi)
    let w (z : N) : ℝ := ∑ᶠ i, ψ i z
    have hw : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, ℝ) ∞ w :=
      contMDiff_finsum hψsmooth (hψfinite.subset fun i ↦ subset_closure)
    have hwpos (z : N) : 0 < w z :=
      finsum_pos (fun i ↦ hφnonneg i (f z)) (hφpos (f z)) (hfinite z)
    let a (z : N) : V₀ z →L[ℝ] W z := (w z)⁻¹ • t z
    have ha : ContMDiff 𝓘(ℝ, D) (𝓘(ℝ, D).prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun z ↦ TotalSpace.mk' (G →L[ℝ] F) z (a z)) :=
      (hw.inv₀ fun z ↦ (hwpos z).ne').smul_section ht
    refine ⟨a, ha, ?_⟩
    intro z v
    have ht_eval : Q z (t z v) = w z • v := by
      have hsum : t z = ∑ i ∈ (hfinite z).toFinset, ψ i z • s i z := by
        apply finsum_eq_sum_of_support_subset
        intro i hi
        exact (hfinite z).mem_toFinset.mpr (left_ne_zero_of_smul hi)
      rw [hsum]
      simp only [sum_apply, smul_apply, map_sum, map_smul]
      calc
        ∑ i ∈ (hfinite z).toFinset, ψ i z • Q z (s i z v) =
            ∑ i ∈ (hfinite z).toFinset, ψ i z • v := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hQs i z (hφsupport i
            (hψsupport i (subset_closure ((hfinite z).mem_toFinset.mp hi)))) v]
        _ = w z • v := by
          rw [← Finset.sum_smul]
          congr 1
          exact (finsum_eq_sum_of_support_subset (fun i ↦ ψ i z)
            (fun i hi ↦ (hfinite z).mem_toFinset.mpr hi)).symm
    change Q z ((w z)⁻¹ • t z v) = v
    rw [map_smul, ht_eval, smul_smul, inv_mul_cancel₀ (hwpos z).ne', one_smul]
  -- The ordered inverse sends (u,v) to a horizontal lift of u plus the canonical i(v).
  have normalized_equiv
      {V₀ W : Type _}
    [AddCommGroup V₀] [Module ℝ V₀] [TopologicalSpace V₀]
    [IsTopologicalAddGroup V₀] [ContinuousSMul ℝ V₀] [T2Space V₀] [FiniteDimensional ℝ V₀]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W] (i : V₀
      →L[ℝ] W) (p : W →L[ℝ] V₀) (s : V₀ →L[ℝ] W)
      (hi : Injective i) (hexact : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
      (hs : RightInverse s p) :
      ∃ e : W ≃L[ℝ] (V₀ × V₀),
        (∀ w, (e w).1 = p w) ∧
        (∀ v, e (i v) = (0, v)) ∧
        (∀ u v, e.symm (u, v) = s u + i v) := by
    let A : (V₀ × V₀) →L[ℝ] W :=
      s.comp (ContinuousLinearMap.fst ℝ V₀ V₀) + i.comp (ContinuousLinearMap.snd ℝ V₀ V₀)
    have hpiv (v : V₀) : p (i v) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hexact]
      exact ⟨v, rfl⟩
    have hpA (u : V₀ × V₀) : p (A u) = u.1 := by
      change p (s u.1 + i u.2) = u.1
      rw [map_add, hs, hpiv, add_zero]
    have hA : Bijective A := by
      constructor
      · intro u v huv
        have hfirst : u.1 = v.1 := by
          simpa only [hpA] using congrArg p huv
        have hsecond : u.2 = v.2 := by
          apply hi
          have h := huv
          change s u.1 + i u.2 = s v.1 + i v.2 at h
          rw [hfirst] at h
          exact add_left_cancel h
        exact Prod.ext hfirst hsecond
      · intro w
        have hker : w - s (p w) ∈ LinearMap.ker p.toLinearMap := by
          change p (w - s (p w)) = 0
          rw [map_sub, hs, sub_self]
        rw [← hexact] at hker
        obtain ⟨v, hv⟩ := hker
        change i v = w - s (p w) at hv
        refine ⟨(p w, v), ?_⟩
        change s (p w) + i v = w
        rw [hv]
        rw [add_comm, sub_add_cancel]
    let b : (V₀ × V₀) ≃L[ℝ] W := (LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv
    have hb (u : V₀ × V₀) : b u = s u.1 + i u.2 := rfl
    refine ⟨b.symm, ?_, ?_, ?_⟩
    · intro w
      have h := congrArg p (b.apply_symm_apply w)
      change p (A (b.symm w)) = p w at h
      rwa [hpA] at h
    · intro v
      apply b.injective
      rw [b.apply_symm_apply, hb, map_zero, zero_add]
    · intro u v
      exact hb (u, v)
  -- Stage 2: retain both canonical quotient maps and the original selected normal atlases.
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let W := ((f : M → N) *ᵖ (TangentSpace 𝓘(ℝ, F)))
  let WP := ((πM : TM → M) *ᵖ W)
  let WT := ((smoothTangentMap f : TM → TN) *ᵖ (TangentSpace 𝓘(ℝ, F × F)))
  let (x : M) : AddCommGroup (W x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : Module ℝ (W x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : IsTopologicalAddGroup (W x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : M) : ContinuousSMul ℝ (W x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F) (f x))
    infer_instance
  let (x : TM) : AddCommGroup (WP x) := by
    change AddCommGroup (W x.proj)
    infer_instance
  let (x : TM) : Module ℝ (WP x) := by
    change Module ℝ (W x.proj)
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (WP x) := by
    change IsTopologicalAddGroup (W x.proj)
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (WP x) := by
    change ContinuousSMul ℝ (W x.proj)
    infer_instance
  let (x : TM) : AddCommGroup (WT x) := by
    change AddCommGroup (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : Module ℝ (WT x) := by
    change Module ℝ (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (WT x) := by
    change IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (WT x) := by
    change ContinuousSMul ℝ (TangentSpace 𝓘(ℝ, F × F) (smoothTangentMap f x))
    infer_instance
  let (x : TM) : AddCommGroup (νP x) := by
    change AddCommGroup (ν x.proj)
    infer_instance
  let (x : TM) : Module ℝ (νP x) := by
    change Module ℝ (ν x.proj)
    infer_instance
  let (x : TM) : IsTopologicalAddGroup (νP x) := by
    change IsTopologicalAddGroup (ν x.proj)
    infer_instance
  let (x : TM) : ContinuousSMul ℝ (νP x) := by
    change ContinuousSMul ℝ (ν x.proj)
    infer_instance
  let q (x : M) := (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQL
  let qT (z : TM) :=
    (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).toLinearMap).mkQL
  let dπ (z : TN) :=
    mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) z
  let i := tangentNormalVerticalMap f hf
  let p := tangentNormalProjection f hf
  have hiSmooth := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.1
  have hpSmooth := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.1
  have hi := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.1
  have hp := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.1
  have he := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.2
  obtain ⟨n, hn, hnq⟩ := exists_smooth_normal_rightInverse f hf.isImmersion
  have hnP : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace V νP ↦ (⟨z.proj, n z.proj.proj z.snd⟩ : TotalSpace F WP)) := by
    exact smooth_pullback_map (F := V) (G := F) (W := ν) (V₀ := W) πM n hn
  have hqT : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace (F × F) WT ↦ (⟨z.proj, qT z.proj z.snd⟩ : TotalSpace VT νT)) :=
    (smoothNormalQuotientMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)).contMDiff
  have hLift : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
      (𝓘(ℝ, F × F).prod 𝓘(ℝ, F)) ∞
      (fun z : TotalSpace F WP ↦
        (⟨smoothTangentMap f z.proj, z.snd⟩ : TotalSpace F
          ((smoothTangentBundleProjection F N : TN → N) *ᵖ (TangentSpace 𝓘(ℝ, F))))) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    constructor
    · exact (smoothTangentMap f).contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj WP)
    · exact (Bundle.contMDiffAt_totalSpace.mp
        (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, F))
          (𝓘(ℝ, E × E).prod 𝓘(ℝ, F)) ∞ id z from contMDiffAt_id)).2
  let πN₀ := smoothTangentBundleProjection F N
  let PN := ((πN₀ : TN → N) *ᵖ (TangentSpace 𝓘(ℝ, F) : N → Type _))
  -- Stage 3: one fixed ambient chart lifts horizontal vectors over its entire base patch.
  have horizontal_chart (x₀ : N) :
      ∃ H : ∀ z : TN, TangentSpace 𝓘(ℝ, F) z.proj →L[ℝ] TangentSpace 𝓘(ℝ, F × F) z,
        ContMDiffOn ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F × F)) ∞
          (fun q : TotalSpace F PN ↦ (⟨q.proj, H q.proj q.snd⟩ : TangentBundle 𝓘(ℝ, F × F) TN))
          {q | q.proj.proj ∈ (chartAt F x₀).source} ∧
        ∀ z : TN, z.proj ∈ (chartAt F x₀).source →
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ z).comp (H z) = ContinuousLinearMap.id ℝ _ := by
    let c := chartAt F x₀
    let z₀ : TN := ⟨x₀, 0⟩
    let d := chartAt (F × F) z₀
    have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N := IsManifold.chart_mem_maximalAtlas x₀
    have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℝ, F × F) ∞ TN := IsManifold.chart_mem_maximalAtlas z₀
    let H := fun z : TN ↦ (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z)).comp
      ((ContinuousLinearMap.inl ℝ F F).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c z.proj))
    refine ⟨H, ?_, ?_⟩
    · -- Pull the original fiber vector to TN before differentiating the fixed chart.
      have hLift : ContMDiff ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F)).prod 𝓘(ℝ, F)) ∞
          (fun q : TotalSpace F PN ↦ (⟨q.proj.proj, q.snd⟩ : TN)) := by
        intro q
        apply Bundle.contMDiffAt_totalSpace.mpr
        constructor
        · exact (πN₀).contMDiff.contMDiffAt.comp q (Bundle.contMDiffAt_proj PN)
        · exact (Bundle.contMDiffAt_totalSpace.mp
            (show ContMDiffAt ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ∞ id q
              from contMDiffAt_id)).2
      intro q hq
      have hq' : q.proj ∈ d.source := by
        exact (TangentBundle.mem_chart_source_iff (I := 𝓘(ℝ, F)) q.proj z₀).mpr hq
      have hbase : ContMDiffAt ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F × F) ∞
          (fun q : TotalSpace F PN ↦ d q.proj) q :=
        (contMDiffAt_of_mem_maximalAtlas hd hq').comp q (Bundle.contMDiffAt_proj PN)
      have hvec : ContMDiffAt ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
          (fun q : TotalSpace F PN ↦ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c q.proj.proj) q.snd) q := by
        have ht := ((contMDiffAt_of_mem_maximalAtlas hc hq).contMDiffAt_tangentMap
          (X := (⟨q.proj.proj, q.snd⟩ : TN)) (m := ∞) (by simp)).comp q
            (hLift q)
        have hmodel := (contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓘(ℝ,
          F))).contMDiffAt.comp q ht
        have hmodel' : ContMDiffAt ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) 𝓘(ℝ, F × F) ∞
            (fun q : TotalSpace F PN ↦ (c q.proj.proj,
              (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c q.proj.proj) q.snd)) q := by
          convert! hmodel using 1
          exact modelWithCornersSelf_prod
        exact contDiff_snd.contDiffAt.comp_contMDiffAt hmodel'
      have hin : ContMDiffAt ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F × F)) ∞
          (fun q : TotalSpace F PN ↦ ((d q.proj,
            ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c q.proj.proj) q.snd, (0 : F))) : ModelProd (F × F) (F ×
              F))) q := by
        exact hbase.prodMk (hvec.prodMk_space (contMDiffAt_const (c := (0 : F))))
      have hin' : ContMDiffAt (M' := ModelProd (F × F) (F × F))
          ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F)) ((𝓘(ℝ, F × F)).prod 𝓘(ℝ, F × F)) ∞
          (fun q : TotalSpace F PN ↦ (d q.proj,
            ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c q.proj.proj) q.snd, (0 : F)))) q := by
        convert! hin using 1
        exact chartedSpaceSelf_prod.symm
      have hinput :=
        (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, F × F))).contMDiffAt.comp
          q hin'
      have hout :=
        ((contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hq')).contMDiffAt_tangentMap
        (X := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F × F)).symm
          (d q.proj, ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c q.proj.proj) q.snd, (0 : F))))
        (m := ∞) (by simp)).comp q hinput
      apply hout.contMDiffWithinAt.congr
      · intro r hr
        have hr' : r.proj ∈ d.source := by
          exact (TangentBundle.mem_chart_source_iff (I := 𝓘(ℝ, F)) r.proj z₀).mpr hr
        exact TotalSpace.ext (d.left_inv hr').symm (by rfl)
      · exact TotalSpace.ext (d.left_inv hq').symm (by rfl)
    · intro z hz
      have hz' : z ∈ d.source := by
        exact (TangentBundle.mem_chart_source_iff (I := 𝓘(ℝ, F)) z z₀).mpr hz
      have hleft : d.symm (d z) = z := d.left_inv hz'
      have hdc := contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hz')
      have hpc := (πN₀).contMDiff.contMDiffAt (x := d.symm (d z))
      have hcomp := mfderiv_comp (I := 𝓘(ℝ, F × F)) (I' := 𝓘(ℝ, F × F)) (I'' := 𝓘(ℝ, F))
        (d z) (hpc.mdifferentiableAt (by simp)) (hdc.mdifferentiableAt (by simp))
      change (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (πN₀ ∘ d.symm) (d z) : (F × F) →L[ℝ] F) =
        (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ (d.symm (d z)) : (F × F) →L[ℝ] F).comp
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z) : (F × F) →L[ℝ] (F × F)) at hcomp
      have hfun : (πN₀ ∘ d.symm) = c.symm ∘ (Prod.fst : F × F → F) := rfl
      -- Differentiate the projection identity in this same fixed chart.
      have hcf := mfderiv_comp (I := 𝓘(ℝ, F × F)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, F)) (d z)
        ((contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hz)).mdifferentiableAt (by simp))
        (differentiableAt_fst.mdifferentiableAt)
      rw [mfderiv_eq_fderiv] at hcf
      change (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (c.symm ∘ Prod.fst) (d z) : (F × F) →L[ℝ] F) =
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm (c z.proj) : F →L[ℝ] F).comp
          (fderiv ℝ (Prod.fst : F × F → F) (d z)) at hcf
      rw [fderiv_fst (𝕜 := ℝ) (E := F) (F := F) (p := d z)] at hcf
      have hcancel := (mdifferentiable_chart (I := 𝓘(ℝ, F)) x₀).symm_comp_deriv hz
      let L : TN → (F × F) →L[ℝ] F := fun t ↦ mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ t
      have hLeq : L z = L (d.symm (d z)) := congrArg L hleft.symm
      have hmatrix : (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ z : (F × F) →L[ℝ] F).comp
          (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z) : (F × F) →L[ℝ] (F × F)) =
          (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c.symm (c z.proj) : F →L[ℝ] F).comp
            (ContinuousLinearMap.fst ℝ F F) := by
        calc
          _ = (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ (d.symm (d z)) : (F × F) →L[ℝ] F).comp
              (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z) : (F × F) →L[ℝ] (F × F)) := by
            exact congrArg (fun A : (F × F) →L[ℝ] F ↦ A.comp
              (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z) : (F × F) →L[ℝ] (F × F)))
                hLeq
          _ = mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (πN₀ ∘ d.symm) (d z) := hcomp.symm
          _ = _ := by rw [hfun]; exact hcf
      ext w
      have hw := DFunLike.congr_fun hmatrix
        ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c z.proj) w, (0 : F))
      change (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) πN₀ z)
        ((mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F × F) d.symm (d z)) ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) c z.proj) w,
          0)) = w
      exact hw.trans (DFunLike.congr_fun hcancel w)
  -- Stage 4: combine those lifts with the same global normal right inverse, then glue.
  choose H hH hHp using fun x : M ↦ horizontal_chart (f x)
  let U (x : M) : Set M := f ⁻¹' (chartAt F (f x)).source
  have hU (x : M) : IsOpen (U x) := (chartAt F (f x)).open_source.preimage f.contMDiff.continuous
  have hxU (x : M) : x ∈ U x := mem_chart_source F (f x)
  let s (x : M) (z : TM) : ν z.proj →L[ℝ] νT z :=
    (qT z).comp ((H x (smoothTangentMap f z)).comp (n z.proj))
  have hsTotal (x : M) : ContMDiffOn (𝓘(ℝ, E × E).prod 𝓘(ℝ, V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace V νP ↦ (⟨z.proj, s x z.proj z.snd⟩ : TotalSpace VT νT))
      {z | z.proj.proj ∈ U x} := by
    intro z hz
    have hOpen : IsOpen {w : TotalSpace F
        ((smoothTangentBundleProjection F N : TN → N) *ᵖ (TangentSpace 𝓘(ℝ, F))) |
        w.proj.proj ∈ (chartAt F (f x)).source} :=
      (chartAt F (f x)).open_source.preimage
        ((smoothTangentBundleProjection F N).contMDiff.continuous.comp
          (FiberBundle.continuous_proj _ _))
    have hHor := ((hH x _ hz).contMDiffAt (hOpen.mem_nhds hz)).comp z
      ((hLift.comp hnP).contMDiffAt)
    have hPull : ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, F × F)) ∞
        (fun w : TotalSpace V νP ↦
          (⟨w.proj, H x (smoothTangentMap f w.proj) (n w.proj.proj w.snd)⟩ :
            TotalSpace (F × F) WT)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨Bundle.contMDiffAt_proj νP, (Bundle.contMDiffAt_totalSpace.mp hHor).2⟩
    exact (hqT.contMDiffAt.comp z hPull).contMDiffWithinAt
  have hs (x : M) : ContMDiffOn 𝓘(ℝ, E × E)
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V →L[ℝ] VT)) ∞
      (fun z : TM ↦ TotalSpace.mk' (V →L[ℝ] VT)
        (E := fun z : TM ↦ νP z →L[ℝ] νT z) z (s x z)) ((πM : TM → M) ⁻¹' U x) := by
    exact smooth_total_to_hom (F := V) (G := VT) (W := νP) (V₀ := νT) (s x)
      ((πM : TM → M) ⁻¹' U x) ((hU x).preimage (smoothTangentBundleProjection E
        M).contMDiff.continuous)
      (hsTotal x)
  have hps (x : M) (z : TM) (hz : z.proj ∈ U x) (v : ν z.proj) :
      p z (s x z v) = v := by
    have hpRep := hp z ((H x (smoothTangentMap f z)) (n z.proj v))
    have hHor := DFunLike.congr_fun (hHp x (smoothTangentMap f z) hz) (n z.proj v)
    change dπ (smoothTangentMap f z) (H x (smoothTangentMap f z) (n z.proj v)) =
      n z.proj v at hHor
    change p z (s x z v) = q z.proj
      (dπ (smoothTangentMap f z) (H x (smoothTangentMap f z) (n z.proj v))) at hpRep
    exact hpRep.trans ((congrArg (q z.proj) hHor).trans (hnq z.proj v))
  obtain ⟨a, ha, hpa⟩ := smooth_rightInverse_over_base (F := VT) (G := V)
    (W := νT) (V₀ := νP) πM p U hU hxU s hs hps
  have hequiv (z : TM) : ∃ e : νT z ≃L[ℝ] (ν z.proj × ν z.proj),
      (∀ w, (e w).1 = p z w) ∧ (∀ v, e (i z v) = (0, v)) ∧
      ∀ u v, e.symm (u, v) = a z u + i z v :=
    normalized_equiv (i z) (p z) (a z) (he z).1 (he z).2.2 (hpa z)
  choose e hefirst hevertical heinverse using hequiv
  -- Stage 5: normalize the ordered splitting and verify both actual total maps are smooth.
  let A (z : TM) : (ν z.proj × ν z.proj) →L[ℝ] νT z :=
    (a z).comp (ContinuousLinearMap.fst ℝ _ _) +
      (i z).comp (ContinuousLinearMap.snd ℝ _ _)
  have hAeq (z : TM) (v : ν z.proj × ν z.proj) : A z v = (e z).symm v :=
    (heinverse z v.1 v.2).symm
  have hfst : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj, z.snd.1⟩ : TotalSpace V νP)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νP ×ᵇ νP), ?_⟩
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : V × V → V)).contDiffAt.comp_contMDiffAt hcoords
  have hsnd : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj, z.snd.2⟩ : TotalSpace V νP)) := by
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νP ×ᵇ νP), ?_⟩
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp
      (show ContMDiffAt (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞ id z from contMDiffAt_id)).2
    exact (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : V × V → V)).contDiffAt.comp_contMDiffAt hcoords
  have hAsmooth : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj, A z.proj z.snd⟩ : TotalSpace VT νT)) := by
    intro z
    have h1 := ((ha z.proj).comp z (Bundle.contMDiffAt_proj (νP ×ᵇ νP))).clm_bundle_apply
      (hfst z)
    have h2 := hiSmooth.contMDiffAt.comp z (hsnd z)
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨Bundle.contMDiffAt_proj (νP ×ᵇ νP), ?_⟩
    have hc1 := (Bundle.contMDiffAt_totalSpace.mp h1).2
    have hc2 := (Bundle.contMDiffAt_totalSpace.mp h2).2
    apply (hc1.add hc2).congr_of_eventuallyEq
    let t := trivializationAt VT νT z.proj
    filter_upwards [(FiberBundle.continuous_proj (V × V) (νP ×ᵇ νP)).continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with w hw
    change (t ⟨w.proj, a w.proj w.snd.1 + i w.proj w.snd.2⟩).2 =
      (t ⟨w.proj, a w.proj w.snd.1⟩).2 + (t ⟨w.proj, i w.proj w.snd.2⟩).2
    rw [← t.continuousLinearMapAt_apply_of_mem ℝ hw,
      ← t.continuousLinearMapAt_apply_of_mem ℝ hw,
      ← t.continuousLinearMapAt_apply_of_mem ℝ hw, map_add]
  have hforward : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V)) ∞
      (fun z : TotalSpace VT νT ↦
        (⟨z.proj, e z.proj z.snd⟩ : TotalSpace (V × V) (νP ×ᵇ νP))) := by
    apply smooth_descent (F := V × V) (G := VT) (H := V × V)
      (W := νP ×ᵇ νP) (V₀ := νT) (Z := νP ×ᵇ νP) A
      (fun z ↦ (e z).toContinuousLinearMap) hAsmooth
    · intro z w
      exact ⟨e z w, (hAeq z (e z w)).trans ((e z).symm_apply_apply w)⟩
    · apply contMDiff_id.congr
      intro z
      change (⟨z.proj, e z.proj (A z.proj z.snd)⟩ :
        TotalSpace (V × V) (νP ×ᵇ νP)) = z
      have hvec := (congrArg (e z.proj) (hAeq z.proj z.snd)).trans
        ((e z.proj).apply_symm_apply z.snd)
      exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace (V × V) (νP ×ᵇ νP))) hvec
  have hinverse : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
      (fun z : TotalSpace (V × V) (νP ×ᵇ νP) ↦
        (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace VT νT)) := by
    apply hAsmooth.congr
    intro z
    exact congrArg (fun v ↦ (⟨z.proj, v⟩ : TotalSpace VT νT)) (hAeq z.proj z.snd).symm
  exact ⟨{
    equiv := e
    contMDiff_toFun := hforward
    contMDiff_invFun := hinverse
    fst_equiv := hefirst
    equiv_vertical := hevertical }⟩

/-- One smooth splitting, selected from the standard splitting existence theorem. -/
def tangentNormalSplitting [T2Space M] [ParacompactSpace M] : TangentNormalSplitting f hf :=
  (nonempty_tangentNormalSplitting f hf).some

namespace TangentNormalSplitting

/-- The actual total homeomorphism to the native double of the original pullback normal bundle. -/
def totalHomeomorph (S : TangentNormalSplitting f hf) :
    TotalSpace VT νT ≃ₜ TotalSpace (V × V) (νP ×ᵇ νP) := by
  letI := normalBundleFiberBundle f hf.isImmersion
  letI := normalBundleVectorBundle f hf.isImmersion
  letI := normalBundleContMDiffVectorBundle f hf.isImmersion
  letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  letI := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  exact
    { toFun := fun z ↦ ⟨z.proj, S.equiv z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (S.equiv z.proj).symm z.snd⟩
      left_inv := fun z ↦ by
        rcases z with ⟨x, v⟩
        exact congrArg (fun w : νT x ↦ (⟨x, w⟩ : TotalSpace VT νT))
          ((S.equiv x).symm_apply_apply v)
      right_inv := fun z ↦ by
        rcases z with ⟨x, v⟩
        exact congrArg (fun w : ν x.proj × ν x.proj ↦
          (⟨x, w⟩ : TotalSpace (V × V) (νP ×ᵇ νP))) ((S.equiv x).apply_symm_apply v)
      continuous_toFun := S.contMDiff_toFun.continuous
      continuous_invFun := S.contMDiff_invFun.continuous }

end TangentNormalSplitting

end AtiyahSinger
