/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Equivariance of the actual relative symbol transport

Public module ID: M0547.

The specified inverse-dual cotangent map and two moving-fiber bundle squares
transport symbol covariance. Outside the open image the symbol is the supplied
equivariant multiplier. This compares actual fiber maps, without choosing an
unrelated equivariant symbol or assuming equality of their K classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n : ℕ} {O M : Type*} [TopologicalSpace O] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G O] [ContinuousSMul G O]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G O]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1800000 in
-- Keep the original four bundle models and both nested cotangent pullbacks during transport.
/-- Relative transport through the same equivariant fiber and cotangent maps fixes the symbol. -/
theorem equivariantGlobalSymbolLinearMap_eq_of_openTransport
    (E F : SmoothFiniteComplexBundle (n := n) O)
    (E' F' : SmoothFiniteComplexBundle (n := n) M)
    (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (ρE : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      EquivariantStructure G E'.Fiber)
    (ρF : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      EquivariantStructure G F'.Fiber)
    (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (he : ∀ (g : G) (x : O), (e (g • x)).val = g • (e x).val)
    (hCot : letI := smoothCotangentMulAction (n := n) (G := G) (M := O) IG
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := O)),
        cotangentOpenInclusion U (cotangentDiffeomorph e (g • z)) =
          g • cotangentOpenInclusion U (cotangentDiffeomorph e z))
    (α : ∀ x : O, E.Fiber x ≃ₗ[ℂ] E'.Fiber (e x).val)
    (β : ∀ x : O, F.Fiber x ≃ₗ[ℂ] F'.Fiber (e x).val)
    (hα : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      ∀ (g : G) (x : O) (v : E.Fiber x),
        (⟨(e (g • x)).val, α (g • x) (σE.linearMap g x v)⟩ : TotalSpace Unit E'.Fiber) =
          ⟨g • (e x).val, ρE.linearMap g (e x).val (α x v)⟩)
    (hβ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (x : O) (v : F.Fiber x),
        (⟨(e (g • x)).val, β (g • x) (σF.linearMap g x v)⟩ : TotalSpace Unit F'.Fiber) =
          ⟨g • (e x).val, ρF.linearMap g (e x).val (β x v)⟩)
    (s : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (t : GlobalSymbolFunction (n := n) E'.Fiber F'.Fiber)
    (hs : ∀ (g : G) (x : O) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s x ξ = s x ξ)
    (hst : ∀ (x : O) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x),
      t (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) = β x (s x ξ v))
    (d : ∀ y : M, E'.Fiber y →ₗ[ℂ] F'.Fiber y)
    (hd : letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      ∀ (g : G) (y : M) (v : E'.Fiber y),
        d (g • y) (ρE.linearMap g y v) = ρF.linearMap g y (d y v))
    (hext : ∀ y : M, y ∉ U → ∀ η v, t y η v = d y v) :
    ∀ (g : G) (y : M) (η : CotangentFiber (n := n) y), η ≠ 0 →
      equivariantGlobalSymbolLinearMap IG ρE ρF g t y η = t y η := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := smoothCotangentMulAction (n := n) (G := G) (M := O) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let X := CotangentTotalSpace (n := n) (M := O)
  let Y := CotangentTotalSpace (n := n) (M := M)
  let p : C(X, O) := cotangentProjection
  let q : C(Y, M) := cotangentProjection
  let W := TotalSpace Unit ((p : X → O) *ᵖ E.Fiber)
  let W' := TotalSpace Unit ((q : Y → M) *ᵖ E'.Fiber)
  let : MulAction G W := (σE.pullback p (fun _ _ ↦ rfl)).toMulAction
  let : MulAction G W' := (ρE.pullback q (fun _ _ ↦ rfl)).toMulAction
  let : MulAction G (TotalSpace Unit F.Fiber) := σF.toMulAction
  let : MulAction G (TotalSpace Unit F'.Fiber) := ρF.toMulAction
  let k : X → Y := fun z ↦ cotangentOpenInclusion U (cotangentDiffeomorph e z)
  let J : W → W' := fun w ↦ ⟨k w.proj, α w.proj.proj w.snd⟩
  let B : TotalSpace Unit F.Fiber → TotalSpace Unit F'.Fiber :=
    fun w ↦ ⟨(e w.proj).val, β w.proj w.snd⟩
  let S : W → TotalSpace Unit F.Fiber :=
    fun w ↦ ⟨w.proj.proj, s w.proj.proj w.proj.snd w.snd⟩
  let T : W' → TotalSpace Unit F'.Fiber :=
    fun w ↦ ⟨w.proj.proj, t w.proj.proj w.proj.snd w.snd⟩
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF s).mp hs
  -- All comparisons are equalities of the original dependent total-space vectors.
  have hJ (g : G) (w : W) : J (g • w) = g • J w := by
    apply TotalSpace.ext (hCot g w.proj)
    exact (TotalSpace.ext_iff.mp (hα g w.proj.proj w.snd)).2
  have hB (g : G) (w : TotalSpace Unit F.Fiber) : B (g • w) = g • B w :=
    hβ g w.proj w.snd
  have hST (w : W) : T (J w) = B (S w) :=
    congrArg (TotalSpace.mk (e w.proj.proj).val) (hst w.proj.proj w.proj.snd w.snd)
  have hT (g : G) (w : W) (hw : w.proj.snd ≠ 0) :
      T (g • J w) = g • T (J w) := by
    have hS : S (g • w) = g • S w :=
      congrArg (TotalSpace.mk (g • w.proj.proj))
        (hcov g w.proj.proj w.proj.snd hw w.snd)
    calc
      T (g • J w) = T (J (g • w)) := congrArg T (hJ g w).symm
      _ = B (S (g • w)) := hST (g • w)
      _ = B (g • S w) := congrArg B hS
      _ = g • B (S w) := hB g (S w)
      _ = g • T (J w) := congrArg (fun z ↦ g • z) (hST w).symm
  apply (equivariantGlobalSymbolLinearMap_eq_iff IG ρE ρF t).mpr
  intro g y η hη v
  by_cases hy : y ∈ U
  · -- The inverse of the specified cotangent homeomorphism supplies this exact covector.
    obtain ⟨z, hz⟩ := (cotangentDiffeomorph e).surjective ⟨⟨y, hy⟩, η⟩
    have hkz : k z = ⟨y, η⟩ := congrArg (cotangentOpenInclusion U) hz
    have hbase : (e z.proj).val = y := congrArg TotalSpace.proj hkz
    let v₀ : E'.Fiber (e z.proj).val := cast (congrArg E'.Fiber hbase.symm) v
    let u : E.Fiber z.proj := (α z.proj).symm v₀
    have hJw : J ⟨z, u⟩ = (⟨⟨y, η⟩, v⟩ : W') := by
      apply TotalSpace.ext hkz
      change HEq (α z.proj ((α z.proj).symm v₀)) v
      rw [LinearEquiv.apply_symm_apply]
      exact cast_heq _ v
    have hz0 : z.snd ≠ 0 := by
      intro hz0
      have hηeq : (k z).snd = η := eq_of_heq (TotalSpace.ext_iff.mp hkz).2
      apply hη
      rw [← hηeq]
      change z.snd.comp _ = 0
      rw [hz0, ContinuousLinearMap.zero_comp]
    have h := hT g ⟨z, u⟩ hz0
    rw [hJw] at h
    exact TotalSpace.mk_injective (g • y) h
  · -- The invariant open image has invariant complement, where the original multiplier applies.
    have hgy : g • y ∉ U := by
      intro hgy
      let x := e.symm ⟨g • y, hgy⟩
      have hx : (e x).val = g • y := congrArg Subtype.val (e.apply_symm_apply _)
      have hxy : (e (g⁻¹ • x)).val = y := by
        rw [he, hx, inv_smul_smul]
      exact hy (hxy ▸ (e (g⁻¹ • x)).property)
    rw [hext (g • y) hgy, hext y hy]
    exact hd g y v

end AtiyahSinger
