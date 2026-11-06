/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedKernelMetric
public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev
public import AtiyahSinger.Geometry.AtlasNativeMetric
public import AtiyahSinger.Geometry.TensorAtlasConnection

/-!
# Native coefficient metrics from the original full sphere kernel

Public module ID: M0098.

Tensor the original base metric with the integral Gram metric of the specified
sphere-kernel representation. Keep the same tensor pairing while choosing its
native fixed-rank model and both smooth comparison maps. This implementation
adapter supplies the coefficient models used at the four corners of the actual
associated Green construction; it does not replace a kernel by its dimension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere
  lieGroup_orthogonalGroup

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (hk : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (y : OrthogonalSphere r) (u v : F.Fiber y),
      k.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = k.pairing y u v)
  (ν : Measure (OrthogonalSphere r)) [IsSmoothPositiveMeasure (n := r) ν]
  (hν : ∀ g : Matrix.orthogonalGroup (Fin r) ℝ,
    Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)

variable (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

variable {d : ℝ}
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν d)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Q.toLinearMap.ker)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : Matrix.orthogonalGroup (Fin r) ℝ) (v : Fin ρ.dimension → ℂ),
        (e (ρ.representation g v)).val =
          σ.smoothSectionRepresentation 𝓘(ℝ, OrthogonalGroupModel r) hσ g (e v).val)

variable {a : ℕ} [CompactSpace B] [T2Space B] [SecondCountableTopology B]
  [IsManifold (𝓡 n) ∞ B] [MeasurableSpace B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (h : SmoothHermitianMetric (n := n) (r := a) E)

local notation "C" => fun x : B ↦ E x ⊗[ℂ] K x

include hk hν he in
set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in
-- Retain the specified kernel representation, tensor model and exact original Gram metric.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified full kernel determines a native coefficient model with its exact Gram metric. -/
theorem PseudodifferentialOperator.exists_associatedKernelCoefficientNativeMetric :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    ∃ (l : ContinuousHermitianMetric C) (N : SmoothFiniteComplexBundle (n := n) B)
      (kN : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber),
      letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
      ∃ (cIso : Iso C N.Fiber)
        (_heC : IsSmoothAtlasBundleMap AC
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber)
          cIso.toHom.linearMap)
        (_hiC : IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber) AC
          cIso.symm.toHom.linearMap),
        AC.IsSmoothHermitianMetric l ∧ N.rank = a * ρ.dimension ∧
        (∀ (x : B) (u v : C x),
          kN.pairing x (cIso.linearEquiv x u) (cIso.linearEquiv x v) =
            (l.toCore x).inner u v) ∧
        ∀ (p : P) (u v : E (projection p)) (s t : Fin ρ.dimension → ℂ),
          (l.toCore (projection p)).inner
              (u ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl s)
              (v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl t) =
            h.pairing (projection p) u v *
              ∫ y, k.pairing y ((e s).val.val y) ((e t).val.val y) ∂ν := by
  classical
  -- Descend the integral pairing of the supplied full kernel before choosing any native model.
  obtain ⟨_, _, _, _, lK, hlK, hK⟩ :=
    Q.exists_associatedKernelMetric S F F' σ hσ k hk ν hν ρ e he
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit C) := tensorTopology (E := E) (F := K)
  intro AC
  let l := tensorAtlasMetric h.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas lK hlK
  have hl := tensorAtlasMetric_properties h.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas lK hlK
  have hr (x : B) : Module.finrank ℂ (C x) = a * ρ.dimension := by
    rw [Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin a)) E x,
      (associatedVectorFiberLinearEquiv S.toIsPrincipalBundle ρ.representation x).finrank_eq]
    simp
  -- Both smooth maps and the transported metric refer to this one chosen tensor model.
  obtain ⟨N, hN, hmaps⟩ := AC.exists_native_model_with_atlasMaps (a * ρ.dimension) hr
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  obtain ⟨cIso, heC, hiC⟩ := hmaps
  obtain ⟨kN, hmetric⟩ := AC.exists_native_smoothHermitianMetric l hl.1 N cIso hiC
  refine ⟨l, N, kN, cIso, heC, hiC, hl.1, hN, hmetric, ?_⟩
  intro p u v s t
  exact (hl.2 (projection p) u v _ _).trans
    (congrArg (fun z : ℂ ↦ h.pairing (projection p) u v * z) (hK p (projection p) rfl s t))

end AtiyahSinger
