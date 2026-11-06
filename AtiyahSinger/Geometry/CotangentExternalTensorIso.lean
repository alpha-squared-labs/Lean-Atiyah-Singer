/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ExternalTensorBundle
public import AtiyahSinger.Geometry.ProductCovectorCoordinates
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# The original external tensor bundles under the cotangent product splitting

Public module ID: M1148.

The actual cotangent product homeomorphism identifies the product of the two
cotangent projection pullbacks with the projection pullback of the external
tensor bundle. Every comparison preserves each tensor vector; continuity uses
the original induced pullback and finite-rank tensor topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_pullback

variable {n m r s : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  (E : M → Type*) (F : N → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]

omit [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F] in
/-- Retyping the native external tensor topology back to Unit gives the original tensor topology. -/
theorem modelTopology_externalTensor :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    letI := externalTensorTopology (r := r) (s := s) E F
    modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) =
      tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := externalTensorTopology (r := r) (s := s) E F
  change TopologicalSpace.induced
    (fun z : TotalSpace Unit (externalTensorFiber E F) ↦
      (⟨z.proj, z.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin (r * s)))
        (externalTensorFiber E F)))
    (TopologicalSpace.induced
      (fun z : TotalSpace (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F) ↦
        (⟨z.proj, z.snd⟩ : TotalSpace Unit (externalTensorFiber E F)))
      (tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F))) = _
  rw [induced_compose]
  exact @induced_id (TotalSpace Unit (externalTensorFiber E F))
    (tensorTopology (E := Prod.fst *ᵖ E) (F := Prod.snd *ᵖ F))

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

set_option maxHeartbeats 1800000 in
-- The original tensor and three iterated pullbacks require explicit dependent transports.
set_option maxRecDepth 4096 in
/-- The prescribed cotangent splitting preserves each original external tensor vector. -/
theorem exists_cotangentExternalTensorIso :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin s)) F
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    let pM := cotangentProjection (n := n) (M := M)
    let pN := cotangentProjection (n := m) (M := N)
    let p := cotangentProjection (n := n + m) (M := M × N)
    let c := cotangentProductHomeomorph (n := n) (m := m) M N
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) (externalTensorFiber E F)
    let := tensorTopology (E := Prod.fst *ᵖ (pM *ᵖ E))
      (F := Prod.snd *ᵖ (pN *ᵖ F))
    ∃ a : Iso ((c : _ → _) *ᵖ (fun z :
        CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N) ↦
        ((Prod.fst : _ → CotangentTotalSpace (n := n) (M := M)) *ᵖ
          ((pM : _ → M) *ᵖ E)) z ⊗[ℂ]
        ((Prod.snd : _ → CotangentTotalSpace (n := m) (M := N)) *ᵖ
          ((pN : _ → N) *ᵖ F)) z))
      ((p : _ → M × N) *ᵖ (externalTensorFiber E F)),
      ∀ z v, HEq (a.linearEquiv z v) v := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin s)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin s)) F
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorTopology (r := r) (s := s) E F
  have htop := modelTopology_externalTensor (r := r) (s := s) E F
  dsimp only
  rw [htop]
  let pM := cotangentProjection (n := n) (M := M)
  let pN := cotangentProjection (n := m) (M := N)
  let p := cotangentProjection (n := n + m) (M := M × N)
  let c₀ : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    ⟨cotangentProductHomeomorph (n := n) (m := m) M N,
      (cotangentProductHomeomorph (n := n) (m := m) M N).continuous⟩
  let fM : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := n) (M := M)) :=
    ContinuousMap.fst
  let fN : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), CotangentTotalSpace (n := m) (M := N)) :=
    ContinuousMap.snd
  let qM : C(M × N, M) := ContinuousMap.fst
  let qN : C(M × N, N) := ContinuousMap.snd
  let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    { toFun := fun z ↦
        (⟨z.proj.1, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩,
        ⟨z.proj.2, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩)
      continuous_toFun := c₀.continuous.congr cotangentProductHomeomorph_apply }
  have hc : c₀ = c := ContinuousMap.ext cotangentProductHomeomorph_apply
  let := tensorTopology (E := fM *ᵖ (pM *ᵖ E)) (F := fN *ᵖ (pN *ᵖ F))
  change ∃ a : Iso (c₀ *ᵖ (fun z ↦
      (fM *ᵖ (pM *ᵖ E)) z ⊗[ℂ] (fN *ᵖ (pN *ᵖ F)) z))
    (p *ᵖ (fun x ↦ (qM *ᵖ E) x ⊗[ℂ] (qN *ᵖ F) x)),
    ∀ z w, HEq (a.linearEquiv z w) w
  rw [hc]
  -- Rewrite the original map by its proved formula before comparing dependent fibers.
  let u := (pullbackCompIso (E := pM *ᵖ E) fM c).trans
    ((pullbackCompIso (E := E) pM (fM.comp c)).trans
      (pullbackCompIso (E := E) qM p).symm)
  let v := (pullbackCompIso (E := pN *ᵖ F) fN c).trans
    ((pullbackCompIso (E := F) pN (fN.comp c)).trans
      (pullbackCompIso (E := F) qN p).symm)
  have hu (z : CotangentTotalSpace (n := n + m) (M := M × N)) (w : E z.proj.1) :
      u.linearEquiv z w = w := by
    apply (pullbackCompIso (E := E) qM p).linearEquiv z |>.injective
    change (pullbackCompIso (E := E) qM p).linearEquiv z
      (((pullbackCompIso (E := E) qM p).linearEquiv z).symm
        ((pullbackCompIso (E := E) pM (fM.comp c)).linearEquiv z
          ((pullbackCompIso (E := pM *ᵖ E) fM c).linearEquiv z w))) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply,
      pullbackCompIso_apply]
  have hv (z : CotangentTotalSpace (n := n + m) (M := M × N)) (w : F z.proj.2) :
      v.linearEquiv z w = w := by
    apply (pullbackCompIso (E := F) qN p).linearEquiv z |>.injective
    change (pullbackCompIso (E := F) qN p).linearEquiv z
      (((pullbackCompIso (E := F) qN p).linearEquiv z).symm
        ((pullbackCompIso (E := F) pN (fN.comp c)).linearEquiv z
          ((pullbackCompIso (E := pN *ᵖ F) fN c).linearEquiv z w))) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply,
      pullbackCompIso_apply]
  -- Tensor and pullback reassociation retain arbitrary tensor vectors, not only pure tensors.
  let := tensorTopology (E := c *ᵖ (fM *ᵖ (pM *ᵖ E)))
    (F := c *ᵖ (fN *ᵖ (pN *ᵖ F)))
  let := tensorTopology (E := p *ᵖ (qM *ᵖ E)) (F := p *ᵖ (qN *ᵖ F))
  let a := (pullbackTensorIso (E := fM *ᵖ (pM *ᵖ E))
    (F := fN *ᵖ (pN *ᵖ F)) c).trans
      ((u.tensor v).trans (pullbackTensorIso (E := qM *ᵖ E) (F := qN *ᵖ F) p).symm)
  refine ⟨a, ?_⟩
  intro z w
  have hu' : u.linearEquiv z = LinearEquiv.refl ℂ (E z.proj.1) := LinearEquiv.ext (hu z)
  have hv' : v.linearEquiv z = LinearEquiv.refl ℂ (F z.proj.2) := LinearEquiv.ext (hv z)
  apply heq_of_eq
  change TensorProduct.congr (u.linearEquiv z) (v.linearEquiv z) w = w
  rw [hu', hv']
  exact LinearEquiv.congr_fun
    (TensorProduct.congr_refl_refl (R := ℂ) (M := E z.proj.1) (N := F z.proj.2)) w

end AtiyahSinger
