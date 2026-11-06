/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteHilbertTensorCoordinates
public import AtiyahSinger.Analysis.GradedTensorGraphNaturality

/-!
# Full finite representations of the closed graded tensor kernel and cokernel

Public module ID: M0716.

The original even tensor inclusion and odd tensor quotient map identify the
whole kernel and actual cokernel. The four supplied finite coordinates give
the two ordered sums of tensor representations, with their complete actions.
The factor and adjoint graph assumptions preserve the actual product range,
so the cokernel comparison holds for every original quotient representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {G H₀ H₁ K₀ K₁ : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)

local notation "Even" =>
  WithLp 2 (HilbertTensorProduct H₀ K₀ × HilbertTensorProduct H₁ K₁)
local notation "Odd" =>
  WithLp 2 (HilbertTensorProduct H₁ K₀ × HilbertTensorProduct H₀ K₁)
local notation "KernelEven" =>
  WithLp 2 (HilbertTensorProduct P.ker Q.ker ×
    HilbertTensorProduct P.adjoint.ker Q.adjoint.ker)
local notation "KernelOdd" =>
  WithLp 2 (HilbertTensorProduct P.adjoint.ker Q.ker ×
    HilbertTensorProduct P.ker Q.adjoint.ker)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compare four finite tensor coordinate maps with the specified two full graph decompositions.
/-- The complete graded kernel and actual quotient carry the original tensor representations. -/
theorem exists_gradedTensorKernelCokernel_coordinates
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (hPrange : IsClosed (P.toFun.range : Set H₁))
    (hQrange : IsClosed (Q.toFun.range : Set K₁))
    (A₀ : G → H₀ →L[ℂ] H₀) (A₁ : G → H₁ →L[ℂ] H₁)
    (B₀ : G → K₀ →L[ℂ] K₀) (B₁ : G → K₁ →L[ℂ] K₁)
    (hP : ∀ g z, z ∈ P.graph → (A₀ g z.1, A₁ g z.2) ∈ P.graph)
    (hP' : ∀ g z, z ∈ P.adjoint.graph → (A₁ g z.1, A₀ g z.2) ∈ P.adjoint.graph)
    (hQ : ∀ g z, z ∈ Q.graph → (B₀ g z.1, B₁ g z.2) ∈ Q.graph)
    (hQ' : ∀ g z, z ∈ Q.adjoint.graph → (B₁ g z.1, B₀ g z.2) ∈ Q.adjoint.graph)
    (ρ₀ ρ₁ σ₀ σ₁ : FiniteContinuousRepresentation G)
    (e₀ : (Fin ρ₀.dimension → ℂ) ≃ₗ[ℂ] P.ker)
    (e₁ : (Fin ρ₁.dimension → ℂ) ≃ₗ[ℂ] P.adjoint.ker)
    (f₀ : (Fin σ₀.dimension → ℂ) ≃ₗ[ℂ] Q.ker)
    (f₁ : (Fin σ₁.dimension → ℂ) ≃ₗ[ℂ] Q.adjoint.ker)
    (he₀ : ∀ g v, (e₀ (ρ₀.representation g v)).val = A₀ g (e₀ v).val)
    (he₁ : ∀ g v, (e₁ (ρ₁.representation g v)).val = A₁ g (e₁ v).val)
    (hf₀ : ∀ g v, (f₀ (σ₀.representation g v)).val = B₀ g (f₀ v).val)
    (hf₁ : ∀ g v, (f₁ (σ₁.representation g v)).val = B₁ g (f₁ v).val) :
    let κ := (ρ₀.tensor σ₀).directSum (ρ₁.tensor σ₁)
    let χ := (ρ₁.tensor σ₀).directSum (ρ₀.tensor σ₁)
    let D := gradedTensorOperator P Q
    ∃ e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] D.ker,
      ∃ f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (Odd ⧸ D.toFun.range),
        (∀ g v, (e (κ.representation g v)).val =
          WithLp.toLp 2
            (hilbertTensorMap (A₀ g) (B₀ g) (WithLp.ofLp (e v).val).1,
              hilbertTensorMap (A₁ g) (B₁ g) (WithLp.ofLp (e v).val).2)) ∧
        ∀ (g : G) (v : Odd), f (χ.representation g (f.symm (D.toFun.range.mkQ v))) =
          D.toFun.range.mkQ (WithLp.toLp 2
            (hilbertTensorMap (A₁ g) (B₀ g) (WithLp.ofLp v).1,
              hilbertTensorMap (A₀ g) (B₁ g) (WithLp.ofLp v).2)) := by
  classical
  let κ₀ := ρ₀.tensor σ₀
  let κ₁ := ρ₁.tensor σ₁
  let χ₀ := ρ₁.tensor σ₀
  let χ₁ := ρ₀.tensor σ₁
  let κ := κ₀.directSum κ₁
  let χ := χ₀.directSum χ₁
  let D := gradedTensorOperator P Q
  let R := D.toFun.range
  -- Use each given finite coordinate map and its actual completed subspace inclusion.
  obtain ⟨c₀₀, hc₀₀⟩ := exists_hilbertTensorSubspace_coordinates P.ker Q.ker
    ρ₀ σ₀ A₀ B₀ e₀ f₀ he₀ hf₀
  obtain ⟨c₁₁, hc₁₁⟩ := exists_hilbertTensorSubspace_coordinates P.adjoint.ker Q.adjoint.ker
    ρ₁ σ₁ A₁ B₁ e₁ f₁ he₁ hf₁
  obtain ⟨c₁₀, hc₁₀⟩ := exists_hilbertTensorSubspace_coordinates P.adjoint.ker Q.ker
    ρ₁ σ₀ A₁ B₀ e₁ f₀ he₁ hf₀
  obtain ⟨c₀₁, hc₀₁⟩ := exists_hilbertTensorSubspace_coordinates P.ker Q.adjoint.ker
    ρ₀ σ₁ A₀ B₁ e₀ f₁ he₀ hf₁
  let s (ρ σ : FiniteContinuousRepresentation G) :
      (Fin (ρ.dimension + σ.dimension) → ℂ) ≃ₗ[ℂ]
        (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
    ((ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ)
      finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
        (Fin ρ.dimension) (Fin σ.dimension) (fun _ ↦ ℂ))).toLinearEquiv
  have hs (ρ σ : FiniteContinuousRepresentation G) (g : G)
      (v : Fin (ρ.dimension + σ.dimension) → ℂ) :
      s ρ σ ((ρ.directSum σ).representation g v) =
        (ρ.representation g (s ρ σ v).1, σ.representation g (s ρ σ v).2) := by
    change s ρ σ ((s ρ σ).symm _) = _
    exact (s ρ σ).apply_symm_apply _
  let cE : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] KernelEven :=
    ((s κ₀ κ₁).trans (c₀₀.prodCongr c₁₁)).trans (WithLp.linearEquiv 2 ℂ _).symm
  let cO : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] KernelOdd :=
    ((s χ₀ χ₁).trans (c₁₀.prodCongr c₀₁)).trans (WithLp.linearEquiv 2 ℂ _).symm
  let iE := gradedTensorKernelInclusion P Q
  let iO : KernelOdd →L[ℂ] Odd :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ
        (HilbertTensorProduct H₁ K₀) (HilbertTensorProduct H₀ K₁)).symm.toContinuousLinearMap.comp
      (((hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL).prodMap
        (hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ
          (HilbertTensorProduct P.adjoint.ker Q.ker)
          (HilbertTensorProduct P.ker Q.adjoint.ker)).toContinuousLinearMap)
  let eA := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct H₀ K₀) (HilbertTensorProduct H₁ K₁)
  let oA := WithLp.prodContinuousLinearEquiv 2 ℂ
    (HilbertTensorProduct H₁ K₀) (HilbertTensorProduct H₀ K₁)
  let Ae (g : G) := eA.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap (A₀ g) (B₀ g)).prodMap
      (hilbertTensorMap (A₁ g) (B₁ g))).comp eA.toContinuousLinearMap)
  let Ao (g : G) := oA.symm.toContinuousLinearMap.comp
    (((hilbertTensorMap (A₁ g) (B₀ g)).prodMap
      (hilbertTensorMap (A₀ g) (B₁ g))).comp oA.toContinuousLinearMap)
  have hE (g : G) (v : Fin κ.dimension → ℂ) :
      iE (cE (κ.representation g v)) = Ae g (iE (cE v)) := by
    change WithLp.toLp 2
      (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL
        (c₀₀ (s κ₀ κ₁ (κ.representation g v)).1),
      hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL
        (c₁₁ (s κ₀ κ₁ (κ.representation g v)).2)) = _
    rw [hs]
    apply WithLp.ofLp_injective
    change (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL
        (c₀₀ (κ₀.representation g (s κ₀ κ₁ v).1)),
      hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL
        (c₁₁ (κ₁.representation g (s κ₀ κ₁ v).2))) = _
    rw [hc₀₀, hc₁₁]
    rfl
  have hO (g : G) (v : Fin χ.dimension → ℂ) :
      iO (cO (χ.representation g v)) = Ao g (iO (cO v)) := by
    change WithLp.toLp 2
      (hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL
        (c₁₀ (s χ₀ χ₁ (χ.representation g v)).1),
      hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL
        (c₀₁ (s χ₀ χ₁ (χ.representation g v)).2)) = _
    rw [hs]
    apply WithLp.ofLp_injective
    change (hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL
        (c₁₀ (χ₀.representation g (s χ₀ χ₁ v).1)),
      hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL
        (c₀₁ (χ₁.representation g (s χ₀ χ₁ v).2))) = _
    rw [hc₁₀, hc₀₁]
    rfl
  -- The established whole-domain decompositions now provide genuine linear equivalences.
  obtain ⟨hinj, hrange⟩ := gradedTensorKernelInclusion_decomposition P Q
    hPdense hQdense hPclosed hQclosed
  let k := (LinearEquiv.ofInjective iE.toLinearMap hinj).trans
    (LinearEquiv.ofEq _ _ hrange)
  let q := LinearEquiv.ofBijective (gradedTensorCokernelMap P Q)
    (gradedTensorCokernelMap_decomposition P Q hPdense hQdense
      hPclosed hQclosed hPrange hQrange).2
  let e := cE.trans k
  let f := cO.trans q
  refine ⟨e, f, ?_, ?_⟩
  · intro g v
    exact hE g v
  · -- Every range representative remains in the original range under the odd action.
    have hR (g : G) : R ≤ R.comap (Ao g).toLinearMap := by
      rintro _ ⟨u, rfl⟩
      have hh := gradedTensorOperator_graph_map P Q hPdense hQdense hPclosed hQclosed
        (A₀ g) (A₁ g) (B₀ g) (B₁ g) (hP g) (hP' g) (hQ g) (hQ' g)
        (u.val, D u) (D.mem_graph_iff'.mpr ⟨u, rfl⟩)
      obtain ⟨v, hv⟩ := D.mem_graph_iff'.mp hh
      exact ⟨v, congrArg Prod.snd hv⟩
    let C (g : G) := R.mapQ R (Ao g).toLinearMap (hR g)
    have hf (g : G) (v : Fin χ.dimension → ℂ) :
        f (χ.representation g v) = C g (f v) := by
      change R.mkQ (iO (cO (χ.representation g v))) = R.mkQ (Ao g (iO (cO v)))
      rw [hO]
    intro g v
    rw [hf, f.apply_symm_apply]
    rfl

end AtiyahSinger
