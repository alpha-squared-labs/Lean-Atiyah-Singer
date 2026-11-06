/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Geometry.SpinCliffordSymbol
public import AtiyahSinger.Geometry.SpinComplexificationFrameSymbol
public import AtiyahSinger.Topology.SpinorTensorExteriorParity

/-!
# The original positive spin tensor block and the exterior parity symbol

Public module ID: M1464.

Both spin factors use the same principal frame. The original reciprocal
normalization makes the reverse Clifford blocks negative. Consequently the
positive product block is intertwined with the exterior symbol after the
specified minus sign on the second source summand. The comparison below
retains the original bundle isomorphisms and canonical complexified metric.

Source: SG I.5 and III.12, the graded Clifford tensor construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.sumTopology ComplexBundle.tensorTopology ComplexBundle.exteriorTopology
  ComplexBundle.exteriorParityTopology

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

set_option maxHeartbeats 2000000 in
-- Keep the original associated, tensor and parity instances in the two pure-tensor comparisons.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original positive reciprocal spin product has the prescribed exterior parity symbol. -/
theorem TopologicalSpinStructure.exists_spinorTensor_exteriorParity_symbol_iso
    (S : TopologicalSpinStructure m E o hm hP)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t)) :
    letI := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    letI := ComplexBundle.exteriorParityTopology (E := fun b ↦ ℂ ⊗[ℝ] E b) (m : ZMod 2)
    letI := ComplexBundle.exteriorParityTopology (E := fun b ↦ ℂ ⊗[ℝ] E b) ((m : ZMod 2) + 1)
    let H := HalfSpinorBundle m hP
    let Q (i : ZMod 2) := fun b ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] E b)) i
    ∃ d₀ : ComplexBundle.Iso
        ((fun b ↦ H 0 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 1 b ⊗[ℂ] H 1 b))
        (fun b ↦ Q (m : ZMod 2) b),
      ∃ d₁ : ComplexBundle.Iso
          ((fun b ↦ H 1 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 0 b ⊗[ℂ] H 1 b))
          (fun b ↦ Q ((m : ZMod 2) + 1) b),
        ∀ (b : B) (v w : E b) (z : (H 0 b ⊗[ℂ] H 0 b) × (H 1 b ⊗[ℂ] H 1 b)),
          letI := (complexificationHermitianCore (E b)).toNormedAddCommGroup
          letI := InnerProductSpace.ofCore (complexificationHermitianCore (E b)).toCore
          d₁.linearEquiv b
              (reciprocalTensorSymbol (S.cliffordParity b v 0) (-(S.cliffordParity b v 1))
                (S.cliffordParity b w 0) (-(S.cliffordParity b w 1)) z) =
            cliffordSymbolParity ((1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w) (m : ZMod 2)
              (d₀.linearEquiv b (z.1, -z.2)) := by
  classical
  let := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := ComplexBundle.exteriorParityTopology (E := fun b ↦ ℂ ⊗[ℝ] E b) (m : ZMod 2)
  let := ComplexBundle.exteriorParityTopology (E := fun b ↦ ℂ ⊗[ℝ] E b) ((m : ZMod 2) + 1)
  obtain ⟨d₀, d₁, h₀, h₁⟩ := S.exists_spinorTensor_exteriorParity_iso e he
  refine ⟨d₀, d₁, ?_⟩
  intro b v w z
  let := (complexificationHermitianCore (E b)).toNormedAddCommGroup
  let := InnerProductSpace.ofCore (complexificationHermitianCore (E b)).toCore
  let V := EuclideanSpace ℂ (Fin m)
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
  let H := HalfSpinorBundle m hP
  let p : P := (hP.projection_properties.2.2 b).choose
  have hp : projection p = b := (hP.projection_properties.2.2 b).choose_spec
  let x := realSpinorCoordinateIsometry m ((S.frame p b hp).symm v)
  let y := realSpinorCoordinateIsometry m ((S.frame p b hp).symm w)
  let ξ : ℂ ⊗[ℝ] E b := (1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w
  let Φ := complexSpinorDoublingExteriorEquiv m e
  let ext := ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
  let mk (i : ZMod 2) := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p hp
  have hmk (i : ZMod 2) (u : E b) (s : W i) :
      S.cliffordParity b u i (mk i s) =
        mk (i + 1) (cliffordSymbolParity
          (realSpinorCoordinateIsometry m ((S.frame p b hp).symm u)) i s) :=
    S.cliffordParity_apply_mk p b hp u i s
  have hγ₀ (s : W 0) : complexSpinorChirality m s.val = s.val := by
    rw [complexSpinorChirality_eq_involute]
    exact CliffordAlgebra.involute_eq_of_mem_even s.property
  have hγ₁ (s : W 1) : complexSpinorChirality m s.val = -s.val := by
    rw [complexSpinorChirality_eq_involute]
    exact CliffordAlgebra.involute_eq_of_mem_odd s.property
  -- The original frame sends the real and imaginary coordinates to the specified two vectors.
  have hsymbol (q : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
      ext (Φ ((TensorProduct.map (cliffordSymbol x)
        (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
        TensorProduct.map (complexSpinorChirality m) (cliffordSymbol y)) q)) =
          cliffordSymbol ξ (ext (Φ q)) := by
    have h := S.complexificationFrame_symbol e he p b hp x y q
    simpa only [x, y, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, ξ, ext, Φ] using h
  let G₀ := (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] E b))
    (m : ZMod 2)).subtype.comp (d₀.linearEquiv b).toLinearMap
  let G₁ := (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (ℂ ⊗[ℝ] E b))
    ((m : ZMod 2) + 1)).subtype.comp (d₁.linearEquiv b).toLinearMap
  have hG₀ (s t : W 0) : G₀ (mk 0 s ⊗ₜ[ℂ] mk 0 t, 0) = ext (Φ (s.val ⊗ₜ[ℂ] t.val)) := by
    have h := h₀ b p hp s t 0 0
    change G₀ (mk 0 s ⊗ₜ[ℂ] mk 0 t, mk 1 0 ⊗ₜ[ℂ] mk 1 0) =
      ext (Φ (s.val ⊗ₜ[ℂ] t.val + (0 : W 1).val ⊗ₜ[ℂ] (0 : W 1).val)) at h
    simpa only [map_zero, Submodule.coe_zero, TensorProduct.zero_tmul, add_zero] using h
  have hG₀' (s t : W 1) : G₀ (0, mk 1 s ⊗ₜ[ℂ] mk 1 t) = ext (Φ (s.val ⊗ₜ[ℂ] t.val)) := by
    have h := h₀ b p hp 0 0 s t
    change G₀ (mk 0 0 ⊗ₜ[ℂ] mk 0 0, mk 1 s ⊗ₜ[ℂ] mk 1 t) =
      ext (Φ ((0 : W 0).val ⊗ₜ[ℂ] (0 : W 0).val + s.val ⊗ₜ[ℂ] t.val)) at h
    simpa only [map_zero, Submodule.coe_zero, TensorProduct.zero_tmul, zero_add] using h
  have hG₁ (s₁ t₁ : W 1) (s₀ t₀ : W 0) :
      G₁ (mk 1 s₁ ⊗ₜ[ℂ] mk 0 t₀, mk 0 s₀ ⊗ₜ[ℂ] mk 1 t₁) =
        ext (Φ (s₁.val ⊗ₜ[ℂ] t₀.val + s₀.val ⊗ₜ[ℂ] t₁.val)) :=
    h₁ b p hp s₁ t₁ s₀ t₀
  let D := reciprocalTensorSymbol (S.cliffordParity b v 0) (-(S.cliffordParity b v 1))
    (S.cliffordParity b w 0) (-(S.cliffordParity b w 1))
  let J : ((H 0 b ⊗[ℂ] H 0 b) × (H 1 b ⊗[ℂ] H 1 b)) →ₗ[ℂ]
      ((H 0 b ⊗[ℂ] H 0 b) × (H 1 b ⊗[ℂ] H 1 b)) :=
    (LinearMap.id : _ →ₗ[ℂ] _).prodMap (-LinearMap.id)
  -- Compare the even-even and odd-odd source blocks on their original pure representatives.
  have hcompare : G₁.comp D = (cliffordSymbol ξ).comp (G₀.comp J) := by
    apply LinearMap.prod_ext
    · apply TensorProduct.ext'
      intro a c
      obtain ⟨s, rfl⟩ := (mk 0).surjective a
      obtain ⟨t, rfl⟩ := (mk 0).surjective c
      change G₁ (D (mk 0 s ⊗ₜ[ℂ] mk 0 t, 0)) =
        cliffordSymbol ξ (G₀ (mk 0 s ⊗ₜ[ℂ] mk 0 t, -0))
      simp only [D, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, map_zero, add_zero, neg_zero, TensorProduct.map_tmul,
        LinearMap.id_apply]
      rw [hmk, hmk]
      change G₁ (mk 1 (cliffordSymbolParity x 0 s) ⊗ₜ[ℂ] mk 0 t,
        mk 0 s ⊗ₜ[ℂ] mk 1 (cliffordSymbolParity y 0 t)) =
          cliffordSymbol ξ (G₀ (mk 0 s ⊗ₜ[ℂ] mk 0 t, 0))
      rw [hG₁, hG₀]
      have h := hsymbol (s.val ⊗ₜ[ℂ] t.val)
      simpa only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        hγ₀, cliffordSymbolParity, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply] using h
    · apply TensorProduct.ext'
      intro a c
      obtain ⟨s, rfl⟩ := (mk 1).surjective a
      obtain ⟨t, rfl⟩ := (mk 1).surjective c
      change G₁ (D (0, mk 1 s ⊗ₜ[ℂ] mk 1 t)) =
        cliffordSymbol ξ (G₀ (0, -(mk 1 s ⊗ₜ[ℂ] mk 1 t)))
      simp only [D, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, LinearMap.neg_apply, map_zero, zero_add, TensorProduct.map_tmul,
        LinearMap.id_apply]
      change G₁ (-(mk 1 s ⊗ₜ[ℂ] (-(S.cliffordParity b w 1 (mk 1 t)))),
        (-(S.cliffordParity b v 1 (mk 1 s))) ⊗ₜ[ℂ] mk 1 t) =
          cliffordSymbol ξ (G₀ (0, -(mk 1 s ⊗ₜ[ℂ] mk 1 t)))
      rw [TensorProduct.tmul_neg, neg_neg, TensorProduct.neg_tmul, hmk, hmk]
      change G₁ (mk 1 s ⊗ₜ[ℂ] mk 0 (cliffordSymbolParity y 1 t),
        -(mk 0 (cliffordSymbolParity x 1 s) ⊗ₜ[ℂ] mk 1 t)) =
          cliffordSymbol ξ (G₀ (0, -(mk 1 s ⊗ₜ[ℂ] mk 1 t)))
      have hleft := hG₁ s t (-(cliffordSymbolParity x 1 s)) (cliffordSymbolParity y 1 t)
      simp only [map_neg, TensorProduct.neg_tmul, Submodule.coe_neg] at hleft
      rw [hleft]
      have hright : G₀ (0, -(mk 1 s ⊗ₜ[ℂ] mk 1 t)) =
          -(ext (Φ (s.val ⊗ₜ[ℂ] t.val))) := by
        have h := congrArg Neg.neg (hG₀' s t)
        simpa only [← map_neg, Prod.neg_mk, neg_zero] using h
      rw [hright, map_neg]
      have h := hsymbol (s.val ⊗ₜ[ℂ] t.val)
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        hγ₁] at h
      change ext (Φ (s.val ⊗ₜ[ℂ] cliffordSymbol y t.val +
        -(cliffordSymbol x s.val ⊗ₜ[ℂ] t.val))) = _
      erw [TensorProduct.neg_tmul] at h
      have hneg : s.val ⊗ₜ[ℂ] cliffordSymbol y t.val +
          -(cliffordSymbol x s.val ⊗ₜ[ℂ] t.val) =
          -(cliffordSymbol x s.val ⊗ₜ[ℂ] t.val +
            -(s.val ⊗ₜ[ℂ] cliffordSymbol y t.val)) := by abel
      rw [hneg, map_neg, map_neg, h]
  -- Equality in the original parity subtype follows from the full exterior-value comparison.
  apply Subtype.ext
  exact LinearMap.congr_fun hcompare z

end AtiyahSinger
