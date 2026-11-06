/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorDoublingParity
public import AtiyahSinger.Topology.SpinorTensorExterior

/-!
# Parity restrictions of the original spinor tensor bundle isomorphism

Public module ID: M2179.

The actual half-spin associated bundles include into the full spinor bundle
through its specified parity splitting. Composing their tensor inclusions
with the original full doubling isomorphism gives continuous maps into the
native exterior bundle. The algebraic parity restrictions prove that these
very maps have the shifted parity ranges and are bijective on each fiber.
The induced parity topology and finite local rank provide inverse continuity.
Every displayed formula uses one common principal representative and its
original complexification frame.

Source: SG I.5 and II.3, the graded self-tensor and associated-bundle models.
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

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original self-tensor isomorphism restricts to the actual half-spin tensor bundles. -/
theorem TopologicalSpinStructure.exists_spinorTensor_exteriorParity_iso
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
        ((fun b ↦ H 0 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 1 b ⊗[ℂ] H 1 b)) (fun b ↦ Q (m : ZMod 2) b),
      ∃ d₁ : ComplexBundle.Iso
          ((fun b ↦ H 1 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 0 b ⊗[ℂ] H 1 b))
          (fun b ↦ Q ((m : ZMod 2) + 1) b),
        (∀ (b : B) (p : P) (hp : projection p = b)
          (s₀ t₀ : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 0)
          (s₁ t₁ : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 1),
          (d₀.linearEquiv b
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp s₀ ⊗ₜ[ℂ]
                associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp t₀,
              associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp s₁ ⊗ₜ[ℂ]
                associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp t₁)).val =
            ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
              (complexSpinorDoublingExteriorEquiv m e
                (s₀.val ⊗ₜ[ℂ] t₀.val + s₁.val ⊗ₜ[ℂ] t₁.val))) ∧
        ∀ (b : B) (p : P) (hp : projection p = b)
          (s₁ t₁ : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 1)
          (s₀ t₀ : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 0),
          (d₁.linearEquiv b
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp s₁ ⊗ₜ[ℂ]
                associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp t₀,
              associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) p hp s₀ ⊗ₜ[ℂ]
                associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) p hp t₁)).val =
            ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
              (complexSpinorDoublingExteriorEquiv m e
                (s₁.val ⊗ₜ[ℂ] t₀.val + s₀.val ⊗ₜ[ℂ] t₁.val)) := by
  classical
  let V := EuclideanSpace ℂ (Fin m)
  let U := V × V
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
  let H := HalfSpinorBundle m hP
  let A := SpinorBundle m hP
  let C (b : B) := ℂ ⊗[ℝ] E b
  let F (b : B) := ExteriorAlgebra ℂ (C b)
  let Q (i : ZMod 2) := fun b ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C b)) i
  let R (b : B) := A b ⊗[ℂ] A b
  let ρ := complexSpinContRepresentation m
  let σ := complexSpinParityContRepresentation m
  let Φ := complexSpinorDoublingExteriorEquiv m e
  let := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := ComplexBundle.exteriorParityTopology (E := C) (m : ZMod 2)
  let := ComplexBundle.exteriorParityTopology (E := C) ((m : ZMod 2) + 1)
  let := ComplexBundle.isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let := ComplexBundle.isFiniteRank_exterior (E := C)
  let (i : ZMod 2) := ComplexBundle.isFiniteRank_exteriorParity (E := C) i
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinRepresentation m)
  let (i : ZMod 2) := isFiniteRank_associatedVector hP (σ i)
    (continuous_complexSpinParityRepresentation m i)
  let (i j : ZMod 2) := ComplexBundle.isFiniteRank_tensor (E := H i) (F := H j)
  let := ComplexBundle.isFiniteRank_tensor (E := A) (F := A)
  let := ComplexBundle.isFiniteRank_sum (E := H 0) (F := H 1)
  let A₀ := (fun b ↦ H 0 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 1 b ⊗[ℂ] H 1 b)
  let A₁ := (fun b ↦ H 1 b ⊗[ℂ] H 0 b) ×ᵇ (fun b ↦ H 0 b ⊗[ℂ] H 1 b)
  let := ComplexBundle.isFiniteRank_sum (E := fun b ↦ H 0 b ⊗[ℂ] H 0 b)
    (F := fun b ↦ H 1 b ⊗[ℂ] H 1 b)
  let := ComplexBundle.isFiniteRank_sum (E := fun b ↦ H 1 b ⊗[ℂ] H 0 b)
    (F := fun b ↦ H 0 b ⊗[ℂ] H 1 b)
  obtain ⟨d, hd⟩ := S.exists_spinorTensor_exterior_iso e he
  obtain ⟨L₀, L₁, hL₀, hL₁⟩ := exists_complexSpinorDoublingParity_equiv m e he
  -- Include both native half-spin bundles through the specified full parity splitting.
  let split := spinorBundleParityIso m hP
  let i₀ : ComplexBundle.Hom (H 0) A := split.symm.toHom.comp
    (ComplexBundle.sumInl (E := H 0) (F := H 1))
  let i₁ : ComplexBundle.Hom (H 1) A := split.symm.toHom.comp
    (ComplexBundle.sumInr (E := H 0) (F := H 1))
  have hi₀ (b : B) (p : P) (hp : projection p = b) (s : W 0) :
      i₀.linearMap b (associatedVectorFiberMk hP (σ 0) p hp s) =
        associatedVectorFiberMk hP ρ p hp s.val := by
    have hs : exteriorParityEquiv V s.val = (s, 0) := by
      apply (exteriorParityEquiv V).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      change s.val = s.val + 0
      simp
    have hsplit := spinorBundleParityIso_apply m hP p b hp s.val
    rw [hs] at hsplit
    have hz : associatedVectorFiberMk hP (σ 1) p hp 0 = 0 :=
      (associatedVectorFiberMkLinearEquiv hP (σ 1) p hp).map_zero
    rw [hz] at hsplit
    change (split.linearEquiv b).symm (_, 0) = _
    exact (split.linearEquiv b).symm_apply_eq.mpr hsplit.symm
  have hi₁ (b : B) (p : P) (hp : projection p = b) (s : W 1) :
      i₁.linearMap b (associatedVectorFiberMk hP (σ 1) p hp s) =
        associatedVectorFiberMk hP ρ p hp s.val := by
    have hs : exteriorParityEquiv V s.val = (0, s) := by
      apply (exteriorParityEquiv V).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      change s.val = 0 + s.val
      simp
    have hsplit := spinorBundleParityIso_apply m hP p b hp s.val
    rw [hs] at hsplit
    have hz : associatedVectorFiberMk hP (σ 0) p hp 0 = 0 :=
      (associatedVectorFiberMkLinearEquiv hP (σ 0) p hp).map_zero
    rw [hz] at hsplit
    change (split.linearEquiv b).symm (0, _) = _
    exact (split.linearEquiv b).symm_apply_eq.mpr hsplit.symm
  -- Addition is taken over one unchanged base point in the native tensor total space.
  let sumHom (i j k l : ZMod 2)
      (a : ComplexBundle.Hom (fun b ↦ H i b ⊗[ℂ] H j b) R)
      (b : ComplexBundle.Hom (fun b ↦ H k b ⊗[ℂ] H l b) R) :
      ComplexBundle.Hom
        ((fun b ↦ H i b ⊗[ℂ] H j b) ×ᵇ (fun b ↦ H k b ⊗[ℂ] H l b)) R := by
    let D := (fun b ↦ H i b ⊗[ℂ] H j b) ×ᵇ (fun b ↦ H k b ⊗[ℂ] H l b)
    let := ComplexBundle.isFiniteRank_sum (E := fun b ↦ H i b ⊗[ℂ] H j b)
      (F := fun b ↦ H k b ⊗[ℂ] H l b)
    refine ⟨fun x ↦ (a.linearMap x).coprod (b.linearMap x), ?_⟩
    let f : C(TotalSpace Unit D, B) := ⟨π Unit D, ComplexBundle.continuous_proj⟩
    let := ComplexBundle.isFiniteRank_pullback (E := R) f
    let c : ∀ z : TotalSpace Unit D, (f *ᵖ R) z := fun z ↦ a.linearMap z.proj z.snd.1
    let d : ∀ z : TotalSpace Unit D, (f *ᵖ R) z := fun z ↦ b.linearMap z.proj z.snd.2
    have hc : Continuous (fun z ↦ (⟨z, c z⟩ : TotalSpace Unit (f *ᵖ R))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit R f).continuous_iff]
      exact continuous_id.prodMk (a.continuous_total.comp ComplexBundle.continuous_sum_fst)
    have hd : Continuous (fun z ↦ (⟨z, d z⟩ : TotalSpace Unit (f *ᵖ R))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit R f).continuous_iff]
      exact continuous_id.prodMk (b.continuous_total.comp ComplexBundle.continuous_sum_snd)
    exact (Pullback.continuous_lift Unit R f).comp
      (ComplexBundle.continuous_add_section (f *ᵖ R) c d hc hd)
  let K₀ := d.toHom.comp (sumHom 0 0 1 1 (i₀.tensor i₀) (i₁.tensor i₁))
  let K₁ := d.toHom.comp (sumHom 1 0 0 1 (i₁.tensor i₀) (i₀.tensor i₁))
  let mk (i : ZMod 2) (b : B) (p : P) (hp : projection p = b) :=
    associatedVectorFiberMkLinearEquiv hP (σ i) p hp
  let coord₀ (b : B) (p : P) (hp : projection p = b) :=
    (TensorProduct.congr (mk 0 b p hp) (mk 0 b p hp)).prodCongr
      (TensorProduct.congr (mk 1 b p hp) (mk 1 b p hp))
  let coord₁ (b : B) (p : P) (hp : projection p = b) :=
    (TensorProduct.congr (mk 1 b p hp) (mk 0 b p hp)).prodCongr
      (TensorProduct.congr (mk 0 b p hp) (mk 1 b p hp))
  have htensor (i j : ZMod 2) (u : ComplexBundle.Hom (H i) A)
      (v : ComplexBundle.Hom (H j) A)
      (hu : ∀ b p hp s, u.linearMap b (associatedVectorFiberMk hP (σ i) p hp s) =
        associatedVectorFiberMk hP ρ p hp s.val)
      (hv : ∀ b p hp s, v.linearMap b (associatedVectorFiberMk hP (σ j) p hp s) =
        associatedVectorFiberMk hP ρ p hp s.val)
      (b : B) (p : P) (hp : projection p = b) (z : W i ⊗[ℂ] W j) :
      d.linearEquiv b (TensorProduct.map (u.linearMap b) (v.linearMap b)
        (TensorProduct.congr (mk i b p hp) (mk j b p hp) z)) =
        ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
          (Φ (TensorProduct.map (W i).subtype (W j).subtype z)) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s t =>
      simp only [TensorProduct.congr_tmul, TensorProduct.map_tmul, Submodule.subtype_apply]
      change d.linearEquiv b
        (u.linearMap b (associatedVectorFiberMk hP (σ i) p hp s) ⊗ₜ[ℂ]
          v.linearMap b (associatedVectorFiberMk hP (σ j) p hp t)) = _
      rw [hu, hv]
      exact hd b p hp s.val t.val
  have hK₀ (b : B) (p : P) (hp : projection p = b)
      (z : (W 0 ⊗[ℂ] W 0) × (W 1 ⊗[ℂ] W 1)) :
      K₀.linearMap b (coord₀ b p hp z) =
        ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
          (Φ (TensorProduct.map (W 0).subtype (W 0).subtype z.1 +
            TensorProduct.map (W 1).subtype (W 1).subtype z.2)) := by
    change d.linearEquiv b
      (TensorProduct.map (i₀.linearMap b) (i₀.linearMap b)
          (TensorProduct.congr (mk 0 b p hp) (mk 0 b p hp) z.1) +
        TensorProduct.map (i₁.linearMap b) (i₁.linearMap b)
          (TensorProduct.congr (mk 1 b p hp) (mk 1 b p hp) z.2)) = _
    rw [map_add, htensor 0 0 i₀ i₀ hi₀ hi₀, htensor 1 1 i₁ i₁ hi₁ hi₁,
      ← map_add, ← map_add]
  have hK₁ (b : B) (p : P) (hp : projection p = b)
      (z : (W 1 ⊗[ℂ] W 0) × (W 0 ⊗[ℂ] W 1)) :
      K₁.linearMap b (coord₁ b p hp z) =
        ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
          (Φ (TensorProduct.map (W 1).subtype (W 0).subtype z.1 +
            TensorProduct.map (W 0).subtype (W 1).subtype z.2)) := by
    change d.linearEquiv b
      (TensorProduct.map (i₁.linearMap b) (i₀.linearMap b)
          (TensorProduct.congr (mk 1 b p hp) (mk 0 b p hp) z.1) +
        TensorProduct.map (i₀.linearMap b) (i₁.linearMap b)
          (TensorProduct.congr (mk 0 b p hp) (mk 1 b p hp) z.2)) = _
    rw [map_add, htensor 1 0 i₁ i₀ hi₁ hi₀, htensor 0 1 i₀ i₁ hi₀ hi₁,
      ← map_add, ← map_add]
  -- The same complexification frame restricts to each native exterior parity carrier.
  let ext (i : ZMod 2) (b : B) (p : P) (hp : projection p = b) :
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U) i ≃ₗ[ℂ] Q i b := by
    let f := S.complexificationFrame p b hp
    -- Both frame directions preserve parity by mapping each exterior generator to a generator.
    have hforward : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U) i).map
        (ExteriorAlgebra.map f.toLinearMap).toLinearMap ≤ Q i b := by
      simp only [Q, CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      apply iSup_mono
      intro k
      gcongr
      rintro z ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨f u, (ExteriorAlgebra.map_apply_ι f.toLinearMap u).symm⟩
    have hbackward : (Q i b).map (ExteriorAlgebra.map f.symm.toLinearMap).toLinearMap ≤
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U) i := by
      simp only [Q, CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
      apply iSup_mono
      intro k
      gcongr
      rintro z ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨f.symm u, (ExteriorAlgebra.map_apply_ι f.symm.toLinearMap u).symm⟩
    let L := ((ExteriorAlgebra.map f.toLinearMap).toLinearMap.comp
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ U) i).subtype).codRestrict (Q i b)
        (fun x ↦ hforward ⟨x.val, x.property, rfl⟩)
    refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      refine ExteriorAlgebra.map_injective (f := f.toLinearMap) ⟨f.symm.toLinearMap, ?_⟩ ?_
      · apply LinearMap.ext
        intro v
        exact f.symm_apply_apply v
      · exact congrArg Subtype.val hxy
    · intro y
      refine ⟨⟨ExteriorAlgebra.map f.symm.toLinearMap y.val,
        hbackward ⟨y.val, y.property, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change ExteriorAlgebra.map f.toLinearMap
        (ExteriorAlgebra.map f.symm.toLinearMap y.val) = y.val
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      have hf : f.toLinearMap.comp f.symm.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro v
        exact f.apply_symm_apply v
      rw [hf, ExteriorAlgebra.map_id, AlgHom.id_apply]
  let p (b : B) : P := (hP.projection_properties.2.2 b).choose
  have hp (b : B) : projection (p b) = b := (hP.projection_properties.2.2 b).choose_spec
  let l₀ (b : B) := (coord₀ b (p b) (hp b)).symm.trans
    (L₀.trans (ext (m : ZMod 2) b (p b) (hp b)))
  let l₁ (b : B) := (coord₁ b (p b) (hp b)).symm.trans
    (L₁.trans (ext ((m : ZMod 2) + 1) b (p b) (hp b)))
  have hl₀ (b : B) (z : A₀ b) : (l₀ b z).val = K₀.linearMap b z := by
    change ExteriorAlgebra.map (S.complexificationFrame (p b) b (hp b)).toLinearMap
      (L₀ ((coord₀ b (p b) (hp b)).symm z)).val = _
    rw [hL₀]
    have hz := hK₀ b (p b) (hp b) ((coord₀ b (p b) (hp b)).symm z)
    rw [LinearEquiv.apply_symm_apply] at hz
    exact hz.symm
  have hl₁ (b : B) (z : A₁ b) : (l₁ b z).val = K₁.linearMap b z := by
    change ExteriorAlgebra.map (S.complexificationFrame (p b) b (hp b)).toLinearMap
      (L₁ ((coord₁ b (p b) (hp b)).symm z)).val = _
    rw [hL₁]
    have hz := hK₁ b (p b) (hp b) ((coord₁ b (p b) (hp b)).symm z)
    rw [LinearEquiv.apply_symm_apply] at hz
    exact hz.symm
  -- The native parity topology is induced by inclusion; the continuous forward maps determine it.
  let D₀ : ComplexBundle.Hom A₀ (fun b ↦ Q (m : ZMod 2) b) :=
    { linearMap b := (l₀ b).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply K₀.continuous_total.congr
        intro z
        apply TotalSpace.ext
        · rfl
        exact heq_of_eq (hl₀ z.proj z.snd).symm }
  let D₁ : ComplexBundle.Hom A₁ (fun b ↦ Q ((m : ZMod 2) + 1) b) :=
    { linearMap b := (l₁ b).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply K₁.continuous_total.congr
        intro z
        apply TotalSpace.ext
        · rfl
        exact heq_of_eq (hl₁ z.proj z.snd).symm }
  refine ⟨D₀.toIso (fun b ↦ (l₀ b).bijective), D₁.toIso (fun b ↦ (l₁ b).bijective), ?_, ?_⟩
  · intro b q hq s₀ t₀ s₁ t₁
    change (l₀ b _).val = _
    rw [hl₀]
    have hz := hK₀ b q hq (s₀ ⊗ₜ[ℂ] t₀, s₁ ⊗ₜ[ℂ] t₁)
    simp only [coord₀, LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
      TensorProduct.map_tmul, Submodule.subtype_apply] at hz
    exact hz
  · intro b q hq s₁ t₁ s₀ t₀
    change (l₁ b _).val = _
    rw [hl₁]
    have hz := hK₁ b q hq (s₁ ⊗ₜ[ℂ] t₀, s₀ ⊗ₜ[ℂ] t₁)
    simp only [coord₁, LinearEquiv.prodCongr_apply, TensorProduct.congr_tmul,
      TensorProduct.map_tmul, Submodule.subtype_apply] at hz
    exact hz

end AtiyahSinger
