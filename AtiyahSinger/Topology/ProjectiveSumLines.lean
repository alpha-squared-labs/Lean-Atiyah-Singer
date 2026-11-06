/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianMetricSum
public import AtiyahSinger.Topology.NormedFixedRankModel
public import AtiyahSinger.Topology.ProjectiveLineSections

/-!
# The two line sections in the projectivization of a sum

Public module ID: M2025.

The two original summands of a sum of complex line bundles give actual
sections of its Hermitian projective bundle. Their pulled-back tautological
lines are identified with the specified original summands by projection.
The native projective model preserves the supplied fiber norms.

Source: the projectivization of line subbundles, Hatcher, Vector Bundles and
K-Theory, Sections 1.1 and 3.1. The result includes the actual bundle maps
needed to restrict tensor products along these sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- Retype a metric to a native model while retaining the originally supplied fiber norms. -/
def ContinuousHermitianMetric.normedNativeModelMetric (h : ContinuousHermitianMetric E)
    (r : ℕ) :
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E := by
  let form := h.toCore
  have hpair := h.continuous_pairing
  have hfinite := h.isFiniteRank
  have ht := ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := E) r
  dsimp only at ht
  letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  refine { toCore := form, continuous_pairing := ?_, isFiniteRank := ?_ }
  · rw [ht]
    exact hpair
  · -- Transport the original finite-rank charts along the exact total-topology equality.
    exact Eq.mpr
      (congrArg (fun t : TopologicalSpace (TotalSpace Unit E) ↦
        @IsFiniteRank X _ E _ _ t) ht) hfinite

variable (F : X → Type u)
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank E] [IsFiniteRank F]

attribute [local instance] sumTopology isFiniteRank_sum
  hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine isFiniteRank_pullback
  InnerProductSpace.Core.toPreInner'

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original summands give projective sections with their actual tautological line Isos. -/
theorem exists_hermitianProjective_sum_line_sections
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (hlineE : ∀ x, Module.finrank ℂ (E x) = 1)
    (hlineF : ∀ x, Module.finrank ℂ (F x) = 1) :
    letI := nativeModelTopology (E ×ᵇ F) (EuclideanSpace ℂ (Fin 2))
    ∃ b : FiberBundle (EuclideanSpace ℂ (Fin 2)) (E ×ᵇ F),
      letI := b
      ∃ v : VectorBundle ℂ (EuclideanSpace ℂ (Fin 2)) (E ×ᵇ F),
        letI := v
        let h := (hE.sum hF).normedNativeModelMetric (E ×ᵇ F) 2
        let Q := HermitianProjectiveBundle 2 (E ×ᵇ F) h
        let L := HermitianProjectiveLine 2 (E ×ᵇ F) h
        ∃ a c : letI := modelTopology (EuclideanSpace ℂ (Fin 2)) (E ×ᵇ F)
            ∀ x, HermitianProjectiveSpace (E x × F x) (h.toCore x),
          ∃ ha : Continuous (fun x ↦ (⟨x, (a x).val⟩ :
              TotalSpace (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
                (fun x ↦ (E x × F x) →L[ℂ] (E x × F x)))),
            ∃ hc : Continuous (fun x ↦ (⟨x, (c x).val⟩ :
                TotalSpace (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
                  (fun x ↦ (E x × F x) →L[ℂ] (E x × F x)))),
              let s := hermitianProjectiveSection 2 (E ×ᵇ F) h a ha
              let t := hermitianProjectiveSection 2 (E ×ᵇ F) h c hc
              Nonempty (Iso ((s : X → Q) *ᵖ L) E) ∧
                Nonempty (Iso ((t : X → Q) *ᵖ L) F) := by
  let D := E ×ᵇ F
  let V := EuclideanSpace ℂ (Fin 2)
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ finite_fiber (E := F) x
  have hdim : ∀ x, Module.finrank ℂ (D x) = 2 := by
    intro x
    change Module.finrank ℂ (E x × F x) = 2
    rw [Module.finrank_prod, hlineE, hlineF]
  obtain ⟨b, v⟩ := exists_nativeFiberBundle_of_normedFibers D 2 hdim
  let := nativeModelTopology D V
  let := b
  let := v
  refine ⟨b, v, ?_⟩
  let h := (hE.sum hF).normedNativeModelMetric D 2
  let form := (hE.sum hF).toCore
  -- Both projectors are the original coordinate projections followed by inclusions.
  let a (x : X) : D x →L[ℂ] D x :=
    ((LinearMap.inl ℂ (E x) (F x)).comp (LinearMap.fst ℂ (E x) (F x))).toContinuousLinearMap
  let c (x : X) : D x →L[ℂ] D x :=
    ((LinearMap.inr ℂ (E x) (F x)).comp (LinearMap.snd ℂ (E x) (F x))).toContinuousLinearMap
  have ha_range (x : X) : Function.Bijective
      ((LinearMap.fst ℂ (E x) (F x)).comp (LinearMap.range (a x).toLinearMap).subtype) := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      have hz : z.val.2 = 0 := by
        obtain ⟨z', hz'⟩ := z.property
        exact (congrArg Prod.snd hz').symm
      have hw : w.val.2 = 0 := by
        obtain ⟨w', hw'⟩ := w.property
        exact (congrArg Prod.snd hw').symm
      exact Prod.ext hzw (hz.trans hw.symm)
    · intro z
      exact ⟨⟨(z, 0), ⟨(z, 0), rfl⟩⟩, rfl⟩
  have hc_range (x : X) : Function.Bijective
      ((LinearMap.snd ℂ (E x) (F x)).comp (LinearMap.range (c x).toLinearMap).subtype) := by
    constructor
    · intro z w hzw
      apply Subtype.ext
      have hz : z.val.1 = 0 := by
        obtain ⟨z', hz'⟩ := z.property
        exact (congrArg Prod.fst hz').symm
      have hw : w.val.1 = 0 := by
        obtain ⟨w', hw'⟩ := w.property
        exact (congrArg Prod.fst hw').symm
      exact Prod.ext (hz.trans hw.symm) hzw
    · intro z
      exact ⟨⟨(0, z), ⟨(0, z), rfl⟩⟩, rfl⟩
  have hzeroE (x : X) (z : E x) :
      (hE.toCore x).inner 0 z = 0 ∧ (hE.toCore x).inner z 0 = 0 := by
    let := hE.toCore x
    exact ⟨InnerProductSpace.Core.inner_zero_left z, InnerProductSpace.Core.inner_zero_right z⟩
  have hzeroF (x : X) (z : F x) :
      (hF.toCore x).inner 0 z = 0 ∧ (hF.toCore x).inner z 0 = 0 := by
    let := hF.toCore x
    exact ⟨InnerProductSpace.Core.inner_zero_left z, InnerProductSpace.Core.inner_zero_right z⟩
  let A (x : X) : HermitianProjectiveSpace (D x) (form x) :=
    ⟨a x, by
      refine ⟨?_, ?_, ?_⟩
      · apply ContinuousLinearMap.ext
        intro z
        rfl
      · exact (LinearEquiv.ofBijective _ (ha_range x)).finrank_eq.trans (hlineE x)
      · intro z w
        change (hE.toCore x).inner z.1 w.1 + (hF.toCore x).inner 0 w.2 =
          (hE.toCore x).inner z.1 w.1 + (hF.toCore x).inner z.2 0
        rw [(hzeroF x w.2).1, (hzeroF x z.2).2]⟩
  let C (x : X) : HermitianProjectiveSpace (D x) (form x) :=
    ⟨c x, by
      refine ⟨?_, ?_, ?_⟩
      · apply ContinuousLinearMap.ext
        intro z
        rfl
      · exact (LinearEquiv.ofBijective _ (hc_range x)).finrank_eq.trans (hlineF x)
      · intro z w
        change (hE.toCore x).inner 0 w.1 + (hF.toCore x).inner z.2 w.2 =
          (hE.toCore x).inner z.1 0 + (hF.toCore x).inner z.2 w.2
        rw [(hzeroE x w.1).1, (hzeroE x z.1).2]⟩
  -- Continuity is checked in the original sum topology and then in the native Hom bundle.
  have ha_total : Continuous (fun z : TotalSpace V D ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace V D)) := by
    exact (nativeModelTotalHomeomorph D V).symm.continuous.comp
      ((continuous_sum_inl (E := E) (F := F)).comp
        ((continuous_sum_fst (E := E) (F := F)).comp
          (nativeModelTotalHomeomorph D V).continuous))
  have hc_total : Continuous (fun z : TotalSpace V D ↦
      (⟨z.proj, c z.proj z.snd⟩ : TotalSpace V D)) := by
    exact (nativeModelTotalHomeomorph D V).symm.continuous.comp
      ((continuous_sum_inr (E := E) (F := F)).comp
        ((continuous_sum_snd (E := E) (F := F)).comp
          (nativeModelTotalHomeomorph D V).continuous))
  have ha := continuous_nativeEndomorphismSection 2 D a ha_total
  have hc := continuous_nativeEndomorphismSection 2 D c hc_total
  have ht := ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := D) 2
  dsimp only at ht
  let e : letI := modelTopology V D; Hom D E := by
    letI := modelTopology V D
    exact {
      linearMap x := LinearMap.fst ℂ (E x) (F x)
      continuous_total := by
        rw [ht]
        exact continuous_sum_fst }
  let f : letI := modelTopology V D; Hom D F := by
    letI := modelTopology V D
    exact {
      linearMap x := LinearMap.snd ℂ (E x) (F x)
      continuous_total := by
        rw [ht]
        exact continuous_sum_snd }
  have he : letI := modelTopology V D
      ∀ x, Function.Bijective
        ((e.linearMap x).comp (LinearMap.range (A x).val.toLinearMap).subtype) := by
    intro x
    change Function.Bijective
      ((LinearMap.fst ℂ (E x) (F x)).comp (LinearMap.range (a x).toLinearMap).subtype)
    exact ha_range x
  have hf : letI := modelTopology V D
      ∀ x, Function.Bijective
        ((f.linearMap x).comp (LinearMap.range (C x).val.toLinearMap).subtype) := by
    intro x
    change Function.Bijective
      ((LinearMap.snd ℂ (E x) (F x)).comp (LinearMap.range (c x).toLinearMap).subtype)
    exact hc_range x
  refine ⟨A, C, ha, hc, ?_, ?_⟩
  · exact ⟨hermitianProjectiveSectionLineIso 2 D h A ha e he⟩
  · exact ⟨hermitianProjectiveSectionLineIso 2 D h C hc f hf⟩

end AtiyahSinger.ComplexBundle
