/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveSumLines

/-!
# Extending an actual line to a larger projective bundle

Public module ID: M2015.

The first summand of a line bundle plus any fixed-rank bundle defines an actual
section of its Hermitian projective bundle. The pullback of the original
tautological range is identified with the original line via the first coordinate.
Taking a trivial complement gives projective extensions of arbitrarily large
fiber dimension for stable-degree characteristic-class comparisons.

The construction uses the original sum, supplied metrics and native topology.
It generalizes the first section of the existing two-line sum construction;
it neither replaces that construction nor assumes any Thom-defect identity.

Source: the projectivization of an actual line subbundle, Hatcher, Vector Bundles
and K-Theory, Sections 1.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X]
  (E F : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] sumTopology isFiniteRank_sum hermitianProjectiveTopology
  hermitianProjectiveLineTopology isFiniteRank_hermitianProjectiveLine isFiniteRank_pullback
  InnerProductSpace.Core.toPreInner'

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A line summand is isomorphic to the tautological pullback along its projective section. -/
theorem exists_hermitianProjective_sum_line_section (n : ℕ)
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (hline : ∀ x, Module.finrank ℂ (E x) = 1)
    (hrank : ∀ x, Module.finrank ℂ (F x) = n) :
    letI := nativeModelTopology (E ×ᵇ F) (EuclideanSpace ℂ (Fin (1 + n)))
    ∃ b : FiberBundle (EuclideanSpace ℂ (Fin (1 + n))) (E ×ᵇ F),
      letI := b
      ∃ v : VectorBundle ℂ (EuclideanSpace ℂ (Fin (1 + n))) (E ×ᵇ F),
        letI := v
        let h := (hE.sum hF).normedNativeModelMetric (E ×ᵇ F) (1 + n)
        let Q := HermitianProjectiveBundle (1 + n) (E ×ᵇ F) h
        let L := HermitianProjectiveLine (1 + n) (E ×ᵇ F) h
        ∃ s : C(X, Q),
          (hermitianProjectiveProjection (1 + n) (E ×ᵇ F) h).comp s = ContinuousMap.id X ∧
            Nonempty (Iso ((s : X → Q) *ᵖ L) E) := by
  let D := E ×ᵇ F
  let V := EuclideanSpace ℂ (Fin (1 + n))
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ finite_fiber (E := F) x
  have hdim : ∀ x, Module.finrank ℂ (D x) = 1 + n := by
    intro x
    change Module.finrank ℂ (E x × F x) = 1 + n
    rw [Module.finrank_prod, hline, hrank]
  obtain ⟨b, v⟩ := exists_nativeFiberBundle_of_normedFibers D (1 + n) hdim
  let := nativeModelTopology D V
  let := b
  let := v
  refine ⟨b, v, ?_⟩
  let h := (hE.sum hF).normedNativeModelMetric D (1 + n)
  let form := (hE.sum hF).toCore
  -- Project onto the original line summand; its range coordinate is the first projection.
  let a (x : X) : D x →L[ℂ] D x :=
    ((LinearMap.inl ℂ (E x) (F x)).comp (LinearMap.fst ℂ (E x) (F x))).toContinuousLinearMap
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
      · exact (LinearEquiv.ofBijective _ (ha_range x)).finrank_eq.trans (hline x)
      · intro z w
        change (hE.toCore x).inner z.1 w.1 + (hF.toCore x).inner 0 w.2 =
          (hE.toCore x).inner z.1 w.1 + (hF.toCore x).inner z.2 0
        rw [(hzeroF x w.2).1, (hzeroF x z.2).2]⟩
  -- Native Hom continuity is the transported continuity of these same coordinate operations.
  have ha_total : Continuous (fun z : TotalSpace V D ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace V D)) := by
    exact (nativeModelTotalHomeomorph D V).symm.continuous.comp
      ((continuous_sum_inl (E := E) (F := F)).comp
        ((continuous_sum_fst (E := E) (F := F)).comp
          (nativeModelTotalHomeomorph D V).continuous))
  have ha := continuous_nativeEndomorphismSection (1 + n) D a ha_total
  have ht := ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := D) (1 + n)
  dsimp only at ht
  let e : letI := modelTopology V D; Hom D E := by
    letI := modelTopology V D
    exact {
      linearMap x := LinearMap.fst ℂ (E x) (F x)
      continuous_total := by
        rw [ht]
        exact continuous_sum_fst }
  have he : letI := modelTopology V D
      ∀ x, Function.Bijective
        ((e.linearMap x).comp (LinearMap.range (A x).val.toLinearMap).subtype) := by
    intro x
    change Function.Bijective
      ((LinearMap.fst ℂ (E x) (F x)).comp (LinearMap.range (a x).toLinearMap).subtype)
    exact ha_range x
  -- Restrict the actual tautological range, rather than merely identifying its Chern class.
  let s := hermitianProjectiveSection (1 + n) D h A ha
  exact ⟨s, rfl, ⟨hermitianProjectiveSectionLineIso (1 + n) D h A ha e he⟩⟩

end AtiyahSinger.ComplexBundle
