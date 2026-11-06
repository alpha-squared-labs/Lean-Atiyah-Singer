/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveDegreeTwoDetection
public import AtiyahSinger.Topology.ProjectiveLowDegreeCohomology
public import AtiyahSinger.Topology.ProjectivePullbackLifts
public import AtiyahSinger.Topology.ProjectiveSumLines
public import AtiyahSinger.Topology.SupportTensorAction
public import AtiyahSinger.Topology.TrivialLineTensor

/-!
# The normalized first Chern class of a tensor product of lines

Public module ID: M1713.

The tensor formula follows on arbitrary bases by enlarging the two given
lines to projective line bundles. The tensor defect restricts to zero on the
two trivial-summand axes. The two degree-two Leray--Hirsch terms detect this
defect, and the original lines are recovered by their other summand sections.
Every class uses the original complex Thom normalization and every comparison
is an actual continuous complex bundle isomorphism.

Source: the line tensor formula in SG III.11, Note 11.5. The double-projective
argument supplies its extension to arbitrary topological bases without a
classifying-map or CW hypothesis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  hermitianProjectiveTopology hermitianProjectiveLineTopology
  isFiniteRank_hermitianProjectiveLine isFiniteRank_pullback

variable {X : Type u} [TopologicalSpace X]
  (E F : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option maxHeartbeats 1000000 in
-- The two successive native projective models retain their dependent fiber and norm instances.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original normalized first Chern class adds under the specified tensor line Iso. -/
theorem firstChernClass_eq_add_of_tensor
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (hlineE : ∀ x, Module.finrank ℂ (E x) = 1)
    (hlineF : ∀ x, Module.finrank ℂ (F x) = 1)
    {G : X → Type u} [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
    [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
    (hlineG : ∀ x, Module.finrank ℂ (G x) = 1)
    (e : Iso G (fun x ↦ E x ⊗[ℂ] F x)) :
    firstChernClass G hlineG = firstChernClass E hlineE + firstChernClass F hlineF := by
  classical
  let U := Bundle.Trivial X (ULift.{u} ℂ)
  let := modelTopology (ULift.{u} ℂ) U
  let := isFiniteRank_model (ULift.{u} ℂ) U
  let hU := trivialLineMetric X
  have hlineU : ∀ x : X, Module.finrank ℂ (U x) = 1 := by
    intro x
    exact (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).finrank_eq.trans
      (Module.finrank_self ℂ)
  have hUzero : firstChernClass U hlineU = 0 := by
    apply firstChernClass_eq_zero_of_nonvanishing_section U hlineU (fun _ ↦ 1)
    · apply (continuous_modelTotal_iff (ULift.{u} ℂ) U _).mpr
      exact (Bundle.Trivial.homeomorphProd X (ULift.{u} ℂ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    · intro x
      exact one_ne_zero
  -- The two summand projective bundles retain the actual original line fibers and norms.
  let D₁ := E ×ᵇ U
  let D₂ := F ×ᵇ U
  let V := EuclideanSpace ℂ (Fin 2)
  obtain ⟨b₁, v₁, A₁, C₁, hA₁, hC₁, ⟨iE⟩, ⟨iU₁⟩⟩ :=
    exists_hermitianProjective_sum_line_sections E U hE hU hlineE hlineU
  let := nativeModelTopology D₁ V
  let := b₁
  let := v₁
  let h₁ := (hE.sum hU).normedNativeModelMetric D₁ 2
  let Q₁ := HermitianProjectiveBundle 2 D₁ h₁
  let L₁ := HermitianProjectiveLine 2 D₁ h₁
  let p₁ := hermitianProjectiveProjection 2 D₁ h₁
  let s₁ := hermitianProjectiveSection 2 D₁ h₁ A₁ hA₁
  let t₁ := hermitianProjectiveSection 2 D₁ h₁ C₁ hC₁
  obtain ⟨b₂, v₂, A₂, C₂, hA₂, hC₂, ⟨iF⟩, ⟨iU₂⟩⟩ :=
    exists_hermitianProjective_sum_line_sections F U hF hU hlineF hlineU
  let := nativeModelTopology D₂ V
  let := b₂
  let := v₂
  let h₂ := (hF.sum hU).normedNativeModelMetric D₂ 2
  let Q₂ := HermitianProjectiveBundle 2 D₂ h₂
  let L₂ := HermitianProjectiveLine 2 D₂ h₂
  let p₂ := hermitianProjectiveProjection 2 D₂ h₂
  let s₂ := hermitianProjectiveSection 2 D₂ h₂ A₂ hA₂
  let t₂ := hermitianProjectiveSection 2 D₂ h₂ C₂ hC₂
  -- The product over X is the second native projective bundle over the first one.
  let D := (p₁ : Q₁ → X) *ᵖ D₂
  let : ∀ y : Q₁, NormedAddCommGroup (D y) := fun _ ↦ Prod.normedAddCommGroup
  let : ∀ y : Q₁, NormedSpace ℂ (D y) := fun _ ↦ Prod.normedSpace
  let := FiberBundle.pullback (F := V) (E := D₂) p₁
  let := VectorBundle.pullback ℂ (F := V) (E := D₂) p₁
  let h := hermitianProjectivePullbackMetric 2 D₂ h₂ p₁
  let Q := HermitianProjectiveBundle 2 D h
  let q := hermitianProjectiveProjection 2 D h
  let g := hermitianProjectivePullback 2 D₂ h₂ p₁
  let a : C(Q₁, Q) := hermitianProjectivePullbackLift 2 D₂ h₂ p₁
    (ContinuousMap.id Q₁) (fun y ↦ C₂ (p₁ y)) (hC₂.comp p₁.continuous)
  have hQ₂ : Continuous (fun z : Q₂ ↦ (⟨p₂ z, z.2.val⟩ :
      TotalSpace (V →L[ℂ] V) (fun x ↦ D₂ x →L[ℂ] D₂ x))) := by
    have hpair : Continuous (fun z : Q₂ ↦
        (z.1, (⟨z.1, z.2.val⟩ :
          TotalSpace (V →L[ℂ] V) (fun x ↦ D₂ x →L[ℂ] D₂ x)))) :=
      continuous_induced_dom
    exact hpair.snd
  let b : C(Q₂, Q) := hermitianProjectivePullbackLift 2 D₂ h₂ p₁
    (t₁.comp p₂) (fun z ↦ z.2) hQ₂
  let j : C(X, Q) := hermitianProjectivePullbackLift 2 D₂ h₂ p₁ s₁ A₂ hA₂
  -- The tautological factors and their tensor product are the actual algebraic bundles on Q.
  let A := (q : Q → Q₁) *ᵖ L₁
  let B := (g : Q → Q₂) *ᵖ L₂
  let : ∀ z : Q, NormedAddCommGroup (A z) := fun z ↦
    Submodule.normedAddCommGroup (LinearMap.range (q z).2.val.toLinearMap)
  let : ∀ z : Q, NormedSpace ℂ (A z) := fun z ↦
    SubmoduleClass.toNormedSpace (LinearMap.range (q z).2.val.toLinearMap)
  let : ∀ z : Q, NormedAddCommGroup (B z) := fun z ↦
    Submodule.normedAddCommGroup (LinearMap.range (g z).2.val.toLinearMap)
  let : ∀ z : Q, NormedSpace ℂ (B z) := fun z ↦
    SubmoduleClass.toNormedSpace (LinearMap.range (g z).2.val.toLinearMap)
  let : ∀ z : Q, FiniteDimensional ℂ (A z) := fun z ↦ finite_fiber (E := A) z
  let : ∀ z : Q, FiniteDimensional ℂ (B z) := fun z ↦ finite_fiber (E := B) z
  have hAline : ∀ z : Q, Module.finrank ℂ (A z) = 1 := fun z ↦ (q z).2.property.2.1
  have hBline : ∀ z : Q, Module.finrank ℂ (B z) = 1 := fun z ↦ (g z).2.property.2.1
  let T := fun z : Q ↦ A z ⊗[ℂ] B z
  have hTline : ∀ z : Q, Module.finrank ℂ (T z) = 1 := by
    intro z
    exact (Module.finrank_tensorProduct (R := ℂ) (S := ℂ) (M := A z) (M' := B z)).trans
      (by rw [hAline, hBline, one_mul])
  let d (z : Q) : T z ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq (T z) ℂ
    ((hTline z).trans (Module.finrank_self ℂ).symm)
  let : ∀ z : Q, NormedAddCommGroup (T z) := fun z ↦
    NormedAddCommGroup.induced (T z) ℂ (d z).toAddMonoidHom (d z).injective
  let : ∀ z : Q, NormedSpace ℂ (T z) := fun z ↦
    NormedSpace.induced ℂ (T z) ℂ (d z).toLinearMap
  let δ := firstChernClass T hTline - firstChernClass A hAline - firstChernClass B hBline
  -- Naturality and a specified Iso compare classes without changing either fiber norm.
  have hclass {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      (J : Y → Type u) [∀ y, NormedAddCommGroup (J y)] [∀ y, NormedSpace ℂ (J y)]
      [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J]
      (hJ : ∀ y, Module.finrank ℂ (J y) = 1) (f : C(Z, Y))
      {K : Z → Type u} [∀ z, NormedAddCommGroup (K z)] [∀ z, NormedSpace ℂ (K z)]
      [TopologicalSpace (TotalSpace Unit K)] [IsFiniteRank K]
      (hK : ∀ z, Module.finrank ℂ (K z) = 1) (i : Iso ((f : Z → Y) *ᵖ J) K) :
      singularCohomologyPullback ℤ f 2 (firstChernClass J hJ) = firstChernClass K hK := by
    let : ∀ z, NormedAddCommGroup (((f : Z → Y) *ᵖ J) z) :=
      fun z ↦ inferInstanceAs (NormedAddCommGroup (J (f z)))
    let : ∀ z, NormedSpace ℂ (((f : Z → Y) *ᵖ J) z) :=
      fun z ↦ inferInstanceAs (NormedSpace ℂ (J (f z)))
    exact (firstChernClass_pullback J hJ f).symm.trans
      (firstChernClass_eq_of_iso ((f : Z → Y) *ᵖ J) (fun z ↦ hJ (f z)) hK i)
  have hrestrict {Y : Type u} [TopologicalSpace Y] (f : C(Y, Q))
      {P R S : Y → Type u}
      [∀ y, NormedAddCommGroup (P y)] [∀ y, NormedSpace ℂ (P y)]
      [TopologicalSpace (TotalSpace Unit P)] [IsFiniteRank P]
      [∀ y, NormedAddCommGroup (R y)] [∀ y, NormedSpace ℂ (R y)]
      [TopologicalSpace (TotalSpace Unit R)] [IsFiniteRank R]
      [∀ y, NormedAddCommGroup (S y)] [∀ y, NormedSpace ℂ (S y)]
      [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S]
      (hP : ∀ y, Module.finrank ℂ (P y) = 1)
      (hR : ∀ y, Module.finrank ℂ (R y) = 1)
      (hS : ∀ y, Module.finrank ℂ (S y) = 1)
      (iA : Iso ((f : Y → Q) *ᵖ A) P) (iB : Iso ((f : Y → Q) *ᵖ B) R)
      (iS : Iso S (fun y ↦ P y ⊗[ℂ] R y)) :
      singularCohomologyPullback ℤ f 2 δ =
        firstChernClass S hS - firstChernClass P hP - firstChernClass R hR := by
    let iT := ((pullbackTensorIso (E := A) (F := B) f).trans
      (iA.tensor iB)).trans iS.symm
    change singularCohomologyPullback ℤ f 2
      (firstChernClass T hTline - firstChernClass A hAline - firstChernClass B hBline) = _
    rw [map_sub, map_sub, hclass T hTline f hS iT, hclass A hAline f hP iA,
      hclass B hBline f hR iB]
  let U₁ := (p₁ : Q₁ → X) *ᵖ U
  let U₂ := (p₂ : Q₂ → X) *ᵖ U
  let : ∀ y : Q₁, NormedAddCommGroup (U₁ y) := fun _ ↦ ULift.normedAddCommGroup
  let : ∀ y : Q₁, NormedSpace ℂ (U₁ y) := fun _ ↦ ULift.normedSpace
  let : ∀ y : Q₂, NormedAddCommGroup (U₂ y) := fun _ ↦ ULift.normedAddCommGroup
  let : ∀ y : Q₂, NormedSpace ℂ (U₂ y) := fun _ ↦ ULift.normedSpace
  have hU₁line : ∀ y : Q₁, Module.finrank ℂ (U₁ y) = 1 := fun y ↦ hlineU (p₁ y)
  have hU₂line : ∀ y : Q₂, Module.finrank ℂ (U₂ y) = 1 := fun y ↦ hlineU (p₂ y)
  have hL₁line : ∀ y : Q₁, Module.finrank ℂ (L₁ y) = 1 := fun y ↦ y.2.property.2.1
  have hL₂line : ∀ y : Q₂, Module.finrank ℂ (L₂ y) = 1 := fun y ↦ y.2.property.2.1
  have hU₁zero : firstChernClass U₁ hU₁line = 0 := by
    rw [firstChernClass_pullback U hlineU p₁, hUzero, map_zero]
  have hU₂zero : firstChernClass U₂ hU₂line = 0 := by
    rw [firstChernClass_pullback U hlineU p₂, hUzero, map_zero]
  -- The comparisons use the same summand sections that define the two axes.
  let iaA : Iso ((a : Q₁ → Q) *ᵖ A) L₁ :=
    (pullbackCompIso (E := L₁) q a).trans (pullbackIdIso (E := L₁))
  let iaB : Iso ((a : Q₁ → Q) *ᵖ B) U₁ :=
    ((pullbackCompIso (E := L₂) g a).trans
      (pullbackCompIso (E := L₂) t₂ p₁).symm).trans (iU₂.pullback p₁)
  let ibA : Iso ((b : Q₂ → Q) *ᵖ A) U₂ :=
    ((pullbackCompIso (E := L₁) q b).trans
      (pullbackCompIso (E := L₁) t₁ p₂).symm).trans (iU₁.pullback p₂)
  let ibB : Iso ((b : Q₂ → Q) *ᵖ B) L₂ :=
    (pullbackCompIso (E := L₂) g b).trans (pullbackIdIso (E := L₂))
  let := modelTopology (ULift.{u} ℂ) (Bundle.Trivial Q₁ (ULift.{u} ℂ))
  let := isFiniteRank_model (ULift.{u} ℂ) (Bundle.Trivial Q₁ (ULift.{u} ℂ))
  let := modelTopology (ULift.{u} ℂ) (Bundle.Trivial Q₂ (ULift.{u} ℂ))
  let := isFiniteRank_model (ULift.{u} ℂ) (Bundle.Trivial Q₂ (ULift.{u} ℂ))
  let iaT : Iso L₁ (fun y ↦ L₁ y ⊗[ℂ] U₁ y) :=
    (tensorTrivialLineIso L₁).symm.trans
      ((Iso.refl L₁).tensor (pullbackTrivialLineIso p₁).symm)
  let ibT : Iso L₂ (fun y ↦ U₂ y ⊗[ℂ] L₂ y) :=
    (trivialLineTensorIso L₂).symm.trans
      ((pullbackTrivialLineIso p₂).symm.tensor (Iso.refl L₂))
  have hδa : singularCohomologyPullback ℤ a 2 δ = 0 := by
    rw [hrestrict a hL₁line hU₁line hL₁line iaA iaB iaT, hU₁zero, sub_self, sub_zero]
  have hδb : singularCohomologyPullback ℤ b 2 δ = 0 := by
    rw [hrestrict b hU₂line hL₂line hL₂line ibA ibB ibT, hU₂zero, sub_zero, sub_self]
  -- Degree-two Leray--Hirsch and degree-zero pullback rule out every remaining coefficient.
  let η := firstChernClass B hBline
  let τ := hermitianProjectiveChernRoot 2 D₂ h₂
  have hη : η = hermitianProjectiveChernRoot 2 D h :=
    (firstChernClass_pullback L₂ hL₂line g).trans
      (hermitianProjectiveChernRoot_pullback 2 D₂ h₂ p₁)
  have hηa : singularCohomologyPullback ℤ a 2 η = 0 :=
    (hclass B hBline a hU₁line iaB).trans hU₁zero
  have hηb : singularCohomologyPullback ℤ b 2 η = τ :=
    hclass B hBline b hL₂line ibB
  have hq := singularCohomology_two_term_bijective_of_powerCombination ℤ q
    (hermitianProjectiveChernRoot 2 D h)
    (hermitianProjectivePowerCombination_int_bijective 2 D h 1
      (fun i ↦ Nat.le_of_lt_succ i.isLt))
  have hp₂ := singularCohomology_two_term_bijective_of_powerCombination ℤ p₂ τ
    (hermitianProjectivePowerCombination_int_bijective 2 D₂ h₂ 1
      (fun i ↦ Nat.le_of_lt_succ i.isLt))
  have hδ : δ = 0 := by
    apply singularCohomology_eq_zero_of_projective_axes ℤ p₁ p₂ q a b rfl rfl
      η τ hηa hηb
      (hermitianProjectiveProjection_cohomologyZero_bijective ℤ 2 D₁ h₁ (by decide)).surjective
      _ hp₂.injective δ hδa hδb
    intro c
    obtain ⟨⟨c₀, c₁⟩, hc⟩ := hq.surjective c
    exact ⟨c₀, c₁, by simpa only [hη] using hc.symm⟩
  -- The other pair of summand sections returns the original three prescribed line bundles.
  let ijA : Iso ((j : X → Q) *ᵖ A) E := (pullbackCompIso (E := L₁) q j).trans iE
  let ijB : Iso ((j : X → Q) *ᵖ B) F := (pullbackCompIso (E := L₂) g j).trans iF
  have hz := hrestrict j hlineE hlineF hlineG ijA ijB e
  rw [hδ, map_zero] at hz
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_sub_sub] using hz.symm

end AtiyahSinger.ComplexBundle
