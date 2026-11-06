/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocallyConstantSingularCohomology
public import AtiyahSinger.Topology.RelativeCohomologyUnionCup
public import AtiyahSinger.Topology.RelativeEvaluationRationalization
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality

/-!
# Zero-dimensional local cup evaluation

Public module ID: M1948.

The positive original zero-dimensional orientation cycle evaluates the constant-one
class to one. Its rationalization therefore supplies the exact scalar by which a
local zero-dimensional class acts on relative cohomology of another space.
The supports, constant projection and degree identification remain explicit.

Source: the degree-zero unit and Kronecker pairing, Hatcher, Algebraic Topology,
Section 3.2. The normalization is checked on the original signed affine simplex.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The zero-dimensional factor acts by evaluation on its specified positive local cycle. -/
theorem relativeSingularCohomologyUnionCup_zero_evaluation
    {W : Type u} [TopologicalSpace W]
    (b₀ : Module.Basis (Fin 0) ℝ (ULift.{u} (Fin 0 → ℝ)))
    (B : Set W) (hB : IsOpen B) (r : ℕ)
    (a : relativeSingularCohomology ℚ
      (Set.ofPred (fun v : ULift.{u} (Fin 0 → ℝ) ↦ v ≠ 0)) 0)
    (b : relativeSingularCohomology ℚ B r) (c : relativeSingularHomology ℚ B r) :
    let V := ULift.{u} (Fin 0 → ℝ)
    let P : Set V := {v | v ≠ 0}
    let f : C(W, V) := ContinuousMap.const W 0
    let A : Set W := f ⁻¹' P
    (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ B) r
      ((eqToIso (congrArg (fun k ↦ relativeSingularCohomology ℚ B k)
        (Nat.zero_add r))).hom
        (relativeSingularCohomologyRestriction ℚ B (A ∪ B)
          (fun _ hb ↦ Or.inr hb) (0 + r)
          (relativeSingularCohomologyUnionCup ℚ A B
            (isOpen_ne.preimage f.continuous) hB 0 r
            (relativeSingularCohomologyPullback ℚ f
              (show Set.MapsTo f A P from fun _ hx ↦ hx) 0 a) b))) c).down =
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ P) 0 a
        (relativeSingularHomologyRationalization P 0
          (realOrientationCycle b₀ b₀.orientation))).down *
        (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ B) r b c).down := by
  classical
  dsimp only
  let V := ULift.{u} (Fin 0 → ℝ)
  let P : Set V := {v | v ≠ 0}
  let f : C(W, V) := ContinuousMap.const W 0
  let A : Set W := f ⁻¹' P
  let z := realOrientationCycle b₀ b₀.orientation
  let zQ := relativeSingularHomologyRationalization P 0 z
  let ε := singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ P) 0
  let aZ : relativeSingularCohomology ℤ P 0 :=
    relativeLocallyConstantSingularCohomologyClass ℤ V P (LocallyConstant.const V 1)
      (fun v hv ↦ False.elim (hv (Subsingleton.elim _ _)))
  let aQ := relativeSingularCohomologyRationalization P 0 aZ
  have honeZ : relativeSingularCohomologyToOrdinary ℤ P 0 aZ =
      singularCohomologyOne ℤ V := by
    rw [relativeLocallyConstantSingularCohomologyClass_toOrdinary,
      locallyConstantSingularCohomologyClass_const, one_smul]
  -- The same positive zero-simplex represents the original local orientation cycle.
  have hnormZ : (singularCochainHomologyEvaluation ℤ
      (relativeSingularChains ℤ P) 0 aZ z).down = 1 := by
    let S := TopCat.toSSet.obj (TopCat.of V)
    let C := singularChains ℤ V
    let π := relativeSingularChainsProjection ℤ P
    let σ := realOrientationSimplex b₀
    let d : (C.sc 0).moduleCatLeftHomologyData.K :=
      ⟨S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1), by
        change C.dFrom 0 _ = 0
        simp⟩
    let h : C.homology 0 :=
      (C.sc 0).moduleCatHomologyIso.inv ((C.sc 0).moduleCatLeftHomologyData.π d)
    have hmap : homologyMap π 0 h = z := by
      apply homologyMap_cycleClass ℤ C (relativeSingularChains ℤ P) π 0 d
        ⟨realOrientationRelativeChain b₀ b₀.orientation,
          realOrientationRelativeChain_mem_cycles b₀ b₀.orientation⟩
      simp only [realOrientationRelativeChain, ite_true]
      rfl
    rw [← hmap, singularCochainHomologyEvaluation_naturality]
    change (singularCochainHomologyEvaluation ℤ C 0
      (relativeSingularCohomologyToOrdinary ℤ P 0 aZ) h).down = 1
    rw [honeZ]
    have hvalue := singularCochainHomologyEvaluation_cycleClass ℤ C 0
      (singularCocycleOne ℤ V) d
    change singularCochainHomologyEvaluation ℤ C 0 (singularCohomologyOne ℤ V) h = _
      at hvalue
    rw [hvalue]
    change (singularCochainEquiv ℤ V 0 (singularCochainOne ℤ V) σ).down = 1
    simp only [singularCochainOne, LinearEquiv.apply_symm_apply]
    rfl
  -- Both the original unit and its evaluation survive the same coefficient map.
  have honeQ : relativeSingularCohomologyToOrdinary ℚ P 0 aQ =
      singularCohomologyOne ℚ V := by
    rw [← relativeSingularCohomologyRationalization_toOrdinary, honeZ,
      singularCohomologyRationalization_one]
  have hnormQ : (ε aQ zQ).down = 1 := by
    exact (singularCochainHomologyEvaluation_rationalization P 0 aZ z).trans
      (by rw [hnormZ]; norm_num)
  -- Every zero-cochain on this one-point space is a constant; identify its actual scalar.
  let e := singularCohomologyZeroEquiv ℚ V
  let τ := realOrientationSimplex b₀
  let aO := relativeSingularCohomologyToOrdinary ℚ P 0 a
  let t := (singularCochainEquiv ℚ V 0 (e aO).val τ).down
  have hclass (α : singularCocycles ℚ V 0) :
      e (singularCocycleClass ℚ V 0 α) = α := by
    rw [← singularCohomologyZeroEquiv_symm_apply]
    exact e.apply_symm_apply α
  have haO : aO = t • singularCohomologyOne ℚ V := by
    apply e.injective
    apply Subtype.ext
    apply (singularCochainEquiv ℚ V 0).injective
    funext σ
    have hστ : σ = τ := by
      apply ULift.ext
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro v
      exact Subsingleton.elim _ _
    subst σ
    rw [map_smul, singularCohomologyOne, hclass]
    change singularCochainEquiv ℚ V 0 (e aO).val τ =
      singularCochainEquiv ℚ V 0 (t • singularCochainOne ℚ V) τ
    rw [map_smul]
    change _ = t • singularCochainEquiv ℚ V 0 (singularCochainOne ℚ V) τ
    simp only [singularCochainOne, LinearEquiv.apply_symm_apply]
    apply ULift.ext
    exact (mul_one t).symm
  have ha : a = t • aQ := by
    let S := singularSubspaceCochainsSequence ℚ P
    have := (shortExact_singularSubspaceCochains ℚ P).mono_f
    have hmono : Mono (homologyMap S.f 0) :=
      mono_homologyMap_of_mono_of_not_rel _ _ (by simp)
    apply (ModuleCat.mono_iff_injective (homologyMap S.f 0)).mp hmono
    change aO = relativeSingularCohomologyToOrdinary ℚ P 0 (t • aQ)
    rw [map_smul, honeQ, haO]
  have ht : (ε a zQ).down = t := by
    rw [ha, map_smul]
    change t * (ε aQ zQ).down = t
    rw [hnormQ, mul_one]
  -- Forgetting the empty factor support turns its pullback into this scalar times one.
  have hf : Set.MapsTo f A P := fun _ hx ↦ hx
  have hpull : relativeSingularCohomologyToOrdinary ℚ A 0
      (relativeSingularCohomologyPullback ℚ f hf 0 a) =
        t • singularCohomologyOne ℚ W := by
    have hnat := congrArg (fun g ↦ g a)
      (relativeSingularCohomologyPullback_toOrdinary ℚ f hf 0)
    change relativeSingularCohomologyToOrdinary ℚ A 0
      (relativeSingularCohomologyPullback ℚ f hf 0 a) =
        singularCohomologyPullback ℚ f 0 aO at hnat
    rw [hnat, haO, map_smul, singularCohomologyPullback_one]
  rw [relativeSingularCohomologyUnionCup_restrict_right, hpull, map_smul]
  simp only [LinearMap.smul_apply, map_smul]
  rw [relativeSingularCohomologyAction_one]
  change t * (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ B) r b c).down =
    (ε a zQ).down *
      (singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ B) r b c).down
  rw [ht]

end AtiyahSinger
