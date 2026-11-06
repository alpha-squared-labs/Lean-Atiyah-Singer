/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequence
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Relative classes over a contractible product factor

Public module ID: M2060.

A relative class on a product with a contractible base is the pullback of its
restriction to any specified fiber. The subspace is the full product with the
given fiber subspace. The homotopy keeps that fiber coordinate unchanged, so the
claim uses the actual pair maps, with no local system or chosen generator.

Source: homotopy invariance of relative cohomology, Hatcher, Algebraic Topology,
Sections 2.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A relative class over a contractible base is pulled back from any one of its fibers. -/
theorem relativeSingularCohomology_prod_eq_pullback_fiber (R : Type) [CommRing R]
    {X Y : Type u} [TopologicalSpace X] [ContractibleSpace X] [TopologicalSpace Y]
    (x : X) (A : Set Y) (k : ℕ)
    (a : relativeSingularCohomology R {z : X × Y | z.2 ∈ A} k) :
    relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
      (A := {z : X × Y | z.2 ∈ A}) (B := A) (fun _ hz ↦ hz) k
      (relativeSingularCohomologyPullback R
        (⟨fun y ↦ (x, y), continuous_const.prodMk continuous_id⟩ : C(Y, X × Y))
        (A := A) (B := {z : X × Y | z.2 ∈ A}) (fun _ hy ↦ hy) k a) = a := by
  obtain ⟨p, ⟨H⟩⟩ := id_nullhomotopic X
  -- Retarget the contraction to the specified x, without selecting another fiber.
  let Hx : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x) :=
    H.trans (H.symm.compContinuousMap (ContinuousMap.const X x))
  let pr : C(X × Y, Y) := ContinuousMap.snd
  let s : C(Y, X × Y) := ⟨fun y ↦ (x, y), continuous_const.prodMk continuous_id⟩
  let B : Set (X × Y) := {z | z.2 ∈ A}
  let Hprod : (s.comp pr).Homotopy (ContinuousMap.id (X × Y)) :=
    Hx.symm.prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id Y))
  have hpr (j : ℕ) : IsIso (singularCohomologyPullback R pr j) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R pr s
      ⟨Hprod⟩ ⟨ContinuousMap.Homotopy.refl _⟩ j
  let prA : C(B, A) :=
    ⟨fun z ↦ ⟨z.val.2, z.property⟩,
      (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  let sA : C(A, B) :=
    ⟨fun y ↦ ⟨(x, y.val), y.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  -- The same contraction preserves B at every time because its second coordinate is fixed.
  let HA : (sA.comp prA).Homotopy (ContinuousMap.id B) := {
    toFun z := ⟨Hprod (z.1, z.2.val), z.2.property⟩
    continuous_toFun := (Hprod.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left z := Subtype.ext (Hprod.map_zero_left z.val)
    map_one_left z := Subtype.ext (Hprod.map_one_left z.val) }
  have hprA (j : ℕ) : IsIso (singularCohomologyPullback R prA j) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R prA sA
      ⟨HA⟩ ⟨ContinuousMap.Homotopy.refl _⟩ j
  let P := relativeSingularCohomologyPullback R pr
    (A := B) (B := A) (fun _ hz ↦ hz) k
  let S := relativeSingularCohomologyPullback R s
    (A := A) (B := B) (fun _ hy ↦ hy) k
  have : IsIso P := isIso_relativeSingularCohomologyPullback_of_absolute
    R pr (fun _ hz ↦ hz) hpr hprA k
  have hPS : P ≫ S = 𝟙 _ := by
    rw [← relativeSingularCohomologyPullback_comp]
    change relativeSingularCohomologyPullback R (ContinuousMap.id Y)
      (A := A) (B := A) (fun _ hy ↦ hy) k = 𝟙 _
    simp [relativeSingularCohomologyPullback, relativeSingularChainsMap, cokernel.map]
  have hSP : S ≫ P = 𝟙 _ := by
    apply (cancel_epi P).mp
    rw [← Category.assoc, hPS, Category.id_comp, Category.comp_id]
  exact congrArg (fun f ↦ f a) hSP

end AtiyahSinger
