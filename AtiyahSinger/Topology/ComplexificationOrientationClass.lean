/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationOrientationSign
public import AtiyahSinger.Topology.ComplexOrientationSumCup
public import AtiyahSinger.Topology.RealOrientationClassSign

/-!
# The normalized fiber class of a real complexification

Public module ID: M1732.

The actual real/imaginary map carries the ordered cup of two real fiber
classes to the complex fiber generator with sign (-1)^m in real rank 2m.
The degree transport only reconciles 2(2m) with 2m+2m; it never changes
the factor order. Arbitrary compatible norms are allowed on the fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory
open scoped TensorProduct

universe u

set_option maxHeartbeats 600000 in
-- The original relative classes retain their exact topologies and degree casts.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual real/imaginary identification has the signed normalized local cup formula. -/
theorem realOrientationClass_rationalization_complexification {m : ℕ} {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : Module.Basis (Fin (2 * m)) ℝ V)
    (a : (ℂ ⊗[ℝ] V) ≃ₗ[ℝ] W) (e : W ≃L[ℝ] V × V)
    (he : a.trans e.toLinearEquiv = complexificationReIm V) :
    let A : Set (V × V) := {z | z.1 ≠ 0}
    let B : Set (V × V) := {z | z.2 ≠ 0}
    let P : Set (V × V) := {z | z ≠ 0}
    ∀ hP : Set.MapsTo (ContinuousMap.id (V × V)) P (A ∪ B),
      relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(W, V × V))
        (A := {v | v ≠ 0}) (B := P)
        (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * m + 2 * m)
        (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (V × V)) hP (2 * m + 2 * m)
          (relativeSingularCohomologyUnionCup ℚ A B
            (isOpen_ne_fun continuous_fst continuous_const)
            (isOpen_ne_fun continuous_snd continuous_const) (2 * m) (2 * m)
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(V × V, V))
              (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * m)
              (relativeSingularCohomologyRationalization {v : V | v ≠ 0} (2 * m)
                (realOrientationClass b b.orientation)))
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(V × V, V))
              (A := B) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * m)
              (relativeSingularCohomologyRationalization {v : V | v ≠ 0} (2 * m)
                (realOrientationClass b b.orientation))))) =
      (-1 : ℤ) ^ m •
        cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ
          {v : W | v ≠ 0} k)) (show 2 * (2 * m) = 2 * m + 2 * m by omega))
          (relativeSingularCohomologyRationalization {v : W | v ≠ 0} (2 * (2 * m))
            (realOrientationClass ((complexBasisRealification (b.baseChange ℂ)).map a)
              ((complexBasisRealification (b.baseChange ℂ)).map a).orientation)) := by
  classical
  dsimp only
  intro hP
  let bC := (complexBasisRealification (b.baseChange ℂ)).map a
  let dC := bC.reindex (finCongr (show 2 * (2 * m) = 2 * m + 2 * m by omega))
  let dR := (b.prod b).reindex
    (finSumFinEquiv : Fin (2 * m) ⊕ Fin (2 * m) ≃ Fin (2 * m + 2 * m))
  let s : ℤˣ := (-1) ^ m
  have hmap : Orientation.map (Fin (2 * m + 2 * m)) e.toLinearEquiv dC.orientation =
      s • dR.orientation := by
    rw [← Module.Basis.orientation_map]
    have hb : dC.map e.toLinearEquiv =
        ((complexBasisRealification (b.baseChange ℂ)).map (complexificationReIm V)).reindex
        (finCongr (show 2 * (2 * m) = 2 * m + 2 * m by omega)) := by
      apply DFunLike.ext
      intro i
      change e (a _) = complexificationReIm V _
      exact congrArg (fun f : (ℂ ⊗[ℝ] V) ≃ₗ[ℝ] V × V ↦ f _) he
    rw [hb]
    exact complexBasisRealification_baseChange_orientation b
  -- Naturality first compares integral classes normalized on the original signed cycles.
  have hnat := realOrientationClass_pullback dC dC.orientation dR (s • dR.orientation) e hmap
  rw [realOrientationClass_units_smul] at hnat
  have hs : (s : ℤ) * (s : ℤ) = 1 := by
    rcases Int.units_eq_one_or s with h | h <;> simp [h]
  have hpull : relativeSingularCohomologyPullback ℤ
      (⟨e, e.continuous⟩ : C(W, V × V))
      (A := {v | v ≠ 0}) (B := {v | v ≠ 0})
      (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * m + 2 * m)
      (realOrientationClass dR dR.orientation) =
        (s : ℤ) • realOrientationClass dC dC.orientation := by
    have h := congrArg (fun a ↦ (s : ℤ) • a) hnat
    simpa only [map_zsmul, smul_smul, hs, one_smul] using h
  -- Rationalization preserves this very pullback and its integral sign.
  have hrat := (relativeSingularCohomologyRationalization_naturality
    (⟨e, e.continuous⟩ : C(W, V × V))
    (A := {v | v ≠ 0}) (B := {v | v ≠ 0})
    (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * m + 2 * m)
    (realOrientationClass dR dR.orientation)).symm
  rw [hpull, map_zsmul] at hrat
  have hprod := realOrientationClass_rationalization_prod b b hP
  have hdR : (b.prod b).reindex
      ((finSumFinEquiv : Fin (2 * m) ⊕ Fin (2 * m) ≃ Fin (2 * m + 2 * m)).trans
        (finCongr (Nat.add_comm (2 * m) (2 * m)))) = dR := by
    rfl
  simp only [cast_eq, hdR] at hprod
  rw [hprod, hrat]
  -- Only the natural-number presentation of the dimension remains to be transported.
  have hreindex := realOrientationClass_reindex bC bC.orientation
    (show 2 * (2 * m) = 2 * m + 2 * m by omega)
  rw [← Module.Basis.orientation_reindex] at hreindex
  have hratCast (k l : ℕ) (h : k = l)
      (a : relativeSingularCohomology ℤ {v : W | v ≠ 0} k) :
      relativeSingularCohomologyRationalization {v : W | v ≠ 0} l
        (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℤ {v : W | v ≠ 0} j)) h) a) =
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ {v : W | v ≠ 0} j)) h)
        (relativeSingularCohomologyRationalization {v : W | v ≠ 0} k a) := by
    subst l
    rfl
  change (s : ℤ) • relativeSingularCohomologyRationalization _ _
    (realOrientationClass dC dC.orientation) = _
  rw [← hreindex, hratCast _ _ (show 2 * (2 * m) = 2 * m + 2 * m by omega)]
  rfl

end AtiyahSinger
