/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ComplexificationOrientationClass
public import AtiyahSinger.Topology.RationalCohomologyOrientation

/-!
# The original geometric orientations under real complexification

Public module ID: M1727.

The real bundle has its given locally positive orientation and its original
metric topology. The complexified bundle has the original ReIm total topology
and any specified continuous Hermitian metric. The comparison uses a positive
local frame only at the fiber being evaluated, so no global frame is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))
  (ho : IsLocallyCompatibleBundleOrientation (2 * m) E o)

set_option maxHeartbeats 600000 in
-- The complexified fibers use the supplied Hermitian norms on the ReIm total topology.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The complexified fiber orientation is the signed cup of the original real orientations. -/
theorem complexificationCohomologyOrientation_fiberClass
    (hV : letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (hr : ∀ x, Module.finrank ℂ (ℂ ⊗[ℝ] E x) = 2 * m) (x : X) :
    let F := fun x ↦ ℂ ⊗[ℝ] E x
    letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    letI := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
    letI : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
    letI := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
    letI := hV.realNativeFiberBundle (2 * m) hr
    letI := hV.realNativeVectorBundle (2 * m) hr
    ∀ e : F x ≃L[ℝ] E x × E x, e.toLinearEquiv = complexificationReIm (E x) →
    let A : Set (E x × E x) := {z | z.1 ≠ 0}
    let B : Set (E x × E x) := {z | z.2 ≠ 0}
    let P : Set (E x × E x) := {z | z ≠ 0}
    ∀ hP : Set.MapsTo (ContinuousMap.id (E x × E x)) P (A ∪ B),
      relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(F x, E x × E x))
        (A := {v | v ≠ 0}) (B := P)
        (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) (2 * (2 * m))
        (cast (congrArg (fun k ↦ ↥(relativeSingularCohomology ℚ P k))
          (show 2 * m + 2 * m = 2 * (2 * m) by omega))
          (relativeSingularCohomologyPullback ℚ (ContinuousMap.id (E x × E x)) hP (2 * m + 2 * m)
          (relativeSingularCohomologyUnionCup ℚ A B
            (isOpen_ne_fun continuous_fst continuous_const)
            (isOpen_ne_fun continuous_snd continuous_const) (2 * m) (2 * m)
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.fst : C(E x × E x, E x))
              (A := A) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * m)
              ((geometricCohomologyOrientation (2 * m) E o ho).rationalization.fiberClass x))
            (relativeSingularCohomologyPullback ℚ (ContinuousMap.snd : C(E x × E x, E x))
              (A := B) (B := {v | v ≠ 0}) (fun _ hv ↦ hv) (2 * m)
              ((geometricCohomologyOrientation (2 * m) E o ho).rationalization.fiberClass x))))) =
      (-1 : ℤ) ^ m • (hV.complexCohomologyOrientation (2 * m) hr).rationalization.fiberClass x := by
  let F := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let := hV.realNativeFiberBundle (2 * m) hr
  let := hV.realNativeVectorBundle (2 * m) hr
  dsimp only
  intro e he hP
  -- Select an actual positive frame on a neighborhood of this same point.
  obtain ⟨U, _, hx, bases, hpositive, _⟩ := ho x
  let b := bases ⟨x, hx⟩
  have hb : b.orientation = o x := hpositive ⟨x, hx⟩
  have hE : (geometricCohomologyOrientation (2 * m) E o ho).fiberClass x =
      realOrientationClass b b.orientation := by
    rw [geometricCohomologyOrientation_fiberClass _ _ _ _ _ b, ← hb]
  have hF : (hV.complexCohomologyOrientation (2 * m) hr).fiberClass x =
      realOrientationClass (complexBasisRealification (b.baseChange ℂ))
        (complexBasisRealification (b.baseChange ℂ)).orientation := by
    have h := geometricCohomologyOrientation_fiberClass (2 * (2 * m)) F
      (hV.complexRealOrientation (2 * m) hr)
      (hV.complexRealOrientation_locally_compatible (2 * m) hr) x
      (complexBasisRealification (b.baseChange ℂ))
    rw [← hV.complexRealOrientation_basis (2 * m) hr x (b.baseChange ℂ)] at h
    exact h
  dsimp only [CohomologyOrientation.rationalization]
  rw [hE, hF]
  have h := realOrientationClass_rationalization_complexification b
    (LinearEquiv.refl ℝ (F x)) e he hP
  -- Move only the dimension cast through the original pullback and scalar action.
  have hpull (k l : ℕ) (hd : k = l)
      (a : relativeSingularCohomology ℚ {v : E x × E x | v ≠ 0} k) :
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ {v : F x | v ≠ 0} j)) hd)
        (relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(F x, E x × E x))
          (A := {v : F x | v ≠ 0}) (B := {v : E x × E x | v ≠ 0})
          (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) k a) =
      relativeSingularCohomologyPullback ℚ (⟨e, e.continuous⟩ : C(F x, E x × E x))
        (A := {v : F x | v ≠ 0}) (B := {v : E x × E x | v ≠ 0})
        (fun _ hv hz ↦ hv (e.injective (hz.trans e.map_zero.symm))) l
        (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ
          {v : E x × E x | v ≠ 0} j)) hd) a) := by
    subst l
    rfl
  have hsmul (k l : ℕ) (hd : k = l)
      (a : relativeSingularCohomology ℚ {v : F x | v ≠ 0} k) :
      cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ {v : F x | v ≠ 0} j)) hd)
        ((-1 : ℤ) ^ m • a) =
      (-1 : ℤ) ^ m • cast
        (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ {v : F x | v ≠ 0} j)) hd) a := by
    subst l
    rfl
  have hc := congrArg
    (cast (congrArg (fun j ↦ ↥(relativeSingularCohomology ℚ {v : F x | v ≠ 0} j))
      (show 2 * m + 2 * m = 2 * (2 * m) by omega))) h
  rw [hpull _ _ (show 2 * m + 2 * m = 2 * (2 * m) by omega),
    hsmul _ _ (show 2 * m + 2 * m = 2 * (2 * m) by omega)] at hc
  have hbmap : (complexBasisRealification (b.baseChange ℂ)).map (LinearEquiv.refl ℝ (F x)) =
      complexBasisRealification (b.baseChange ℂ) := by
    apply DFunLike.ext
    intro i
    rfl
  simpa only [hbmap, cast_cast, cast_eq] using hc

end AtiyahSinger
