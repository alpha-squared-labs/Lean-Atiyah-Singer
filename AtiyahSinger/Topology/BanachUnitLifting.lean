/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Lifting paths of invertible elements

Public module ID: M1562.

KRL01/KRL02 under K01/K02. Karoubi II.2 Lemmas 2.21 and 2.22, pp.64–65.
Use unital real Banach algebras, not necessarily commutative. The homomorphism
is a continuous unital ring homomorphism; no complex linearity is assumed.
The full-path lemma retains surjectivity on interval-function algebras separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

variable {A B : Type*} [NormedRing A] [hAR : NormedAlgebra ℝ A] [hAC : CompleteSpace A]
  [NormedRing B] [hBR : NormedAlgebra ℝ B] [hBC : CompleteSpace B]


omit hAR hAC hBR hBC in
/-- A continuous ring homomorphism induces a continuous map on units. -/
theorem continuous_unitsMap (f : A →+* B) (hf : Continuous f) :
    Continuous (Units.map f.toMonoidHom) := by
  /- The units topology records both an element and its inverse. The unit map
  applies the continuous homomorphism to each of these coordinates, giving continuity. -/
  exact hf.units_map f.toMonoidHom

/-- The actual continuous map on invertible elements. -/
def unitsMapContinuous (f : A →+* B) (hf : Continuous f) : C(Aˣ, Bˣ) :=
  ⟨Units.map f.toMonoidHom, continuous_unitsMap f hf⟩

include hAR hAC hBR hBC

/-- Karoubi II.2.21: the terminal unit of a path has a lift. -/
theorem exists_unit_lift_endpoint (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (a : Aˣ) (p : C(I, Bˣ))
    (h₀ : p 0 = Units.map f.toMonoidHom a) :
    ∃ b : Aˣ, Units.map f.toMonoidHom b = p 1 := by
  /- A continuous additive map between real topological vector spaces is real-linear.
  The Banach open mapping theorem therefore makes f open. Its image on units is an
  open subgroup, hence also closed. Pulling this subgroup back along p gives a
  clopen subset of the connected interval containing zero, so it contains one. -/
  -- Derive real linearity from continuity; it is not an additional hypothesis.
  let F : A →L[ℝ] B := f.toAddMonoidHom.toRealLinearMap hf
  have hopen : IsOpenMap f := F.isOpenMap hs
  let H : Subgroup Bˣ := (Units.map f.toMonoidHom).range
  have hH : (H : Set Bˣ) = Units.val ⁻¹' (f '' {x : A | IsUnit x}) := by
    ext b
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c.val, c.isUnit, rfl⟩
    · rintro ⟨x, ⟨c, hc⟩, hx⟩
      refine ⟨c, ?_⟩
      apply Units.ext
      exact (congrArg f hc).trans hx
  have hHopen : IsOpen (H : Set Bˣ) := by
    rw [hH]
    exact (hopen _ Units.isOpen).preimage Units.continuous_val
  let U : OpenSubgroup Bˣ := { H with isOpen' := hHopen }
  -- Connectedness propagates membership from the specified initial lift to the endpoint.
  have hclopen : IsClopen (p ⁻¹' (H : Set Bˣ)) :=
    ⟨U.isClosed.preimage p.continuous, hHopen.preimage p.continuous⟩
  have hzero : (0 : I) ∈ p ⁻¹' (H : Set Bˣ) := by
    change p 0 ∈ H
    rw [h₀]
    exact ⟨a, rfl⟩
  have hall := hclopen.eq_univ ⟨0, hzero⟩
  have hone : (1 : I) ∈ p ⁻¹' (H : Set Bˣ) := by
    rw [hall]
    trivial
  exact hone

/-- Choose an endpoint lift with its image specified by the preceding lemma. -/
def unitLiftEndpoint (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (a : Aˣ) (p : C(I, Bˣ))
    (h₀ : p 0 = Units.map f.toMonoidHom a) : Aˣ :=
  (exists_unit_lift_endpoint f hf hs a p h₀).choose

/-- The chosen endpoint maps to the prescribed terminal unit. -/
theorem map_unitLiftEndpoint (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (a : Aˣ) (p : C(I, Bˣ))
    (h₀ : p 0 = Units.map f.toMonoidHom a) :
    Units.map f.toMonoidHom (unitLiftEndpoint f hf hs a p h₀) = p 1 := by
  /- Use the image equation carried by the existential witness selecting the
  lift. No path or uniqueness of the endpoint lift is asserted by this choice. -/
  exact (exists_unit_lift_endpoint f hf hs a p h₀).choose_spec

-- The full-path argument uses interval-function surjectivity hI.
set_option linter.unusedVariables false in
/-- Karoubi II.2.22: lift the entire path with its prescribed initial value. -/
theorem exists_unit_path_lift (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f)
    (hI : Function.Surjective (f.compLeftContinuous I hf))
    (a : Aˣ) (p : C(I, Bˣ)) (h₀ : p 0 = Units.map f.toMonoidHom a) :
    ∃ q : C(I, Aˣ), q 0 = a ∧ ∀ t, Units.map f.toMonoidHom (q t) = p t := by
  /- Apply the endpoint lemma in the interval-function Banach algebras to the
  path s ↦ (t ↦ p(s*t)). Its initial value is the image of the constant function a.
  The additional hI supplies the needed surjectivity. Regard the lifted unit
  function as a continuous unit-valued path q₁, then replace q₁(t) by
  q₁(t)*q₁(0)⁻¹*a. This keeps its image equal to p(t) and fixes its initial value. -/
  -- Curry the actual contraction of the parameter interval, including the inverse coordinate.
  let P : C(I, C(I, B)ˣ) := {
    toFun := fun s ↦ ContinuousMap.unitsLift
      ⟨fun t ↦ p (s * t), p.continuous.comp (continuous_const.mul continuous_id)⟩
    continuous_toFun := by
      apply Units.continuous_iff.mpr
      constructor
      · apply ContinuousMap.continuous_of_continuous_uncurry
        exact Units.continuous_val.comp (p.continuous.comp (continuous_fst.mul continuous_snd))
      · apply ContinuousMap.continuous_of_continuous_uncurry
        exact Units.continuous_coe_inv.comp
          (p.continuous.comp (continuous_fst.mul continuous_snd)) }
  let aI : C(I, A)ˣ := ContinuousMap.unitsLift (ContinuousMap.const I a)
  have hfI : Continuous (f.compLeftContinuous I hf) :=
    ContinuousMap.continuous_postcomp ⟨f, hf⟩
  have hPzero : P 0 = Units.map (f.compLeftContinuous I hf).toMonoidHom aI := by
    apply Units.ext
    apply ContinuousMap.ext
    intro t
    change (p (0 * t) : B) = f a
    rw [zero_mul, h₀]
    rfl
  obtain ⟨bI, hbI⟩ := exists_unit_lift_endpoint (f.compLeftContinuous I hf) hfI hI
    aI P hPzero
  -- The lifted invertible continuous function is a path of actual units in A.
  let q₁ : C(I, Aˣ) := ContinuousMap.unitsLift.symm bI
  have hq₁ (t : I) : Units.map f.toMonoidHom (q₁ t) = p t := by
    apply Units.ext
    have h := congrArg (fun c : C(I, B)ˣ ↦ (c : C(I, B)) t) hbI
    change f ((bI : C(I, A)) t) = (p (1 * t) : B) at h
    change f ((bI : C(I, A)) t) = (p t : B)
    simpa only [one_mul] using h
  -- Right multiplication by the constant kernel correction fixes precisely the starting unit.
  let q : C(I, Aˣ) := {
    toFun := fun t ↦ q₁ t * (q₁ 0)⁻¹ * a
    continuous_toFun := (q₁.continuous.mul continuous_const).mul continuous_const }
  refine ⟨q, ?_, ?_⟩
  · change q₁ 0 * (q₁ 0)⁻¹ * a = a
    rw [mul_inv_cancel, one_mul]
  · intro t
    change Units.map f.toMonoidHom (q₁ t * (q₁ 0)⁻¹ * a) = p t
    rw [map_mul, map_mul, map_inv, hq₁ t, hq₁ 0, h₀, inv_mul_cancel_right]

/-- Choose a full path lift satisfying the initial and image equations. -/
def unitPathLift (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f)
    (hI : Function.Surjective (f.compLeftContinuous I hf))
    (a : Aˣ) (p : C(I, Bˣ)) (h₀ : p 0 = Units.map f.toMonoidHom a) : C(I, Aˣ) :=
  (exists_unit_path_lift f hf hs hI a p h₀).choose

/-- The chosen path lift starts at the given unit. -/
theorem unitPathLift_zero (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (hI : Function.Surjective (f.compLeftContinuous I hf))
    (a : Aˣ) (p : C(I, Bˣ)) (h₀ : p 0 = Units.map f.toMonoidHom a) :
    unitPathLift f hf hs hI a p h₀ 0 = a := by
  /- Use the first component of the existence theorem's characterization.
  The normalization in the source argument is necessary to enforce this exact start. -/
  exact (exists_unit_path_lift f hf hs hI a p h₀).choose_spec.1

/-- The chosen path lift maps to the original path at every time. -/
theorem map_unitPathLift (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (hI : Function.Surjective (f.compLeftContinuous I hf))
    (a : Aˣ) (p : C(I, Bˣ)) (h₀ : p 0 = Units.map f.toMonoidHom a) (t : I) :
    Units.map f.toMonoidHom (unitPathLift f hf hs hI a p h₀ t) = p t := by
  /- Use the second characterization of the chosen lift at the specified time.
  This is an equality of actual units, not merely of connected components. -/
  exact (exists_unit_path_lift f hf hs hI a p h₀).choose_spec.2 t

/-- Units connected to one lift to units when interval functions lift. -/
theorem exists_unit_path_from_one (f : A →+* B) (hf : Continuous f)
    (hs : Function.Surjective f) (hI : Function.Surjective (f.compLeftContinuous I hf))
    (p : C(I, Bˣ)) (h₀ : p 0 = 1) :
    ∃ q : C(I, Aˣ), q 0 = 1 ∧ ∀ t, Units.map f.toMonoidHom (q t) = p t := by
  /- Specialize the full path-lifting lemma to the unit one in A. A unital
  homomorphism maps it to one in B, so the stated endpoint hypothesis applies. -/
  apply exists_unit_path_lift f hf hs hI 1 p
  simpa only [map_one] using h₀

end AtiyahSinger
