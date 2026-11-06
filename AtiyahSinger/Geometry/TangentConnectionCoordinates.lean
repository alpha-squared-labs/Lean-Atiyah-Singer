/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local coordinates of the supplied tangent connection

Public module ID: M1472.

In an actual native tangent frame, the original connection is ordinary
coordinate differentiation plus its values on the local constant frame.
Those coefficients are smooth when the supplied connection is smooth.
These are the tangent-slot corrections in the full tensor formula of
SG III.2 (2.1); no new connection is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)

set_option backward.isDefEq.respectTransparency false in
/-- The actual tangent connection has its usual derivative-plus-frame-coefficients formula. -/
theorem tangentCovariantDerivative_coord_apply
    (covT : CovariantDerivative MI H TM)
    (t : Trivialization H (π H TM)) [MemTrivializationAtlas t]
    (σ : ∀ y : M, TM y) (x : M) (hx : x ∈ t.baseSet)
    (hσ : MDifferentiableAt MI (MI).tangent
      (fun y ↦ (⟨y, σ y⟩ : TangentBundle MI M)) x) (v : TM x) :
    t.continuousLinearMapAt ℝ x (covT σ x v) =
      mvfderiv MI (fun y ↦ t.continuousLinearMapAt ℝ y (σ y)) x v +
        ∑ b : Fin n, (t.continuousLinearMapAt ℝ x (σ x)) b •
          t.continuousLinearMapAt ℝ x
            (covT (fun y ↦ t.symmL ℝ y (EuclideanSpace.single b 1)) x v) := by
  classical
  let coord (Y : ∀ y : M, TM y) (y : M) : H := t.continuousLinearMapAt ℝ y (Y y)
  have hcoordinates (Y : ∀ y : M, TM y) (y : M) (hy : y ∈ t.baseSet) :
      coord Y =ᶠ[nhds y] (fun z ↦ (t ⟨z, Y z⟩).2) := by
    filter_upwards [t.open_baseSet.mem_nhds hy] with z hz
    exact t.continuousLinearMapAt_apply_of_mem ℝ hz (Y z)
  have hcoordinateDiff (Y : ∀ y : M, TM y) (y : M) (hy : y ∈ t.baseSet)
      (hY : MDifferentiableAt MI (MI).tangent
        (fun z ↦ (⟨z, Y z⟩ : TangentBundle MI M)) y) :
      MDifferentiableAt MI MI (coord Y) y :=
    ((t.mdifferentiableAt_section_iff MI Y hy).mp hY).congr_of_eventuallyEq
      (hcoordinates Y y hy)
  -- Subtract the flat connection in this same frame; the difference is fiber-linear.
  let flat (Y : ∀ y : M, TM y) (y : M) : TM y →L[ℝ] TM y :=
    (t.symmL ℝ y).comp (mvfderiv MI (coord Y) y)
  have hflat : IsCovariantDerivativeOn H flat t.baseSet := by
    constructor
    · intro Y Z y hY hZ hy
      have hsum : coord (Y + Z) = coord Y + coord Z := by
        funext z
        exact map_add (t.continuousLinearMapAt ℝ z) (Y z) (Z z)
      dsimp only [flat]
      rw [hsum, mvfderiv_add (hcoordinateDiff Y y hy hY)
        (hcoordinateDiff Z y hy hZ), ContinuousLinearMap.comp_add]
    · intro Y f y hY hf hy
      have hsmul : coord (f • Y) = f • coord Y := by
        funext z
        exact map_smul (t.continuousLinearMapAt ℝ z) (f z) (Y z)
      dsimp only [flat]
      rw [hsmul, mvfderiv_smul hf (hcoordinateDiff Y y hy hY)]
      ext w
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      change f y • t.symmL ℝ y (mvfderiv MI (coord Y) y w) +
        mvfderiv MI f y w • t.symmL ℝ y (t.continuousLinearMapAt ℝ y (Y y)) = _
      rw [t.symmL_continuousLinearMapAt hy]
  let D : TM x →L[ℝ] TM x →L[ℝ] TM x :=
    (covT.isCovariantDerivativeOn (s := t.baseSet)).difference hflat x
  have hD (Y : ∀ y : M, TM y)
      (hY : MDifferentiableAt MI (MI).tangent
        (fun y ↦ (⟨y, Y y⟩ : TangentBundle MI M)) x) :
      D (Y x) = covT Y x - flat Y x :=
    IsCovariantDerivativeOn.difference_apply _ _ hx hY
  let frameField (b : Fin n) (y : M) : TM y := t.symmL ℝ y (EuclideanSpace.single b 1)
  have hlocalCoordinates (b : Fin n) :
      coord (frameField b) =ᶠ[nhds x] (fun _ ↦ EuclideanSpace.single b 1) := by
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    exact t.continuousLinearMapAt_symmL hy _
  have hlocalSmooth (b : Fin n) : ContMDiffAt MI (MI).tangent ∞
      (fun y ↦ (⟨y, frameField b y⟩ : TangentBundle MI M)) x := by
    apply (t.contMDiffAt_section_iff hx).mpr
    exact contMDiffAt_const.congr_of_eventuallyEq
      ((hcoordinates (frameField b) x hx).symm.trans (hlocalCoordinates b))
  have hflatLocal (b : Fin n) : flat (frameField b) x = 0 := by
    dsimp only [flat]
    have hd := (hlocalCoordinates b).mfderiv_eq (I := MI) (I' := MI)
    simp only [mvfderiv, hd, mfderiv_const, ContinuousLinearMap.comp_zero]
  have hDb (b : Fin n) : D (frameField b x) = covT (frameField b) x := by
    rw [hD (frameField b) ((hlocalSmooth b).mdifferentiableAt (by simp)), hflatLocal, sub_zero]
  -- Expand the actual vector in the same original frame and apply the tensorial difference.
  have hrepr : (∑ b : Fin n, coord σ x b • frameField b x) = σ x := by
    have hsum := congrArg (t.symmL ℝ x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr
      (coord σ x))
    simpa only [coord, frameField, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, t.symmL_continuousLinearMapAt hx] using hsum
  have hDsum : D (σ x) = ∑ b : Fin n, coord σ x b • covT (frameField b) x := by
    rw [← hrepr, map_sum]
    simp only [map_smul, hDb]
  have hcov : covT σ x = flat σ x + ∑ b : Fin n, coord σ x b • covT (frameField b) x := by
    rw [← hDsum, hD σ hσ]
    rw [← add_sub_assoc, add_sub_cancel_left]
  rw [hcov]
  simp only [add_apply, sum_apply, smul_apply, map_add, map_sum, map_smul]
  congr 1
  exact t.continuousLinearMapAt_symmL hx _

set_option backward.isDefEq.respectTransparency false in
/-- In a valid original tangent frame the supplied smooth connection has smooth coefficients. -/
theorem contMDiffAt_tangentCovariantDerivative_coord [T2Space M]
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (t : Trivialization H (π H TM)) [MemTrivializationAtlas t]
    (a b : H) (x : M) (hx : x ∈ t.baseSet) :
    ContMDiffAt MI MI ∞ (fun y ↦ t.continuousLinearMapAt ℝ y
      (covT (fun z ↦ t.symmL ℝ z b) y (t.symmL ℝ y a))) x := by
  let frameField (v : H) (y : M) : TM y := t.symmL ℝ y v
  have hfield (v : H) (y : M) (hy : y ∈ t.baseSet) :
      ContMDiffAt MI (MI).tangent ∞
        (fun z ↦ (⟨z, frameField v z⟩ : TangentBundle MI M)) y := by
    apply (t.contMDiffAt_section_iff hy).mpr
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds hy] with z hz
    change (t ⟨z, t.symmL ℝ z v⟩).2 = v
    rw [t.symmL_apply hz, t.apply_mk_symm hz]
  -- A bump makes the local frame a genuine global smooth input for the supplied connection.
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := MI) x).mem_iff.mp
    (t.open_baseSet.mem_nhds hx)
  let σ := (χ : M → ℝ) • frameField b
  have hσ : ContMDiff MI (MI).tangent ∞
      (fun y ↦ (⟨y, σ y⟩ : TangentBundle MI M)) := by
    exact ContMDiffOn.smul_section_of_tsupport χ.contMDiff.contMDiffOn
      t.open_baseSet hχ (fun y hy ↦ (hfield b y hy).contMDiffWithinAt)
  have hout := hcovT.contMDiff.contMDiff (by simpa using hσ.contMDiffOn)
  have hlocal : ContMDiffAt MI ((MI).prod 𝓘(ℝ, H →L[ℝ] H)) ∞
      (fun y ↦ (⟨y, covT (frameField b) y⟩ : TotalSpace (H →L[ℝ] H)
        (fun z ↦ TM z →L[ℝ] TM z))) x := by
    apply (contMDiffOn_univ.mp hout).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [χ.eventuallyEq_one.eventually_nhds, t.open_baseSet.mem_nhds hx]
      with y hχy hy
    congr 1
    apply (covT.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq
      ((hfield b y hy).mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp)) Filter.univ_mem
    filter_upwards [hχy] with z hz
    change frameField b z = (χ : M → ℝ) z • frameField b z
    rw [show (χ : M → ℝ) z = 1 from hz, one_smul]
  -- Evaluation on the original local field and the same frame preserve smoothness.
  have happ := hlocal.clm_bundle_apply (hfield a x hx)
  have hcoord := (t.contMDiffAt_section_iff hx).mp happ
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
  exact t.continuousLinearMapAt_apply_of_mem ℝ hy _

end AtiyahSinger
