/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Local smoothness of the Levi-Civita coefficients

Public module ID: M1287.

The scalar coefficients of mathlib's actual Levi-Civita connection are smooth
when tested against vector fields smooth on the same open set. The proof uses
the Koszul formula for the supplied metric and local smoothness of directional
derivatives and Lie brackets. The fields may have arbitrary values outside
that open set, so this applies to the zero-extended frames in the original
spin-connection formula without separation or global extension assumptions.

This is the standard local regularity consequence of the Koszul formula; its
application to the induced spin connection is described in Spin Geometry II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)

/-- The original Levi-Civita connection has smooth scalar coefficients on every open set
where the three supplied vector fields are smooth. -/
theorem contMDiffOn_leviCivitaConnection_inner (U : Set M) (hU : IsOpen U)
    (X Y Z : ∀ x : M, TM x)
    (hX : ContMDiffOn I (I).tangent ∞
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) U)
    (hY : ContMDiffOn I (I).tangent ∞
      (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) U)
    (hZ : ContMDiffOn I (I).tangent ∞
      (fun x ↦ (⟨x, Z x⟩ : TangentBundle I M)) U) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x ↦ inner ℝ (CovariantDerivative.leviCivitaConnection I M Y x (X x))
        (Z x)) U := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  have : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  -- Differentiating a scalar function along a locally smooth field is locally smooth.
  have hdir (f : M → ℝ) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
      (V : ∀ x : M, TM x)
      (hV : ContMDiffOn I (I).tangent ∞
        (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) U) :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ mvfderiv I f x (V x)) U := by
    intro x hx
    have hfAt := (hf x hx).contMDiffAt (hU.mem_nhds hx)
    have hVAt := (hV x hx).contMDiffAt (hU.mem_nhds hx)
    have hderiv := hfAt.contMDiffAt_tangentMap
      (X := (⟨x, V x⟩ : TangentBundle I M)) (m := ∞) (by simp)
    have hcomp := hderiv.comp x hVAt
    have hscalar := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).contMDiffAt.comp
      x hcomp
    exact hscalar.contMDiffWithinAt
  -- Lie brackets use the same local fields; no smooth zero extension is asserted.
  have hbr (V W : ∀ x : M, TM x)
      (hV : ContMDiffOn I (I).tangent ∞
        (fun x ↦ (⟨x, V x⟩ : TangentBundle I M)) U)
      (hW : ContMDiffOn I (I).tangent ∞
        (fun x ↦ (⟨x, W x⟩ : TangentBundle I M)) U) :
      ContMDiffOn I (I).tangent ∞
        (fun x ↦ (⟨x, VectorField.mlieBracket I V W x⟩ : TangentBundle I M)) U := by
    intro x hx
    exact (((hV x hx).contMDiffAt (hU.mem_nhds hx)).mlieBracket_vectorField
      ((hW x hx).contMDiffAt (hU.mem_nhds hx)) (m := ⊤) (n := ⊤)
      (by simp)).contMDiffWithinAt
  -- The Koszul formula expresses each coefficient using only these smooth terms.
  have hmetricDerivatives : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x ↦ mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) +
        mvfderiv I (fun y ↦ inner ℝ (Z y) (X y)) x (Y x) -
        mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x)) U :=
    ((hdir _ (hY.inner_bundle hZ) X hX).add
      (hdir _ (hZ.inner_bundle hX) Y hY)).sub (hdir _ (hX.inner_bundle hY) Z hZ)
  have hkoszul := ((hmetricDerivatives.sub
    (hY.inner_bundle (hbr X Z hX hZ))).sub
    (hZ.inner_bundle (hbr Y X hY hX))).add
    (hX.inner_bundle (hbr Z Y hZ hY))
  have hscale : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ ↦ t / 2) :=
    (contDiff_id.div_const 2).contMDiff
  apply (hscale.comp_contMDiffOn hkoszul).congr
  intro x hx
  exact CovariantDerivative.leviCivitaConnection_apply_inner I
    (((hX x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    (((hY x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    (((hZ x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))

end AtiyahSinger
