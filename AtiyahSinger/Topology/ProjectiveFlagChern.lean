/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagCoordinates
public import AtiyahSinger.Topology.ProjectiveChernDescent

/-!
# Comparing projective coefficients on one original flag bundle

Public module ID: M2012.

An actual bundle isomorphism transports the coordinates of one fixed flag
splitting. Their joint kernel is zero, so the projective coefficients pull
back to the elementary symmetric classes of these same flag lines. The
isomorphic bundles retain their separate original norms, modeled total
topologies and metrics; no orthogonality for the transported metric is used.

The actual two projective power-basis bijections remain explicit premises.
This comparison supplies the common flag used for existence and invariance
of the normalized original Chern classes once those bijections are proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin r)) F
    ContinuousHermitianMetric F)

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  isFiniteRank_hermitianFlagLine hermitianProjectiveTopology

local instance : ∀ p, NormedAddCommGroup
    (((hermitianFlagProjection r F hF : HermitianFlagBundle r F hF → X) *ᵖ E) p) :=
  fun p ↦ inferInstanceAs (NormedAddCommGroup (E p.1))

local instance : ∀ p, NormedSpace ℂ
    (((hermitianFlagProjection r F hF : HermitianFlagBundle r F hF → X) *ᵖ E) p) :=
  fun p ↦ inferInstanceAs (NormedSpace ℂ (E p.1))

local instance : FiberBundle (EuclideanSpace ℂ (Fin r))
    ((hermitianFlagProjection r F hF : HermitianFlagBundle r F hF → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E)
    (hermitianFlagProjection r F hF)

local instance : VectorBundle ℂ (EuclideanSpace ℂ (Fin r))
    ((hermitianFlagProjection r F hF : HermitianFlagBundle r F hF → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E)
    (hermitianFlagProjection r F hF)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The coefficients of E pull back to the symmetric line classes on a specified flag of F. -/
theorem hermitianProjectiveChernCoefficient_flag_pullback_of_iso
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r)) F
      Iso E F)
    (hb : Function.Bijective
      (singularCohomologyPowerCombination ℤ (hermitianProjectiveProjection r E h)
        (hermitianProjectiveChernRoot r E h) r r (fun i ↦ Nat.le_of_lt i.isLt)))
    (hb' : let f := hermitianFlagProjection r F hF
      Function.Bijective
        (singularCohomologyPowerCombination ℤ
          (hermitianProjectiveProjection r ((f : HermitianFlagBundle r F hF → X) *ᵖ E)
            (hermitianProjectivePullbackMetric r E h f))
          (hermitianProjectiveChernRoot r ((f : HermitianFlagBundle r F hF → X) *ᵖ E)
            (hermitianProjectivePullbackMetric r E h f)) r r
          (fun i ↦ Nat.le_of_lt i.isLt))) (k : ℕ) :
    singularCohomologyPullback ℤ (hermitianFlagProjection r F hF) (2 * k)
        (projectiveChernCoefficient (hermitianProjectiveProjection r E h) r
          (hermitianProjectiveChernRoot r E h) hb k) =
      singularCohomologyElementarySymmetric ℤ (HermitianFlagBundle r F hF)
        (List.ofFn (fun i ↦ firstChernClass (HermitianFlagLine r F hF i)
          (fun p ↦ p.2.property.2.1 i))) k := by
  let V := EuclideanSpace ℂ (Fin r)
  let := modelTopology V E
  let := modelTopology V F
  let Q := HermitianFlagBundle r F hF
  let p := hermitianFlagProjection r F hF
  let L := HermitianFlagLine r F hF
  -- Use precisely the inverse splitting coordinates of this one flag after the original Iso.
  let a (i : Fin r) : Hom ((p : Q → X) *ᵖ E) (L i) :=
    (hermitianFlagCoordinateHom r F hF i).comp (e.pullback p).toHom
  have hdetect (q : Q) (v : E (p q))
      (hz : ∀ i, (a i).linearMap q v = 0) : v = 0 := by
    have hev : e.linearEquiv (p q) v = 0 := by
      apply hermitianFlagCoordinates_injective r F hF q
      funext i
      change (hermitianFlagCoordinateHom r F hF i).linearMap q
          (e.linearEquiv (p q) v) =
        (hermitianFlagCoordinateHom r F hF i).linearMap q 0
      rw [map_zero]
      exact hz i
    apply (e.linearEquiv (p q)).injective
    exact hev.trans (map_zero (e.linearEquiv (p q))).symm
  -- Naturality and the coordinate open cover now identify every degree on this same base.
  exact hermitianProjectiveChernCoefficient_pullback_eq_elementarySymmetric r E h p
    hb hb' L a (fun i q ↦ q.2.property.2.1 i) hdetect k

end AtiyahSinger.ComplexBundle
