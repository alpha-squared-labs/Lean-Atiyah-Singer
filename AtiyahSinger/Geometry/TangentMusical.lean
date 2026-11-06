/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentMetric
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The metric musical identification of the actual tangent and cotangent bundles

Public module ID: M1483.

A supplied smooth positive definite metric on the original tangent fibers
gives the flat map (x,v) ↦ (x,g_x(v,·)). This file fixes that actual formula
before packaging its homeomorphism certificate. The codomain is the existing
continuous-dual cotangent bundle with its native total-space topology.

The metric is mathlib's `ContMDiffRiemannianMetric`, whose fiber forms are
continuous for the original tangent topology. No global tangent norm or new
fiber topology is installed. Finite-dimensional positive definiteness makes
the flat map invertible, and the inverse Gram matrices give a continuous
inverse in the same original local bundle charts.

This is the standard musical isomorphism used to compare the cotangent symbol
picture with the tangent-bundle topological index. The flat map and its
continuous inverse define the homeomorphism used in compact-support K-theory
transport.

Sources: SG II.3, Examples 3.1--3.2, printed p.94, identifies the tangent
representation, the inverse-transpose dual representation and their metric
isomorphism. SG II.5, printed p.113, explicitly identifies T(X) and T*(X)
using the Riemannian metric. The local Gram-matrix argument below expands
that standard identification; it is not a separately numbered lemma in SG.
The map is canonical for the supplied g. Independence of g on compact-support
K-theory is a separate downstream assertion, not part of this definition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- A smooth positive definite metric on the original tangent fibers and their topology. -/
abbrev SmoothTangentMetric : Type _ :=
  ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)

namespace SmoothTangentMetric

/-- A second-countable Hausdorff smooth manifold admits a smooth tangent metric. -/
theorem nonempty [T2Space M] [SecondCountableTopology M] :
    Nonempty (SmoothTangentMetric (n := n) (M := M)) := by
  classical
  let (x : M) : IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin n))
      ((TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)) x).isNormableSpace
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let (x : M) : TopologicalSpace (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :=
    inferInstance
  let (x : M) : AddCommGroup (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :=
    inferInstance
  let (x : M) : Module ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :=
    inferInstance
  -- Positive symmetric forms are a convex family in the original bilinear Hom bundle.
  let P (x : M) : Set (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) := {q |
    (∀ u v, q u v = q v u) ∧ (∀ v, v ≠ 0 → 0 < q v v)}
  have hconv (x : M) : Convex ℝ (P x) := by
    intro q hq p hp a b ha hb hab
    constructor
    · intro u v
      change a * q u v + b * p u v = a * q v u + b * p v u
      rw [hq.1, hp.1]
    · intro v hv
      change 0 < a * q v v + b * p v v
      have hqv := hq.2 v hv
      have hpv := hp.2 v hv
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hpv
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hqv)
          (mul_nonneg hb hpv.le)
  -- The model form is the ordinary inner product on the tangent model.
  let R : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.refl ℝ _
  let Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp R.toContinuousLinearMap R.toContinuousLinearMap
  -- Original tangent charts pull the fixed model form back to smooth positive local forms.
  have hlocal (x : M) : ∃ U ∈ 𝓝 x,
      ∃ s : ∀ y, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y →L[ℝ] ℝ,
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
          (fun y ↦ TotalSpace.mk'
            (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y (s y)) U ∧
      ∀ y ∈ U, s y ∈ P y := by
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) x
    let t := trivializationAt ℝ (Bundle.Trivial M ℝ) x
    let d := e.continuousLinearMap (RingHom.id ℝ) t
    let f := e.continuousLinearMap (RingHom.id ℝ) d
    let s (y : M) : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y →L[ℝ] ℝ :=
      Q.bilinearComp (e.continuousLinearMapAt ℝ y) (e.continuousLinearMapAt ℝ y)
    refine ⟨e.baseSet, e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x),
      s, ?_, ?_⟩
    · apply (f.contMDiffOn_section_iff e.open_baseSet ?_).mpr
      · apply (contMDiffOn_const (c := Q)).congr
        intro y hy
        ext u v
        rw [show f = e.continuousLinearMap (RingHom.id ℝ) d from rfl,
          Trivialization.continuousLinearMap_apply]
        simp only [ContinuousLinearMap.comp_apply]
        rw [d.continuousLinearMapAt_apply_of_mem ℝ ⟨hy, by simp [t]⟩]
        change (t.continuousLinearMapAt ℝ y)
          (s y (e.symmL ℝ y u) (e.symmL ℝ y v)) = Q u v
        simp only [s, ContinuousLinearMap.bilinearComp_apply,
          e.continuousLinearMapAt_symmL hy]
        simp [t]
      · intro y hy
        exact ⟨hy, hy, by simp [t]⟩
    · intro y hy
      constructor
      · intro u v
        change inner ℝ (R (e.continuousLinearMapAt ℝ y u))
          (R (e.continuousLinearMapAt ℝ y v)) = _
        exact real_inner_comm _ _
      · intro v hv
        change 0 < inner ℝ (R (e.continuousLinearMapAt ℝ y v))
          (R (e.continuousLinearMapAt ℝ y v))
        apply real_inner_self_pos.mpr
        intro hzero
        have hcoord : e.continuousLinearMapAt ℝ y v = 0 := R.injective (by simpa using hzero)
        have hinv := e.symmL_continuousLinearMapAt (R := ℝ) hy v
        rw [hcoord, map_zero] at hinv
        exact hv hinv.symm
  -- Smooth partition-of-unity gluing takes place in that same bundle and preserves this cone.
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (F_fiber := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun x : M ↦
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) P hconv hlocal
  refine ⟨{ inner := s
            symm := fun x ↦ (hs x).1
            pos := fun x ↦ (hs x).2
            isVonNBounded := ?_
            contMDiff := s.contMDiff }⟩
  intro x
  -- Put the induced inner-product norm on a temporary copy; retain the original fiber topology.
  let q := s x
  have hsymm := (hs x).1
  have hpos := (hs x).2
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    LinearEquiv.finiteDimensional
      (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) x).symm.toLinearEquiv
  let core : InnerProductSpace.Core ℝ (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    { inner u v := q u.down v.down
      conj_inner_symm u v := hsymm v.down u.down
      re_inner_nonneg v := by
        by_cases hv : v.down = 0
        · simp [hv]
        · exact (hpos v.down hv).le
      add_left u v w := by simp
      smul_left a u v := by simp
      definite v h := by
        have hv : v.down = 0 := by
          by_contra hv
          exact (ne_of_gt (hpos v.down hv)) h
        exact ULift.ext hv }
  let : InnerProductSpace.Core ℝ (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) := core
  let t : TopologicalSpace (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    core.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedAddCommGroup (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    core.toNormedAddCommGroup
  let : NormedSpace ℝ (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    InnerProductSpace.Core.toNormedSpace
  let : InnerProductSpace ℝ (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    InnerProductSpace.ofCore core.toCore
  let : FiniteDimensional ℝ (ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :=
    (ULift.moduleEquiv (R := ℝ) 
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).symm.finiteDimensional
  -- Finite-dimensional linear equivalence transfers the bounded unit ball to the original fiber.
  let e : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) ≃L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
    (ULift.moduleEquiv (R := ℝ) 
      (M := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toContinuousLinearEquiv
  have hball : Bornology.IsVonNBounded ℝ
      (Metric.ball (0 : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 1) :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr Metric.isBounded_ball
  have himage := hball.image e.toContinuousLinearMap
  have hset : e '' Metric.ball (0 : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 1 =
      {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x | q v v < 1} := by
    ext v
    simp only [Set.mem_image, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hnorm : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      change q u.down u.down = ‖u‖ ^ 2 at hnorm
      change q u.down u.down < 1
      nlinarith [norm_nonneg u]
    · intro hv
      refine ⟨ULift.up v, ?_, rfl⟩
      have hnorm : inner ℝ (ULift.up v) (ULift.up v) =
          ‖(ULift.up v : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      change q v v =
        ‖(ULift.up v : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))‖ ^ 2 at hnorm
      have hn := norm_nonneg
        (ULift.up v : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
      nlinarith
  change Bornology.IsVonNBounded ℝ
    (e '' Metric.ball (0 : ULift.{0} (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) 1) at himage
  rwa [hset] at himage

variable (g : SmoothTangentMetric (n := n) (M := M))

/-- The flat musical map sends an original tangent vector to its metric covector. -/
def flatMap : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M →
    CotangentTotalSpace (n := n) (M := M) :=
  fun z ↦ ⟨z.proj, g.inner z.proj z.snd⟩

/-- The actual flat map is a homeomorphism of the original total-space topologies. -/
theorem isHomeomorph_flatMap : IsHomeomorph g.flatMap := by
  classical
  -- The Riesz maps use the supplied metric and retain each original tangent topology.
  let : RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e (x : M) : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x ≃L[ℝ]
      CotangentFiber (n := n) x :=
    (InnerProductSpace.toDual ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)).toContinuousLinearEquiv
  have hforward : Continuous g.flatMap := by
    exact (g.contMDiff.continuous.comp
      (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) _)).clm_bundle_apply continuous_id
  let inverseMap (z : CotangentTotalSpace (n := n) (M := M)) :
      TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M :=
    ⟨z.proj, (e z.proj).symm z.snd⟩
  -- In the same native frames, the inverse Riesz map is the inverse coordinate operator.
  have hcoordinates (x : M) : ContinuousAt
      (fun y ↦ ContinuousLinearMap.inCoordinates (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _)
        x y x y (e y).symm.toContinuousLinearMap) x := by
    let a := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _) x
    let b := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    let A (y : M) : EuclideanSpace ℝ (Fin n) →L[ℝ] CotangentModel n :=
      (b.continuousLinearMapAt ℝ y).comp ((e y).toContinuousLinearMap.comp (a.symmL ℝ y))
    let B (y : M) : CotangentModel n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (a.continuousLinearMapAt ℝ y).comp ((e y).symm.toContinuousLinearMap.comp (b.symmL ℝ y))
    have hAB (y : M) (ha : y ∈ a.baseSet) (hb : y ∈ b.baseSet) :
        (A y).comp (B y) = ContinuousLinearMap.id ℝ (CotangentModel n) ∧
          (B y).comp (A y) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      constructor
      · apply ContinuousLinearMap.ext
        intro v
        change b.continuousLinearMapAt ℝ y (e y (a.symmL ℝ y
          (a.continuousLinearMapAt ℝ y ((e y).symm (b.symmL ℝ y v))))) = v
        rw [a.symmL_continuousLinearMapAt (R := ℝ) ha, (e y).apply_symm_apply,
          b.continuousLinearMapAt_symmL hb]
      · apply ContinuousLinearMap.ext
        intro v
        change a.continuousLinearMapAt ℝ y ((e y).symm (b.symmL ℝ y
          (b.continuousLinearMapAt ℝ y (e y (a.symmL ℝ y v))))) = v
        rw [b.symmL_continuousLinearMapAt (R := ℝ) hb, (e y).symm_apply_apply,
          a.continuousLinearMapAt_symmL ha]
    have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt _ _ x
    have hbx : x ∈ b.baseSet := mem_baseSet_trivializationAt _ _ x
    have hA : ContinuousAt A x :=
      (continuousAt_hom_bundle (RingHom.id ℝ) (fun y ↦ TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] CotangentModel n) y (g.inner y))).mp
        g.contMDiff.continuous.continuousAt |>.2
    have hinvertible : (A x).IsInvertible :=
      ContinuousLinearMap.IsInvertible.of_inverse (hAB x hax hbx).1 (hAB x hax hbx).2
    have hinverse := (hinvertible.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hA
    change ContinuousAt B x
    apply hinverse.congr_of_eventuallyEq
    filter_upwards [a.open_baseSet.mem_nhds hax, b.open_baseSet.mem_nhds hbx] with y ha hb
    exact (ContinuousLinearMap.inverse_eq (hAB y ha hb).1 (hAB y ha hb).2).symm
  have hinverse : Continuous inverseMap := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((hcoordinates z.proj).comp
      (FiberBundle.continuous_proj (CotangentModel n) _).continuousAt).clm_apply_of_inCoordinates
      continuousAt_id (FiberBundle.continuous_proj (CotangentModel n) _).continuousAt
  -- Package the original forward formula with this continuous inverse on the same fibers.
  let h : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ≃ₜ
      CotangentTotalSpace (n := n) (M := M) :=
    { toFun := g.flatMap
      invFun := inverseMap
      left_inv := by
        rintro ⟨x, v⟩
        change (⟨x, (e x).symm (e x v)⟩ : TangentBundle _ M) = ⟨x, v⟩
        rw [(e x).symm_apply_apply]
      right_inv := by
        rintro ⟨x, ξ⟩
        change (⟨x, e x ((e x).symm ξ)⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, ξ⟩
        rw [(e x).apply_symm_apply]
      continuous_toFun := hforward
      continuous_invFun := hinverse }
  exact h.isHomeomorph

/-- The musical homeomorphism with exactly the specified metric flat map as its forward map. -/
def flatHomeomorph : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ≃ₜ
    CotangentTotalSpace (n := n) (M := M) :=
  g.isHomeomorph_flatMap.homeomorph g.flatMap

end SmoothTangentMetric

end AtiyahSinger
