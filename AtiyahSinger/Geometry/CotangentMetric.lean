/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Explicit cotangent metrics

Public module ID: M1150.

D03/D05/A08: reuse mathlib's smooth real vector bundle metric on the actual
continuous dual of the tangent bundle. Length is an explicit scalar function;
the original vector operations and total-space topology are never replaced.
Metric existence uses smooth partitions of unity. Radial normalization and
compact sphere arguments are project details supporting SG III.7.10--7.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The real continuous dual of the actual tangent fiber. -/
abbrev CotangentFiber (x : M) : Type _ :=
  TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ

/-- The model fiber of the real cotangent bundle. -/
abbrev CotangentModel (n : ℕ) : Type := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ

/-- The cotangent total space with mathlib's vector bundle topology. -/
abbrev CotangentTotalSpace : Type _ :=
  TotalSpace (CotangentModel n) (CotangentFiber (n := n) (M := M))

/-- A standard smooth positive definite metric on the real cotangent bundle. -/
abbrev SmoothCotangentMetric : Type _ :=
  ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (CotangentModel n) (CotangentFiber (n := n) (M := M))

namespace SmoothCotangentMetric

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Length for the supplied metric, without installing a new norm. -/
def length (x : M) (ξ : CotangentFiber (n := n) x) : ℝ :=
  Real.sqrt (g.inner x ξ ξ)

/-- Metric length is nonnegative. -/
theorem length_nonneg (x : M) (ξ : CotangentFiber (n := n) x) :
    0 ≤ g.length x ξ := by
  exact Real.sqrt_nonneg _

/-- The square of length recovers the metric quadratic form. -/
theorem length_sq (x : M) (ξ : CotangentFiber (n := n) x) :
    g.length x ξ ^ 2 = g.inner x ξ ξ := by
  -- Positivity supplies the nonnegative input to the square-root identity.
  apply Real.sq_sqrt
  by_cases hξ : ξ = 0
  · simp [hξ]
  · exact (g.pos x ξ hξ).le

/-- Only the zero covector has zero length. -/
theorem length_eq_zero_iff (x : M) (ξ : CotangentFiber (n := n) x) :
    g.length x ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro hzero
    by_contra hξ
    have hpos := g.pos x ξ hξ
    have hsquare := g.length_sq x ξ
    rw [hzero] at hsquare
    norm_num at hsquare
    exact (ne_of_gt hpos) hsquare.symm
  · rintro rfl
    simp [length]

/-- A nonzero covector has strictly positive length. -/
theorem length_pos (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
    0 < g.length x ξ := by
  exact Real.sqrt_pos.mpr (g.pos x ξ hξ)

/-- Real scaling multiplies length by the absolute scalar. -/
theorem length_smul (x : M) (t : ℝ) (ξ : CotangentFiber (n := n) x) :
    g.length x (t • ξ) = |t| * g.length x ξ := by
  -- Bilinearity gives the square of the scalar, including a zero scalar.
  simp only [length, map_smul, smul_apply, smul_eq_mul]
  rw [show t * (t * g.inner x ξ ξ) = t ^ 2 * g.inner x ξ ξ by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

/-- Length satisfies the triangle inequality in each fixed fiber. -/
theorem length_add_le (x : M) (ξ η : CotangentFiber (n := n) x) :
    g.length x (ξ + η) ≤ g.length x ξ + g.length x η := by
  -- The native Riemannian interface supplies a norm with exactly the original topology.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (inner ℝ (ξ + η) (ξ + η)) ≤
    Real.sqrt (inner ℝ ξ ξ) + Real.sqrt (inner ℝ η η)
  simpa only [← norm_eq_sqrt_real_inner] using norm_add_le ξ η

/-- Metric length is continuous on the actual cotangent total space. -/
theorem continuous_length :
    Continuous (fun z : CotangentTotalSpace (n := n) (M := M) ↦ g.length z.proj z.snd) := by
  -- Evaluate the same smooth bilinear form twice on the tautological bundle vector.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) :=
    ⟨g.toRiemannianMetric⟩
  let : ∀ x : M, NormedAddCommGroup (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  let : ∀ x : M, InnerProductSpace ℝ (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  let : IsContinuousRiemannianBundle (CotangentModel n)
      (CotangentFiber (n := n) (M := M)) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hdiag : Continuous (fun z : CotangentTotalSpace (n := n) (M := M) ↦
      inner ℝ z.snd z.snd) := continuous_id.inner_bundle continuous_id
  exact Real.continuous_sqrt.comp hdiag

/-- Length is smooth on the punctured cotangent bundle. -/
theorem contMDiffOn_length :
    ContMDiffOn
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) 𝓘(ℝ, ℝ) ∞
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦ g.length z.proj z.snd)
      {z | z.snd ≠ 0} := by
  -- Square root is smooth on the positive diagonal, hence away from the zero section.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) :=
    ⟨g.toRiemannianMetric⟩
  let : ∀ x : M, NormedAddCommGroup (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  let : ∀ x : M, InnerProductSpace ℝ (CotangentFiber (n := n) x) := fun x ↦ inferInstance
  have hdiag : ContMDiff
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, CotangentModel n)) 𝓘(ℝ, ℝ) ∞
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦ inner ℝ z.snd z.snd) :=
    contMDiff_id.inner_bundle contMDiff_id
  intro z hz
  exact ((Real.contDiffAt_sqrt (ne_of_gt (g.pos z.proj z.snd hz))).contMDiffAt.comp z
    hdiag.contMDiffAt).contMDiffWithinAt

/-- In a valid chart the metric length is equivalent to the coordinate Euclidean norm. -/
theorem exists_length_bounds
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (x : M) (hx : x ∈ c.source) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ η : EuclideanSpace ℝ (Fin n),
      b * ‖η‖ ≤ g.length x (covectorFromChart c x η) ∧
        g.length x (covectorFromChart c x η) ≤ B * ‖η‖ := by
  classical
  -- Use the metric norm only through the native topology-compatible Riemannian interface.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) :=
    ⟨g.toRiemannianMetric⟩
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] CotangentFiber (n := n) x :=
    { toFun := covectorFromChart c x
      map_add' u v := by
        ext w
        change inner ℝ (u + v) (mfderiv _ _ c x w) = _
        exact inner_add_left u v _
      map_smul' t u := by
        ext w
        change inner ℝ (t • u) (mfderiv _ _ c x w) = _
        exact real_inner_smul_left u _ t }
  have hLne (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) : L u ≠ 0 := by
    intro hz
    let e := (mdifferentiable_of_mem_atlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc).mfderiv hx
    have he : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x (e.symm u) = u := e.apply_symm_apply u
    have htest := congrArg (fun ξ : CotangentFiber (n := n) x ↦ ξ (e.symm u)) hz
    change inner ℝ u (mfderiv _ _ c x (e.symm u)) = 0 at htest
    rw [he] at htest
    exact hu ((inner_self_eq_zero (𝕜 := ℝ)).mp htest)
  have hnorm (u : EuclideanSpace ℝ (Fin n)) : g.length x (L u) = ‖L u‖ :=
    (norm_eq_sqrt_real_inner (L u)).symm
  have hcont : Continuous (fun u ↦ g.length x (L u)) := by
    simpa only [hnorm] using L.continuous_of_finiteDimensional.norm
  -- Bounds on the compact coordinate sphere include the empty sphere in rank zero.
  have hs := isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨b, hb, hlow⟩ := hs.exists_forall_le' hcont.continuousOn (a := 0) (by
    intro u hu
    exact g.length_pos x (L u) (hLne u (by intro hz; simp [hz] at hu)))
  obtain ⟨B, hupper⟩ := (hs.image hcont).bddAbove
  refine ⟨b, max B 1, hb, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro u
  change b * ‖u‖ ≤ g.length x (L u) ∧ g.length x (L u) ≤ max B 1 * ‖u‖
  by_cases hu : u = 0
  · subst u
    simp [length]
  let v := ‖u‖⁻¹ • u
  have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hu
  have hscale : ‖u‖ • v = u := by simp [v, smul_smul, norm_ne_zero_iff.mpr hu]
  have hlen : g.length x (L u) = ‖u‖ * g.length x (L v) := by
    conv_lhs => rw [← hscale, map_smul, g.length_smul]
    rw [abs_of_nonneg (norm_nonneg u)]
  rw [hlen]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hlow v hv) (norm_nonneg u)]
  · have hbound := (hupper ⟨v, hv, rfl⟩).trans (le_max_left B 1)
    nlinarith [mul_le_mul_of_nonneg_left hbound (norm_nonneg u)]

/-- A cotangent metric exists on a second countable Hausdorff smooth manifold. -/
theorem nonempty [T2Space M] [SecondCountableTopology M] :
    Nonempty (SmoothCotangentMetric (n := n) (M := M)) := by
  classical
  let (x : M) : IsNormableSpace ℝ (CotangentFiber (n := n) x) :=
    (VectorBundle.continuousLinearEquivAt ℝ (CotangentModel n)
      (CotangentFiber (n := n) (M := M)) x).isNormableSpace
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let (x : M) : TopologicalSpace (CotangentFiber (n := n) x →L[ℝ] ℝ) := inferInstance
  let (x : M) : AddCommGroup (CotangentFiber (n := n) x →L[ℝ] ℝ) := inferInstance
  let (x : M) : Module ℝ (CotangentFiber (n := n) x →L[ℝ] ℝ) := inferInstance
  -- Positive symmetric forms are a convex family in the original bilinear Hom bundle.
  let P (x : M) : Set ((CotangentFiber (n := n) x →L[ℝ] CotangentFiber (n := n) x →L[ℝ] ℝ)) := {q |
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
  -- The model form is the ordinary inner product under the Riesz isomorphism.
  let R : CotangentModel n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv
  let Q : CotangentModel n →L[ℝ] CotangentModel n →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp R.toContinuousLinearMap R.toContinuousLinearMap
  -- Original cotangent charts pull the fixed model form back to smooth positive local forms.
  have hlocal (x : M) : ∃ U ∈ 𝓝 x,
      ∃ s : ∀ y, CotangentFiber (n := n) y →L[ℝ] CotangentFiber (n := n) y →L[ℝ] ℝ,
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
          𝓘(ℝ, CotangentModel n →L[ℝ] CotangentModel n →L[ℝ] ℝ)) ∞
          (fun y ↦ TotalSpace.mk' (CotangentModel n →L[ℝ] CotangentModel n →L[ℝ] ℝ) y (s y)) U ∧
      ∀ y ∈ U, s y ∈ P y := by
    let e := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    let t := trivializationAt ℝ (Bundle.Trivial M ℝ) x
    let d := e.continuousLinearMap (RingHom.id ℝ) t
    let f := e.continuousLinearMap (RingHom.id ℝ) d
    let s (y : M) : CotangentFiber (n := n) y →L[ℝ] CotangentFiber (n := n) y →L[ℝ] ℝ :=
      Q.bilinearComp (e.continuousLinearMapAt ℝ y) (e.continuousLinearMapAt ℝ y)
    refine ⟨e.baseSet, e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (CotangentModel n) (CotangentFiber (n := n)) x),
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
    (F_fiber := CotangentModel n →L[ℝ] CotangentModel n →L[ℝ] ℝ)
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun x : M ↦
    CotangentFiber (n := n) x →L[ℝ] CotangentFiber (n := n) x →L[ℝ] ℝ) P hconv hlocal
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
  let : FiniteDimensional ℝ (CotangentFiber (n := n) x) :=
    (VectorBundle.continuousLinearEquivAt ℝ (CotangentModel n)
      (CotangentFiber (n := n) (M := M)) x).symm.toLinearEquiv.finiteDimensional
  let core : InnerProductSpace.Core ℝ (ULift.{0} (CotangentFiber (n := n) x)) :=
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
  let : InnerProductSpace.Core ℝ (ULift.{0} (CotangentFiber (n := n) x)) := core
  let t : TopologicalSpace (ULift.{0} (CotangentFiber (n := n) x)) :=
    core.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : NormedAddCommGroup (ULift.{0} (CotangentFiber (n := n) x)) := core.toNormedAddCommGroup
  let : NormedSpace ℝ (ULift.{0} (CotangentFiber (n := n) x)) :=
    InnerProductSpace.Core.toNormedSpace
  let : InnerProductSpace ℝ (ULift.{0} (CotangentFiber (n := n) x)) :=
    InnerProductSpace.ofCore core.toCore
  let : FiniteDimensional ℝ (ULift.{0} (CotangentFiber (n := n) x)) :=
    (ULift.moduleEquiv (R := ℝ) (M := CotangentFiber (n := n) x)).symm.finiteDimensional
  -- Finite-dimensional linear equivalence transfers the bounded unit ball to the original fiber.
  let e : ULift.{0} (CotangentFiber (n := n) x) ≃L[ℝ] CotangentFiber (n := n) x :=
    (ULift.moduleEquiv (R := ℝ) (M := CotangentFiber (n := n) x)).toContinuousLinearEquiv
  have hball : Bornology.IsVonNBounded ℝ
      (Metric.ball (0 : ULift.{0} (CotangentFiber (n := n) x)) 1) :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr Metric.isBounded_ball
  have himage := hball.image e.toContinuousLinearMap
  have hset : e '' Metric.ball (0 : ULift.{0} (CotangentFiber (n := n) x)) 1 =
      {v : CotangentFiber (n := n) x | q v v < 1} := by
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
          ‖(ULift.up v : ULift.{0} (CotangentFiber (n := n) x))‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      change q v v = ‖(ULift.up v : ULift.{0} (CotangentFiber (n := n) x))‖ ^ 2 at hnorm
      nlinarith [norm_nonneg (ULift.up v : ULift.{0} (CotangentFiber (n := n) x))]
  change Bornology.IsVonNBounded ℝ
    (e '' Metric.ball (0 : ULift.{0} (CotangentFiber (n := n) x)) 1) at himage
  rwa [hset] at himage

/-- Two smooth cotangent lengths are uniformly equivalent over a compact Hausdorff base. -/
theorem exists_comparison [T2Space M] [CompactSpace M]
    (k : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ ξ : CotangentFiber (n := n) x,
      c * g.length x ξ ≤ k.length x ξ ∧ k.length x ξ ≤ C * g.length x ξ := by
  /- Both directions of each original bundle chart have local operator-norm bounds
  for each supplied metric. Compose those bounds in the same coordinates, take a
  finite subcover of the compact base, and invert the reverse positive bound. -/
  classical
  let chart (x : M) :=
    trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
  -- For each supplied metric, both directions of one original chart are locally bounded.
  have hchart (l : SmoothCotangentMetric (n := n) (M := M)) (x : M) :
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ y in 𝓝 x,
        ∀ ξ : CotangentFiber (n := n) y,
          ‖(chart x).continuousLinearMapAt ℝ y ξ‖ ≤ A * l.length y ξ ∧
          l.length y ξ ≤ B *
            ‖(chart x).continuousLinearMapAt ℝ y ξ‖ := by
    let : RiemannianBundle (CotangentFiber (n := n) (M := M)) := ⟨l.toRiemannianMetric⟩
    let : ∀ x : M, NormedAddCommGroup (CotangentFiber (n := n) x) := fun x ↦ inferInstance
    let : ∀ x : M, InnerProductSpace ℝ (CotangentFiber (n := n) x) := fun x ↦ inferInstance
    let : IsContinuousRiemannianBundle (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) :=
      ⟨l.inner, l.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    let e := chart x
    obtain ⟨A, hA, hforward⟩ := eventually_norm_trivializationAt_lt
      (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    obtain ⟨B, hB, hinverse⟩ := eventually_norm_symmL_trivializationAt_lt
      (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    refine ⟨A, B, hA, hB, ?_⟩
    filter_upwards [hforward, hinverse,
      e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) x)] with y hyA hyB hy
    intro ξ
    have hlength : l.length y ξ = ‖ξ‖ := (norm_eq_sqrt_real_inner ξ).symm
    rw [hlength]
    constructor
    · exact (e.continuousLinearMapAt ℝ y).le_opNorm ξ |>.trans
        (mul_le_mul_of_nonneg_right hyA.le (norm_nonneg ξ))
    · calc
        ‖ξ‖ = ‖e.symmL ℝ y (e.continuousLinearMapAt ℝ y ξ)‖ := by
          rw [e.symmL_continuousLinearMapAt (R := ℝ) hy]
        _ ≤ ‖e.symmL ℝ y‖ * ‖e.continuousLinearMapAt ℝ y ξ‖ :=
          (e.symmL ℝ y).le_opNorm _
        _ ≤ B * ‖e.continuousLinearMapAt ℝ y ξ‖ :=
          mul_le_mul_of_nonneg_right hyB.le (norm_nonneg _)
  -- The two metrics use the same original coordinates, so their local bounds compose.
  have hupper (a b : SmoothCotangentMetric (n := n) (M := M)) :
      ∃ C : ℝ, 0 < C ∧ ∀ x : M, ∀ ξ : CotangentFiber (n := n) x,
        b.length x ξ ≤ C * a.length x ξ := by
    have hpoint (x : M) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
        ∀ ξ : CotangentFiber (n := n) y, b.length y ξ ≤ C * a.length y ξ := by
      obtain ⟨A, B, hA, hB, ha⟩ := hchart a x
      obtain ⟨D, E, hD, hE, hb⟩ := hchart b x
      refine ⟨E * A, mul_pos hE hA, ?_⟩
      filter_upwards [ha, hb] with y hya hyb
      intro ξ
      calc
        b.length y ξ ≤ E *
            ‖(chart x).continuousLinearMapAt ℝ y ξ‖ := (hyb ξ).2
        _ ≤ E * (A * a.length y ξ) := mul_le_mul_of_nonneg_left (hya ξ).1 hE.le
        _ = (E * A) * a.length y ξ := (mul_assoc _ _ _).symm
    choose C hC hnear using hpoint
    let U (x : M) : Set M := {y | ∀ ξ : CotangentFiber (n := n) y,
      b.length y ξ ≤ C x * a.length y ξ}
    obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hnear
    have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ ↦ (hC x).le)
    refine ⟨1 + ∑ x ∈ s, C x, by positivity, ?_⟩
    intro y ξ
    have hy : y ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp hy
    have hxle : C x ≤ ∑ z ∈ s, C z :=
      Finset.single_le_sum (fun z _ ↦ (hC z).le) hx
    exact (hyx ξ).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.sqrt_nonneg (a.inner y ξ ξ)))
  -- Obtain each uniform direction separately, then invert the reverse positive constant.
  obtain ⟨A, hA, ha⟩ := hupper g k
  obtain ⟨B, hB, hb⟩ := hupper k g
  refine ⟨B⁻¹, A, inv_pos.mpr hB, hA, ?_⟩
  intro x ξ
  refine ⟨?_, ha x ξ⟩
  calc
    B⁻¹ * g.length x ξ ≤ B⁻¹ * (B * k.length x ξ) :=
      mul_le_mul_of_nonneg_left (hb x ξ) (inv_pos.mpr hB).le
    _ = k.length x ξ := by rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

end SmoothCotangentMetric

end AtiyahSinger
