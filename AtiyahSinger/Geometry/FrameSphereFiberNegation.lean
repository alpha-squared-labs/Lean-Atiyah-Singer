/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereStereographic
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Fiber negation on the actual frame-associated sphere

Public module ID: M1244.

Negate the original bundle vector and keep the last real coordinate in its
sphere compactification. The original frame comparison transports this to a
smooth involution of the original associated sphere. It fixes both pole
sections and intertwines the same stereographic inverse with bundle negation.

This is the central orthogonal reflection used to average a horizontal lift
along the south section. It is distinct from reflection of the last coordinate,
which exchanges the two poles. No quotient topology or associated atlas changes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 35 in
set_option maxHeartbeats 1000000 in
-- Smoothness is checked through the original sphere embedding into the native bundle and line.
set_option backward.isDefEq.respectTransparency false in
/-- The actual frame sphere has a smooth fiber-negation involution with its specified
stereographic formula, preserving the bundle base and fixing the south section. -/
theorem exists_frameSphereFiberNegation :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    let a := frameSphereStereographic (EB := EB) r V
    let c := frameSphereHomeomorph (EB := EB) r V
    ∃ d : Z ≃ₘ⟮𝓘(ℝ, EB × R), 𝓘(ℝ, EB × R)⟯ Z,
      (∀ z : Z, (c (d z)).val =
        ((⟨(c z).val.1.proj, -(c z).val.1.snd⟩ : TotalSpace R V), (c z).val.2)) ∧
      (∀ z : Z, d (d z) = z) ∧
      (∀ v : TotalSpace R V, d (a.symm v) = a.symm ⟨v.proj, -v.snd⟩) ∧
      (∀ x : B, d (a.symm ⟨x, 0⟩) = a.symm ⟨x, 0⟩) := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let Q := 𝓘(ℝ, EB × R)
  let J := 𝓘(ℝ, EB).prod 𝓘(ℝ, R)
  let K := J.prod 𝓘(ℝ, ℝ)
  let a := frameSphereStereographic (EB := EB) r V
  let c := frameSphereHomeomorph (EB := EB) r V
  have hc := (frameSphereHomeomorph_spec (EB := EB) r V).2
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let negV (v : TotalSpace R V) : TotalSpace R V := ⟨v.proj, -v.snd⟩
  -- Fiberwise negation is smooth in each original vector-bundle trivialization.
  have hneg : ContMDiff J J ∞ negV := by
    intro v
    let t := trivializationAt R V v.proj
    have hv : v.proj ∈ t.baseSet := mem_baseSet_trivializationAt R V v.proj
    apply (t.contMDiffAt_iff (f := negV) (t.mem_source.mpr hv)).mpr
    have hid : ContMDiffAt J J ∞ (id : TotalSpace R V → TotalSpace R V) v := contMDiffAt_id
    have hparts := (t.contMDiffAt_iff (t.mem_source.mpr hv)).mp hid
    refine ⟨hparts.1, ?_⟩
    apply hparts.2.neg.congr_of_eventuallyEq
    filter_upwards [hparts.1.continuousAt.preimage_mem_nhds (t.open_baseSet.mem_nhds hv)]
      with w hw
    change (t ⟨w.proj, -w.snd⟩).2 = -(t w).2
    exact map_neg (t.linearEquivAt ℝ w.proj hw) w.snd
  let negSphere (z : SphereCompactification r V) : SphereCompactification r V :=
    ⟨(negV z.val.1, z.val.2), by
      change ‖-z.val.1.snd‖ ^ 2 + z.val.2 ^ 2 = 1
      rw [norm_neg]
      exact z.property⟩
  have hN : Function.Involutive negSphere := by
    intro z
    apply Subtype.ext
    change ((⟨z.val.1.proj, -(-z.val.1.snd)⟩ : TotalSpace R V), z.val.2) = z.val
    rw [neg_neg]
  let f (z : Z) : Z := c.symm (negSphere (c z))
  have hcf (z : Z) : c (f z) = negSphere (c z) := c.apply_symm_apply _
  have hf : Function.Involutive f := by
    intro z
    apply c.injective
    rw [hcf, hcf, hN]
  -- The ambient reflection is smooth; the original sphere inclusion detects smoothness.
  have hambient : ContMDiff Q K ∞ (fun z : Z ↦ (negV (c z).val.1, (c z).val.2)) :=
    (hneg.comp (contMDiff_fst.comp hc.contMDiff)).prodMk
      (contMDiff_snd.comp hc.contMDiff)
  have hfcont : Continuous f :=
    c.symm.continuous.comp (hambient.continuous.subtype_mk _)
  have hfs : ContMDiff Q Q ∞ f := by
    apply (ContMDiff.iff_comp_isImmersion hc.isImmersion).mpr
    refine ⟨hfcont, ?_⟩
    exact hambient.congr (fun z ↦ congrArg Subtype.val (hcf z))
  let d : Z ≃ₘ⟮Q, Q⟯ Z := {
    toFun := f
    invFun := f
    left_inv := hf
    right_inv := hf
    contMDiff_toFun := hfs
    contMDiff_invFun := hfs }
  have hchart (v : TotalSpace R V) : d (a.symm v) = a.symm ⟨v.proj, -v.snd⟩ := by
    apply c.injective
    apply Subtype.ext
    change (c (f (a.symm v))).val = _
    rw [hcf]
    change ((⟨(c (a.symm v)).val.1.proj, -(c (a.symm v)).val.1.snd⟩ : TotalSpace R V),
      (c (a.symm v)).val.2) = _
    rw [ha.2.2.2.1, ha.2.2.2.1]
    simp only [norm_neg, smul_neg]
  refine ⟨d, (fun z ↦ congrArg Subtype.val (hcf z)), hf, hchart, ?_⟩
  intro x
  simpa only [neg_zero] using hchart (⟨x, 0⟩ : TotalSpace R V)

end AtiyahSinger
