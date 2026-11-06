/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereCompactification
public import AtiyahSinger.Geometry.OrthogonalStereographic

/-!
# Stereographic coordinates on the original frame-associated sphere

Public module ID: M1249.

Removing the infinity section from the original associated sphere gives the
original vector-bundle total space. One open partial homeomorphism supplies
both directions, the exact fiberwise formulas and their smoothness for the
same chosen frame atlas. No new topology or independent sphere atlas is used.

The normalization is mathlib's stereographic projection `2 v / (1 - t)`.
Its inverse has horizontal coordinate `4 v / (norm(v)^2 + 4)` and vertical
coordinate `(norm(v)^2 - 4) / (norm(v)^2 + 4)`. In particular, the zero section
maps to the south pole. Squared norms retain smoothness at zero. Rank zero
and empty bases are included.

Sources: SG III.13, p.251, equation (13.15), and Appendix A, pp.370--371,
for the original sphere compactification and frame reconstruction. The exact
coordinate and native-atlas comparison is a standard supplement using the
specified equivariant stereographic chart.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [hEB : FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [hB : IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [hV : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [hMetric : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "Rr" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

include hEB hB hV hMetric

/-- Stereographic projection identifies the original sphere minus infinity with the bundle. -/
theorem exists_frameSphereStereographic :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    let c := frameSphereHomeomorph (EB := EB) r V
    ∃ e : OpenPartialHomeomorph Z (TotalSpace Rr V),
      e.source = {z : Z | (c z).val.2 ≠ 1} ∧
      e.target = Set.univ ∧
      (∀ z ∈ e.source,
        e z = ⟨(c z).val.1.proj, (2 / (1 - (c z).val.2)) • (c z).val.1.snd⟩) ∧
      (∀ v : TotalSpace Rr V,
        (c (e.symm v)).val =
          ((⟨v.proj, (4 / (‖v.snd‖ ^ 2 + 4)) • v.snd⟩ : TotalSpace Rr V),
            (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4))) ∧
      ContMDiffOn 𝓘(ℝ, EB × Rr) (𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)) ∞ e e.source ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)) 𝓘(ℝ, EB × Rr) ∞ e.symm := by
  /- Stage 1: use the existing frameSphereHomeomorph to write a sphere point
  as its original vector v and real coordinate t. The locus t different from
  one is open. On this locus send (v,t) to 2/(1-t) times v in the same fiber.
  The sphere equation identifies t=1 exactly with the infinity section.
  Stage 2: for each original vector w, put q=norm(w)^2. The denominator q+4
  is positive. The displayed inverse lies on the original sphere and has
  t different from one. Elementary algebra proves both inverse identities;
  this includes w=0 and zero-dimensional fibers. The existing homeomorphism
  transfers this point to the original associated quotient.
  Stage 3: both formulas are continuous in the original bundle topology.
  Equip their mutually inverse restrictions with OpenPartialHomeomorph, whose
  source is exactly the stated complement and whose target is the whole bundle.
  The values of its forward map outside the source are irrelevant.
  Stage 4: in each selected compatible orthogonal frame, these formulas are
  exactly orthogonalSphereStereographic and its inverse, with normalization
  2x/(1-t). Equivariance makes the expressions agree on overlaps. The original
  frame columns and metric are smooth, and the squared norm is smooth even
  at zero. Thus the forward map is smooth on its source and its inverse is
  smooth everywhere, for the same associated atlas and original bundle atlas.
  No compact base, global frame, positive rank or altered target atlas is used. -/
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let c := frameSphereHomeomorph (EB := EB) r V
  let I := 𝓘(ℝ, EB)
  let Q := 𝓘(ℝ, EB × Rr)
  let J := I.prod 𝓘(ℝ, Rr)
  let K := J.prod 𝓘(ℝ, ℝ)
  have hc : Manifold.IsSmoothEmbedding Q K ∞ (fun z : Z ↦ (c z).val) :=
    (frameSphereHomeomorph_spec (EB := EB) r V).2
  let f (z : Z) : TotalSpace Rr V :=
    ⟨(c z).val.1.proj, (2 / (1 - (c z).val.2)) • (c z).val.1.snd⟩
  let U : Set Z := {z | (c z).val.2 ≠ 1}
  -- Squared norms, rather than norms, are smooth at the zero section.
  have hnorm : ContMDiff J 𝓘(ℝ, ℝ) ∞
      (fun v : TotalSpace Rr V ↦ ‖v.snd‖ ^ 2) := by
    have hid : ContMDiff J J ∞ (id : TotalSpace Rr V → TotalSpace Rr V) := contMDiff_id
    simpa only [real_inner_self_eq_norm_sq] using hid.inner_bundle hid
  have hden (v : TotalSpace Rr V) : 0 < ‖v.snd‖ ^ 2 + 4 := by positivity
  let invSphere (v : TotalSpace Rr V) : SphereCompactification r V :=
    ⟨((⟨v.proj, (4 / (‖v.snd‖ ^ 2 + 4)) • v.snd⟩ : TotalSpace Rr V),
      (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4)), by
      change ‖(4 / (‖v.snd‖ ^ 2 + 4)) • v.snd‖ ^ 2 +
        ((‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4)) ^ 2 = 1
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      field_simp
      ring⟩
  let g (v : TotalSpace Rr V) : Z := c.symm (invSphere v)
  have hcg (v : TotalSpace Rr V) : c (g v) = invSphere v := c.apply_symm_apply _
  have hgU (v : TotalSpace Rr V) : g v ∈ U := by
    change (c (g v)).val.2 ≠ 1
    rw [hcg]
    change (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4) ≠ 1
    intro h
    have hmul := (div_eq_iff (ne_of_gt (hden v))).mp h
    linarith
  -- Both inverse identities are in the original fibers; no frame is selected here.
  have hfg (v : TotalSpace Rr V) : f (g v) = v := by
    dsimp [f]
    rw [hcg]
    change (⟨v.proj, (2 / (1 - (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4))) •
      ((4 / (‖v.snd‖ ^ 2 + 4)) • v.snd)⟩ : TotalSpace Rr V) = v
    have hscalar :
        (2 / (1 - (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4))) *
          (4 / (‖v.snd‖ ^ 2 + 4)) = 1 := by
      field_simp
      ring
    rw [smul_smul, hscalar, one_smul]
  have hgf (z : Z) (hz : z ∈ U) : g (f z) = z := by
    apply c.injective
    rw [hcg]
    let v := (c z).val.1
    let t := (c z).val.2
    have hsphere : ‖v.snd‖ ^ 2 + t ^ 2 = 1 := (c z).property
    have hneq : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hq : ‖(f z).snd‖ ^ 2 = (2 / (1 - t)) ^ 2 * ‖v.snd‖ ^ 2 := by
      change ‖(2 / (1 - t)) • v.snd‖ ^ 2 = _
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hd : (2 / (1 - t)) ^ 2 * ‖v.snd‖ ^ 2 + 4 ≠ 0 := by
      rw [← hq]
      exact ne_of_gt (hden (f z))
    have hscalar : (4 / ((2 / (1 - t)) ^ 2 * ‖v.snd‖ ^ 2 + 4)) *
        (2 / (1 - t)) = 1 := by
      field_simp
      nlinarith
    have hvertical : ((2 / (1 - t)) ^ 2 * ‖v.snd‖ ^ 2 - 4) /
        ((2 / (1 - t)) ^ 2 * ‖v.snd‖ ^ 2 + 4) = t := by
      field_simp
      nlinarith
    apply Subtype.ext
    change ((⟨v.proj, (4 / (‖(f z).snd‖ ^ 2 + 4)) •
      ((2 / (1 - t)) • v.snd)⟩ : TotalSpace Rr V),
        (‖(f z).snd‖ ^ 2 - 4) / (‖(f z).snd‖ ^ 2 + 4)) = (c z).val
    rw [hq, smul_smul, hscalar, one_smul, hvertical]
  -- The fiberwise scalar operation is smooth for the original vector-bundle atlas.
  have hscale : ContMDiff K J ∞
      (fun a : TotalSpace Rr V × ℝ ↦
        (⟨a.1.proj, a.2 • a.1.snd⟩ : TotalSpace Rr V)) := by
    intro a
    let eV := trivializationAt Rr V a.1.proj
    have ha : a.1.proj ∈ eV.baseSet := mem_baseSet_trivializationAt Rr V a.1.proj
    apply (eV.contMDiffAt_iff (f := fun w : TotalSpace Rr V × ℝ ↦
      (⟨w.1.proj, w.2 • w.1.snd⟩ : TotalSpace Rr V)) ((eV.mem_source).mpr ha)).mpr
    have hfst : ContMDiffAt K J ∞ (fun w : TotalSpace Rr V × ℝ ↦ w.1) a :=
      contMDiffAt_fst
    have hparts := (eV.contMDiffAt_iff ((eV.mem_source).mpr ha)).mp hfst
    refine ⟨hparts.1, ?_⟩
    apply (contMDiffAt_snd.smul hparts.2).congr_of_eventuallyEq
    filter_upwards [hparts.1.continuousAt.preimage_mem_nhds (eV.open_baseSet.mem_nhds ha)]
      with w hw
    exact map_smul (eV.linearEquivAt ℝ w.1.proj hw) w.2 w.1.snd
  have hgin : ContMDiff J K ∞ (fun v : TotalSpace Rr V ↦ (invSphere v).val) := by
    have hd : ContMDiff J 𝓘(ℝ, ℝ) ∞
        (fun v : TotalSpace Rr V ↦ ‖v.snd‖ ^ 2 + 4) := hnorm.add contMDiff_const
    have hfactor : ContMDiff J 𝓘(ℝ, ℝ) ∞
        (fun v : TotalSpace Rr V ↦ 4 / (‖v.snd‖ ^ 2 + 4)) := by
      have hconst : ContMDiff J 𝓘(ℝ, ℝ) ∞
          (fun _ : TotalSpace Rr V ↦ (4 : ℝ)) := contMDiff_const
      apply (hconst.smul (hd.inv₀ (fun v ↦ ne_of_gt (hden v)))).congr
      intro v
      exact div_eq_mul_inv _ _
    have hlast : ContMDiff J 𝓘(ℝ, ℝ) ∞
        (fun v : TotalSpace Rr V ↦ (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4)) := by
      apply ((hnorm.sub (contMDiff_const (c := (4 : ℝ)))).smul
        (hd.inv₀ (fun v ↦ ne_of_gt (hden v)))).congr
      intro v
      exact div_eq_mul_inv _ _
    exact (hscale.comp (contMDiff_id.prodMk hfactor)).prodMk hlast
  have hgcont : Continuous g :=
    c.symm.continuous.comp (hgin.continuous.subtype_mk _)
  have hgsmooth : ContMDiff J Q ∞ g := by
    apply (ContMDiff.iff_comp_isImmersion hc.isImmersion).mpr
    refine ⟨hgcont, ?_⟩
    exact hgin.congr (fun v ↦ congrArg Subtype.val (hcg v))
  have hfsmooth : ContMDiffOn Q J ∞ f U := by
    have hdenom : ContMDiffOn Q 𝓘(ℝ, ℝ) ∞
        (fun z : Z ↦ 1 - (c z).val.2) U :=
      contMDiffOn_const.sub hc.contMDiff.snd.contMDiffOn
    have hfactor : ContMDiffOn Q 𝓘(ℝ, ℝ) ∞
        (fun z : Z ↦ 2 / (1 - (c z).val.2)) U := by
      have hconst : ContMDiffOn Q 𝓘(ℝ, ℝ) ∞ (fun _ : Z ↦ (2 : ℝ)) U :=
        contMDiffOn_const
      apply (hconst.smul
        (hdenom.inv₀ (fun z hz ↦ sub_ne_zero.mpr (Ne.symm hz)))).congr
      intro z _
      exact div_eq_mul_inv _ _
    exact hscale.comp_contMDiffOn (hc.contMDiff.fst.contMDiffOn.prodMk hfactor)
  have hopenU : IsOpen U := by
    exact isClosed_singleton.isOpen_compl.preimage hc.contMDiff.continuous.snd
  let e : OpenPartialHomeomorph Z (TotalSpace Rr V) :=
    { toFun := f
      invFun := g
      source := U
      target := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := fun v _ ↦ hgU v
      left_inv' := hgf
      right_inv' := fun v _ ↦ hfg v
      open_source := hopenU
      open_target := isOpen_univ
      continuousOn_toFun := hfsmooth.continuousOn
      continuousOn_invFun := hgcont.continuousOn }
  exact ⟨e, rfl, rfl, fun _ _ ↦ rfl, fun v ↦ congrArg Subtype.val (hcg v),
    hfsmooth, hgsmooth⟩

/-- The chosen stereographic chart on the original sphere, with the original bundle as target. -/
def frameSphereStereographic : OpenPartialHomeomorph Z (TotalSpace Rr V) :=
  (exists_frameSphereStereographic (EB := EB) r V).choose

/-- Both coordinates and smoothness refer to the same chosen stereographic chart. -/
theorem frameSphereStereographic_spec :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    let c := frameSphereHomeomorph (EB := EB) r V
    let e := frameSphereStereographic (EB := EB) r V
    e.source = {z : Z | (c z).val.2 ≠ 1} ∧
      e.target = Set.univ ∧
      (∀ z ∈ e.source,
        e z = ⟨(c z).val.1.proj, (2 / (1 - (c z).val.2)) • (c z).val.1.snd⟩) ∧
      (∀ v : TotalSpace Rr V,
        (c (e.symm v)).val =
          ((⟨v.proj, (4 / (‖v.snd‖ ^ 2 + 4)) • v.snd⟩ : TotalSpace Rr V),
            (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4))) ∧
      ContMDiffOn 𝓘(ℝ, EB × Rr) (𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)) ∞ e e.source ∧
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)) 𝓘(ℝ, EB × Rr) ∞ e.symm := by
  /- Extract all certificates from the single witness used by the selector.
  The source, target, inverse formulas and smoothness use that same chart;
  no second coordinate choice or scalar normalization is introduced. -/
  exact (exists_frameSphereStereographic (EB := EB) r V).choose_spec

end AtiyahSinger
