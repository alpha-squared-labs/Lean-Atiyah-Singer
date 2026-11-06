/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRadialCompression
public import AtiyahSinger.Geometry.BundleVaryingRadius
public import AtiyahSinger.Geometry.NormalBundle
public import AtiyahSinger.Geometry.NormalTubularGerm
public import AtiyahSinger.Geometry.SmoothRiemannianMetric
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Normalized tubular neighborhoods of the actual quotient normal bundle

Public module ID: M1505.

A tubular neighborhood identifies the whole normal bundle with an open
neighborhood of the embedded manifold. In addition to fixing the zero section,
the induced derivative on the normal quotient is the identity. This last
condition fixes the normal identification: an arbitrary fiber reflection must
not be accepted as the same normalized tube.

The derivative is written in a fiber chart of the same selected normal atlas.
Its chart inverse is a continuous linear isomorphism, so the displayed equation
is precisely the intrinsic normal derivative identity. The zero-section equation
identifies its target tangent space with the tangent space at the original image.
The germ-compression proof chooses an auxiliary smooth metric on the normal
bundle, compatible with its quotient topology; the tube data require no metric.

The carrier is the actual quotient normal bundle defined in `NormalBundle`,
with its coinduced topology and the same selected smooth quotient atlas. MS
Section 11, Theorem 11.1 states the tubular neighborhood theorem. Its detailed
proof in the supplied book treats a compact submanifold; the noncompact case
is referred to Lang and needs a varying positive smooth radius. The extension
to the quotient model uses HU XVIII.2.6 and the standard smooth analogue of
HU III.9.6: the latter states continuous splitting, while the smooth version
uses smooth local splittings and a smooth partition of unity. This source
boundary is retained in the proof outline.

The theorem below is restricted to proper smooth embeddings of second-countable
Hausdorff finite-dimensional real manifolds without boundary. No chosen tube is
asserted canonical, and no isotopy between arbitrary choices is supplied here.
The proof uses a normalized local addition and a smooth right inverse of the
actual quotient map. Noncompact shrinking yields one inverse branch along the
entire zero section; a positive smooth varying radius and normalized radial
compression then give a diffeomorphism from the whole original normal bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

/-- A standard tubular neighborhood, normalized on the actual quotient normal fibers. -/
structure TubularNeighborhood where
  /-- The open neighborhood in the original ambient manifold. -/
  target : TopologicalSpace.Opens N
  /-- A diffeomorphism from the whole original normal bundle onto this open neighborhood. -/
  diffeomorph :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    Diffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F)
      (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) target ∞
  /-- The zero section is sent to the original embedding, pointwise. -/
  map_zero : ∀ x : M, (diffeomorph ⟨x, 0⟩ : N) = f x
  /-- The derivative is the identity on the normal quotient, in its selected fiber chart. -/
  normal_deriv :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    ∀ x : M,
      let e := (trivializationAt (NormalModel E F)
        (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt (NormalModel E F)
          (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x)
      ∀ v : NormalModel E F,
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F)
            (fun w ↦ (diffeomorph ⟨x, e.symm w⟩ : N)) 0
            ((NormedSpace.fromTangentSpace (0 : NormalModel E F)).symm v)) = e.symm v

namespace TubularNeighborhood

/-- The actual continuous tubular map into the original ambient manifold. -/
def totalMap (T : TubularNeighborhood f hf) :
    C(TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f), N) := by
  letI := normalBundleFiberBundle f hf
  exact
    { toFun := fun z ↦ T.diffeomorph z
      continuous_toFun := continuous_subtype_val.comp T.diffeomorph.continuous }

end TubularNeighborhood

section GermCompression

variable [T2Space M] [SecondCountableTopology M]

set_option maxHeartbeats 600000 in
-- The final chain rule unfolds the selected quotient atlas and compatible metric instances.
/-- A normalized tubular germ extends to the whole normal bundle by compression within each
fiber. Every value of the resulting tube is a value of the given germ over the same base point. -/
theorem exists_tubularNeighborhood_of_normalTubeGerm :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F)) 𝓘(ℝ, F)
        (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) N ∞,
      (∀ x, (⟨x, 0⟩ : TotalSpace _ _) ∈ Ψ.source) →
      (∀ x, Ψ ⟨x, 0⟩ = f x) →
      (∀ x : M,
        let e := (trivializationAt (NormalModel E F)
          (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x).continuousLinearEquivAt ℝ x
          (mem_baseSet_trivializationAt (NormalModel E F)
            (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f) x)
        ∀ v : NormalModel E F,
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, NormalModel E F) 𝓘(ℝ, F)
              (fun w ↦ Ψ ⟨x, e.symm w⟩) 0
                ((NormedSpace.fromTangentSpace (0 : NormalModel E F)).symm v)) = e.symm v) →
      ∃ tube : TubularNeighborhood f hf,
        ∀ z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f),
          ∃ w ∈ Ψ.source, w.proj = z.proj ∧ tube.totalMap f hf z = Ψ w := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : ParacompactSpace M := inferInstance
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  intro Ψ hΨzero hΨmap hΨnormal
  -- Choose a smooth metric compatible with the original normal topology and atlas.
  let m := smoothRiemannianMetric (EB := E) G V
  let : RiemannianBundle V := ⟨m.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle G V :=
    ⟨⟨m.inner, m.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ G V :=
    ⟨m.inner, m.contMDiff, fun _ _ _ ↦ rfl⟩
  obtain ⟨ε, hεpos, hεsub⟩ :=
    exists_contMDiff_radius_subset (EB := E) Ψ.open_source hΨzero
  let q (z : NB) : ℝ := inner ℝ z.snd z.snd / (ε z.proj) ^ 2
  have hq : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ) ∞ q := by
    have hinner : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ) ∞
        (fun z : NB ↦ inner ℝ z.snd z.snd) := contMDiff_id.inner_bundle contMDiff_id
    exact hinner.mul (((ε.contMDiff.comp (contMDiff_proj V)).pow 2).inv₀
      (fun z ↦ pow_ne_zero 2 (hεpos z.proj).ne'))
  have hqnonneg (z : NB) : 0 ≤ q z := div_nonneg (real_inner_self_nonneg) (sq_nonneg _)
  have hqzero (x : M) : q (⟨x, 0⟩ : NB) = 0 := by simp [q]
  have hquad (a : ℝ) (z : NB) : q ⟨z.proj, a • z.snd⟩ = a ^ 2 * q z := by
    simp only [q, real_inner_smul_left, real_inner_smul_right]
    ring
  have hqsub (z : NB) (hz : q z < 1) : z ∈ Ψ.source := by
    apply hεsub z.proj z.snd
    have h := (div_lt_one (sq_pos_of_pos (hεpos z.proj))).mp hz
    rw [real_inner_self_eq_norm_sq] at h
    exact (sq_lt_sq₀ (norm_nonneg z.snd) (hεpos z.proj).le).mp h
  -- The time-one radial formula maps the whole normal bundle diffeomorphically to this disk.
  let C := bundleRadialCompressionCylinder q hq.continuous hquad
  have hsource (z : NB) : (1, z) ∈ C.source := by
    change 0 < 1 + 1 * q z
    linarith [hqnonneg z]
  have htarget (z : NB) (hz : q z < 1) : (1, z) ∈ C.target := by
    change 0 < 1 - 1 * q z
    linarith
  have hR := contMDiffOn_bundleRadialCompression q hq
  let R : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, G)) NB NB ∞ :=
    { toFun := fun z ↦ bundleRadialCompression q (1, z)
      invFun := fun z ↦ bundleRadialCompression q (-1, z)
      source := univ
      target := {z | q z < 1}
      map_source' := fun z _ ↦ by
        have h := C.map_source (hsource z)
        change 0 < 1 - 1 * q (bundleRadialCompression q (1, z)) at h
        change q (bundleRadialCompression q (1, z)) < 1
        linarith
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := fun z _ ↦ congrArg Prod.snd (C.left_inv (hsource z))
      right_inv' := fun z hz ↦ congrArg Prod.snd (C.right_inv (htarget z hz))
      open_source := isOpen_univ
      open_target := isOpen_lt hq.continuous continuous_const
      contMDiffOn_toFun := hR.comp
        (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun z _ ↦ hsource z)
      contMDiffOn_invFun := hR.comp
        (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun z hz ↦ by
          change 0 < 1 + -1 * q z
          change q z < 1 at hz
          linarith) }
  have hRzero (x : M) : R (⟨x, 0⟩ : NB) = ⟨x, 0⟩ := by
    change (⟨x, (Real.sqrt (1 + 1 * q ⟨x, 0⟩))⁻¹ • (0 : V x)⟩ : NB) = _
    rw [smul_zero]
  let K := R.trans Ψ
  have hKsource (z : NB) : z ∈ K.source :=
    ⟨mem_univ z, hqsub _ (R.toPartialEquiv.map_source (mem_univ z))⟩
  let T : TopologicalSpace.Opens N := ⟨K.target, K.open_target⟩
  let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) NB T ∞ :=
    { toFun := fun z ↦ ⟨K z, K.toPartialEquiv.map_source (hKsource z)⟩
      invFun := fun y ↦ K.toPartialEquiv.symm y.val
      left_inv := fun z ↦ K.toPartialEquiv.left_inv (hKsource z)
      right_inv := fun y ↦ Subtype.ext (K.toPartialEquiv.right_inv y.property)
      contMDiff_toFun := by
        apply (ContMDiff.subtypeVal_comp_iff T _).mp
        intro z
        exact K.contMDiffOn.contMDiffAt (K.open_source.mem_nhds (hKsource z))
      contMDiff_invFun := by
        intro y
        change ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
          (fun y : T ↦ K.toPartialEquiv.symm y.val) y
        apply contMDiffAt_subtype_iff.mpr
        exact K.contMDiffOn_invFun.contMDiffAt (K.open_target.mem_nhds y.property) }
  have hDapply (z : NB) : (D z : N) = Ψ (R z) := rfl
  have htube : ∃ tube : TubularNeighborhood f hf,
      ∀ z : NB, tube.totalMap f hf z = Ψ (R z) := by
    refine ⟨⟨T, D, ?_, ?_⟩, fun _ ↦ rfl⟩
    · intro x
      rw [hDapply, hRzero]
      exact hΨmap x
    · -- Radial compression has identity differential at zero in the same selected fiber chart.
      intro x
      dsimp only
      let t := trivializationAt G V x
      have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt G V x
      let e := t.continuousLinearEquivAt ℝ x hx
      let incl : G → NB := fun w ↦ ⟨x, e.symm w⟩
      have hi : ContMDiff 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ incl := by
        intro w
        rw [t.contMDiffAt_iff (t.mem_source.mpr hx)]
        refine ⟨contMDiffAt_const, ?_⟩
        apply contMDiffAt_id.congr_of_eventuallyEq
        apply Filter.Eventually.of_forall
        intro v
        change (t ⟨x, e.symm v⟩).2 = v
        rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx]
        exact e.apply_symm_apply v
      let c (w : G) : ℝ := (Real.sqrt (1 + q (incl w)))⁻¹
      have hc₀ : c 0 = 1 := by simp [c, incl, hqzero]
      have hqcurve : ContDiff ℝ ∞ (q ∘ incl) :=
        contMDiff_iff_contDiff.mp (hq.comp hi)
      have hc : ContDiffAt ℝ ∞ c 0 := by
        have hd : ContDiffAt ℝ ∞ (fun w ↦ 1 + q (incl w)) 0 :=
          contDiffAt_const.add hqcurve.contDiffAt
        have hpos : 0 < 1 + q (incl 0) := by linarith [hqnonneg (incl 0)]
        exact ((Real.contDiffAt_sqrt hpos.ne').comp 0 hd).inv (Real.sqrt_pos.mpr hpos).ne'
      let α (w : G) : G := c w • w
      have hαzero : α 0 = 0 := smul_zero _
      have hα : HasFDerivAt α (ContinuousLinearMap.id ℝ G) 0 := by
        have h : HasFDerivAt α
            (c 0 • ContinuousLinearMap.id ℝ G + (fderiv ℝ c 0).smulRight (0 : G)) 0 :=
          (hc.differentiableAt (by simp)).hasFDerivAt.smul (hasFDerivAt_id (0 : G))
        rw [hc₀, one_smul, ContinuousLinearMap.smulRight_zero, add_zero] at h
        exact h
      let b (w : G) : N := Ψ (incl w)
      have hb : ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, F) ∞ b 0 := by
        have hzero : incl 0 ∈ Ψ.source := by
          change (⟨x, e.symm 0⟩ : NB) ∈ Ψ.source
          rw [e.symm.map_zero]
          exact hΨzero x
        exact (Ψ.contMDiffOn.contMDiffAt (Ψ.open_source.mem_nhds hzero)).comp 0 hi.contMDiffAt
      let B : G →L[ℝ] F := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) b 0
      have hB : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, F) b (α 0) B := by
        rw [hαzero]
        exact (hb.mdifferentiableAt (by simp)).hasMFDerivAt
      have hcomp : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, F) (b ∘ α) 0 B := by
        simpa only [ContinuousLinearMap.comp_id] using! hB.comp 0 hα.hasMFDerivAt
      have heq : (fun w : G ↦ (D ⟨x, e.symm w⟩ : N)) = b ∘ α := by
        funext w
        rw [hDapply]
        change Ψ (⟨x, (Real.sqrt (1 + 1 * q (incl w)))⁻¹ • e.symm w⟩ : NB) =
          Ψ ⟨x, e.symm (c w • w)⟩
        rw [map_smul, one_mul]
      intro v
      rw [heq, hcomp.mfderiv]
      exact hΨnormal x v
  obtain ⟨tube, htube⟩ := htube
  refine ⟨tube, fun z ↦ ⟨R z, ?_, rfl, htube z⟩⟩
  exact hqsub _ (R.toPartialEquiv.map_source (mem_univ z))

end GermCompression

variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]

/-- The tubular neighborhood theorem for a proper smooth embedding and its quotient normal. -/
theorem nonempty_tubularNeighborhood (he : IsEmbedding f) (hp : IsProperMap f) :
    Nonempty (TubularNeighborhood f hf) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  cases isEmpty_or_nonempty M with
  | inl hEmpty =>
    let := hEmpty
    let : IsEmpty NB := ⟨fun z ↦ isEmptyElim z.proj⟩
    let T : TopologicalSpace.Opens N := ⊥
    let : IsEmpty T := ⟨fun y ↦ y.property⟩
    let D : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) NB T ∞ :=
      { toEquiv := Equiv.equivOfIsEmpty _ _
        contMDiff_toFun := fun z ↦ isEmptyElim z
        contMDiff_invFun := fun z ↦ isEmptyElim z }
    exact ⟨⟨T, D, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩⟩
  | inr hNonempty =>
    let := hNonempty
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
    let : ParacompactSpace M := inferInstance
    obtain ⟨Ψ, hΨzero, hΨmap, hΨnormal⟩ := exists_normalTubeGerm f hf he hp
    obtain ⟨T, _⟩ := exists_tubularNeighborhood_of_normalTubeGerm f hf Ψ
      hΨzero hΨmap hΨnormal
    exact ⟨T⟩

end AtiyahSinger
