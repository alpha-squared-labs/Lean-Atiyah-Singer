/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousIdempotentKernel
public import AtiyahSinger.Topology.HermitianProjectiveBundle
public import AtiyahSinger.Topology.NormedFixedRankModel

/-!
# The original orthogonal complement over the projective bundle

Public module ID: M1893.

Over a rank-r-plus-one bundle, the complement to its tautological projective
line is literally the kernel of the supplied orthogonal projector. It has
the original subspace norm, the induced pullback total topology and the
restricted Hermitian form. The continuous idempotent-kernel theorem supplies
local triviality; rank-nullity gives its constant rank r.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin (r + 1))) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin (r + 1))) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin (r + 1))) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin (r + 1))) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

local instance : ∀ p : HermitianProjectiveBundle (r + 1) E h,
    NormedAddCommGroup (((hermitianProjectiveProjection (r + 1) E h :
      HermitianProjectiveBundle (r + 1) E h → X) *ᵖ E) p) :=
  fun p ↦ inferInstanceAs (NormedAddCommGroup (E p.1))

local instance : ∀ p : HermitianProjectiveBundle (r + 1) E h,
    NormedSpace ℂ (((hermitianProjectiveProjection (r + 1) E h :
      HermitianProjectiveBundle (r + 1) E h → X) *ᵖ E) p) :=
  fun p ↦ inferInstanceAs (NormedSpace ℂ (E p.1))

/-- The complementary fiber is the literal kernel of the original rank-one projector. -/
abbrev HermitianProjectiveComplement (p : HermitianProjectiveBundle (r + 1) E h) : Type u :=
  LinearMap.ker p.2.val.toLinearMap

/-- The complementary total space has the original pulled-back subspace topology. -/
@[reducible]
def hermitianProjectiveComplementTopology :
    TopologicalSpace (TotalSpace Unit (HermitianProjectiveComplement r E h)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (HermitianProjectiveComplement r E h) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace (EuclideanSpace ℂ (Fin (r + 1)))
        ((hermitianProjectiveProjection (r + 1) E h :
          HermitianProjectiveBundle (r + 1) E h → X) *ᵖ E))) inferInstance

attribute [local instance] hermitianProjectiveComplementTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The original projectors are continuous as endomorphisms of the same native pullback. -/
theorem continuous_hermitianProjectivePullbackProjection :
    let proj := hermitianProjectiveProjection (r + 1) E h
    let F := (proj : HermitianProjectiveBundle (r + 1) E h → X) *ᵖ E
    letI : FiberBundle (EuclideanSpace ℂ (Fin (r + 1))) F :=
      FiberBundle.pullback (F := EuclideanSpace ℂ (Fin (r + 1))) (E := E) proj
    letI : VectorBundle ℂ (EuclideanSpace ℂ (Fin (r + 1))) F :=
      VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin (r + 1))) (E := E) proj
    Continuous (fun p : HermitianProjectiveBundle (r + 1) E h ↦
      (⟨p, p.2.val⟩ : TotalSpace
        (EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (r + 1)))
          (fun p ↦ F p →L[ℂ] F p))) := by
  let V := EuclideanSpace ℂ (Fin (r + 1))
  let Q := HermitianProjectiveBundle (r + 1) E h
  let proj := hermitianProjectiveProjection (r + 1) E h
  let F := (proj : Q → X) *ᵖ E
  let : FiberBundle V F := FiberBundle.pullback (F := V) (E := E) proj
  let : VectorBundle ℂ V F := VectorBundle.pullback ℂ (F := V) (E := E) proj
  have hc : Continuous (fun p : Q ↦
      (p.1, (⟨p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
    continuous_induced_dom
  -- Pullback charts use exactly the original Hom coordinates at the projected base point.
  apply continuous_iff_continuousAt.mpr
  intro p
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨continuous_id.continuousAt, ?_⟩
  have hcoord := (continuousAt_hom_bundle (RingHom.id ℂ) _ (x₀ := p)).mp
    hc.snd.continuousAt
  apply hcoord.2.congr_of_eventuallyEq
  let e := trivializationAt V E p.1
  have hnear : ∀ᶠ q : Q in nhds p, q.1 ∈ e.baseSet :=
    proj.continuous.continuousAt.eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt V E p.1))
  filter_upwards [hnear] with q hq
  apply ContinuousLinearMap.ext
  intro v
  change ((e.pullback proj).continuousLinearMapAt ℂ q)
      (q.2.val ((e.pullback proj).symmL ℂ q v)) =
    e.continuousLinearMapAt ℂ q.1 (q.2.val (e.symmL ℂ q.1 v))
  rw [e.continuousLinearMapAt_apply_of_mem ℂ hq,
    (e.pullback proj).continuousLinearMapAt_apply_of_mem ℂ hq,
    e.symmL_apply hq, (e.pullback proj).symmL_apply hq]
  rw [(e.pullback proj).symm_apply hq]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The literal complementary kernels form a locally finite-rank complex bundle. -/
theorem isFiniteRank_hermitianProjectiveComplement :
    IsFiniteRank (HermitianProjectiveComplement r E h) := by
  let V := EuclideanSpace ℂ (Fin (r + 1))
  let Q := HermitianProjectiveBundle (r + 1) E h
  let proj := hermitianProjectiveProjection (r + 1) E h
  let F := (proj : Q → X) *ᵖ E
  let : FiberBundle V F := FiberBundle.pullback (F := V) (E := E) proj
  let : VectorBundle ℂ V F := VectorBundle.pullback ℂ (F := V) (E := E) proj
  have hk := isFiniteRank_idempotentKernel V F (fun p ↦ p.2.val)
    (continuous_hermitianProjectivePullbackProjection r E h) (fun p ↦ p.2.property.1)
  exact hk

/-- Rank-nullity gives the exact complementary rank, including a zero-dimensional complement. -/
theorem finrank_hermitianProjectiveComplement (p : HermitianProjectiveBundle (r + 1) E h) :
    Module.finrank ℂ (HermitianProjectiveComplement r E h p) = r := by
  let V := EuclideanSpace ℂ (Fin (r + 1))
  let : FiniteDimensional ℂ (E p.1) := VectorBundle.finiteDimensional ℂ V E p.1
  have hd : Module.finrank ℂ (E p.1) = r + 1 := by
    have he := ((trivializationAt V E p.1).linearEquivAt ℂ p.1
      (FiberBundle.mem_baseSet_trivializationAt V E p.1)).finrank_eq
    simpa [V] using he
  have hr := p.2.val.toLinearMap.finrank_range_add_finrank_ker
  rw [p.2.property.2.1, hd] at hr
  change Module.finrank ℂ (LinearMap.ker p.2.val.toLinearMap) = r
  omega

/-- The actual complementary projection sends v to v minus its specified rank-one projection. -/
def hermitianProjectiveComplementProjection (p : HermitianProjectiveBundle (r + 1) E h) :
    E p.1 →L[ℂ] HermitianProjectiveComplement r E h p :=
  (ContinuousLinearMap.id ℂ (E p.1) - p.2.val).codRestrict _ (by
    intro v
    have hp : p.2.val (p.2.val v) = p.2.val v := DFunLike.congr_fun p.2.property.1 v
    change p.2.val (v - p.2.val v) = 0
    rw [map_sub, hp, sub_self])

/-- Retype the complementary total topology for the standard rank-r complex model. -/
@[reducible]
def hermitianProjectiveComplementModelTopology :
    TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r))
      (HermitianProjectiveComplement r E h)) :=
  nativeModelTopology (HermitianProjectiveComplement r E h) (EuclideanSpace ℂ (Fin r))

attribute [local instance] hermitianProjectiveComplementModelTopology

/-- Native complementary charts use the existing subspace norms and the actual induced topology. -/
@[reducible]
def hermitianProjectiveComplementFiberBundle :
    FiberBundle (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h) := by
  letI := isFiniteRank_hermitianProjectiveComplement r E h
  exact (exists_nativeFiberBundle_of_normedFibers (HermitianProjectiveComplement r E h) r
    (finrank_hermitianProjectiveComplement r E h)).choose

attribute [local instance] hermitianProjectiveComplementFiberBundle

set_option linter.defProp false in
/-- The selected native complementary charts have complex-linear continuous transitions. -/
@[reducible]
def hermitianProjectiveComplementVectorBundle :
    VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h) := by
  let := isFiniteRank_hermitianProjectiveComplement r E h
  exact (exists_nativeFiberBundle_of_normedFibers (HermitianProjectiveComplement r E h) r
    (finrank_hermitianProjectiveComplement r E h)).choose_spec

attribute [local instance] hermitianProjectiveComplementVectorBundle

/-- The two inverse phantom-model retypings recover the exact complementary total topology. -/
theorem modelTopology_hermitianProjectiveComplement :
    modelTopology (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h) =
      hermitianProjectiveComplementTopology r E h := by
  dsimp only [modelTopology, hermitianProjectiveComplementModelTopology, nativeModelTopology]
  rw [induced_compose]
  exact induced_id

/-- The complement carries the restriction of the same supplied Hermitian form. -/
def hermitianProjectiveComplementMetric :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h)
    ContinuousHermitianMetric (HermitianProjectiveComplement r E h) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin (r + 1))) E
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h)
  refine
    { toCore := fun p ↦
        { inner := fun v w ↦ (h.toCore p.1).inner v.val w.val
          conj_inner_symm := fun v w ↦ (h.toCore p.1).conj_inner_symm v.val w.val
          re_inner_nonneg := fun v ↦ (h.toCore p.1).re_inner_nonneg v.val
          add_left := fun v w z ↦ (h.toCore p.1).add_left v.val w.val z.val
          smul_left := fun v w a ↦ (h.toCore p.1).smul_left v.val w.val a
          definite := fun v hv ↦ Subtype.ext ((h.toCore p.1).definite v.val hv) }
      continuous_pairing := ?_
      isFiniteRank := isFiniteRank_model (EuclideanSpace ℂ (Fin r))
        (HermitianProjectiveComplement r E h) }
  rw [modelTopology_hermitianProjectiveComplement]
  let := hermitianProjectiveComplementTopology r E h
  let V := EuclideanSpace ℂ (Fin (r + 1))
  let Q := HermitianProjectiveBundle (r + 1) E h
  let K := HermitianProjectiveComplement r E h
  let proj := hermitianProjectiveProjection (r + 1) E h
  let F := (proj : Q → X) *ᵖ E
  let := modelTopology V E
  let := sumTopology (E := E) (F := E)
  let := sumTopology (E := K) (F := K)
  have hinc : Continuous (fun z : TotalSpace Unit K ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace V F)) := continuous_induced_dom
  have hlift : Continuous (fun z : TotalSpace Unit K ↦
      (⟨z.proj.1, z.snd.val⟩ : TotalSpace Unit E)) :=
    (continuous_unitTotalEquiv_symm V E).comp ((Pullback.continuous_lift V E proj).comp hinc)
  have hp : Continuous (fun z : TotalSpace Unit (K ×ᵇ K) ↦
      (⟨z.proj.1, z.snd.1.val, z.snd.2.val⟩ : TotalSpace Unit (E ×ᵇ E))) := by
    apply continuous_induced_rng.mpr
    exact (hlift.comp (continuous_sum_fst (E := K) (F := K))).prodMk
      (hlift.comp (continuous_sum_snd (E := K) (F := K)))
  exact h.continuous_pairing.comp hp

end AtiyahSinger.ComplexBundle
