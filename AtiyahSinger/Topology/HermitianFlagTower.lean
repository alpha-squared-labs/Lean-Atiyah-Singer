/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagBundle
public import AtiyahSinger.Topology.HermitianProjectiveComplement

/-!
# The actual projective-to-flag tower

Public module ID: M1885.

An ordered flag in the orthogonal complement of a specified projective line
gives an ordered flag in the original bundle by prepending that line. The
complement has its original subspace norm and induced topology. The map below
uses the literal original projection tuples and preserves the base projection.
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

attribute [local instance] hermitianProjectiveTopology hermitianFlagTopology
  hermitianProjectiveComplementModelTopology
  hermitianProjectiveComplementFiberBundle hermitianProjectiveComplementVectorBundle

local instance : TopologicalSpace (TotalSpace Unit (HermitianProjectiveComplement r E h)) :=
  modelTopology (EuclideanSpace ℂ (Fin r)) (HermitianProjectiveComplement r E h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem complementMetric_inner (p : HermitianProjectiveBundle (r + 1) E h)
    (v w : HermitianProjectiveComplement r E h p) :
    letI := modelTopology (EuclideanSpace ℂ (Fin (r + 1))) E
    ((hermitianProjectiveComplementMetric r E h).toCore p).inner v w =
      (h.toCore p.1).inner v.val w.val := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Extend the complementary flag projections by zero on the specified first projective line. -/
def hermitianFlagTowerFiber (p : HermitianProjectiveBundle (r + 1) E h)
    (q : HermitianFlagSpace r (HermitianProjectiveComplement r E h p)
      ((hermitianProjectiveComplementMetric r E h).toCore p)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin (r + 1))) E
    HermitianFlagSpace (r + 1) (E p.1) (h.toCore p.1) := by
  classical
  letI := modelTopology (EuclideanSpace ℂ (Fin (r + 1))) E
  let K := LinearMap.ker p.2.val.toLinearMap
  let incl : K →L[ℂ] E p.1 := K.subtypeL
  let proj := hermitianProjectiveComplementProjection r E h p
  let L (i : Fin r) : E p.1 →L[ℂ] E p.1 := incl.comp ((q.val i).comp proj)
  -- The original complementary projection retracts the literal subspace inclusion.
  have hproj (v : K) : proj (incl v) = v := by
    apply Subtype.ext
    change v.val - p.2.val v.val = v.val
    have hv : p.2.val v.val = 0 := v.property
    rw [hv, sub_zero]
  have hprojP (v : E p.1) : proj (p.2.val v) = 0 := by
    apply Subtype.ext
    change p.2.val v - p.2.val (p.2.val v) = 0
    have hp : p.2.val (p.2.val v) = p.2.val v := DFunLike.congr_fun p.2.property.1 v
    rw [hp, sub_self]
  have hsurj : Function.Surjective proj := fun v ↦ ⟨incl v, hproj v⟩
  have hLL (i j : Fin r) : (L i).comp (L j) =
      incl.comp (((q.val i).comp (q.val j)).comp proj) := by
    ext v
    exact congrArg incl (congrArg (q.val i) (hproj (q.val j (proj v))))
  -- Extension preserves each rank because the retraction is onto and inclusion is injective.
  have hrank (i : Fin r) : Module.finrank ℂ (LinearMap.range (L i).toLinearMap) = 1 := by
    change Module.finrank ℂ (LinearMap.range
      (K.subtype.comp ((q.val i).toLinearMap.comp proj.toLinearMap))) = 1
    rw [LinearMap.range_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj),
      Submodule.finrank_map_subtype_eq]
    exact q.property.2.1 i
  have hinner_right (v : K) (w : E p.1) :
      (h.toCore p.1).inner v.val (proj w).val = (h.toCore p.1).inner v.val w := by
    have hv : p.2.val v.val = 0 := v.property
    change (h.toCore p.1).inner v.val (w - p.2.val w) = _
    rw [InnerProductSpace.Core.inner_sub_right (c := (h.toCore p.1).toCore),
      ← p.2.property.2.2 v.val w,
      hv, InnerProductSpace.Core.inner_zero_left (c := (h.toCore p.1).toCore), sub_zero]
  have hinner_left (v : E p.1) (w : K) :
      (h.toCore p.1).inner (proj v).val w.val = (h.toCore p.1).inner v w.val := by
    have hw : p.2.val w.val = 0 := w.property
    change (h.toCore p.1).inner (v - p.2.val v) w.val = _
    rw [InnerProductSpace.Core.inner_sub_left (c := (h.toCore p.1).toCore),
      p.2.property.2.2 v w.val,
      hw, InnerProductSpace.Core.inner_zero_right (c := (h.toCore p.1).toCore), sub_zero]
  refine ⟨Fin.cons p.2.val L, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases p.2.property.1 (fun j ↦ ?_) i
    change (L j).comp (L j) = L j
    rw [hLL, q.property.1 j]
  · intro i
    exact Fin.cases p.2.property.2.1 hrank i
  · intro i j hij
    refine Fin.cases (fun j hij ↦ ?_) (fun i j hij ↦ ?_) i j hij
    · refine Fin.cases (fun hne ↦ (hne rfl).elim) (fun k _ ↦ ?_) j hij
      ext v
      exact (q.val k (proj v)).property
    · refine Fin.cases (fun _ ↦ ?_) (fun j hij ↦ ?_) j hij
      · ext v
        change incl (q.val i (proj (p.2.val v))) = 0
        rw [hprojP, map_zero, map_zero]
      · change (L i).comp (L j) = 0
        rw [hLL, q.property.2.2.1 i j (fun he ↦ hij (congrArg Fin.succ he))]
        ext v
        exact map_zero incl
  · -- The complementary flag sums to its identity, hence to id minus the first projector.
    ext v
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      add_apply, sum_apply]
    change p.2.val v + ∑ i, incl (q.val i (proj v)) = v
    rw [← map_sum incl, ← sum_apply, q.property.2.2.2.1]
    change p.2.val v + (v - p.2.val v) = v
    abel
  · intro i
    refine Fin.cases p.2.property.2.2 (fun j u v ↦ ?_) i
    change (h.toCore p.1).inner (q.val j (proj u)).val v =
      (h.toCore p.1).inner u (q.val j (proj v)).val
    calc
      _ = (h.toCore p.1).inner (q.val j (proj u)).val (proj v).val :=
        (hinner_right (q.val j (proj u)) v).symm
      _ = (h.toCore p.1).inner (proj u).val (q.val j (proj v)).val :=
        by simpa only [complementMetric_inner] using q.property.2.2.2.2 j (proj u) (proj v)
      _ = _ := hinner_left u (q.val j (proj v))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Extend the complementary projections continuously in the original native Hom coordinates.
private theorem continuous_flagTowerColumn (i : Fin r) :
    Continuous (fun z : HermitianFlagBundle r (HermitianProjectiveComplement r E h)
      (hermitianProjectiveComplementMetric r E h) ↦
      (⟨z.1.1, (LinearMap.ker z.1.2.val.toLinearMap).subtypeL.comp
        ((z.2.val i).comp (hermitianProjectiveComplementProjection r E h z.1))⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ]
          EuclideanSpace ℂ (Fin (r + 1))) (fun x ↦ E x →L[ℂ] E x))) := by
  let V := EuclideanSpace ℂ (Fin (r + 1))
  let W := EuclideanSpace ℂ (Fin r)
  let Q := HermitianProjectiveBundle (r + 1) E h
  let K := HermitianProjectiveComplement r E h
  let S := HermitianFlagBundle r K (hermitianProjectiveComplementMetric r E h)
  let base := hermitianProjectiveProjection (r + 1) E h
  let first := hermitianFlagProjection r K (hermitianProjectiveComplementMetric r E h)
  let F := (base : Q → X) *ᵖ E
  have hb : Continuous (fun z : S ↦ z.1.1) := base.continuous.comp first.continuous
  have hpraw : Continuous (fun p : Q ↦
      (p.1, (⟨p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)))) :=
    continuous_induced_dom
  have hP : Continuous (fun z : S ↦
      (⟨z.1.1, z.1.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) :=
    hpraw.snd.comp first.continuous
  have hqraw : Continuous (fun z : S ↦
      (z.1, fun j : Fin r ↦
        (⟨z.1, z.2.val j⟩ : TotalSpace (W →L[ℂ] W) (fun p ↦ K p →L[ℂ] K p)))) :=
    continuous_induced_dom
  have hQ : Continuous (fun z : S ↦
      (⟨z.1, z.2.val i⟩ : TotalSpace (W →L[ℂ] W) (fun p ↦ K p →L[ℂ] K p))) :=
    (continuous_apply i).comp hqraw.snd
  -- Native complementary vectors retain the same induced pullback embedding.
  let := hermitianProjectiveComplementTopology r E h
  have hnative : Topology.IsInducing (fun z : TotalSpace W K ↦
      (⟨z.proj, z.snd⟩ : TotalSpace Unit K)) := ⟨rfl⟩
  have hsub : Topology.IsInducing (fun z : TotalSpace Unit K ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace V F)) := ⟨rfl⟩
  have htest : Topology.IsInducing (fun z : TotalSpace W K ↦
      (z.proj, (⟨z.proj.1, z.snd.val⟩ : TotalSpace V E))) :=
    (inducing_pullbackTotalSpaceEmbedding V E base).comp (hsub.comp hnative)
  have hinc : Continuous (fun z : TotalSpace W K ↦
      (⟨z.proj.1, z.snd.val⟩ : TotalSpace V E)) := htest.continuous.snd
  -- In finite-dimensional native Hom coordinates, continuity is detected on each vector.
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hb.continuousAt, ?_⟩
  apply continuousAt_clm_apply.mpr
  intro v
  let e := trivializationAt V E z₀.1.1
  have hz₀ : z₀.1.1 ∈ e.baseSet := mem_baseSet_trivializationAt V E z₀.1.1
  have hnear : ∀ᶠ z : S in nhds z₀, z.1.1 ∈ e.baseSet :=
    hb.continuousAt.eventually (e.open_baseSet.mem_nhds hz₀)
  have hsection (w : S → V) (hw : ContinuousAt w z₀) :
      ContinuousAt (fun z : S ↦
        (⟨z.1.1, e.symmL ℂ z.1.1 (w z)⟩ : TotalSpace V E)) z₀ := by
    have hc := (e.toOpenPartialHomeomorph.continuousAt_symm
      (e.mem_target.mpr hz₀)).comp (hb.continuousAt.prodMk hw)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    rw [e.symmL_apply hz, e.mk_symm hz]
    rfl
  let u (z : S) := e.symmL ℂ z.1.1 v
  let A (z : S) : V →L[ℂ] V :=
    (e.continuousLinearMapAt ℂ z.1.1).comp (z.1.2.val.comp (e.symmL ℂ z.1.1))
  have hA : ContinuousAt A z₀ :=
    ((continuousAt_hom_bundle (RingHom.id ℂ) _).mp hP.continuousAt).2
  -- The actual vector v-Pv is recovered in the same original chart before restriction to ker P.
  have hcomplement : ContinuousAt (fun z : S ↦
      (⟨z.1.1, u z - z.1.2.val (u z)⟩ : TotalSpace V E)) z₀ := by
    have hc := hsection (fun z ↦ v - A z v)
      (continuousAt_const.sub (hA.clm_apply continuousAt_const))
    apply hc.congr_of_eventuallyEq
    filter_upwards [hnear] with z hz
    apply TotalSpace.mk_inj.mpr
    rw [map_sub]
    change u z - z.1.2.val (u z) =
      u z - e.symmL ℂ z.1.1 (e.continuousLinearMapAt ℂ z.1.1 (z.1.2.val (u z)))
    rw [e.symmL_continuousLinearMapAt hz]
  have hk : ContinuousAt (fun z : S ↦
      (⟨z.1, hermitianProjectiveComplementProjection r E h z.1 (u z)⟩ :
        TotalSpace W K)) z₀ :=
    htest.continuousAt_iff.mpr (first.continuous.continuousAt.prodMk hcomplement)
  have hout := hinc.continuousAt.comp (hQ.continuousAt.clm_bundle_apply hk)
  have hcoord := (e.continuousAt (e.mem_source.mpr hz₀)).comp hout
  apply hcoord.snd.congr_of_eventuallyEq
  filter_upwards [hnear] with z hz
  exact e.continuousLinearMapAt_apply_of_mem ℂ hz _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Prepending the specified projective line assembles the actual original flag continuously. -/
def hermitianFlagTowerAssembly :
    C(HermitianFlagBundle r (HermitianProjectiveComplement r E h)
      (hermitianProjectiveComplementMetric r E h), HermitianFlagBundle (r + 1) E h) where
  toFun z := ⟨z.1.1, hermitianFlagTowerFiber r E h z.1 z.2⟩
  continuous_toFun := by
    let K := HermitianProjectiveComplement r E h
    let S := HermitianFlagBundle r K (hermitianProjectiveComplementMetric r E h)
    let first := hermitianFlagProjection r K (hermitianProjectiveComplementMetric r E h)
    have hb := (hermitianProjectiveProjection (r + 1) E h).continuous.comp first.continuous
    apply continuous_induced_rng.mpr
    refine hb.prodMk (continuous_pi (fun i ↦ ?_))
    refine Fin.cases ?_ (fun j ↦ continuous_flagTowerColumn r E h j) i
    have hp : Continuous (fun p : HermitianProjectiveBundle (r + 1) E h ↦
        (p.1, (⟨p.1, p.2.val⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ]
            EuclideanSpace ℂ (Fin (r + 1))) (fun x ↦ E x →L[ℂ] E x)))) :=
      continuous_induced_dom
    exact hp.snd.comp first.continuous

/-- The assembly map commutes with the original two successive base projections. -/
theorem hermitianFlagProjection_comp_towerAssembly :
    (hermitianFlagProjection (r + 1) E h).comp (hermitianFlagTowerAssembly r E h) =
      (hermitianProjectiveProjection (r + 1) E h).comp
        (hermitianFlagProjection r (HermitianProjectiveComplement r E h)
          (hermitianProjectiveComplementMetric r E h)) := by
  rfl

end AtiyahSinger.ComplexBundle
