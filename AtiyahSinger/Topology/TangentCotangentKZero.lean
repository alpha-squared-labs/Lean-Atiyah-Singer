/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.TangentMusical
public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# The metric-independent tangent and cotangent compact-support K equivalence

Public module ID: M2227.

A supplied smooth tangent metric gives the actual musical homeomorphism from
the original tangent bundle to its real continuous dual bundle. Transport by
this homeomorphism is the existing inverse pullback on compact-support K groups.
The resulting additive equivalence is independent of the supplied metric.

The metric homotopy must be proper as a whole. For the inverse musical maps,
the varying forward musical maps carry every compact tangent set into one
compact cotangent set, uniformly over the compact time interval. This works
without a compact base or any uniform metric bound over the whole manifold.
The original bundle topologies, model fibers and pointwise vector operations
are retained. The compatible metric norm is used only as a local proof device.

Sources: SG II.3, Examples 3.1--3.2, p.94, and II.5, p.113, identify the
tangent and cotangent bundles through a metric. III.13 uses tangent K classes
on p.243 and cotangent K classes on p.247. The explicit proper-cylinder
argument below is a project supplement using compact-support homotopy invariance.
The metric-independence theorem is proved by this proper homotopy on the original bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

/-- The original musical homeomorphism transports actual compact-support K classes. -/
def tangentCotangentKZeroEquiv (g : SmoothTangentMetric (n := n) (M := M)) :
    letI : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      g.flatHomeomorph.symm.t2Space
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      g.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) ≃+
      CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) := by
  -- Transfer separation and local compactness on the unchanged native topologies.
  let : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    g.flatHomeomorph.symm.t2Space
  let : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    g.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
  exact compactSupportKZeroHomeomorphEquiv g.flatHomeomorph

set_option maxHeartbeats 1000000 in

/-- The musical identification of compact-support K groups does not depend on the metric. -/
theorem tangentCotangentKZeroEquiv_independent_metric
    (g h : SmoothTangentMetric (n := n) (M := M)) :
    tangentCotangentKZeroEquiv g = tangentCotangentKZeroEquiv h := by
  /- Interpolate the original forms, invert them in native bundle coordinates, and
  prove that the resulting sharp homotopy is proper using one compact flat image.
  Proper-homotopy invariance then compares the specified inverse pullbacks. -/
  classical
  -- The local metric norms have the original topology; no total-space topology changes.
  let : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    g.flatHomeomorph.symm.t2Space
  let : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    g.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
  let E : M → Type _ := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (M := M)
  let F : Type := EuclideanSpace ℝ (Fin n)
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  let (x : M) : FiniteDimensional ℝ (E x) :=
    LinearEquiv.finiteDimensional
      (VectorBundle.continuousLinearEquivAt ℝ F E x).symm.toLinearEquiv
  let (x : M) : CompleteSpace (E x) := FiniteDimensional.complete ℝ (E x)
  let eg (x : M) : E x ≃L[ℝ] CotangentFiber (n := n) x :=
    (InnerProductSpace.toDual ℝ (E x)).toContinuousLinearEquiv
  let A (t : unitInterval) (x : M) : E x →L[ℝ] CotangentFiber (n := n) x :=
    (1 - (t : ℝ)) • g.inner x + (t : ℝ) • h.inner x
  -- Positive convex forms give actual equivalences on each original finite fiber.
  have hpos (t : unitInterval) (x : M) (v : E x) (hv : v ≠ 0) : 0 < A t x v v := by
    change 0 < (1 - (t : ℝ)) * g.inner x v v + (t : ℝ) * h.inner x v v
    have hg := g.pos x v hv
    have hh := h.pos x v hv
    have ht := t.property
    by_cases ht0 : (t : ℝ) = 0
    · simpa [ht0] using hg
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hg.le)
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hh)
  have hbij (t : unitInterval) (x : M) : Function.Bijective (A t x) := by
    -- Positivity kills the kernel; the fixed Riesz map reduces surjectivity to an endomorphism.
    have hinj : Function.Injective (A t x) := by
      apply (injective_iff_map_eq_zero (A t x)).mpr
      intro v hv
      by_contra hne
      have hp := hpos t x v hne
      rw [hv] at hp
      exact (lt_irrefl 0) hp
    have hs : Function.Surjective
        ((eg x).symm.toLinearEquiv.toLinearMap.comp (A t x).toLinearMap) :=
      LinearMap.surjective_of_injective ((eg x).symm.injective.comp hinj)
    refine ⟨hinj, ?_⟩
    intro w
    obtain ⟨v, hv⟩ := hs ((eg x).symm w)
    exact ⟨v, (eg x).symm.injective hv⟩
  let e (t : unitInterval) (x : M) : E x ≃L[ℝ] CotangentFiber (n := n) x :=
    (LinearEquiv.ofBijective (A t x).toLinearMap (hbij t x)).toContinuousLinearEquiv
  -- Coordinates retain both the time parameter and the same native tangent/dual frames.
  have hcoord (t : unitInterval) (x : M) : ContinuousAt
      (fun p : unitInterval × M ↦ ContinuousLinearMap.inCoordinates F E (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) x p.2 x p.2 (A p.1 p.2)) (t, x) := by
    have hg : ContinuousAt (fun y ↦ ContinuousLinearMap.inCoordinates F E (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) x y x y (g.inner y)) x :=
      (continuousAt_hom_bundle (RingHom.id ℝ) (fun y ↦ TotalSpace.mk'
        (F →L[ℝ] CotangentModel n) y (g.inner y))).mp
          g.contMDiff.continuous.continuousAt |>.2
    have hh : ContinuousAt (fun y ↦ ContinuousLinearMap.inCoordinates F E (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) x y x y (h.inner y)) x :=
      (continuousAt_hom_bundle (RingHom.id ℝ) (fun y ↦ TotalSpace.mk'
        (F →L[ℝ] CotangentModel n) y (h.inner y))).mp
          h.contMDiff.continuous.continuousAt |>.2
    have ht : ContinuousAt (fun p : unitInterval × M ↦ (p.1 : ℝ)) (t, x) :=
      continuous_subtype_val.continuousAt.comp continuousAt_fst
    convert (((continuousAt_const (y := (1 : ℝ))).sub ht).smul
      (hg.comp continuousAt_snd)).add
      (ht.smul (hh.comp continuousAt_snd)) using 1
    ext p v
    simp [ContinuousLinearMap.inCoordinates, A, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
  let flat (p : unitInterval × TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :
      CotangentTotalSpace (n := n) (M := M) := ⟨p.2.proj, A p.1 p.2.proj p.2.snd⟩
  have hflat : Continuous flat := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hb : ContinuousAt (fun q : unitInterval × TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ↦
        (q.1, q.2.proj)) p :=
      continuousAt_fst.prodMk
        ((FiberBundle.continuous_proj F E).continuousAt.comp continuousAt_snd)
    have hc : ContinuousAt (fun q : unitInterval × TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ↦
        ContinuousLinearMap.inCoordinates F E (CotangentModel n)
          (CotangentFiber (n := n) (M := M)) p.2.proj q.2.proj p.2.proj q.2.proj
          (A q.1 q.2.proj)) p := (hcoord p.1 p.2.proj).comp_of_eq hb rfl
    exact ContinuousAt.clm_apply_of_inCoordinates (F₁ := F) (E₁ := E)
      (F₂ := CotangentModel n) (E₂ := CotangentFiber (n := n) (M := M))
      (b₁ := fun q : unitInterval × TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ↦ q.2.proj)
      (b₂ := fun q : unitInterval × TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M ↦ q.2.proj)
      (ϕ := fun q ↦ A q.1 q.2.proj) (v := fun q ↦ q.2.snd) hc
      continuousAt_snd ((FiberBundle.continuous_proj F E).continuousAt.comp continuousAt_snd)
  let sharp (p : unitInterval × CotangentTotalSpace (n := n) (M := M)) :
      TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M :=
    ⟨p.2.proj, (e p.1 p.2.proj).symm p.2.snd⟩
  -- In each pair of native frames, the sharp family is the inverse coordinate operator.
  have hcoordInv (t : unitInterval) (x : M) : ContinuousAt
      (fun p : unitInterval × M ↦ ContinuousLinearMap.inCoordinates (CotangentModel n)
        (CotangentFiber (n := n) (M := M)) F E x p.2 x p.2
          (e p.1 p.2).symm.toContinuousLinearMap) (t, x) := by
    let a := trivializationAt F E x
    let b := trivializationAt (CotangentModel n) (CotangentFiber (n := n) (M := M)) x
    let C (p : unitInterval × M) : F →L[ℝ] CotangentModel n :=
      (b.continuousLinearMapAt ℝ p.2).comp
        ((e p.1 p.2).toContinuousLinearMap.comp (a.symmL ℝ p.2))
    let D (p : unitInterval × M) : CotangentModel n →L[ℝ] F :=
      (a.continuousLinearMapAt ℝ p.2).comp
        ((e p.1 p.2).symm.toContinuousLinearMap.comp (b.symmL ℝ p.2))
    have hCD (p : unitInterval × M) (ha : p.2 ∈ a.baseSet) (hb : p.2 ∈ b.baseSet) :
        (C p).comp (D p) = ContinuousLinearMap.id ℝ (CotangentModel n) ∧
          (D p).comp (C p) = ContinuousLinearMap.id ℝ F := by
      constructor
      · apply ContinuousLinearMap.ext
        intro v
        change b.continuousLinearMapAt ℝ p.2 (e p.1 p.2 (a.symmL ℝ p.2
          (a.continuousLinearMapAt ℝ p.2 ((e p.1 p.2).symm (b.symmL ℝ p.2 v))))) = v
        rw [a.symmL_continuousLinearMapAt (R := ℝ) ha, (e p.1 p.2).apply_symm_apply,
          b.continuousLinearMapAt_symmL hb]
      · apply ContinuousLinearMap.ext
        intro v
        change a.continuousLinearMapAt ℝ p.2 ((e p.1 p.2).symm (b.symmL ℝ p.2
          (b.continuousLinearMapAt ℝ p.2 (e p.1 p.2 (a.symmL ℝ p.2 v))))) = v
        rw [b.symmL_continuousLinearMapAt (R := ℝ) hb, (e p.1 p.2).symm_apply_apply,
          a.continuousLinearMapAt_symmL ha]
    have hax : x ∈ a.baseSet := mem_baseSet_trivializationAt _ _ x
    have hbx : x ∈ b.baseSet := mem_baseSet_trivializationAt _ _ x
    have hC : ContinuousAt C (t, x) := hcoord t x
    have hinvertible : (C (t, x)).IsInvertible :=
      ContinuousLinearMap.IsInvertible.of_inverse (hCD (t, x) hax hbx).1
        (hCD (t, x) hax hbx).2
    have hinverse := (hinvertible.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hC
    change ContinuousAt D (t, x)
    apply hinverse.congr_of_eventuallyEq
    have ha : ∀ᶠ p : unitInterval × M in 𝓝 (t, x), p.2 ∈ a.baseSet :=
      continuousAt_snd (a.open_baseSet.mem_nhds hax)
    have hb : ∀ᶠ p : unitInterval × M in 𝓝 (t, x), p.2 ∈ b.baseSet :=
      continuousAt_snd (b.open_baseSet.mem_nhds hbx)
    filter_upwards [ha, hb] with p hpa hpb
    exact (ContinuousLinearMap.inverse_eq (hCD p hpa hpb).1 (hCD p hpa hpb).2).symm
  have hsharp : Continuous sharp := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hb : ContinuousAt (fun q : unitInterval × CotangentTotalSpace (n := n) (M := M) ↦
        (q.1, q.2.proj)) p :=
      continuousAt_fst.prodMk
        ((FiberBundle.continuous_proj (CotangentModel n)
          (CotangentFiber (n := n) (M := M))).continuousAt.comp continuousAt_snd)
    have hc : ContinuousAt (fun q : unitInterval × CotangentTotalSpace (n := n) (M := M) ↦
        ContinuousLinearMap.inCoordinates (CotangentModel n)
          (CotangentFiber (n := n) (M := M)) F E p.2.proj q.2.proj p.2.proj q.2.proj
          (e q.1 q.2.proj).symm.toContinuousLinearMap) p :=
      (hcoordInv p.1 p.2.proj).comp_of_eq hb rfl
    exact ContinuousAt.clm_apply_of_inCoordinates (F₁ := CotangentModel n)
      (E₁ := CotangentFiber (n := n) (M := M)) (F₂ := F) (E₂ := E)
      (b₁ := fun q : unitInterval × CotangentTotalSpace (n := n) (M := M) ↦ q.2.proj)
      (b₂ := fun q : unitInterval × CotangentTotalSpace (n := n) (M := M) ↦ q.2.proj)
      (ϕ := fun q ↦ (e q.1 q.2.proj).symm.toContinuousLinearMap)
      (v := fun q ↦ q.2.snd) hc
      continuousAt_snd ((FiberBundle.continuous_proj (CotangentModel n)
        (CotangentFiber (n := n) (M := M))).continuousAt.comp continuousAt_snd)
  -- The inverse family has exactly the original endpoint homeomorphisms.
  have hflat_zero (z : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :
      flat (0, z) = g.flatHomeomorph z := by
    rcases z with ⟨x, v⟩
    change (⟨x, A 0 x v⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, g.inner x v⟩
    simp [A]
  have hflat_one (z : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :
      flat (1, z) = h.flatHomeomorph z := by
    rcases z with ⟨x, v⟩
    change (⟨x, A 1 x v⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, h.inner x v⟩
    simp [A]
  have hflat_sharp (t : unitInterval) (z : CotangentTotalSpace (n := n) (M := M)) :
      flat (t, sharp (t, z)) = z := by
    rcases z with ⟨x, ξ⟩
    change (⟨x, e t x ((e t x).symm ξ)⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨x, ξ⟩
    rw [(e t x).apply_symm_apply]
  let f : C(CotangentTotalSpace (n := n) (M := M),
      TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩
  let k : C(CotangentTotalSpace (n := n) (M := M),
      TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
    ⟨h.flatHomeomorph.symm, h.flatHomeomorph.symm.continuous⟩
  let H : ContinuousMap.Homotopy f k :=
    { toFun := sharp
      continuous_toFun := hsharp
      map_zero_left := by
        intro z
        apply g.flatHomeomorph.injective
        change g.flatHomeomorph (sharp (0, z)) = g.flatHomeomorph (g.flatHomeomorph.symm z)
        rw [← hflat_zero, hflat_sharp, g.flatHomeomorph.apply_symm_apply]
      map_one_left := by
        intro z
        apply h.flatHomeomorph.injective
        change h.flatHomeomorph (sharp (1, z)) = h.flatHomeomorph (h.flatHomeomorph.symm z)
        rw [← hflat_one, hflat_sharp, h.flatHomeomorph.apply_symm_apply] }
  -- A single compact forward image controls every time slice of the sharp homotopy.
  have hH : IsProperMap H := by
    apply (isProperMap_homotopy_iff H).mpr
    intro K hK
    refine ⟨flat '' (Set.univ ×ˢ K), (isCompact_univ.prod hK).image hflat, ?_⟩
    intro t z hz
    exact ⟨(t, sharp (t, z)), ⟨Set.mem_univ t, hz⟩, hflat_sharp t z⟩
  have hpull := compactSupportKZeroPullback_eq_of_proper_homotopy
    g.flatHomeomorph.symm.isProperMap h.flatHomeomorph.symm.isProperMap H hH
  -- The original additive equivalences use precisely these inverse pullbacks.
  apply AddEquiv.ext
  intro a
  exact DFunLike.congr_fun hpull a

end AtiyahSinger
