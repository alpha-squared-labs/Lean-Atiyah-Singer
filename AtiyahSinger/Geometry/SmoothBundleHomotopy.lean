/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import Mathlib.Topology.Homotopy.Basic

import AtiyahSinger.Geometry.RelativeBundleSmoothing
import AtiyahSinger.Topology.BundleHomotopyType

/-!
# Smooth isomorphisms between homotopic pullback bundles

Public module ID: M1372.

K01: smooth maps joined by a continuous homotopy have smoothly isomorphic
pullbacks of the same smooth complex bundle. The maps are linear equivalences
between the original fibers, and smoothness uses the native pullback atlases.
The homotopy need not be smooth. In the relative theorem it is stationary on
an open neighborhood of a closed set, where the resulting map is the identity
after the endpoint equality transports the fiber.

The topological input is Hatcher, Vector Bundles and K-Theory, Theorem 1.6
and Proposition 1.7, used in the proof of SG III.13 Lemma 13.3. The relative
stationary-neighborhood argument and relative smoothing are project supplements,
not additional statements quoted from SG. The manifolds are finite dimensional,
Hausdorff and second countable, without boundary; neither is assumed compact.
The bundle has a fixed finite rank, including zero. The existing
`IsSmoothBundleMap.symm` theorem also gives smoothness of these same inverses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff unitInterval

attribute [local instance] ComplexBundle.isFiniteRank_pullback

variable {n m r : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hMT : T2Space M] [hNT : T2Space N]
  [hMS : SecondCountableTopology M] [hNS : SecondCountableTopology N]
  (E : N → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hE : IsSmoothComplexBundle (n := m) (r := r) E]

include hM hN hMT hNT hMS hNS hE

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
/-- Continuously homotopic smooth maps have smoothly isomorphic original pullback bundles. -/
theorem exists_smooth_pullback_linearEquiv_of_homotopy (f g : C(M, N))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g)
    (H : ContinuousMap.Homotopy f g) :
    ∃ e : ∀ x, ((f : M → N) *ᵖ E) x ≃ₗ[ℂ] ((g : M → N) *ᵖ E) x,
      IsSmoothBundleMap (n := n) (r := r) (q := r)
        (E := (f : M → N) *ᵖ E) (F := (g : M → N) *ᵖ E)
        (fun x ↦ (e x).toLinearMap) := by
  /- Stage 1: topological homotopy invariance gives an isomorphism of the two
  specified endpoint pullbacks. Auxiliary norms and small-bundle identifications
  retain their original fibers and total-space topologies.
  Stage 2: hf and hg give smoothness of both native pullback atlases. Apply
  Iso.exists_smooth_homotopy_relative with the empty fixed set to the same
  topological isomorphism. Its fine approximation preserves invertibility
  using point-dependent error bounds, without compactness of M.
  Stage 3: return the smoothed isomorphism's original-fiber linear equivalences
  and their bundle-map smoothness. The symm theorem separately supplies
  smoothness of those inverses; the construction claims no canonical choice. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  -- Auxiliary fiber norms use the original topology, via the original continuous frames.
  let c (y : N) : E y ≃L[ℂ] V := VectorBundle.continuousLinearEquivAt ℂ V E y
  let nE (y : N) : NormedAddCommGroup (E y) :=
    NormedAddCommGroup.induced (E y) V (c y).toLinearMap (c y).injective
  let : ∀ y, NormedAddCommGroup (E y) := fun y ↦
    { (nE y).toMetricSpace.replaceTopology (c y).toHomeomorph.isInducing.eq_induced,
      nE y with }
  let : ∀ y, NormedSpace ℂ (E y) := fun y ↦
    { norm_smul_le a v := by
        change ‖c y (a • v)‖ ≤ ‖a‖ * ‖c y v‖
        rw [map_smul]
        exact norm_smul_le a (c y v) }
  let tE : TopologicalSpace (TotalSpace Unit E) := ComplexBundle.modelTopology V E
  let : ComplexBundle.IsFiniteRank E := ComplexBundle.isFiniteRank_model V E
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- Topological homotopy invariance retains the two specified endpoint pullbacks.
  let P := ComplexBundle.smallBundle E
  let eP := ComplexBundle.smallBundleIso E
  obtain ⟨aP⟩ := ComplexBundle.nonempty_pullback_iso_of_homotopic P f g ⟨H⟩
  let a := (eP.pullback f).trans (aP.trans (eP.pullback g).symm)
  let : IsSmoothComplexBundle (n := n) (r := r) ((f : M → N) *ᵖ E) :=
    isSmoothComplexBundle_pullback E f hf
  let : IsSmoothComplexBundle (n := n) (r := r) ((g : M → N) *ᵖ E) :=
    isSmoothComplexBundle_pullback E g hg
  -- Retyping the native pullback and pulling back the retyped original give the same topology.
  have htop (k : C(M, N)) :
      ComplexBundle.modelTopology V ((k : M → N) *ᵖ E) =
        (inferInstance : TopologicalSpace (TotalSpace Unit ((k : M → N) *ᵖ E))) := by
    change TopologicalSpace.induced (ComplexBundle.unitTotalEquiv V ((k : M → N) *ᵖ E))
        (Pullback.TotalSpace.topologicalSpace V E k) =
      Pullback.TotalSpace.topologicalSpace Unit E k
    simp only [Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      tE, ComplexBundle.modelTopology, induced_inf, induced_compose]
    rfl
  have a' :
      letI := ComplexBundle.modelTopology V ((f : M → N) *ᵖ E)
      letI := ComplexBundle.modelTopology V ((g : M → N) *ᵖ E)
      ComplexBundle.Iso ((f : M → N) *ᵖ E) ((g : M → N) *ᵖ E) := by
    rw [htop f, htop g]
    exact a
  let : TopologicalSpace (TotalSpace Unit ((f : M → N) *ᵖ E)) :=
    ComplexBundle.modelTopology V ((f : M → N) *ᵖ E)
  let : TopologicalSpace (TotalSpace Unit ((g : M → N) *ᵖ E)) :=
    ComplexBundle.modelTopology V ((g : M → N) *ᵖ E)
  -- Fine relative smoothing with the empty fixed set preserves invertibility everywhere.
  obtain ⟨b, hb, _⟩ := ComplexBundle.Iso.exists_smooth_homotopy_relative
    (M := M) (E := (f : M → N) *ᵖ E) (F := (g : M → N) *ᵖ E)
    (n := n) (r := r) (q := r) a' ∅ isClosed_empty ⊥ (by simp) (by
      intro e he d hd j x
      exact False.elim x.property)
  exact ⟨b.linearEquiv, hb⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
/-- A stationary neighborhood allows the smooth pullback isomorphism to fix a closed set. -/
theorem exists_smooth_pullback_linearEquiv_of_homotopy_relative (f g : C(M, N))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ g)
    (H : ContinuousMap.Homotopy f g)
    (A U : Set M) (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (hH : ∀ (t : unitInterval) (x : M), x ∈ U → H (t, x) = f x) :
    ∃ e : ∀ x, ((f : M → N) *ᵖ E) x ≃ₗ[ℂ] ((g : M → N) *ᵖ E) x,
      IsSmoothBundleMap (n := n) (r := r) (q := r)
          (E := (f : M → N) *ᵖ E) (F := (g : M → N) *ᵖ E)
          (fun x ↦ (e x).toLinearMap) ∧
        ∀ (x : M), x ∈ A → ∀ v : ((f : M → N) *ᵖ E) x, HEq (e x v) v := by
  /- Stage 1: shrink the stationary neighborhood to a buffer around A.
  Use one cylinder isomorphism from the pullback of f to the pullback of H.
  A continuous cutoff time chi is one near A and zero outside U. Since H
  is stationary on U, its value at (chi(x), x) is f(x) everywhere. The
  chi-slice is thus an automorphism of the original f-pullback. Compose its
  inverse with the time-one slice. Near A both slices use the same time,
  so they cancel to the original vector identity under f(x) = g(x).
  This works without trivializing the bundle on U or normalizing a chosen
  isomorphism at time zero.
  Stage 2: both endpoint bundles have the original smooth pullback atlases.
  Their identity comparison is smooth near A: in original bundle frames
  its columns are the original smooth transition columns composed with f.
  Fine relative smoothing then preserves invertibility and fixes A.
  Stage 3: the terminal equation of that same isomorphism homotopy retains
  the original vectors on A, recorded by heterogeneous equality. Auxiliary
  norms and small models are returned through the original topology and
  the specified small-bundle isomorphisms; no endpoint type is changed. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  -- Auxiliary fiber norms use the original topology, via the original continuous frames.
  let c (y : N) : E y ≃L[ℂ] V := VectorBundle.continuousLinearEquivAt ℂ V E y
  let nE (y : N) : NormedAddCommGroup (E y) :=
    NormedAddCommGroup.induced (E y) V (c y).toLinearMap (c y).injective
  let : ∀ y, NormedAddCommGroup (E y) := fun y ↦
    { (nE y).toMetricSpace.replaceTopology (c y).toHomeomorph.isInducing.eq_induced,
      nE y with }
  let : ∀ y, NormedSpace ℂ (E y) := fun y ↦
    { norm_smul_le a v := by
        change ‖c y (a • v)‖ ≤ ‖a‖ * ‖c y v‖
        rw [map_smul]
        exact norm_smul_le a (c y v) }
  let tE : TopologicalSpace (TotalSpace Unit E) := ComplexBundle.modelTopology V E
  let : ComplexBundle.IsFiniteRank E := ComplexBundle.isFiniteRank_model V E
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- A single isomorphism on the cylinder supplies every time slice with the same witnesses.
  let X := M × unitInterval
  let fX : C(X, N) := ⟨fun z ↦ f z.1, f.continuous.comp continuous_fst⟩
  let hX : C(X, N) := ⟨fun z ↦ H (z.2, z.1), H.continuous.comp continuous_swap⟩
  let J : ContinuousMap.Homotopy fX hX :=
    { toFun z := H (z.1 * z.2.2, z.2.1)
      continuous_toFun := H.continuous.comp
        ((continuous_fst.mul (continuous_snd.comp continuous_snd)).prodMk
          (continuous_fst.comp continuous_snd))
      map_zero_left z := by simp [fX]
      map_one_left z := by simp only [one_mul]; rfl }
  let P := ComplexBundle.smallBundle E
  let eP := ComplexBundle.smallBundleIso E
  obtain ⟨aP⟩ := ComplexBundle.nonempty_pullback_iso_of_homotopic P fX hX ⟨J⟩
  let a := (eP.pullback fX).trans (aP.trans (eP.pullback hX).symm)
  -- Equality transport changes only the fiber's dependent type, never its vector.
  let transport (y z : N) (h : y = z) : E y ≃ₗ[ℂ] E z := by
    subst z
    exact LinearEquiv.refl ℂ (E y)
  have htransport (y z : N) (h : y = z) (v : E y) : HEq (transport y z h v) v := by
    subst z
    rfl
  have htransportTotal (y z : N) (h : y = z) (v : E y) :
      (⟨z, transport y z h v⟩ : TotalSpace Unit E) = ⟨y, v⟩ := by
    subst z
    rfl
  have makeSlice (k : C(M, unitInterval)) (l : C(M, N))
      (h : ∀ x : M, H (k x, x) = l x) :
      ∃ b : ComplexBundle.Iso ((f : M → N) *ᵖ E) ((l : M → N) *ᵖ E),
        ∀ (x : M) (v : E (f x)), HEq (b.linearEquiv x v) (a.linearEquiv (x, k x) v) := by
    let L (x : M) : E (f x) ≃ₗ[ℂ] E (l x) :=
      (a.linearEquiv (x, k x)).trans (transport (H (k x, x)) (l x) (h x))
    have hin : Continuous (fun z : TotalSpace Unit ((f : M → N) *ᵖ E) ↦
        (⟨(z.proj, k z.proj), z.snd⟩ : TotalSpace Unit ((fX : X → N) *ᵖ E))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E fX).continuous_iff]
      exact ((Pullback.continuous_proj Unit E f).prodMk
        (k.continuous.comp (Pullback.continuous_proj Unit E f))).prodMk
          (Pullback.continuous_lift Unit E f)
    have hraw := (Pullback.continuous_lift Unit E hX).comp
      (a.toHom.continuous_total.comp hin)
    let b : ComplexBundle.Hom ((f : M → N) *ᵖ E) ((l : M → N) *ᵖ E) :=
      { linearMap x := (L x).toLinearMap
        continuous_total := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit E l).continuous_iff]
          apply (Pullback.continuous_proj Unit E f).prodMk
          apply hraw.congr
          intro z
          exact (htransportTotal (H (k z.proj, z.proj)) (l z.proj) (h z.proj)
            (a.linearEquiv (z.proj, k z.proj) z.snd)).symm }
    refine ⟨b.toIso (fun x ↦ (L x).bijective), ?_⟩
    intro x v
    exact htransport (H (k x, x)) (l x) (h x) (a.linearEquiv (x, k x) v)
  -- A cutoff time is one near A and zero outside the stationary region.
  obtain ⟨V₀, hV₀, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  have hdisjoint : Disjoint Uᶜ (closure V₀) :=
    Set.disjoint_left.mpr (fun _ hx hv ↦ hx (hVU hv))
  obtain ⟨w, hwzero, hwone, hwbounds⟩ :=
    exists_continuous_zero_one_of_isClosed hU.isClosed_compl isClosed_closure hdisjoint
  let χ : C(M, unitInterval) := ⟨fun x ↦ ⟨w x, hwbounds x⟩, w.continuous.subtype_mk _⟩
  have hχone (x : M) (hx : x ∈ V₀) : χ x = 1 :=
    Subtype.ext (hwone (subset_closure hx))
  have htime (x : M) : H (χ x, x) = f x := by
    by_cases hx : x ∈ U
    · exact hH (χ x) x hx
    · have hzero : χ x = 0 := Subtype.ext (hwzero hx)
      rw [hzero]
      exact H.apply_zero x
  obtain ⟨aχ, haχ⟩ := makeSlice χ f htime
  obtain ⟨a₁, ha₁⟩ := makeSlice ⟨fun _ ↦ 1, continuous_const⟩ g H.apply_one
  let b := aχ.symm.trans a₁
  have hfixed (x : M) (hx : x ∈ V₀) (v : E (f x)) : HEq (b.linearEquiv x v) v := by
    have hχ := haχ x ((aχ.linearEquiv x).symm v)
    rw [LinearEquiv.apply_symm_apply, hχone x hx] at hχ
    exact (ha₁ x ((aχ.linearEquiv x).symm v)).trans hχ.symm
  have hgf (x : M) (hx : x ∈ V₀) : g x = f x :=
    (H.apply_one x).symm.trans (hH 1 x (hVU (subset_closure hx)))
  -- The normalized endpoint is the original vector identity on an open neighborhood of A.
  let : IsSmoothComplexBundle (n := n) (r := r) ((f : M → N) *ᵖ E) :=
    isSmoothComplexBundle_pullback E f hf
  let : IsSmoothComplexBundle (n := n) (r := r) ((g : M → N) *ᵖ E) :=
    isSmoothComplexBundle_pullback E g hg
  have htop (k : C(M, N)) :
      ComplexBundle.modelTopology V ((k : M → N) *ᵖ E) =
        (inferInstance : TopologicalSpace (TotalSpace Unit ((k : M → N) *ᵖ E))) := by
    change TopologicalSpace.induced (ComplexBundle.unitTotalEquiv V ((k : M → N) *ᵖ E))
        (Pullback.TotalSpace.topologicalSpace V E k) =
      Pullback.TotalSpace.topologicalSpace Unit E k
    simp only [Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      tE, ComplexBundle.modelTopology, induced_inf, induced_compose]
    rfl
  have b' :
      letI := ComplexBundle.modelTopology V ((f : M → N) *ᵖ E)
      letI := ComplexBundle.modelTopology V ((g : M → N) *ᵖ E)
      ∃ b' : ComplexBundle.Iso ((f : M → N) *ᵖ E) ((g : M → N) *ᵖ E),
        ∀ (x : M) (hx : x ∈ V₀) (v : E (f x)), HEq (b'.linearEquiv x v) v := by
    rw [htop f, htop g]
    exact ⟨b, hfixed⟩
  let : TopologicalSpace (TotalSpace Unit ((f : M → N) *ᵖ E)) :=
    ComplexBundle.modelTopology V ((f : M → N) *ᵖ E)
  let : TopologicalSpace (TotalSpace Unit ((g : M → N) *ᵖ E)) :=
    ComplexBundle.modelTopology V ((g : M → N) *ᵖ E)
  obtain ⟨b', hb'⟩ := b'
  let V' : Opens M := ⟨V₀, hV₀⟩
  let i : C(V', M) := ContinuousMap.subtypeVal V₀
  have hbsmooth : IsSmoothBundleMap (n := n) (r := r) (q := r) (M := V')
      (E := (i : V' → M) *ᵖ ((f : M → N) *ᵖ E))
      (F := (i : V' → M) *ᵖ ((g : M → N) *ᵖ E))
      (fun x ↦ (b'.linearEquiv x.val).toLinearMap) := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨d, hd, rfl⟩ j
    rcases he.out with ⟨e, he, rfl⟩
    rcases hd.out with ⟨d, hd, rfl⟩
    let := he
    let := hd
    have hmatrix := (IsSmoothComplexBundle.contMDiffOn_coordChange (n := m) e d).comp
      (hf.comp contMDiff_subtype_val).contMDiffOn
      (show Set.MapsTo (fun x : V' ↦ f x.val)
        (((e.pullback f).pullback i).baseSet ∩ ((d.pullback g).pullback i).baseSet)
        (e.baseSet ∩ d.baseSet) from by
          intro x hx
          refine ⟨hx.1, ?_⟩
          have hd' : g x.val ∈ d.baseSet := hx.2
          simpa only [hgf x.val x.property] using hd')
    have hcolumn := ((ContinuousLinearMap.apply ℂ V
      (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn hmatrix
    refine hcolumn.congr ?_
    intro x hx
    have hs : ((e.pullback f).pullback i).symmL ℂ x (EuclideanSpace.single j 1) =
        e.symmL ℂ (f x.val) (EuclideanSpace.single j 1) := by
      rw [((e.pullback f).pullback i).symmL_apply (R := ℂ) hx.1]
      change ((e.pullback f).pullback i).symm x (EuclideanSpace.single j 1) =
        e.symmL ℂ (f x.val) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) (b := f x.val) hx.1,
        ((e.pullback f).pullback i).symm_apply hx.1]
      change (e.pullback f).symm (i x) (EuclideanSpace.single j 1) =
        e.symm (f x.val) (EuclideanSpace.single j 1)
      rw [(e.pullback f).symm_apply hx.1]
      rfl
    change (d ⟨g x.val, b'.linearEquiv x.val
      (((e.pullback f).pullback i).symmL ℂ x (EuclideanSpace.single j 1))⟩).2 = _
    rw [hs]
    have hv : (⟨g x.val, b'.linearEquiv x.val
        (e.symmL ℂ (f x.val) (EuclideanSpace.single j 1))⟩ : TotalSpace V E) =
        ⟨f x.val, e.symmL ℂ (f x.val) (EuclideanSpace.single j 1)⟩ :=
      TotalSpace.ext (hgf x.val x.property) (hb' x.val x.property _)
    rw [hv, e.symmL_apply (R := ℂ) (b := f x.val) hx.1]
    exact (e.coordChangeL_apply (R := ℂ) d ⟨hx.1, by
      change f x.val ∈ d.baseSet
      have hd' : g x.val ∈ d.baseSet := hx.2
      simpa only [hgf x.val x.property] using hd'⟩ (EuclideanSpace.single j 1)).symm
  -- Smooth this very endpoint map while leaving A fixed throughout the homotopy.
  obtain ⟨e, hesmooth, K, hK⟩ := ComplexBundle.Iso.exists_smooth_homotopy_relative
    (M := M) (E := (f : M → N) *ᵖ E) (F := (g : M → N) *ᵖ E)
    (n := n) (r := r) (q := r) b' A hA V' hAV hbsmooth
  refine ⟨e.linearEquiv, hesmooth, ?_⟩
  intro x hx v
  have heq : e.linearEquiv x v = b'.linearEquiv x v :=
    (K.map_one x v).symm.trans (hK 1 x hx v)
  rw [heq]
  exact hb' x (hAV hx) v

end AtiyahSinger
