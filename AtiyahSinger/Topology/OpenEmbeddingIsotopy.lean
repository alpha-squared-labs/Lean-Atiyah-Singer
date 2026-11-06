/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OpenEmbeddingKZero

/-!
# Isotopy invariance of actual open extension

Public module ID: M1969.

An open isotopy has an open embedding of cylinders `(t,x) ↦ (t,H(t,x))`.
Its inverse on the open image is jointly continuous. The actual one-point
collapse sends a finite point in that image to its unique source point and
every other point to infinity. Compactness of the parameter interval gives
joint continuity at infinity, so the original compact-support open extensions
at the two endpoints agree.

This is a standard project supplement to compactification and K homotopy
invariance, used by the tubular-neighborhood construction in SG III.12,
printed p.241 / PDF p.253, and the embedding-isotopy argument in III.13,
printed p.244 / PDF p.256. Those passages do not state this general locally
compact Hausdorff formulation as a separate numbered lemma.
The proof uses KA II.2.43, printed p.70 / PDF p.87, for homotopy invariance,
and II.4.1--4.3, printed p.83 / PDF p.100, for the one-point and open-collapse
models. Open covariant extension is kept distinct from proper pullback.

The cylinder hypothesis is explicit: joint continuity together with separate
open embeddings of time slices is not substituted for a jointly continuous
inverse. No slice is assumed proper. The result does not assert existence of
a tubular neighborhood or an isotopy between two geometric choices.
The proofs retain the original collapse maps and open pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology
open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open scoped Classical in
/-- Collapse along an embedding, using its actual inverse on the image and infinity elsewhere. -/
def openEmbeddingOnePointCollapse (f : X → Y) : OnePoint Y → OnePoint X :=
  fun y ↦ y.elim ∞ (fun y ↦
    if hy : y ∈ Set.range f then ((Classical.choose hy : X) : OnePoint X) else ∞)

variable [hXL : LocallyCompactSpace X] [hXT : T2Space X]
  [hYL : LocallyCompactSpace Y] [hYT : T2Space Y]

include hXL hXT hYL hYT


set_option linter.unusedSectionVars false in
/-- An open embedding of cylinders gives a jointly continuous family of the actual collapses. -/
theorem continuous_openEmbeddingOnePointCollapse_isotopy (H : C(I × X, Y))
    (hH : IsOpenEmbedding (fun p : I × X ↦ (p.1, H p))) :
    Continuous (fun p : I × OnePoint Y ↦
      openEmbeddingOnePointCollapse (fun x : X ↦ H (p.1, x)) p.2) := by
  /- Stage 1: injectivity of the cylinder map gives injectivity of every slice.
  On its open image the actual inverse of the cylinder embedding sends (t,y)
  to (t,x). Its second component is the source point chosen by the displayed
  collapse formula. Thus this formula is jointly continuous wherever finite.
  Stage 2: let K be a compact subset of X. The image of I times K under the
  cylinder map is compact. Its image in I times Y-plus is still compact and
  is closed because this target is Hausdorff. The complement is precisely the
  inverse image of X-plus minus K under the family of collapse maps.
  Stage 3: these complements supply the neighborhoods needed at every point
  sent to infinity, including finite points outside the slice image and the
  original infinity of Y-plus. The same compact image works for all times.
  This argument uses compact source controls, not properness of the slices,
  and uses the joint cylinder inverse rather than separately chosen inverses. -/
  classical
  let C (p : I × OnePoint Y) : OnePoint X :=
    openEmbeddingOnePointCollapse (fun x : X ↦ H (p.1, x)) p.2
  let F (p : I × X) : I × OnePoint Y := (p.1, (H p : OnePoint Y))
  have hF : Continuous F :=
    continuous_fst.prodMk (OnePoint.continuous_coe.comp H.continuous)
  have hFopen : IsOpenMap F :=
    (IsOpenMap.id.prodMap OnePoint.isOpenMap_coe).comp hH.isOpenMap
  -- The actual cylinder embedding makes every finite slice inverse unique.
  have hinj (t : I) : Function.Injective (fun x : X ↦ H (t, x)) := by
    intro x y h
    have hp : (t, H (t, x)) = (t, H (t, y)) := Prod.ext rfl h
    have hxy : (t, x) = (t, y) := hH.injective hp
    exact congrArg Prod.snd hxy
  have hfinite (t : I) (x : X) : C (t, (H (t, x) : OnePoint Y)) = (x : OnePoint X) := by
    have hx : H (t, x) ∈ Set.range (fun x : X ↦ H (t, x)) := ⟨x, rfl⟩
    change (if hy : H (t, x) ∈ Set.range (fun x : X ↦ H (t, x)) then
      ((Classical.choose hy : X) : OnePoint X) else ∞) = (x : OnePoint X)
    rw [dite_eq_left hx]
    exact congrArg OnePoint.some (hinj t (Classical.choose_spec hx))
  have houtside (t : I) (y : Y) (hy : y ∉ Set.range (fun x : X ↦ H (t, x))) :
      C (t, (y : OnePoint Y)) = ∞ := by
    change (if hz : y ∈ Set.range (fun x : X ↦ H (t, x)) then
      ((Classical.choose hz : X) : OnePoint X) else ∞) = ∞
    rw [dite_eq_right hy]
  -- The same image formula handles finite open sets and finite compact sets.
  have himage (K : Set X) : F '' ((Set.univ : Set I) ×ˢ K) =
      C ⁻¹' (((↑) : X → OnePoint X) '' K) := by
    ext p
    constructor
    · rintro ⟨⟨t, x⟩, hx, rfl⟩
      exact ⟨x, hx.2, (hfinite t x).symm⟩
    · intro hp
      rcases p with ⟨t, z⟩
      cases z using OnePoint.rec with
      | infty =>
        obtain ⟨x, _, hx⟩ := hp
        exact (OnePoint.coe_ne_infty x hx).elim
      | coe y =>
        by_cases hy : y ∈ Set.range (fun x : X ↦ H (t, x))
        · obtain ⟨x, rfl⟩ := hy
          obtain ⟨x', hx', heq⟩ := hp
          rw [hfinite t x] at heq
          have hxx : x' = x := OnePoint.coe_injective heq
          exact ⟨(t, x), ⟨Set.mem_univ _, hxx ▸ hx'⟩, rfl⟩
        · obtain ⟨x, _, hx⟩ := hp
          rw [houtside t y hy] at hx
          exact (OnePoint.coe_ne_infty x hx).elim
  apply continuous_def.mpr
  intro s hs
  by_cases hinfty : ∞ ∈ s
  · -- Compact source control is uniform over the full compact time interval.
    let K : Set X := (((↑) : X → OnePoint X) ⁻¹' s)ᶜ
    have hK : IsCompact K := ((OnePoint.isOpen_iff_of_mem hinfty).mp hs).2
    have hcompl : sᶜ = (((↑) : X → OnePoint X) '' K) := by
      ext z
      cases z using OnePoint.rec with
      | infty => simp [hinfty]
      | coe x => simp [K]
    have hc : IsClosed (C ⁻¹' s)ᶜ := by
      rw [← Set.preimage_compl, hcompl, ← himage K]
      exact ((isCompact_univ.prod hK).image hF).isClosed
    simpa only [compl_compl] using hc.isOpen_compl
  · -- On finite open sets, the actual cylinder embedding supplies open images.
    let U : Set X := ((↑) : X → OnePoint X) ⁻¹' s
    have hU : IsOpen U := OnePoint.continuous_coe.isOpen_preimage s hs
    have hsimage : s = (((↑) : X → OnePoint X) '' U) := by
      ext z
      cases z using OnePoint.rec with
      | infty => simp [hinfty]
      | coe x => simp [U]
    change IsOpen (C ⁻¹' s)
    rw [hsimage, ← himage U]
    exact hFopen _ (isOpen_univ.prod hU)

/-- Open embeddings joined by a genuine open isotopy induce the same compact-support extension. -/
theorem compactSupportKZeroOpenPushforward_eq_of_isotopy {f g : C(X, Y)}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (H : ContinuousMap.Homotopy f g)
    (hH : IsOpenEmbedding (fun p : I × X ↦ (p.1, H p))) :
    compactSupportKZeroOpenPushforward f hf = compactSupportKZeroOpenPushforward g hg := by
  /- Stage 1: the preceding continuity theorem applied to H gives the actual
  homotopy of one-point collapse maps from Y-plus to X-plus. Every slice fixes
  infinity. At time zero and one the defining equations of H give exactly
  openEmbeddingOnePointCollapse f and openEmbeddingOnePointCollapse g.
  Stage 2: for each endpoint, compare this formula with the map underlying the
  existing open pushforward: collapse onto the open range, then apply the
  one-point extension of the inverse range homeomorphism. At a finite image
  point both formulas select its unique preimage; outside the range and at
  infinity both give infinity. Reduced pullback composition therefore recovers
  the original open pushforward, with its original image identification.
  Stage 3: absolute K-zero homotopy invariance on the compact Hausdorff
  compactifications identifies the two pullbacks. Restrict to the kernels of
  evaluation at infinity. No proper pullback along f or g is introduced, and
  an unspecified isotopy of tubular neighborhoods is not assumed to exist. -/
  classical
  let := hf.isOpen_range.locallyCompactSpace
  let := hg.isOpen_range.locallyCompactSpace
  -- Keep the range identification and collapse used by the existing open extension.
  let collapse (k : C(X, Y)) (hk : IsOpenEmbedding k) : C(OnePoint Y, OnePoint X) :=
    let := hk.isOpen_range.locallyCompactSpace
    let e := hk.isEmbedding.toHomeomorph
    (properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range k), continuous_onePointCollapse _ hk.isOpen_range⟩
  have hcollapse (k : C(X, Y)) (hk : IsOpenEmbedding k) :
      openEmbeddingOnePointCollapse k = collapse k hk := by
    funext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe y =>
      by_cases hy : y ∈ Set.range k
      · obtain ⟨x, rfl⟩ := hy
        have hx : k x ∈ Set.range k := ⟨x, rfl⟩
        have hchoose : Classical.choose hx = x := hk.injective (Classical.choose_spec hx)
        change (if hy : k x ∈ Set.range k then
          ((Classical.choose hy : X) : OnePoint X) else ∞) =
            OnePoint.map (fun y : Set.range k ↦ hk.isEmbedding.toHomeomorph.symm y)
              (onePointCollapse (Set.range k) (k x))
        rw [dite_eq_left hx, hchoose,
          onePointCollapse_coe_of_mem (Set.range k) (k x) hx, OnePoint.map_some]
        exact (congrArg OnePoint.some (hk.isEmbedding.toHomeomorph_symm_apply x)).symm
      · change (if hy : y ∈ Set.range k then
          ((Classical.choose hy : X) : OnePoint X) else ∞) =
            OnePoint.map (fun y : Set.range k ↦ hk.isEmbedding.toHomeomorph.symm y)
              (onePointCollapse (Set.range k) y)
        rw [dite_eq_right hy, onePointCollapse_coe_of_notMem (Set.range k) y hy,
          OnePoint.map_infty]
  -- The cylinder hypothesis gives a pointed homotopy between exactly these endpoint maps.
  let K : ContinuousMap.Homotopy (collapse f hf) (collapse g hg) :=
    { toFun := fun p ↦ openEmbeddingOnePointCollapse (fun x : X ↦ H (p.1, x)) p.2
      continuous_toFun := continuous_openEmbeddingOnePointCollapse_isotopy H.toContinuousMap hH
      map_zero_left := by
        intro z
        have hzero : (fun x : X ↦ H (0, x)) = f := funext H.apply_zero
        rw [hzero]
        exact congrFun (hcollapse f hf) z
      map_one_left := by
        intro z
        have hone : (fun x : X ↦ H (1, x)) = g := funext H.apply_one
        rw [hone]
        exact congrFun (hcollapse g hg) z }
  -- Homotopy invariance on compactifications descends to the original evaluation kernels.
  have h := complexKZeroPullback_eq_of_homotopy (collapse f hf) (collapse g hg) K
  dsimp only [collapse] at h
  rw [complexKZeroPullback_comp, complexKZeroPullback_comp] at h
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun h a.val

end AtiyahSinger
