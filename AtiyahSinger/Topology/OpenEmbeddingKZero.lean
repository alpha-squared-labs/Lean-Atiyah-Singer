/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# Extension of compactly supported K classes along open embeddings

Public module ID: M1970.

Factor the actual embedding through its open image, transport to that
image, and apply the existing one-point collapse. This is covariant open extension;
it does not require the embedding to be proper. The functor laws keep this map.
Sources: SG I.9.26 and III.13.4; Karoubi II.4, relative and compact-support functoriality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  [LocallyCompactSpace Z] [T2Space Z]

/-- Extension along an open embedding, using its actual homeomorphism onto the open image. -/
def compactSupportKZeroOpenPushforward (f : X → Y) (hf : IsOpenEmbedding f) :
    CompactSupportKZero X →+ CompactSupportKZero Y :=
  letI := hf.isOpen_range.locallyCompactSpace
  (compactSupportKZeroOpenExtension (Set.range f) hf.isOpen_range).comp
    (compactSupportKZeroHomeomorph hf.isEmbedding.toHomeomorph)

/-- Open extension along the identity is the identity on the original compact-support group. -/
theorem compactSupportKZeroOpenPushforward_id :
    compactSupportKZeroOpenPushforward (id : X → X) IsOpenEmbedding.id =
      AddMonoidHom.id (CompactSupportKZero X) := by
  /- The identity has the entire space as image. Transport to this image
  followed by its open collapse is the identity on the original one-point
  compactification, including infinity. Apply reduced-K pullback functoriality. -/
  let hf := (IsOpenEmbedding.id : IsOpenEmbedding (id : X → X))
  let := hf.isOpen_range.locallyCompactSpace
  let e := hf.isEmbedding.toHomeomorph
  let c : C(OnePoint X, OnePoint (Set.range (id : X → X))) :=
    ⟨onePointCollapse (Set.range (id : X → X)),
      continuous_onePointCollapse _ hf.isOpen_range⟩
  let i : C(Set.range (id : X → X), X) := ⟨e.symm, e.symm.continuous⟩
  have hmap : (properOnePointMap i e.symm.isProperMap).comp c =
      ContinuousMap.id (OnePoint X) := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      change OnePoint.map i (onePointCollapse (Set.range (id : X → X)) x) = (x : OnePoint X)
      rw [onePointCollapse_coe_of_mem (Set.range (id : X → X)) x ⟨x, rfl⟩, OnePoint.map_some]
      exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  -- Evaluate the equality on the original reduced class, using the actual composite map.
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback c (complexKZeroPullback (properOnePointMap i _) a.val) = a.val
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hmap]
  change kZeroMap (RingHom.id C(OnePoint X, ℂ)) a.val = a.val
  rw [kZeroMap_id]
  rfl

/-- Extension along successive open embeddings is extension along their actual composite. -/
theorem compactSupportKZeroOpenPushforward_comp (f : X → Y) (hf : IsOpenEmbedding f)
    (g : Y → Z) (hg : IsOpenEmbedding g) :
    compactSupportKZeroOpenPushforward (g ∘ f) (hg.comp hf) =
      (compactSupportKZeroOpenPushforward g hg).comp
        (compactSupportKZeroOpenPushforward f hf) := by
  /- Stage 1: include the image identifications in both collapse maps. A
  finite point of Z survives both collapses exactly when it lies in g(f(X));
  on this image the inverse is f⁻¹ after g⁻¹. All other points go to infinity.
  Stage 2: these are equal pointed continuous maps on the actual one-point
  compactifications. Contravariant reduced-K pullback reverses their order,
  yielding the displayed covariant composition law.
  No properness assumption on f or g is required. -/
  let := hf.isOpen_range.locallyCompactSpace
  let := hg.isOpen_range.locallyCompactSpace
  let := (hg.comp hf).isOpen_range.locallyCompactSpace
  let ef := hf.isEmbedding.toHomeomorph
  let eg := hg.isEmbedding.toHomeomorph
  let egf := (hg.comp hf).isEmbedding.toHomeomorph
  let ifn : C(Set.range f, X) := ⟨ef.symm, ef.symm.continuous⟩
  let ign : C(Set.range g, Y) := ⟨eg.symm, eg.symm.continuous⟩
  let igfn : C(Set.range (g ∘ f), X) := ⟨egf.symm, egf.symm.continuous⟩
  let cf : C(OnePoint Y, OnePoint X) :=
    (properOnePointMap ifn ef.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  let cg : C(OnePoint Z, OnePoint Y) :=
    (properOnePointMap ign eg.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range g), continuous_onePointCollapse _ hg.isOpen_range⟩
  let cgf : C(OnePoint Z, OnePoint X) :=
    (properOnePointMap igfn egf.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range (g ∘ f)),
        continuous_onePointCollapse _ (hg.comp hf).isOpen_range⟩
  -- On the actual images these inverse collapses recover the original source points.
  have hcf (x : X) : cf (f x) = (x : OnePoint X) := by
    change OnePoint.map ifn (onePointCollapse (Set.range f) (f x)) = (x : OnePoint X)
    rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have hcg (y : Y) : cg (g y) = (y : OnePoint Y) := by
    change OnePoint.map ign (onePointCollapse (Set.range g) (g y)) = (y : OnePoint Y)
    rw [onePointCollapse_coe_of_mem (Set.range g) (g y) ⟨y, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hg.isEmbedding.toHomeomorph_symm_apply y)
  have hcgf (x : X) : cgf (g (f x)) = (x : OnePoint X) := by
    change OnePoint.map igfn (onePointCollapse (Set.range (g ∘ f)) (g (f x))) =
      (x : OnePoint X)
    rw [onePointCollapse_coe_of_mem (Set.range (g ∘ f)) (g (f x)) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some ((hg.comp hf).isEmbedding.toHomeomorph_symm_apply x)
  have hsquare : cgf = cf.comp cg := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe z =>
      by_cases hz : z ∈ Set.range g
      · obtain ⟨y, rfl⟩ := hz
        by_cases hy : y ∈ Set.range f
        · obtain ⟨x, rfl⟩ := hy
          change cgf (g (f x)) = cf (cg (g (f x)))
          rw [hcgf, hcg, hcf]
        · have hnot : g y ∉ Set.range (g ∘ f) := by
            rintro ⟨x, hx⟩
            exact hy ⟨x, hg.injective hx⟩
          change cgf (g y) = cf (cg (g y))
          rw [hcg]
          change OnePoint.map igfn (onePointCollapse (Set.range (g ∘ f)) (g y)) =
            OnePoint.map ifn (onePointCollapse (Set.range f) y)
          rw [onePointCollapse_coe_of_notMem _ _ hnot,
            onePointCollapse_coe_of_notMem _ _ hy, OnePoint.map_infty, OnePoint.map_infty]
      · have hnot : z ∉ Set.range (g ∘ f) := by
          rintro ⟨x, hx⟩
          exact hz ⟨f x, hx⟩
        change OnePoint.map igfn (onePointCollapse (Set.range (g ∘ f)) z) =
          cf (OnePoint.map ign (onePointCollapse (Set.range g) z))
        rw [onePointCollapse_coe_of_notMem _ _ hnot,
          onePointCollapse_coe_of_notMem _ _ hz, OnePoint.map_infty, OnePoint.map_infty]
        rfl
  -- Contravariance of the same pointed maps gives covariant open extension.
  have h := congrArg complexKZeroPullback hsquare
  simp only [cf, cg, cgf, complexKZeroPullback_comp] at h
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun h a.val

/-- For a homeomorphism, open extension agrees with transport by inverse proper pullback. -/
theorem compactSupportKZeroOpenPushforward_homeomorph (e : X ≃ₜ Y) :
    compactSupportKZeroOpenPushforward e e.isOpenEmbedding =
      compactSupportKZeroHomeomorph e := by
  /- The range is all of Y. After identifying that range with X, the collapse
  sends a finite y to e.symm y and infinity to infinity. It is precisely the
  proper one-point extension of e.symm used by the existing transport map. -/
  let hf := e.isOpenEmbedding
  let := hf.isOpen_range.locallyCompactSpace
  let er := hf.isEmbedding.toHomeomorph
  let i : C(Set.range e, X) := ⟨er.symm, er.symm.continuous⟩
  let c : C(OnePoint Y, OnePoint (Set.range e)) :=
    ⟨onePointCollapse (Set.range e), continuous_onePointCollapse _ hf.isOpen_range⟩
  have hmap : (properOnePointMap i er.symm.isProperMap).comp c =
      properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap := by
    ext z
    cases z using OnePoint.rec with
    | infty => rfl
    | coe y =>
      obtain ⟨x, rfl⟩ := e.surjective y
      change OnePoint.map i (onePointCollapse (Set.range e) (e x)) =
        (e.symm (e x) : OnePoint X)
      rw [onePointCollapse_coe_of_mem (Set.range e) (e x) ⟨x, rfl⟩,
        OnePoint.map_some, e.symm_apply_apply]
      exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have h := congrArg complexKZeroPullback hmap
  rw [complexKZeroPullback_comp] at h
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun h a.val

end AtiyahSinger
