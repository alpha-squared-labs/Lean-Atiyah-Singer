/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.LocalHomologyLinearization

/-!
# Local orientation transport through one fixed chart

Public module ID: M1942.

Actual open excision transports common relative orientation classes into a chart.
Translations inside one convex compact control then identify their local values.
The statements retain the specified local homology chart equivalence and do not
choose or assume a positive simplex generator.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Chart transport commutes with the actual pair map into its source. -/
theorem localHomologyChartEquiv_naturality
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space X] [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) (p : C(Z, X)) (hp : ∀ z, p z ∈ e.source)
    {A : Set Z} (hA : Set.MapsTo p A ({x}ᶜ : Set X)) (k : ℕ) :
    relativeSingularHomologyMap ℤ p hA k ≫
      ModuleCat.ofHom (localHomologyChartEquiv e x hx k).toLinearMap =
      relativeSingularHomologyMap ℤ
        (⟨fun z ↦ e (p z), e.continuousOn.comp_continuous p.continuous hp⟩ : C(Z, Y))
        (A := A) (B := ({e x}ᶜ : Set Y))
        (fun z hz heq ↦ hA hz (e.injOn (hp z) hx heq)) k := by
  let pS : C(Z, e.source) := ⟨fun z ↦ ⟨p z, hp z⟩, p.continuous.subtype_mk _⟩
  let iS : C(e.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(e.source, e.target) :=
    ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
  let iT : C(e.target, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hpS : Set.MapsTo pS A ({⟨x, hx⟩}ᶜ : Set e.source) := by
    intro z hz heq
    exact hA hz (congrArg Subtype.val heq)
  have hiS : Set.MapsTo iS ({⟨x, hx⟩}ᶜ : Set e.source) ({x}ᶜ : Set X) :=
    fun z hz heq ↦ hz (Subtype.ext heq)
  have hq : Set.MapsTo q ({⟨x, hx⟩}ᶜ : Set e.source)
      ({e.toHomeomorphSourceTarget ⟨x, hx⟩}ᶜ : Set e.target) :=
    fun z hz heq ↦ hz (e.toHomeomorphSourceTarget.injective heq)
  have hiT : Set.MapsTo iT ({e.toHomeomorphSourceTarget ⟨x, hx⟩}ᶜ : Set e.target)
      ({e x}ᶜ : Set Y) := fun z hz heq ↦ hz (Subtype.ext heq)
  let F := relativeSingularHomologyMap ℤ pS hpS k
  let S := (localHomologyOpenInclusionEquiv e.source e.open_source ⟨x, hx⟩ k).toModuleIso
  let Q := (localHomologyHomeomorphEquiv e.toHomeomorphSourceTarget ⟨x, hx⟩ k).toModuleIso
  let T := (localHomologyOpenInclusionEquiv e.target e.open_target
    (e.toHomeomorphSourceTarget ⟨x, hx⟩) k).toModuleIso
  have hsource : relativeSingularHomologyMap ℤ p hA k = F ≫ S.hom := by
    change HomologicalComplex.homologyMap _ k =
      HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have htarget : relativeSingularHomologyMap ℤ
      (⟨fun z ↦ e (p z), e.continuousOn.comp_continuous p.continuous hp⟩ : C(Z, Y))
      (A := A) (B := ({e x}ᶜ : Set Y))
      (fun z hz heq ↦ hA hz (e.injOn (hp z) hx heq)) k = F ≫ Q.hom ≫ T.hom := by
    change HomologicalComplex.homologyMap _ k =
      HomologicalComplex.homologyMap _ k ≫
        HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  rw [hsource, htarget]
  change (F ≫ S.hom) ≫ (S.inv ≫ Q.hom ≫ T.hom) = F ≫ Q.hom ≫ T.hom
  simp only [Category.assoc, S.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A common class on a convex control has the same local value after translating its
points to zero. This is the relative-homology constancy underlying a local orientation. -/
theorem relativeSingularHomology_translate_from_convex
    (R : Type) [CommRing R] {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set V) (hK : Convex ℝ K) (a b : V) (ha : a ∈ K) (hb : b ∈ K) (k : ℕ)
    (c : relativeSingularHomology R Kᶜ k) :
    relativeSingularHomologyMap R
        (⟨fun v : V ↦ b + v, continuous_const.add continuous_id⟩ : C(V, V))
        (A := {v : V | v ≠ 0}) (B := ({b}ᶜ : Set V))
        (fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero b).symm))) k
        (relativeSingularHomologyMap R
          (⟨fun v : V ↦ v - a, continuous_id.sub continuous_const⟩ : C(V, V))
          (A := Kᶜ) (B := {v : V | v ≠ 0})
          (fun _ hv h ↦ hv (sub_eq_zero.mp h ▸ ha)) k c) =
      relativeSingularHomologyInclusion R Kᶜ ({b}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hb)) k c := by
  let f : C(V, V) := ⟨fun v ↦ v - a, continuous_id.sub continuous_const⟩
  let g : C(V, V) := ⟨fun v ↦ v - b, continuous_id.sub continuous_const⟩
  have hf : Set.MapsTo f Kᶜ {v : V | v ≠ 0} :=
    fun _ hv h ↦ hv (sub_eq_zero.mp h ▸ ha)
  have hg : Set.MapsTo g Kᶜ {v : V | v ≠ 0} :=
    fun _ hv h ↦ hv (sub_eq_zero.mp h ▸ hb)
  let H : f.Homotopy g :=
    { toFun p := p.2 - ((1 - (p.1 : ℝ)) • a + (p.1 : ℝ) • b)
      continuous_toFun := by fun_prop
      map_zero_left := by intro v; simp [f]
      map_one_left := by intro v; simp [g] }
  have hH (t : unitInterval) (v : V) (hv : v ∈ Kᶜ) : H (t, v) ≠ 0 := by
    intro hzero
    have hmem := hK ha hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : v = (1 - (t : ℝ)) • a + (t : ℝ) • b := sub_eq_zero.mp hzero
    apply hv
    rw [heq]
    exact hmem
  have heq := relativeSingularHomologyMap_eq_of_homotopy R hf hg H hH k
  let p : C(V, V) := ⟨fun v ↦ b + v, continuous_const.add continuous_id⟩
  have hp : Set.MapsTo p {v : V | v ≠ 0} ({b}ᶜ : Set V) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero b).symm))
  have hcancel : relativeSingularHomologyMap R g hg k ≫
      relativeSingularHomologyMap R p hp k =
        relativeSingularHomologyInclusion R Kᶜ ({b}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hb)) k := by
    change HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k =
      HomologicalComplex.homologyMap _ k
    rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
    have hid : p.comp g = ContinuousMap.id V := by ext v; simp [p, g]
    generalize_proofs at *
    generalize hfun : p.comp g = q at *
    clear hfun
    subst q
    rfl
  have hvalue := congrArg (fun F ↦ F c) hcancel
  change relativeSingularHomologyMap R p hp k
    (relativeSingularHomologyMap R f hf k c) = _
  rw [heq]
  exact hvalue

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A given local homological orientation is constant in translated coordinates on a
sufficiently small neighborhood of any point in a fixed Euclidean chart. -/
theorem exists_chart_localOrientation_transport
    {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    (O : HomologicalOrientation n M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (x : M) (hx : x ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ hUe : U ⊆ e.source,
      ∃ z : relativeSingularHomology ℤ
          {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n,
        ∀ y (hy : y ∈ U),
          relativeSingularHomologyMap ℤ
              (⟨fun v : EuclideanSpace ℝ (Fin n) ↦ e y + v,
                continuous_const.add continuous_id⟩ : C(_, _))
              (A := {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}) (B := ({e y}ᶜ : Set _))
              (fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero (e y)).symm))) n z =
            localHomologyChartEquiv e y (hUe hy) n (O.localGenerator y 1) := by
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨U₀, hU₀, hx₀, c, hc⟩ := O.locally_compatible x
  -- A compact chart ball fits inside both the chart source and the common-cycle neighborhood.
  have hOpen : IsOpen (e '' (U₀ ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hU₀.inter e.open_source) Set.inter_subset_right
  have hxImage : e x ∈ e '' (U₀ ∩ e.source) := ⟨x, ⟨hx₀, hx⟩, rfl⟩
  obtain ⟨ρ, hρ, hρsmall⟩ := Metric.isOpen_iff.mp hOpen (e x) hxImage
  let δ := ρ / 2
  have hδ : 0 < δ := half_pos hρ
  let L : Set V := Metric.closedBall (e x) δ
  have hLimage : L ⊆ e '' (U₀ ∩ e.source) :=
    (Metric.closedBall_subset_ball (by dsimp [δ]; linarith)).trans hρsmall
  have hLt : L ⊆ e.target := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hLimage hv
    exact e.map_source hy.2
  let K : Set M := e.symm '' L
  have hKsub : K ⊆ U₀ ∩ e.source := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨z, hz, heq⟩ := hLimage hv
    rw [← heq, e.left_inv hz.2]
    exact hz
  have hKclosed : IsClosed K :=
    ((isCompact_closedBall (e x) δ).image_of_continuousOn
      (e.continuousOn_symm.mono hLt)).isClosed
  let U : Set M := e.symm '' Metric.ball (e x) δ
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hLt)
  have hxU : x ∈ U := ⟨e x, Metric.mem_ball_self hδ, e.left_inv hx⟩
  have hUK : U ⊆ K := Set.image_mono Metric.ball_subset_closedBall
  have hUe : U ⊆ e.source := fun y hy ↦ (hKsub (hUK hy)).2
  have haL : e x ∈ L := Metric.mem_closedBall_self hδ.le
  -- Lift the restricted common class through the actual open-excision map of the chart source.
  let j : C(e.source, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let A : Set e.source := (j ⁻¹' K)ᶜ
  have hj : Set.MapsTo j A Kᶜ := fun _ hv ↦ hv
  let J := relativeSingularHomologyMap ℤ j hj n
  have hKr : K ⊆ Set.range j := fun y hy ↦ ⟨⟨y, (hKsub hy).2⟩, rfl⟩
  let : IsIso J := by
    obtain ⟨q, hq⟩ := homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ j
      e.open_source.isOpenEmbedding_subtypeVal K hKclosed hKr
    change IsIso (HomologicalComplex.homologyMap _ n)
    erw [← hq]
    change IsIso (q.toHomologyIso n).hom
    infer_instance
  have hU₀K : U₀ᶜ ⊆ Kᶜ := Set.compl_subset_compl.mpr
    (fun y hy ↦ (hKsub hy).1)
  let cK := relativeSingularHomologyInclusion ℤ U₀ᶜ Kᶜ hU₀K n c
  obtain ⟨cS, hcS⟩ := ((ConcreteCategory.isIso_iff_bijective J).mp inferInstance).surjective cK
  let g : C(e.source, V) := ⟨fun v ↦ e v.val, e.continuousOn.domRestrict⟩
  have hg : Set.MapsTo g A Lᶜ := by
    intro v hv hL
    exact hv ⟨e v.val, hL, e.left_inv v.property⟩
  let d := relativeSingularHomologyMap ℤ g hg n cS
  let z := relativeSingularHomologyMap ℤ
    (⟨fun v : V ↦ v - e x, continuous_id.sub continuous_const⟩ : C(V, V))
    (A := Lᶜ) (B := {v : V | v ≠ 0})
    (fun _ hv h ↦ hv (sub_eq_zero.mp h ▸ haL)) n d
  refine ⟨U, hU, hxU, hUe, z, ?_⟩
  intro y hy
  have hyK : y ∈ K := hUK hy
  have hy₀ : y ∈ U₀ := (hKsub hyK).1
  have hyL : e y ∈ L := by
    obtain ⟨v, hv, rfl⟩ := hyK
    rw [e.right_inv (hLt hv)]
    exact hv
  have hKy : Kᶜ ⊆ ({y}ᶜ : Set M) :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyK)
  have hLy : Lᶜ ⊆ ({e y}ᶜ : Set V) :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyL)
  have hjy : Set.MapsTo j A ({y}ᶜ : Set M) := fun _ hv ↦ hKy (hj hv)
  have hgy : Set.MapsTo g A ({e y}ᶜ : Set V) := fun _ hv ↦ hLy (hg hv)
  have hJlocal : relativeSingularHomologyMap ℤ j hjy n cS = O.localGenerator y 1 := by
    have hsquare : J ≫ relativeSingularHomologyInclusion ℤ Kᶜ ({y}ᶜ) hKy n =
        relativeSingularHomologyMap ℤ j hjy n := by
      change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
        HomologicalComplex.homologyMap _ n
      rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    have hv := congrArg (fun F ↦ F cS) hsquare
    change relativeSingularHomologyInclusion ℤ Kᶜ ({y}ᶜ) hKy n (J cS) = _ at hv
    rw [hcS] at hv
    refine hv.symm.trans ?_
    have hincl := congrArg (fun F ↦ F c)
      (relativeSingularHomologyInclusion_comp ℤ U₀ᶜ Kᶜ ({y}ᶜ) hU₀K hKy n)
    exact hincl.trans (hc y hy₀)
  have hGlocal : relativeSingularHomologyInclusion ℤ Lᶜ ({e y}ᶜ) hLy n d =
      relativeSingularHomologyMap ℤ g hgy n cS := by
    have hsquare : relativeSingularHomologyMap ℤ g hg n ≫
        relativeSingularHomologyInclusion ℤ Lᶜ ({e y}ᶜ) hLy n =
          relativeSingularHomologyMap ℤ g hgy n := by
      change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
        HomologicalComplex.homologyMap _ n
      rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    exact congrArg (fun F ↦ F cS) hsquare
  have hchart := congrArg (fun F ↦ F cS)
    (localHomologyChartEquiv_naturality e y (hUe hy) j (fun v ↦ v.property) hjy n)
  change localHomologyChartEquiv e y (hUe hy) n
    (relativeSingularHomologyMap ℤ j hjy n cS) =
      relativeSingularHomologyMap ℤ g hgy n cS at hchart
  rw [hJlocal] at hchart
  -- The convex chart control keeps every translation homotopy away from the removed point.
  exact (relativeSingularHomology_translate_from_convex ℤ L (convex_closedBall (e x) δ)
    (e x) (e y) haL hyL n d).trans (hGlocal.trans hchart.symm)

end AtiyahSinger
