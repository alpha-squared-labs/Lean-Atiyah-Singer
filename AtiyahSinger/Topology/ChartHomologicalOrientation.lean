/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactConvexLocalHomology
public import AtiyahSinger.Topology.LocalOrientationTransport

/-!
# Integral orientations from locally constant chart generators

Public module ID: M1604.

Specified primitive local classes determine a homological orientation when one
fixed chart makes them translations of one model class on a neighborhood.
The proof first lifts that class to a compact convex ball, then uses the actual
open-excision map and inverse chart to return a common relative class to the
original manifold. It constructs local compatibility before any global
orientation or fundamental class is assumed. This is the standard local-chart
construction of Hatcher, section 3.3, with explicit original pair maps.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Primitive local classes with constant translated chart values
define one integral orientation. -/
theorem existsUnique_homologicalOrientation_of_chart_transport
    {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (z : ∀ x : M, relativeSingularHomology ℤ ({x}ᶜ : Set M) n)
    (hgen : ∀ x, Function.Bijective (LinearMap.toSpanSingleton ℤ _ (z x)))
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hUe : U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source,
      ∃ c : relativeSingularHomology ℤ
          {v : EuclideanSpace ℝ (Fin n) | v ≠ 0} n,
        ∀ y (hy : y ∈ U),
          relativeSingularHomologyMap ℤ
              (⟨fun v : EuclideanSpace ℝ (Fin n) ↦
                chartAt (EuclideanSpace ℝ (Fin n)) x y + v,
                continuous_const.add continuous_id⟩ : C(_, _))
              (A := {v : EuclideanSpace ℝ (Fin n) | v ≠ 0})
              (B := ({chartAt (EuclideanSpace ℝ (Fin n)) x y}ᶜ : Set _))
              (fun _ hv h ↦ hv (add_left_cancel
                (h.trans (add_zero (chartAt (EuclideanSpace ℝ (Fin n)) x y)).symm))) n c =
            localHomologyChartEquiv (chartAt (EuclideanSpace ℝ (Fin n)) x)
              y (hUe hy) n (z y)) :
    ∃! O : HomologicalOrientation n M, ∀ x : M, O.localGenerator x 1 = z x := by
  let V := EuclideanSpace ℝ (Fin n)
  -- The prescribed primitive classes fix each integral generator map without a scalar choice.
  let G (x : M) : ℤ ≃ₗ[ℤ] relativeSingularHomology ℤ ({x}ᶜ : Set M) n :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ _ (z x)) (hgen x)
  have hG (x : M) : G x 1 = z x := by simp [G]
  have hcompat (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ c : relativeSingularHomology ℤ Uᶜ n, ∀ (y : M) (hy : y ∈ U),
        relativeSingularHomologyInclusion ℤ Uᶜ ({y}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n c = G y 1 := by
    obtain ⟨U₀, hU₀, hx₀, hU₀e, c₀, hc₀⟩ := hlocal x
    let e := chartAt V x
    have hx : x ∈ e.source := hU₀e hx₀
    -- A compact chart ball supports a class lifting the specified local model class.
    have hOpen : IsOpen (e '' U₀) := e.isOpen_image_of_subset_source hU₀ hU₀e
    have hxImage : e x ∈ e '' U₀ := ⟨x, hx₀, rfl⟩
    obtain ⟨ρ, hρ, hρsmall⟩ := Metric.isOpen_iff.mp hOpen (e x) hxImage
    let δ := ρ / 2
    have hδ : 0 < δ := half_pos hρ
    let L : Set V := Metric.closedBall (e x) δ
    have hLimage : L ⊆ e '' U₀ :=
      (Metric.closedBall_subset_ball (by dsimp [δ]; linarith)).trans hρsmall
    have hLt : L ⊆ e.target := by
      rintro v hv
      obtain ⟨y, hy, rfl⟩ := hLimage hv
      exact e.map_source (hU₀e hy)
    let K : Set M := e.symm '' L
    have hKU₀ : K ⊆ U₀ := by
      rintro y ⟨v, hv, rfl⟩
      obtain ⟨w, hw, heq⟩ := hLimage hv
      rw [← heq, e.left_inv (hU₀e hw)]
      exact hw
    let U : Set M := e.symm '' Metric.ball (e x) δ
    have hU : IsOpen U := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans hLt)
    have hxU : x ∈ U := ⟨e x, Metric.mem_ball_self hδ, e.left_inv hx⟩
    have hUK : U ⊆ K := Set.image_mono Metric.ball_subset_closedBall
    have haL : e x ∈ L := Metric.mem_closedBall_self hδ.le
    let ta : C(V, V) := ⟨fun v ↦ e x + v, continuous_const.add continuous_id⟩
    let sa : C(V, V) := ⟨fun v ↦ v - e x, continuous_id.sub continuous_const⟩
    have hta : Set.MapsTo ta {v : V | v ≠ 0} ({e x}ᶜ : Set V) :=
      fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero (e x)).symm))
    have hsa : Set.MapsTo sa ({e x}ᶜ : Set V) {v : V | v ≠ 0} :=
      fun _ hv h ↦ hv (sub_eq_zero.mp h)
    let Ta := relativeSingularHomologyMap ℤ ta hta n
    let : IsIso Ta := isIso_relativeSingularHomologyMap_of_inverse ℤ ta sa hta hsa
      (by apply ContinuousMap.ext; intro v; dsimp [ta, sa]; abel)
      (by apply ContinuousMap.ext; intro v; dsimp [ta, sa]; abel) n
    obtain ⟨d, hd⟩ := (relativeSingularHomologyInclusion_compactConvex_bijective ℤ
      L (isCompact_closedBall _ _) (convex_closedBall _ _) (e x) haL n).surjective (Ta c₀)
    have hsaL : Set.MapsTo sa Lᶜ {v : V | v ≠ 0} :=
      fun _ hv h ↦ hv (sub_eq_zero.mp h ▸ haL)
    have hcenter : relativeSingularHomologyMap ℤ sa hsaL n d = c₀ := by
      apply ((ConcreteCategory.isIso_iff_bijective Ta).mp inferInstance).injective
      exact (relativeSingularHomology_translate_from_convex ℤ L (convex_closedBall _ _)
        (e x) (e x) haL haL n d).trans hd
    -- Excision lifts that same class into the chart target, then the inverse chart returns it to M.
    let j : C(e.target, V) := ⟨Subtype.val, continuous_subtype_val⟩
    let A : Set e.target := (j ⁻¹' L)ᶜ
    have hj : Set.MapsTo j A Lᶜ := fun _ hv ↦ hv
    let J := relativeSingularHomologyMap ℤ j hj n
    have hLr : L ⊆ Set.range j := fun y hy ↦ ⟨⟨y, hLt hy⟩, rfl⟩
    let : IsIso J := by
      obtain ⟨q, hq⟩ := homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ j
        e.open_target.isOpenEmbedding_subtypeVal L (isCompact_closedBall _ _).isClosed hLr
      change IsIso (HomologicalComplex.homologyMap _ n)
      erw [← hq]
      change IsIso (q.toHomologyIso n).hom
      infer_instance
    obtain ⟨dT, hdT⟩ := ((ConcreteCategory.isIso_iff_bijective J).mp inferInstance).surjective d
    let p : C(e.target, M) := ⟨fun v ↦ e.symm v.val, e.continuousOn_symm.domRestrict⟩
    have hp : ∀ v, p v ∈ e.source := fun v ↦ e.symm.map_source v.property
    have hpK : Set.MapsTo p A Kᶜ := by
      intro v hv hvK
      obtain ⟨w, hw, heq⟩ := hvK
      have hweq : w = v.val := e.symm.injOn (hLt hw) v.property heq
      apply hv
      change v.val ∈ L
      exact hweq ▸ hw
    let cK := relativeSingularHomologyMap ℤ p hpK n dT
    have hKU : Kᶜ ⊆ Uᶜ := Set.compl_subset_compl.mpr hUK
    let cU := relativeSingularHomologyInclusion ℤ Kᶜ Uᶜ hKU n cK
    refine ⟨U, hU, hxU, cU, ?_⟩
    intro y hy
    have hyK : y ∈ K := hUK hy
    have hy₀ : y ∈ U₀ := hKU₀ hyK
    have hyE : y ∈ e.source := hU₀e hy₀
    have hyL : e y ∈ L := by
      obtain ⟨v, hv, rfl⟩ := hyK
      rw [e.right_inv (hLt hv)]
      exact hv
    have hKy : Kᶜ ⊆ ({y}ᶜ : Set M) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyK)
    have hLy : Lᶜ ⊆ ({e y}ᶜ : Set V) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyL)
    have hpy : Set.MapsTo p A ({y}ᶜ : Set M) := fun _ hv ↦ hKy (hpK hv)
    have hjy : Set.MapsTo j A ({e y}ᶜ : Set V) := fun _ hv ↦ hLy (hj hv)
    have hJlocal : relativeSingularHomologyMap ℤ j hjy n dT =
        relativeSingularHomologyInclusion ℤ Lᶜ ({e y}ᶜ) hLy n d := by
      have hsquare : J ≫ relativeSingularHomologyInclusion ℤ Lᶜ ({e y}ᶜ) hLy n =
          relativeSingularHomologyMap ℤ j hjy n := by
        change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
        rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
        rfl
      have h := congrArg (fun F ↦ F dT) hsquare
      change relativeSingularHomologyInclusion ℤ Lᶜ ({e y}ᶜ) hLy n (J dT) = _ at h
      rw [hdT] at h
      exact h.symm
    have hPlocal : relativeSingularHomologyInclusion ℤ Uᶜ ({y}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n cU =
          relativeSingularHomologyMap ℤ p hpy n dT := by
      have hfirst := congrArg (fun F ↦ F cK)
        (relativeSingularHomologyInclusion_comp ℤ Kᶜ Uᶜ ({y}ᶜ) hKU
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n)
      change relativeSingularHomologyInclusion ℤ Uᶜ ({y}ᶜ) _ n cU = _ at hfirst
      refine hfirst.trans ?_
      have hsquare : relativeSingularHomologyMap ℤ p hpK n ≫
          relativeSingularHomologyInclusion ℤ Kᶜ ({y}ᶜ) hKy n =
            relativeSingularHomologyMap ℤ p hpy n := by
        change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
        rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
        rfl
      exact congrArg (fun F ↦ F dT) hsquare
    rw [hPlocal, hG]
    apply (localHomologyChartEquiv e y hyE n).injective
    have hchart := congrArg (fun F ↦ F dT)
      (localHomologyChartEquiv_naturality e y hyE p hp hpy n)
    have hchartValue : localHomologyChartEquiv e y hyE n
        (relativeSingularHomologyMap ℤ p hpy n dT) =
          relativeSingularHomologyMap ℤ j hjy n dT := by
      have hfun : (⟨fun v : e.target ↦ e (p v),
          e.continuousOn.comp_continuous p.continuous hp⟩ : C(e.target, V)) = j := by
        apply ContinuousMap.ext
        intro v
        exact e.right_inv v.property
      change localHomologyChartEquiv e y hyE n
        (relativeSingularHomologyMap ℤ p hpy n dT) = _ at hchart
      simpa only [hfun] using hchart
    rw [hchartValue, hJlocal]
    have htranslation := relativeSingularHomology_translate_from_convex ℤ L
      (convex_closedBall _ _) (e x) (e y) haL hyL n d
    change relativeSingularHomologyMap ℤ _ _ n
      (relativeSingularHomologyMap ℤ sa hsaL n d) = _ at htranslation
    rw [hcenter] at htranslation
    exact htranslation.symm.trans (hc₀ y hy₀)
  -- Local compatibility completes the structure; its values on one determine it uniquely.
  let O : HomologicalOrientation n M := ⟨G, hcompat⟩
  refine ⟨O, hG, ?_⟩
  intro O' hO'
  have hmaps : O'.localGenerator = O.localGenerator := by
    funext x
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro a
    have h₁ := (O'.localGenerator x).map_smul a (1 : ℤ)
    have h₂ := (O.localGenerator x).map_smul a (1 : ℤ)
    simp only [smul_eq_mul, mul_one, hO' x] at h₁
    simp only [smul_eq_mul, mul_one, show O.localGenerator x 1 = z x from hG x] at h₂
    exact h₁.trans h₂.symm
  rcases O' with ⟨G', hG'⟩
  change G' = G at hmaps
  cases hmaps
  rfl

end AtiyahSinger
