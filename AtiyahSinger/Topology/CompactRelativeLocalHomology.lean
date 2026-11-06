/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactConvexLocalHomology
public import AtiyahSinger.Topology.EuclideanHomologyULift
public import AtiyahSinger.Topology.RelativeSingularFunctoriality
public import AtiyahSinger.Topology.RelativeSingularMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact supports and local singular homology

Public module ID: M1648.

Hatcher, Lemma 3.27, detects compact-relative classes by their restrictions at
points and proves vanishing above the manifold dimension. The argument starts
with compact convex controls, passes to finite unions by relative Mayer–Vietoris,
and then uses the finite support of singular chains. Every restriction below is
the original relative pair-inclusion map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite Topology
open scoped DirectSum Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The original relative homology inclusions compose with the prescribed inclusions of sets. -/
theorem relativeSingularHomologyInclusion_comp (A B C : Set X)
    (hAB : A ⊆ B) (hBC : B ⊆ C) (k : ℕ) :
    relativeSingularHomologyInclusion R A B hAB k ≫
      relativeSingularHomologyInclusion R B C hBC k =
        relativeSingularHomologyInclusion R A C (hAB.trans hBC) k := by
  let F := relativeSingularChainsFunctor R X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) k
  exact (F.map_comp (homOfLE hAB) (homOfLE hBC)).symm

/-- The relative group of a space modulo all its own chains is zero in every degree. -/
theorem relativeSingularHomology_subsingleton_univ (k : ℕ) :
    Subsingleton (relativeSingularHomology R (Set.univ : Set X) k) := by
  let e : TopCat.of (Set.univ : Set X) ≅ TopCat.of X :=
    { hom := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      inv := TopCat.ofHom ⟨fun x ↦ ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }
  have : IsIso (singularSubspaceChains R (Set.univ : Set X)) :=
    inferInstanceAs (IsIso ((singularChainsFunctor R).mapIso e).hom)
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} R)
    (ComplexShape.down ℕ) k).map_isZero (isZero_cokernel_of_epi _)

/-- The local detection and dimension bounds used together in compact-support induction. -/
private def HasRelativeLocalControl (n : ℕ) (A : Set X) : Prop :=
  (∀ k : ℕ, n < k → Subsingleton (relativeSingularHomology R A k)) ∧
    ∀ c : relativeSingularHomology R A n,
      (∀ (x : X) (hx : x ∉ A), relativeSingularHomologyInclusion R A ({x}ᶜ)
        (fun _y hy h ↦ hx (h ▸ hy)) n c = 0) → c = 0

private theorem hasRelativeLocalControl_univ (n : ℕ) :
    HasRelativeLocalControl R n (Set.univ : Set X) := by
  constructor
  · intro k _
    exact relativeSingularHomology_subsingleton_univ R k
  · intro c _
    have := relativeSingularHomology_subsingleton_univ (X := X) R n
    exact Subsingleton.elim _ _

private theorem hasRelativeLocalControl_inter (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (h₁ : HasRelativeLocalControl R n A)
    (h₂ : HasRelativeLocalControl R n B) (h₃ : HasRelativeLocalControl R n (A ∪ B)) :
    HasRelativeLocalControl R n (A ∩ B) := by
  constructor
  · -- The preceding intersection-support group vanishes as well, in degree k + 1.
    intro k hk
    have := h₁.1 k hk
    have := h₂.1 k hk
    have := h₃.1 (k + 1) (by omega)
    exact relativeSingularHomology_subsingleton_inter R A B hA hB k
  · -- Local detection first kills each restriction; Mayer–Vietoris then kills the class.
    intro c hc
    have hca : relativeSingularHomologyInclusion R (A ∩ B) A Set.inter_subset_left n c = 0 := by
      apply h₁.2
      intro x hx
      have h := congrArg (fun f ↦ f c)
        (relativeSingularHomologyInclusion_comp R (A ∩ B) A ({x}ᶜ)
          Set.inter_subset_left (fun y hy h ↦ hx (h ▸ hy)) n)
      exact h.trans (hc x (fun hi ↦ hx hi.1))
    have hcb : relativeSingularHomologyInclusion R (A ∩ B) B Set.inter_subset_right n c = 0 := by
      apply h₂.2
      intro x hx
      have h := congrArg (fun f ↦ f c)
        (relativeSingularHomologyInclusion_comp R (A ∩ B) B ({x}ᶜ)
          Set.inter_subset_right (fun y hy h ↦ hx (h ▸ hy)) n)
      exact h.trans (hc x (fun hi ↦ hx hi.2))
    have := h₃.1 (n + 1) (by omega)
    apply relativeSingularHomologyInclusion_inter_jointly_injective R A B hA hB n
    exact Prod.ext (hca.trans (map_zero _).symm) (hcb.trans (map_zero _).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasRelativeLocalControl_openEmbedding_image
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (n : ℕ) (f : C(X, Y)) (hf : IsOpenEmbedding f) (K : Set X) (hK : IsCompact K) :
    HasRelativeLocalControl R n Kᶜ ↔ HasRelativeLocalControl R n (f '' K)ᶜ := by
  have hpair (T : Set X) : Set.MapsTo f Tᶜ (f '' T)ᶜ := by
    rintro x hx ⟨y, hy, hyx⟩
    exact hx ((hf.injective hyx) ▸ hy)
  have hbij (T : Set X) (L : Set Y) (hT : IsCompact T) (hL : f '' T = L)
      (hp : Set.MapsTo f Tᶜ Lᶜ) (k : ℕ) :
      Function.Bijective (relativeSingularHomologyMap R f hp k) := by
    have hclosed : IsClosed L := hL ▸ (hT.image f.continuous).isClosed
    have hrange : L ⊆ Set.range f := by
      rw [← hL]
      exact Set.image_subset_range _ _
    have hpre : f ⁻¹' L = T := by rw [← hL, Set.preimage_image_eq _ hf.injective]
    have hexc {A : Set X} (hA : A = (f ⁻¹' L)ᶜ) (hp : Set.MapsTo f A Lᶜ) :
        HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
          (relativeSingularChainsMap R f hp) := by
      subst A
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f hf L hclosed hrange
    obtain ⟨e, he⟩ := hexc (congrArg Set.compl hpre.symm) hp
    have : IsIso (relativeSingularHomologyMap R f hp k) := by
      change IsIso (HomologicalComplex.homologyMap _ k)
      erw [← he]
      exact inferInstanceAs (IsIso (e.toHomologyIso k).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hpoint (x : X) : Set.MapsTo f ({x}ᶜ : Set X) ({f x}ᶜ : Set Y) := by
    intro y hy h
    exact hy (hf.injective h)
  have hnat (x : X) (hx : x ∈ K) (k : ℕ) :=
    (relativeSingularHomologyMap_inclusion R f
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hx)))
      (hpair K) (hpoint x) k).symm
  constructor
  · intro h
    constructor
    · intro k hk
      have := h.1 k hk
      exact (hbij K (f '' K) hK rfl (hpair K) k).surjective.subsingleton
    · intro c hc
      obtain ⟨d, hd⟩ := (hbij K (f '' K) hK rfl (hpair K) n).surjective c
      have hd0 : d = 0 := by
        apply h.2
        intro x hx
        have hxK : x ∈ K := not_not.mp hx
        apply (hbij {x} {f x} isCompact_singleton (by simp) (hpoint x) n).injective
        have hcomm := congrArg (fun g ↦ g d) (hnat x hxK n)
        have hvalue := congrArg
          (fun z ↦ relativeSingularHomologyInclusion R (f '' K)ᶜ ({f x}ᶜ)
            (Set.compl_subset_compl.mpr
              (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hxK))) n z) hd
        exact (hcomm.symm.trans (hvalue.trans
          (hc (f x) (fun h ↦ h (Set.mem_image_of_mem f hxK))))).trans (map_zero _).symm
      rw [hd0, map_zero] at hd
      exact hd.symm
  · intro h
    constructor
    · intro k hk
      have := h.1 k hk
      exact (hbij K (f '' K) hK rfl (hpair K) k).injective.subsingleton
    · intro c hc
      apply (hbij K (f '' K) hK rfl (hpair K) n).injective
      have hzero : relativeSingularHomologyMap R f (hpair K) n c = 0 := by
        apply h.2
        intro y hy
        obtain ⟨x, hx, rfl⟩ := not_not.mp hy
        have hcomm := congrArg (fun g ↦ g c) (hnat x hx n)
        have hvalue := congrArg (fun z ↦ relativeSingularHomologyMap R f (hpoint x) n z)
          (hc x (fun h ↦ h hx))
        exact hcomm.trans (hvalue.trans (map_zero _))
      exact hzero.trans (map_zero _).symm

private theorem hasRelativeLocalControl_compactConvex
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hvan : ∀ (k : ℕ) (x : E), n < k →
      Subsingleton (relativeSingularHomology R ({x}ᶜ) k)) (K : Set E)
    (hK : IsCompact K) (hconv : Convex ℝ K) : HasRelativeLocalControl R n Kᶜ := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hiso (k : ℕ) := relativeSingularHomologyInclusion_compactConvex_bijective
      R K hK hconv x hx k
    constructor
    · intro k hk
      have : Subsingleton (relativeSingularHomology R ({x}ᶜ) k) :=
        hvan k x hk
      exact (hiso k).injective.subsingleton
    · intro c hc
      apply (hiso n).injective
      exact (hc x (by simpa using hx)).trans (map_zero _).symm
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.compl_empty]
    exact hasRelativeLocalControl_univ R n

private theorem hasRelativeLocalControl_finiteUnion_compactConvex
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hvan : ∀ (k : ℕ) (x : E), n < k →
      Subsingleton (relativeSingularHomology R ({x}ᶜ) k)) {ι : Type*} (s : Finset ι) :
    ∀ (K : ι → Set E),
      (∀ i ∈ s, IsCompact (K i)) → (∀ i ∈ s, Convex ℝ (K i)) →
        HasRelativeLocalControl R n (⋃ i ∈ s, K i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K _ _
    simpa using hasRelativeLocalControl_univ (X := E) R n
  | @insert a s ha ih =>
    intro K hK hconv
    let L := ⋃ i ∈ s, K i
    have hL : IsCompact L := s.isCompact_biUnion fun i hi ↦ hK i (Finset.mem_insert_of_mem hi)
    have h₁ := hasRelativeLocalControl_compactConvex R n hvan (K a)
      (hK a (Finset.mem_insert_self _ _)) (hconv a (Finset.mem_insert_self _ _))
    have h₂ : HasRelativeLocalControl R n Lᶜ :=
      ih K (fun i hi ↦ hK i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hconv i (Finset.mem_insert_of_mem hi))
    -- The overlap is a union indexed by the same smaller family, of convex intersections.
    have h₃ := ih (fun i ↦ K a ∩ K i)
      (fun i hi ↦ (hK a (Finset.mem_insert_self _ _)).inter
        (hK i (Finset.mem_insert_of_mem hi)))
      (fun i hi ↦ (hconv a (Finset.mem_insert_self _ _)).inter
        (hconv i (Finset.mem_insert_of_mem hi)))
    have hInter : (⋃ i ∈ s, K a ∩ K i) = K a ∩ L := by
      exact (Set.inter_iUnion₂ (K a) (fun i (_ : i ∈ s) ↦ K i)).symm
    rw [hInter] at h₃
    have hUnion : (⋃ i ∈ insert a s, K i) = K a ∪ L := by
      exact Finset.set_biUnion_insert a s K
    rw [hUnion, Set.compl_union]
    apply hasRelativeLocalControl_inter R n (K a)ᶜ Lᶜ
      (hK a (Finset.mem_insert_self _ _)).isClosed.isOpen_compl hL.isClosed.isOpen_compl h₁ h₂
    simpa only [Set.compl_inter] using h₃

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every ordinary singular chain is supported in a compact subspace, using its original
finite simplex expression. No separation or local compactness hypothesis is needed. -/
theorem exists_isCompact_singularChain_support (n : ℕ) (c : (singularChains R X).X n) :
    ∃ K : Set X, IsCompact K ∧ c ∈ ((singularSubspaceChains R K).f n).hom.range := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  let e : (singularChains R X).X n ≅
      ModuleCat.of R (⨁ _σ : S.obj (op ⦋n⦌), singularCoefficient R) :=
    ModuleCat.coprodIsoDirectSum (fun _σ : S.obj (op ⦋n⦌) ↦ singularCoefficient R)
  have hall (d : ⨁ _σ : S.obj (op ⦋n⦌), singularCoefficient R) :
      ∃ K : Set X, IsCompact K ∧ e.inv d ∈ ((singularSubspaceChains R K).f n).hom.range := by
    induction d using DirectSum.induction_on with
    | zero =>
      exact ⟨∅, isCompact_empty, by rw [map_zero]; exact Submodule.zero_mem _⟩
    | of σ a =>
      -- A single simplex factors through its compact image in the original ambient space.
      let f := (TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ
      let K := Set.range f
      let τ := ((TopCat.of K).toSSetObjEquiv (op ⦋n⦌)).symm
        (⟨fun t ↦ ⟨f t, ⟨t, rfl⟩⟩, f.continuous.subtype_mk _⟩ :
          C(Convexity.StdSimplex ℝ (Fin (n + 1)), K))
      refine ⟨K, isCompact_range f.continuous,
        (TopCat.toSSet.obj (TopCat.of K)).ιChainComplex (R := singularCoefficient R) τ a, ?_⟩
      have hgen : e.inv (DirectSum.of (fun _σ : S.obj (op ⦋n⦌) ↦
          singularCoefficient R) σ a) = S.ιChainComplex (R := singularCoefficient R) σ a := by
        exact congrArg (fun f ↦ f a)
          (ModuleCat.lof_coprodIsoDirectSum_inv
            (fun _σ : S.obj (op ⦋n⦌) ↦ singularCoefficient R) σ)
      rw [hgen]
      change ((TopCat.toSSet.obj (TopCat.of K)).ιChainComplex τ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(K, X))))
          (singularCoefficient R)).f n) a = _
      rw [SSet.ι_chainComplexMap_f]
      rfl
    | add a b ha hb =>
      obtain ⟨K, hK, x, hx⟩ := ha
      obtain ⟨L, hL, y, hy⟩ := hb
      -- A finite union of the compact simplex images supports the sum.
      have hmono (U V : Set X) (hUV : U ⊆ V) :
          ((singularSubspaceChains R U).f n).hom.range ≤
            ((singularSubspaceChains R V).f n).hom.range := by
        let f : C(U, V) :=
          ⟨fun z ↦ ⟨z.val, hUV z.property⟩, continuous_subtype_val.subtype_mk _⟩
        have hmap : (singularChainsFunctor R).map (TopCat.ofHom f) ≫
            singularSubspaceChains R V = singularSubspaceChains R U := by
          simp only [singularSubspaceChains, ← Functor.map_comp]
          rfl
        rintro z ⟨w, rfl⟩
        exact ⟨((singularChainsFunctor R).map (TopCat.ofHom f)).f n w,
          congrArg (fun f ↦ f.f n w) hmap⟩
      refine ⟨K ∪ L, hK.union hL, ?_⟩
      rw [map_add]
      exact Submodule.add_mem _ (hmono K (K ∪ L) Set.subset_union_left ⟨x, hx⟩)
        (hmono L (K ∪ L) Set.subset_union_right ⟨y, hy⟩)
  obtain ⟨K, hK, hc⟩ := hall (e.hom c)
  have he : e.inv (e.hom c) = c := congrArg (fun f ↦ f c) e.hom_inv_id
  exact ⟨K, hK, he ▸ hc⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A relative homology class already comes from a compact part of its relative subspace.
The compact part supports the boundary of one finite ambient-chain representative. -/
theorem exists_isCompact_relativeSingularHomology_support
    (A : Set X) (k : ℕ) (c : relativeSingularHomology R A k) :
    ∃ (L : Set X) (_ : IsCompact L) (hLA : L ⊆ A)
      (d : relativeSingularHomology R L k),
        relativeSingularHomologyInclusion R L A hLA k d = c := by
  let C := singularChains R X
  let CA := relativeSingularChains R A
  let qA := relativeSingularChainsProjection R A
  let j := (ComplexShape.down ℕ).next k
  -- Choose a cycle class and lift its finite relative chain to the original ambient chains.
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective (CA.homologyπ k)).mp inferInstance c
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (qA.f k)).mp inferInstance (CA.iCycles k v)
  have hboundary : qA.f j (C.d k j z) = 0 := by
    have hcomm := congrArg (fun f ↦ f z) (qA.comm k j)
    have hcycle := congrArg (fun f ↦ f v) (CA.iCycles_d k j)
    exact hcomm.symm.trans ((congrArg (fun x ↦ CA.d k j x) hz).trans hcycle)
  have hexact := (shortExact_singularSubspaceChains R A).exact.map
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) j)
  obtain ⟨b, hb⟩ : ∃ b : (singularChains R A).X j,
      (singularSubspaceChains R A).f j b = C.d k j z :=
    (ShortComplex.moduleCat_exact_iff _).mp hexact _ hboundary
  obtain ⟨T, hT, dT, hdT⟩ := exists_isCompact_singularChain_support R j b
  -- The compact boundary support in A has its actual compact image in X.
  let L : Set X := Subtype.val '' T
  have hL : IsCompact L := hT.image continuous_subtype_val
  have hLA : L ⊆ A := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  let f : C(T, L) :=
    ⟨fun x ↦ ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let dL := ((singularChainsFunctor R).map (TopCat.ofHom f)).f j dT
  have hmap : (singularChainsFunctor R).map (TopCat.ofHom f) ≫
      singularSubspaceChains R L = singularSubspaceChains R T ≫ singularSubspaceChains R A := by
    simp only [singularSubspaceChains, ← Functor.map_comp]
    rfl
  have hdL : (singularSubspaceChains R L).f j dL = C.d k j z := by
    have h := congrArg (fun f ↦ f.f j dT) hmap
    exact h.trans ((congrArg (fun x ↦ (singularSubspaceChains R A).f j x) hdT).trans hb)
  -- The same ambient representative is now a cycle relative to L.
  let CL := relativeSingularChains R L
  let qL := relativeSingularChainsProjection R L
  have hcycleL : CL.d k j (qL.f k z) = 0 := by
    have hcomm := congrArg (fun f ↦ f z) (qL.comm k j)
    have hzero := congrArg (fun f ↦ f.f j dL) (cokernel.condition (singularSubspaceChains R L))
    exact hcomm.trans ((congrArg (fun x ↦ qL.f j x) hdL.symm).trans hzero)
  let vL : CL.cycles k := (CL.sc k).moduleCatCyclesIso.inv ⟨qL.f k z, hcycleL⟩
  have hvL : CL.iCycles k vL = qL.f k z := by
    exact congrArg (fun f ↦ f ⟨qL.f k z, hcycleL⟩)
      ((CL.sc k).moduleCatCyclesIso_inv_iCycles)
  let inc := (relativeSingularChainsFunctor R X).map (homOfLE hLA)
  have hq : qL ≫ inc = qA := by
    simp [qL, qA, inc, relativeSingularChainsFunctor, relativeSingularChainsMap]
  have hvmap : HomologicalComplex.cyclesMap inc k vL = v := by
    apply (ModuleCat.mono_iff_injective (CA.iCycles k)).mp inferInstance
    have h := congrArg (fun f ↦ f vL) (HomologicalComplex.cyclesMap_i inc k)
    exact h.trans ((congrArg (fun x ↦ inc.f k x) hvL).trans
      ((congrArg (fun f ↦ f.f k z) hq).trans hz))
  refine ⟨L, hL, hLA, CL.homologyπ k vL, ?_⟩
  have h := congrArg (fun f ↦ f vL) (HomologicalComplex.homologyπ_naturality inc k)
  change relativeSingularHomologyInclusion R L A hLA k (CL.homologyπ k vL) = _
  exact h.trans ((congrArg (fun x ↦ CA.homologyπ k x) hvmap).trans hv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A compact-relative class lifts to a finite closed-ball neighborhood with centers in the
original compact set. The balls avoid the finite boundary support of its representative. -/
theorem exists_finite_closedBall_relativeSingularHomology_lift
    {E : Type u} [MetricSpace E] (K : Set E) (hK : IsCompact K)
    (k : ℕ) (c : relativeSingularHomology R Kᶜ k) :
    ∃ (s : Finset K) (r : K → ℝ), (∀ x, 0 < r x) ∧
      ∃ (hcover : K ⊆ ⋃ x ∈ s, Metric.closedBall x.val (r x))
        (d : relativeSingularHomology R (⋃ x ∈ s, Metric.closedBall x.val (r x))ᶜ k),
        relativeSingularHomologyInclusion R (⋃ x ∈ s, Metric.closedBall x.val (r x))ᶜ Kᶜ
          (Set.compl_subset_compl.mpr hcover) k d = c := by
  classical
  obtain ⟨L, hL, hLK, d, hd⟩ := exists_isCompact_relativeSingularHomology_support R Kᶜ k c
  -- Every center has a closed ball disjoint from the compact boundary support.
  have hball (x : K) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ Lᶜ := by
    apply Metric.nhds_basis_closedBall.mem_iff.mp
    apply hL.isClosed.isOpen_compl.mem_nhds
    intro hx
    exact hLK hx x.property
  choose r hr hdisj using hball
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ Metric.ball x.val (r x))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hcover : K ⊆ ⋃ x ∈ s, Metric.closedBall x.val (r x) := by
    intro x hx
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hy', hxy⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy', Metric.ball_subset_closedBall hxy⟩⟩
  let N := ⋃ x ∈ s, Metric.closedBall x.val (r x)
  have hLN : L ⊆ Nᶜ := by
    intro x hx hN
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hN
    obtain ⟨_, hxy⟩ := Set.mem_iUnion.mp hy
    exact hdisj y hxy hx
  refine ⟨s, r, hr, hcover, relativeSingularHomologyInclusion R L Nᶜ hLN k d, ?_⟩
  have h := congrArg (fun f ↦ f d)
    (relativeSingularHomologyInclusion_comp R L Nᶜ Kᶜ hLN
      (Set.compl_subset_compl.mpr hcover) k)
  exact h.trans hd

private theorem hasRelativeLocalControl_compact_normedSpace
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (n : ℕ) (hvan : ∀ (k : ℕ) (x : E), n < k →
      Subsingleton (relativeSingularHomology R ({x}ᶜ) k)) (K : Set E) (hK : IsCompact K) :
    HasRelativeLocalControl R n Kᶜ := by
  constructor
  · intro k hk
    have hz (c : relativeSingularHomology R Kᶜ k) : c = 0 := by
      obtain ⟨s, r, _, hcover, d, hd⟩ :=
        exists_finite_closedBall_relativeSingularHomology_lift R K hK k c
      have hN := hasRelativeLocalControl_finiteUnion_compactConvex R n hvan s
        (fun x ↦ Metric.closedBall x.val (r x))
        (fun _ _ ↦ isCompact_closedBall _ _) (fun _ _ ↦ convex_closedBall _ _)
      have := hN.1 k hk
      have hd0 : d = 0 := Subsingleton.elim _ _
      rw [hd0, map_zero] at hd
      exact hd.symm
    exact ⟨fun c d ↦ (hz c).trans (hz d).symm⟩
  · intro c hc
    obtain ⟨s, r, hr, hcover, d, hd⟩ :=
      exists_finite_closedBall_relativeSingularHomology_lift R K hK n c
    let N := ⋃ x ∈ s, Metric.closedBall x.val (r x)
    have hN := hasRelativeLocalControl_finiteUnion_compactConvex R n hvan s
      (fun x ↦ Metric.closedBall x.val (r x))
      (fun _ _ ↦ isCompact_closedBall _ _) (fun _ _ ↦ convex_closedBall _ _)
    have hcenter (x : K) : relativeSingularHomologyInclusion R Nᶜ ({x.val}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr (hcover x.property))) n d =
          0 := by
      have hcomp := congrArg (fun f ↦ f d)
        (relativeSingularHomologyInclusion_comp R Nᶜ Kᶜ ({x.val}ᶜ)
          (Set.compl_subset_compl.mpr hcover)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr x.property)) n)
      have hvalue := congrArg
        (fun z ↦ relativeSingularHomologyInclusion R Kᶜ ({x.val}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr x.property)) n z) hd
      exact hcomp.symm.trans (hvalue.trans (hc x.val (fun h ↦ h x.property)))
    have hball (x : K) (hx : x ∈ s) :
        Metric.closedBall x.val (r x) ⊆ N := by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hy⟩⟩
    -- Every selected ball meets K at its center. The convex isomorphism therefore
    -- turns the given zero local restriction into a zero class on the whole ball.
    have hballZero (x : K) (hx : x ∈ s) :
        relativeSingularHomologyInclusion R Nᶜ (Metric.closedBall x.val (r x))ᶜ
          (Set.compl_subset_compl.mpr (hball x hx)) n d = 0 := by
      have hmem : x.val ∈ Metric.closedBall x.val (r x) := Metric.mem_closedBall_self (hr x).le
      apply (relativeSingularHomologyInclusion_compactConvex_bijective R
        (Metric.closedBall x.val (r x)) (isCompact_closedBall _ _) (convex_closedBall _ _)
        x.val hmem n).injective
      have hcomp := congrArg (fun f ↦ f d)
        (relativeSingularHomologyInclusion_comp R Nᶜ (Metric.closedBall x.val (r x))ᶜ
          ({x.val}ᶜ) (Set.compl_subset_compl.mpr (hball x hx))
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hmem)) n)
      exact (hcomp.trans (hcenter x)).trans (map_zero _).symm
    have hd0 : d = 0 := by
      apply hN.2
      intro y hy
      have hyN : y ∈ N := not_not.mp hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hyN
      obtain ⟨hx', hxy⟩ := Set.mem_iUnion.mp hx
      have hcomp := congrArg (fun f ↦ f d)
        (relativeSingularHomologyInclusion_comp R Nᶜ (Metric.closedBall x.val (r x))ᶜ
          ({y}ᶜ) (Set.compl_subset_compl.mpr (hball x hx'))
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxy)) n)
      have hvalue := congrArg
        (fun z ↦ relativeSingularHomologyInclusion R (Metric.closedBall x.val (r x))ᶜ ({y}ᶜ)
          (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxy)) n z) (hballZero x hx')
      exact hcomp.symm.trans (hvalue.trans (map_zero _))
    rw [hd0, map_zero] at hd
    exact hd.symm

/-- Compact-relative Euclidean homology vanishes above the dimension for every coefficient ring. -/
theorem relativeSingularHomology_subsingleton_compact_euclidean
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (k : ℕ) (hk : n < k) : Subsingleton (relativeSingularHomology R Kᶜ k) :=
  (hasRelativeLocalControl_compact_normedSpace R n
    (subsingleton_relativeSingularHomology_euclidean R n) K hK).1 k hk

/-- A top-degree compact-relative Euclidean class is detected by all its local restrictions. -/
theorem relativeSingularHomology_eq_zero_of_point_restrictions_euclidean
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (c : relativeSingularHomology R Kᶜ n)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K),
      relativeSingularHomologyInclusion R Kᶜ ({x}ᶜ)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) n c = 0) : c = 0 := by
  apply (hasRelativeLocalControl_compact_normedSpace R n
    (subsingleton_relativeSingularHomology_euclidean R n) K hK).2
  intro x hx
  exact hc x (by simpa using hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasRelativeLocalControl_compact_chart
    {M : Type u} [TopologicalSpace M] [T2Space M] (n : ℕ)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    HasRelativeLocalControl R n Kᶜ := by
  let f : C(e.source, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let E := ULift.{u} (EuclideanSpace ℝ (Fin n))
  let g : C(e.source, E) :=
    ⟨fun x ↦ ULift.up (e x),
      Homeomorph.ulift.symm.continuous.comp e.isOpenEmbedding_restrict.continuous⟩
  let : ProperSpace E := ⟨fun x r ↦ by
    have h := (isCompact_closedBall x.down r).image Homeomorph.ulift.symm.continuous
    convert h using 1
    ext y
    simp only [Set.mem_image, Metric.mem_closedBall, Homeomorph.ulift, Equiv.ulift]
    constructor
    · intro hy
      exact ⟨y.down, hy, by cases y; rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz⟩
  have hf : IsOpenEmbedding f := e.open_source.isOpenEmbedding_subtypeVal
  have hg : IsOpenEmbedding g :=
    Homeomorph.ulift.symm.isOpenEmbedding.comp e.isOpenEmbedding_restrict
  let L : Set e.source := f ⁻¹' K
  have hrange : K ⊆ Set.range f := by
    intro x hx
    exact ⟨⟨x, hKs hx⟩, rfl⟩
  have hL : IsCompact L := hf.toIsEmbedding.isInducing.isCompact_preimage' hK hrange
  have himage : f '' L = K := Set.image_preimage_eq_of_subset hrange
  have hE := hasRelativeLocalControl_compact_normedSpace R n
    (subsingleton_relativeSingularHomology_ulift_euclidean R n) (g '' L)
    (hL.image g.continuous)
  have hsource := (hasRelativeLocalControl_openEmbedding_image R n g hg L hL).mpr hE
  have hambient := (hasRelativeLocalControl_openEmbedding_image R n f hf L hL).mp hsource
  rwa [himage] at hambient

private theorem hasRelativeLocalControl_finiteUnion_compact
    [T2Space X] (n : ℕ) {ι : Type*} (s : Finset ι) :
    ∀ (K : ι → Set X), (∀ i ∈ s, IsCompact (K i)) →
      (∀ i ∈ s, ∀ L : Set X, IsCompact L → L ⊆ K i → HasRelativeLocalControl R n Lᶜ) →
        HasRelativeLocalControl R n (⋃ i ∈ s, K i)ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K _ _
    simpa using hasRelativeLocalControl_univ (X := X) R n
  | @insert a s ha ih =>
    intro K hK hlocal
    let L := ⋃ i ∈ s, K i
    have hL : IsCompact L := s.isCompact_biUnion fun i hi ↦ hK i (Finset.mem_insert_of_mem hi)
    have h₁ := hlocal a (Finset.mem_insert_self _ _) (K a)
      (hK a (Finset.mem_insert_self _ _)) Set.Subset.rfl
    have h₂ : HasRelativeLocalControl R n Lᶜ := ih K
      (fun i hi ↦ hK i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hlocal i (Finset.mem_insert_of_mem hi))
    -- Every compact overlap remains in one of the original chart pieces.
    have h₃ := ih (fun i ↦ K a ∩ K i)
      (fun i hi ↦ (hK a (Finset.mem_insert_self _ _)).inter
        (hK i (Finset.mem_insert_of_mem hi)))
      (fun i hi T hT hsub ↦ hlocal i (Finset.mem_insert_of_mem hi) T hT
        (hsub.trans Set.inter_subset_right))
    have hInter : (⋃ i ∈ s, K a ∩ K i) = K a ∩ L := by
      exact (Set.inter_iUnion₂ (K a) (fun i (_ : i ∈ s) ↦ K i)).symm
    rw [hInter] at h₃
    have hUnion : (⋃ i ∈ insert a s, K i) = K a ∪ L := by
      exact Finset.set_biUnion_insert a s K
    rw [hUnion, Set.compl_union]
    apply hasRelativeLocalControl_inter R n (K a)ᶜ Lᶜ
      (hK a (Finset.mem_insert_self _ _)).isClosed.isOpen_compl hL.isClosed.isOpen_compl h₁ h₂
    simpa only [Set.compl_inter] using h₃

private theorem hasRelativeLocalControl_compact_manifold
    {M : Type u} [TopologicalSpace M] [T2Space M] (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) : HasRelativeLocalControl R n Kᶜ := by
  -- Shrink a finite open chart cover to compact pieces; no compactness of M is required.
  let U (x : M) := (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hU (x : M) : IsOpen (U x) := (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin n)) x⟩)
  obtain ⟨L, hL, hLU, hcover⟩ := hK.finite_compact_cover s U (fun x _ ↦ hU x) hs
  have hfinite := hasRelativeLocalControl_finiteUnion_compact R n s L (fun x _ ↦ hL x)
    (fun x _ T hT hTL ↦ hasRelativeLocalControl_compact_chart R n
      (chartAt (EuclideanSpace ℝ (Fin n)) x) T hT (hTL.trans (hLU x)))
  rwa [← hcover] at hfinite

/-- Compact-relative homology of a topological manifold vanishes above its dimension. -/
theorem relativeSingularHomology_subsingleton_compact_manifold
    {M : Type u} [TopologicalSpace M] [T2Space M] (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) (hK : IsCompact K) (k : ℕ) (hk : n < k) :
    Subsingleton (relativeSingularHomology R Kᶜ k) :=
  (hasRelativeLocalControl_compact_manifold R n K hK).1 k hk

/-- Top-dimensional compact-relative manifold classes are detected by their local restrictions. -/
theorem relativeSingularHomology_eq_zero_of_point_restrictions
    {M : Type u} [TopologicalSpace M] [T2Space M] (n : ℕ)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set M) (hA : IsCompact Aᶜ) (c : relativeSingularHomology R A n)
    (hc : ∀ (x : M) (hx : x ∉ A), relativeSingularHomologyInclusion R A ({x}ᶜ)
      (fun _y hy h ↦ hx (h ▸ hy)) n c = 0) : c = 0 := by
  have hcontrol : HasRelativeLocalControl R n A := by
    simpa only [compl_compl] using hasRelativeLocalControl_compact_manifold R n Aᶜ hA
  exact hcontrol.2 c hc

end AtiyahSinger
