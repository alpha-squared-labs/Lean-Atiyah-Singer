/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.RelativeKZeroNeighborhood

/-!
# Compact-support K theory on a directed open cover

Public module ID: M1671.

Karoubi II.4.21 identifies compact-support K theory with the direct limit over
an inductive family of open subsets containing every compact set. These two
degree-zero statements give its representation and zero criteria using the
existing one-point compactification groups and actual open-extension maps.
No new colimit object or independently selected group map is introduced.

A nonempty directed open cover contains every compact subset in one member:
take a finite subcover and a common upper bound. The members themselves need
not be relatively compact, and the family need not be countable. Empty bases
are allowed. Open-extension maps are not assumed to be injective.
Sources: Karoubi II.4.21, printed p.91 / PDF p.108; its proof uses II.4.22,
printed pp.91--92 / PDF pp.108--109, on closed neighborhoods of infinity.
The proofs use those closed-neighborhood criteria on the actual compactifications.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  {ι : Type*} [hι : Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)

include hι hdir hcover

open OnePoint in
/-- KA II.4.21: every class is the actual open extension of a class on one cover member. -/
theorem exists_compactSupportKZero_openExtension (a : CompactSupportKZero X) :
    ∃ i : ι, letI := (hU i).locallyCompactSpace
      ∃ b : CompactSupportKZero (U i), compactSupportKZeroOpenExtension (U i) (hU i) b = a := by
  /- Stage 1: regard a as a class relative to infinity in the actual one-point
  compactification. KA II.4.22(a) represents it relative to a closed neighborhood
  S of infinity. Its complement is controlled by one compact window K in X.
  Stage 2: a finite subcover and directedness put K inside one U_i, also when
  K is empty because the index type is nonempty. The quotient X-plus → X-plus/S
  factors through the actual open collapse to U_i-plus. This collapse is a
  surjective closed map, so the factor is continuous.
  Stage 3: pull the original quotient class back along that factor. The same
  factorization and contravariant functoriality identify its open extension
  with a. No compactness of U_i or countable exhaustion is required. -/
  classical
  -- First retain a relative representative on a genuine closed neighborhood of infinity.
  obtain ⟨ap, hap⟩ := relativeKZeroPointToReduced_surjective.{_, 0} (∞ : OnePoint X) a
  obtain ⟨S, hS, hN, b, hb⟩ := exists_relativeKZero_neighborhood (∞ : OnePoint X) ap
  have hforget : relativeKZeroForget S hS b = a.val := by
    calc
      _ = relativeKZeroForget ({∞} : Set (OnePoint X)) isClosed_singleton
          (relativeKZeroNeighborhoodToPoint ∞ S hS hN b) :=
        (DFunLike.congr_fun (relativeKZeroForget_enlarge ({∞} : Set (OnePoint X)) S
          isClosed_singleton hS (singleton_subset_of_mem_nhds ∞ S hN)) b).symm
      _ = a.val := by
        rw [hb]
        exact congrArg Subtype.val hap
  obtain ⟨K, ⟨_, hK⟩, hKS⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hN
  obtain ⟨i, hKi⟩ := hK.elim_directed_cover U hU (by rw [hcover]; exact Set.subset_univ K)
    hdir
  let := (hU i).locallyCompactSpace
  let := PointedQuotient.compactSpace S
  let := PointedQuotient.t2Space S hS
  -- The quotient map is constant on every fiber of the actual open collapse.
  let c : C(OnePoint X, OnePoint (U i)) :=
    ⟨onePointCollapse (U i), continuous_onePointCollapse (U i) (hU i)⟩
  let g : OnePoint (U i) → PointedQuotient S :=
    fun z ↦ z.elim (PointedQuotient.basepoint S)
      (fun x ↦ PointedQuotient.of S (x.val : OnePoint X))
  have hfactor (z : OnePoint X) : g (c z) = PointedQuotient.of S z := by
    cases z using OnePoint.rec with
    | infty =>
      exact ((PointedQuotient.of_eq_basepoint_iff S ∞).2 (mem_of_mem_nhds hN)).symm
    | coe x =>
      by_cases hx : x ∈ U i
      · change g (onePointCollapse (U i) x) = _
        rw [onePointCollapse_coe_of_mem (U i) x hx]
        rfl
      · have hxK : x ∉ K := fun h ↦ hx (hKi h)
        have hxS : (x : OnePoint X) ∈ S := hKS (Or.inl ⟨x, hxK, rfl⟩)
        change g (onePointCollapse (U i) x) = _
        rw [onePointCollapse_coe_of_notMem (U i) x hx]
        exact ((PointedQuotient.of_eq_basepoint_iff S x).2 hxS).symm
  have hsurj : Function.Surjective c := by
    intro z
    cases z using OnePoint.rec with
    | infty => exact ⟨∞, rfl⟩
    | coe x => exact ⟨(x.val : OnePoint X), onePointCollapse_coe_of_mem (U i) x x.property⟩
  have hg : Continuous g :=
    (c.continuous.isClosedMap.isQuotientMap c.continuous hsurj).continuous_iff.mpr
      ((PointedQuotient.continuous_of S).congr (fun z ↦ (hfactor z).symm))
  let G : C(OnePoint (U i), PointedQuotient S) := ⟨g, hg⟩
  let d : CompactSupportKZero (U i) :=
    reducedComplexKZeroPullback ∞ (PointedQuotient.basepoint S) G rfl b
  refine ⟨i, d, ?_⟩
  -- Pullback along the same factorization recovers the original reduced class.
  apply Subtype.ext
  change complexKZeroPullback c (complexKZeroPullback G b.val) = a.val
  have hsquare : G.comp c =
      (⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩ :
        C(OnePoint X, PointedQuotient S)) := ContinuousMap.ext hfactor
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
  exact hforget

open OnePoint in
/-- KA II.4.21: global vanishing is detected after extension to a larger cover member. -/
theorem compactSupportKZeroOpenExtension_eq_zero_iff (i : ι)
    (a : letI := (hU i).locallyCompactSpace; CompactSupportKZero (U i)) :
    letI : ∀ k : ι, LocallyCompactSpace (U k) := fun k ↦ (hU k).locallyCompactSpace
    compactSupportKZeroOpenExtension (U i) (hU i) a = 0 ↔
      ∃ j : ι, ∃ hij : U i ⊆ U j,
        compactSupportKZeroOpenPushforward (Set.inclusion hij)
          (.inclusion hij ((hU i).preimage continuous_subtype_val)) a = 0 := by
  /- Stage 1: choose a compact window inside U_i representing a. Interpret its
  extension as a class relative to a closed neighborhood of infinity in X-plus.
  Global vanishing and KA II.4.22(b) give zero after shrinking that neighborhood.
  In the original lemma, stabilization extends the boundary isomorphism at
  infinity; compactness of the homotopy interval gives one smaller neighborhood
  on which the whole boundary homotopy is invertible. Thus its finite support
  remains inside a single enlarged compact window, not a time-dependent one.
  Stage 2: put this enlarged window in some U_k. Directedness gives U_j containing
  both U_k and the original U_i. The same quotient-factorization square identifies
  the vanishing relative class with the displayed actual inclusion pushforward.
  Stage 3: conversely, compose that same inclusion with U_j into X. The one-point
  collapse formulas identify the composite with open extension from U_i to X,
  so zero at U_j implies global zero. No open-extension map is assumed injective,
  and no assertion is made that a already vanishes at its original stage. -/
  classical
  let : ∀ k : ι, LocallyCompactSpace (U k) := fun k ↦ (hU k).locallyCompactSpace
  let collapse (k : ι) : C(OnePoint X, OnePoint (U k)) :=
    ⟨onePointCollapse (U k), continuous_onePointCollapse (U k) (hU k)⟩
  -- Record the precise collapse underlying each original inclusion pushforward.
  have inclusionCollapse (j : ι) (hij : U i ⊆ U j) :
      ∃ v : C(OnePoint (U j), OnePoint (U i)),
        v.comp (collapse j) = collapse i ∧
        ∀ z : CompactSupportKZero (U i),
          (compactSupportKZeroOpenPushforward (Set.inclusion hij)
            (.inclusion hij ((hU i).preimage continuous_subtype_val)) z).val =
              complexKZeroPullback v z.val := by
    let f : U i → U j := Set.inclusion hij
    have hf : IsOpenEmbedding f :=
      .inclusion hij ((hU i).preimage continuous_subtype_val)
    let := hf.isOpen_range.locallyCompactSpace
    let e := hf.isEmbedding.toHomeomorph
    let inverse : C(Set.range f, U i) := ⟨e.symm, e.symm.continuous⟩
    let c : C(OnePoint (U j), OnePoint (Set.range f)) :=
      ⟨onePointCollapse (Set.range f),
        continuous_onePointCollapse (Set.range f) hf.isOpen_range⟩
    let v := (properOnePointMap inverse e.symm.isProperMap).comp c
    have hfinite (x : U i) : v (f x) = (x : OnePoint (U i)) := by
      change OnePoint.map inverse (onePointCollapse (Set.range f) (f x)) = _
      rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
      exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
    have houtside (x : U j) (hx : (x : X) ∉ U i) : v x = ∞ := by
      have hnot : x ∉ Set.range f := by
        rintro ⟨y, hy⟩
        exact hx ((congrArg Subtype.val hy) ▸ y.property)
      change OnePoint.map inverse (onePointCollapse (Set.range f) x) = ∞
      rw [onePointCollapse_coe_of_notMem (Set.range f) x hnot, OnePoint.map_infty]
    refine ⟨v, ?_, ?_⟩
    · ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe x =>
        change v (onePointCollapse (U j) x) = onePointCollapse (U i) x
        by_cases hxi : x ∈ U i
        · rw [onePointCollapse_coe_of_mem (U j) x (hij hxi),
            onePointCollapse_coe_of_mem (U i) x hxi]
          exact hfinite ⟨x, hxi⟩
        · rw [onePointCollapse_coe_of_notMem (U i) x hxi]
          by_cases hxj : x ∈ U j
          · rw [onePointCollapse_coe_of_mem (U j) x hxj]
            exact houtside ⟨x, hxj⟩ hxi
          · rw [onePointCollapse_coe_of_notMem (U j) x hxj]
            rfl
    · intro z
      change complexKZeroPullback c
        (complexKZeroPullback (properOnePointMap inverse e.symm.isProperMap) z.val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
  constructor
  · intro ha
    -- Represent the original member class relative to its own infinity neighborhood.
    obtain ⟨ap, hap⟩ := relativeKZeroPointToReduced_surjective.{_, 0}
      (∞ : OnePoint (U i)) a
    obtain ⟨S, hS, hN, b, hb⟩ :=
      exists_relativeKZero_neighborhood (∞ : OnePoint (U i)) ap
    have hforget : relativeKZeroForget S hS b = a.val := by
      calc
        _ = relativeKZeroForget ({∞} : Set (OnePoint (U i))) isClosed_singleton
            (relativeKZeroNeighborhoodToPoint ∞ S hS hN b) :=
          (DFunLike.congr_fun (relativeKZeroForget_enlarge
            ({∞} : Set (OnePoint (U i))) S isClosed_singleton hS
            (singleton_subset_of_mem_nhds ∞ S hN)) b).symm
        _ = a.val := by
          rw [hb]
          exact congrArg Subtype.val hap
    let T : Set (OnePoint X) := collapse i ⁻¹' S
    have hT : IsClosed T := hS.preimage (collapse i).continuous
    have hTN : T ∈ 𝓝 (∞ : OnePoint X) :=
      (collapse i).continuous.continuousAt.preimage_mem_nhds hN
    let p : RelativeKZero T hT :=
      relativeKZeroPullback T hT S hS (collapse i) (fun _ hx ↦ hx) b
    have hpforget : relativeKZeroForget T hT p = 0 := by
      have hn := DFunLike.congr_fun
        (relativeKZeroForget_natural T hT S hS (collapse i) (fun _ hx ↦ hx)) b
      change relativeKZeroForget T hT p =
        complexKZeroPullback (collapse i) (relativeKZeroForget S hS b) at hn
      rw [hn, hforget]
      exact congrArg Subtype.val ha
    have hpzero : relativeKZeroNeighborhoodToPoint ∞ T hT hTN p = 0 := by
      apply relativeKZeroPointToReduced_injective ∞
      apply Subtype.ext
      change relativeKZeroForget ({∞} : Set (OnePoint X)) isClosed_singleton
        (relativeKZeroNeighborhoodToPoint ∞ T hT hTN p) = 0
      exact (DFunLike.congr_fun (relativeKZeroForget_enlarge ({∞} : Set (OnePoint X)) T
        isClosed_singleton hT (singleton_subset_of_mem_nhds ∞ T hTN)) p).trans hpforget
    -- Global zero is witnessed on one smaller closed neighborhood, hence one compact window.
    obtain ⟨R, hR, hRN, hRT, hzero⟩ :=
      relativeKZero_neighborhood_eventually_zero ∞ T hT hTN p hpzero
    obtain ⟨K, ⟨_, hK⟩, hKR⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hRN
    obtain ⟨k, hKk⟩ := hK.elim_directed_cover U hU
      (by rw [hcover]; exact Set.subset_univ K) hdir
    obtain ⟨j, hij, hkj⟩ := hdir i k
    have hKj : K ⊆ U j := hKk.trans hkj
    let := PointedQuotient.compactSpace R
    let := PointedQuotient.t2Space R hR
    let := PointedQuotient.compactSpace T
    let := PointedQuotient.t2Space T hT
    let := PointedQuotient.compactSpace S
    let := PointedQuotient.t2Space S hS
    let g : OnePoint (U j) → PointedQuotient R :=
      fun z ↦ z.elim (PointedQuotient.basepoint R)
        (fun x ↦ PointedQuotient.of R (x.val : OnePoint X))
    have hfactor (z : OnePoint X) : g (collapse j z) = PointedQuotient.of R z := by
      cases z using OnePoint.rec with
      | infty =>
        exact ((PointedQuotient.of_eq_basepoint_iff R ∞).2
          (mem_of_mem_nhds hRN)).symm
      | coe x =>
        by_cases hx : x ∈ U j
        · change g (onePointCollapse (U j) x) = _
          rw [onePointCollapse_coe_of_mem (U j) x hx]
          rfl
        · have hxK : x ∉ K := fun h ↦ hx (hKj h)
          have hxR : (x : OnePoint X) ∈ R := hKR (Or.inl ⟨x, hxK, rfl⟩)
          change g (onePointCollapse (U j) x) = _
          rw [onePointCollapse_coe_of_notMem (U j) x hx]
          exact ((PointedQuotient.of_eq_basepoint_iff R x).2 hxR).symm
    have hsurj : Function.Surjective (collapse j) := by
      intro z
      cases z using OnePoint.rec with
      | infty => exact ⟨∞, rfl⟩
      | coe x =>
        exact ⟨(x.val : OnePoint X), onePointCollapse_coe_of_mem (U j) x x.property⟩
    have hg : Continuous g :=
      ((collapse j).continuous.isClosedMap.isQuotientMap
        (collapse j).continuous hsurj).continuous_iff.mpr
          ((PointedQuotient.continuous_of R).congr (fun z ↦ (hfactor z).symm))
    let G : C(OnePoint (U j), PointedQuotient R) := ⟨g, hg⟩
    let F := PointedQuotient.mapContinuous T S (collapse i) (fun _ hx ↦ hx)
    let H := PointedQuotient.mapContinuous R T (ContinuousMap.id (OnePoint X)) hRT
    obtain ⟨v, hv, hvval⟩ := inclusionCollapse j hij
    let q : C(OnePoint (U i), PointedQuotient S) :=
      ⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩
    have hsquare : (F.comp H).comp G = q.comp v := by
      ext z
      obtain ⟨w, rfl⟩ := hsurj z
      change F (H (g (collapse j w))) = PointedQuotient.of S (v (collapse j w))
      rw [hfactor]
      change PointedQuotient.of S (collapse i w) =
        PointedQuotient.of S (v (collapse j w))
      exact congrArg (PointedQuotient.of S) (ContinuousMap.congr_fun hv w).symm
    have hzeroVal : complexKZeroPullback H (complexKZeroPullback F b.val) = 0 :=
      congrArg Subtype.val hzero
    refine ⟨j, hij, ?_⟩
    -- This is the very inclusion pushforward from the original U_i into the chosen U_j.
    apply Subtype.ext
    rw [hvval]
    rw [← hforget]
    change complexKZeroPullback v (complexKZeroPullback q b.val) = 0
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, ← hsquare,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply, complexKZeroPullback_comp,
      AddMonoidHom.comp_apply, hzeroVal, map_zero]
  · rintro ⟨j, hij, hzero⟩
    obtain ⟨v, hv, hvval⟩ := inclusionCollapse j hij
    -- Conversely the same collapse square composes the two specified extensions.
    apply Subtype.ext
    change complexKZeroPullback (collapse i) a.val = 0
    rw [← hv, complexKZeroPullback_comp, AddMonoidHom.comp_apply, ← hvval, hzero]
    exact map_zero _

end AtiyahSinger
