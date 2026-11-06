/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativePointKZero
public import AtiyahSinger.Topology.TripleKZeroComparison

/-!
# Finite-neighborhood statements of Karoubi II.4.22

Public module ID: M2082.

For a point of a compact Hausdorff space, relative classes are represented
on closed neighborhoods, and equality holds after shrinking a neighborhood.
These are the representation and equality criteria underlying the source lemma's
direct-limit isomorphism. No categorical colimit object is defined here.
Sources: Karoubi II.4.21–4.22, printed pp.91–92; II.2.28 and I.5.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle OnePoint
open scoped unitInterval Topology

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

variable {X : Type*} [TopologicalSpace X]


/-- A neighborhood contains the distinguished point. -/
theorem singleton_subset_of_mem_nhds (x : X) (S : Set X) (hS : S ∈ 𝓝 x) : ({x} : Set X) ⊆ S := by
  /- Every neighborhood contains its center. Any point of the singleton equals x, so the
  neighborhood membership of x gives the stated singleton inclusion. -/
  intro y hy
  simpa only [Set.mem_singleton_iff.mp hy] using mem_of_mem_nhds hS

variable [hX : CompactSpace X] [hT : T2Space X]
include hX hT

/-- The actual map from a closed-neighborhood relative group to the point pair. -/
def relativeKZeroNeighborhoodToPoint (x : X) (S : Set X) (hS : IsClosed S)
    (hN : S ∈ 𝓝 x) : RelativeKZero S hS →+ RelativeKZero ({x} : Set X) isClosed_singleton :=
  relativeKZeroEnlarge ({x} : Set X) S isClosed_singleton hS (singleton_subset_of_mem_nhds x S hN)


set_option backward.isDefEq.respectTransparency false in
/-- KA II.4.22(a): a point-relative class is represented on a closed neighborhood. -/
theorem exists_relativeKZero_neighborhood (x : X)
    (a : RelativeKZero ({x} : Set X) isClosed_singleton) :
    ∃ S : Set X, ∃ hS : IsClosed S, ∃ hN : S ∈ 𝓝 x,
      ∃ b : RelativeKZero S hS, relativeKZeroNeighborhoodToPoint x S hS hN b = a := by
  /- Represent a by a geometric triple at the point. The boundary fiber isomorphism extends to
  a neighborhood using local bundle charts. Shrink to a closed neighborhood by compact
  Hausdorff regularity and retain this actual extension there. Naturality of the difference
  construction identifies its point restriction with a. -/
  classical
  have chartIso (E : FiniteBundle X) (r : ℕ)
      (t : Trivialization (Fin r → ℂ) (π Unit E.Fiber))
      (hlin : ∀ y ∈ t.baseSet, IsLinearMap ℂ (fun v : E.Fiber y ↦ (t ⟨y, v⟩).2))
      (W : Set X) (hW : W ⊆ t.baseSet) :
      let := trivialTopology (X := W) (n := r)
      ∃ e : Iso (Restrict E.Fiber W) (Bundle.Trivial W (Fin r → ℂ)),
        ∀ w v, e.linearEquiv w v = (t ⟨w.val, v⟩).2 := by
    let := trivialTopology (X := W) (n := r)
    let f : C(W, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let c (y : X) (hy : y ∈ t.baseSet) : E.Fiber y ≃ₗ[ℂ] (Fin r → ℂ) :=
      { toFun := fun v ↦ (t ⟨y, v⟩).2
        invFun := fun v ↦ cast (congrArg E.Fiber (t.proj_symm_apply' hy))
          (t.toOpenPartialHomeomorph.symm (y, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E.Fiber ↦ z.snd)
            (t.symm_apply_mk_proj (x := ⟨y, v⟩) (t.mem_source.mpr hy))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E.Fiber)
            (t.proj_symm_apply' (x := v) hy) (t.toOpenPartialHomeomorph.symm (y, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E.Fiber ↦ (t z).2) hp).trans
            (congrArg Prod.snd (t.apply_symm_apply' hy))
        map_add' := (hlin y hy).map_add
        map_smul' := (hlin y hy).map_smul }
    have hinv (w : W) (v : Fin r → ℂ) :
        t.toOpenPartialHomeomorph.symm (w.val, v) =
          (⟨w.val, (c w.val (hW w.property)).symm v⟩ : TotalSpace Unit E.Fiber) := by
      exact (TotalSpace.mk_cast (F := Unit) (E := E.Fiber)
        (t.proj_symm_apply' (hW w.property))
        (t.toOpenPartialHomeomorph.symm (w.val, v)).snd).symm
    refine ⟨{ linearEquiv := fun w ↦ c w.val (hW w.property)
              continuous_total := ?_
              continuous_symm := ?_ }, fun _ _ ↦ rfl⟩
    · apply continuous_induced_rng.mpr
      have hbase := Pullback.continuous_proj Unit E.Fiber f
      have hcoords : Continuous (fun z : TotalSpace Unit (Restrict E.Fiber W) ↦
          (t ⟨z.proj.val, z.snd⟩).2) :=
        continuous_snd.comp (t.toOpenPartialHomeomorph.continuousOn.comp_continuous
          (Pullback.continuous_lift Unit E.Fiber f)
          (fun z ↦ t.mem_source.mpr (hW z.proj.property)))
      exact hbase.prodMk hcoords
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber f).continuous_iff]
      have hcoord : Continuous (fun z : TotalSpace Unit (Bundle.Trivial W (Fin r → ℂ)) ↦
          (z.proj, z.snd)) := continuous_induced_dom
      have hback := t.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (((continuous_subtype_val).comp hcoord.fst).prodMk hcoord.snd)
        (fun z ↦ t.mem_target.mpr (hW z.proj.property))
      exact hcoord.fst.prodMk (hback.congr (fun z ↦ hinv z.proj z.snd))
  -- Represent the original point class without replacing either bundle.
  obtain ⟨t, ht⟩ := ComplexBundle.bundleTriple_relativeClass_surjective
    ({x} : Set X) isClosed_singleton a
  obtain ⟨r, e, he, hlinearE⟩ :=
    ComplexBundle.IsFiniteRank.exists_linear_trivialization (E := t.source.Fiber) x
  obtain ⟨s, d, hd, hlinearF⟩ :=
    ComplexBundle.IsFiniteRank.exists_linear_trivialization (E := t.target.Fiber) x
  obtain ⟨S, hSN, hS, hSU⟩ := exists_mem_nhds_isClosed_subset
    (Filter.inter_mem (e.open_baseSet.mem_nhds he) (d.open_baseSet.mem_nhds hd))
  let := ComplexBundle.trivialTopology (X := S) (n := r)
  let := ComplexBundle.trivialTopology (X := S) (n := s)
  obtain ⟨eS, heS⟩ := chartIso t.source r e hlinearE S (fun _ h ↦ (hSU h).1)
  obtain ⟨dS, hdS⟩ := chartIso t.target s d hlinearF S (fun _ h ↦ (hSU h).2)
  let sx : S := ⟨x, mem_of_mem_nhds hSN⟩
  -- Freeze the given fiber isomorphism in these actual source and target charts.
  let c : (Fin r → ℂ) ≃ₗ[ℂ] (Fin s → ℂ) :=
    (eS.linearEquiv sx).symm.trans
      ((t.boundary.linearEquiv ⟨x, Set.mem_singleton x⟩).trans (dS.linearEquiv sx))
  let cS : ComplexBundle.Iso (Bundle.Trivial S (Fin r → ℂ))
      (Bundle.Trivial S (Fin s → ℂ)) :=
    { linearEquiv := fun _ ↦ c
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hc : Continuous (fun z : Bundle.TotalSpace Unit
            (Bundle.Trivial S (Fin r → ℂ)) ↦ (z.proj, z.snd)) := continuous_induced_dom
        exact hc.fst.prodMk (c.toContinuousLinearEquiv.continuous.comp hc.snd)
      continuous_symm := by
        apply continuous_induced_rng.mpr
        have hc : Continuous (fun z : Bundle.TotalSpace Unit
            (Bundle.Trivial S (Fin s → ℂ)) ↦ (z.proj, z.snd)) := continuous_induced_dom
        exact hc.fst.prodMk (c.toContinuousLinearEquiv.symm.continuous.comp hc.snd) }
  let b := ComplexBundle.BundleTriple.ofBoundary t.source t.target
    (eS.trans (cS.trans dS.symm))
  have hpoint (v : t.source.Fiber x) :
      b.boundary.linearEquiv sx v = t.boundary.linearEquiv ⟨x, Set.mem_singleton x⟩ v := by
    change (dS.linearEquiv sx).symm
      (dS.linearEquiv sx (t.boundary.linearEquiv ⟨x, Set.mem_singleton x⟩
        ((eS.linearEquiv sx).symm (eS.linearEquiv sx v)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hboundary : b.boundary.restrict (singleton_subset_of_mem_nhds x S hSN) =
      t.boundary := by
    apply Iso.ext
    intro y
    have hy : y = ⟨x, Set.mem_singleton x⟩ :=
      Subtype.ext (Set.mem_singleton_iff.mp y.property)
    subst y
    apply LinearEquiv.ext
    intro v
    exact (Iso.restrictTo_apply b.boundary
      (singleton_subset_of_mem_nhds x S hSN) ⟨x, Set.mem_singleton x⟩ v).trans (hpoint v)
  let bp := BundleTriple.ofBoundary t.source t.target
    (b.boundary.restrict (singleton_subset_of_mem_nhds x S hSN))
  have hbp : bp = t := by
    change BundleTriple.ofBoundary t.source t.target
      (b.boundary.restrict (singleton_subset_of_mem_nhds x S hSN)) = t
    rw [hboundary]
  refine ⟨S, hS, hSN, b.relativeClass hS, ?_⟩
  -- For the singleton pair only, forgetting is injective by its actual quotient homeomorphism.
  apply relativeKZeroPointToReduced_injective x
  apply Subtype.ext
  change relativeKZeroForget ({x} : Set X) isClosed_singleton
    (relativeKZeroEnlarge ({x} : Set X) S isClosed_singleton hS
      (singleton_subset_of_mem_nhds x S hSN) (b.relativeClass hS)) =
        relativeKZeroForget ({x} : Set X) isClosed_singleton a
  rw [← ht, ← hbp]
  have hforget := DFunLike.congr_fun
    (relativeKZeroForget_enlarge ({x} : Set X) S isClosed_singleton hS
      (singleton_subset_of_mem_nhds x S hSN)) (b.relativeClass hS)
  change relativeKZeroForget ({x} : Set X) isClosed_singleton
    (relativeKZeroEnlarge ({x} : Set X) S isClosed_singleton hS
      (singleton_subset_of_mem_nhds x S hSN) (b.relativeClass hS)) = _ at hforget
  rw [hforget, ComplexBundle.BundleTriple.relativeClass_forget,
    ComplexBundle.BundleTriple.relativeClass_forget]
  rfl

set_option maxHeartbeats 3000000 in

set_option backward.isDefEq.respectTransparency false in

set_option linter.unusedVariables false in
/-- KA II.4.22(b): a class vanishing at the point vanishes on a smaller neighborhood. -/
theorem relativeKZero_neighborhood_eventually_zero (x : X) (S : Set X) (hS : IsClosed S)
    (hN : S ∈ 𝓝 x) (a : RelativeKZero S hS)
    (ha : relativeKZeroNeighborhoodToPoint x S hS hN a = 0) :
    ∃ T : Set X, ∃ hT : IsClosed T, ∃ hTN : T ∈ 𝓝 x, ∃ hTS : T ⊆ S,
      relativeKZeroEnlarge T S hT hS hTS a = 0 := by
  /- Use the triple zero criterion at the point to stabilize the boundary to a global
  isomorphism. On S, linearly interpolate between that isomorphism and the original
  stabilized boundary map. At the distinguished point the path stays invertible. Compactness
  of the time interval gives one smaller closed neighborhood where all its values are
  invertible. Boundary homotopy there makes the class zero. -/
  classical
  have changePair {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hBA : B ⊆ A)
      (a : BundleTriple A) :
      (BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)).relativeClass hB =
        relativeKZeroEnlarge B A hB hA hBA (a.relativeClass hA) := by
    let b := BundleTriple.ofBoundary a.source a.target (a.boundary.restrict hBA)
    let := DoubleSpace.t2Space A hA
    let := DoubleSpace.t2Space B hB
    let Wa := clutchingBundle hA a
    let d := DoubleSpace.mapContinuous B A (ContinuousMap.id X) hBA
    let W := Wa.pullback d
    -- The two original charts pull back along the identity on each copy of X.
    let eL : Iso ((DoubleSpace.leftMap B : X → DoubleSpace B) *ᵖ W.Fiber) a.source.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).trans
        (clutchingLeftIso hA a)
    let eR : Iso ((DoubleSpace.rightMap B : X → DoubleSpace B) *ᵖ W.Fiber) a.target.Fiber :=
      (pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).trans
        (clutchingRightIso hA a)
    have heL (x : X) (v : Wa.Fiber (DoubleSpace.left A x)) :
        eL.linearEquiv x v = (clutchingLeftIso hA a).linearEquiv x v := by
      change (clutchingLeftIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.leftMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have heR (x : X) (v : Wa.Fiber (DoubleSpace.right A x)) :
        eR.linearEquiv x v = (clutchingRightIso hA a).linearEquiv x v := by
      change (clutchingRightIso hA a).linearEquiv x
        ((pullbackCompIso (E := Wa.Fiber) d (DoubleSpace.rightMap B)).linearEquiv x v) = _
      rw [pullbackCompIso_apply]
    have hinv (x : X) (v : a.source.Fiber x) :
        (eL.linearEquiv x).symm v = ((clutchingLeftIso hA a).linearEquiv x).symm v := by
      apply (eL.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, heL, LinearEquiv.apply_symm_apply]
    have hseam : ClutchingCompatible b W eL eR := by
      intro x v
      change eR.linearEquiv x
        (cast (congrArg W.Fiber (DoubleSpace.left_eq_right B x))
          ((eL.linearEquiv x).symm v)) = (a.boundary.restrict hBA).linearEquiv x v
      rw [heR, hinv]
      exact (clutching_seam_apply hA a ⟨x, hBA x.property⟩ v).trans
        (Iso.restrictTo_apply a.boundary hBA x v).symm
    obtain ⟨e⟩ := nonempty_clutching_iso hB b W eL eR hseam
    let := W.isFiniteRank
    let := (clutchingBundle hB b).isFiniteRank
    have hglued := kZeroClass_eq_of_iso e.symm
    change (clutchingBundle hB b).kZeroClass = (Wa.pullback d).kZeroClass at hglued
    rw [FiniteBundle.kZeroClass_pullback] at hglued
    -- Both sides subtract the pullback of the same target bundle along projection.
    have hproj : (DoubleSpace.projMap A).comp d = DoubleSpace.projMap B := by
      ext z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    have hprojection : complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
        complexKZeroPullback d
          (complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass) := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp d (DoubleSpace.projMap A)) a.target.kZeroClass
      rw [hproj] at h
      exact h
    have hdouble : b.doubleDifference hB = complexKZeroPullback d (a.doubleDifference hA) := by
      change (clutchingBundle hB b).kZeroClass -
        complexKZeroPullback (DoubleSpace.projMap B) a.target.kZeroClass =
          complexKZeroPullback d
            (Wa.kZeroClass - complexKZeroPullback (DoubleSpace.projMap A) a.target.kZeroClass)
      rw [map_sub, hglued, hprojection]
    let RA := DoubleSpace.rightRange A
    let RB := DoubleSpace.rightRange B
    have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
    have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
    have hd : Set.MapsTo d RB RA := by
      rintro z ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    let dPull := relativeKZeroPullback RB hRB RA hRA d hd
    -- Forgetting is used injectively only on the retracting source double.
    have hlift : b.differenceLift hB = dPull (a.differenceLift hA) := by
      apply relativeKZeroForget_injective_of_retraction RB hRB
        (DoubleSpace.rightRetraction B) (DoubleSpace.rightRetraction_apply B)
      have hn := relativeKZeroForget_natural RB hRB RA hRA d hd
      calc
        _ = b.doubleDifference hB := b.forget_differenceLift hB
        _ = complexKZeroPullback d (a.doubleDifference hA) := hdouble
        _ = complexKZeroPullback d
            (relativeKZeroForget RA hRA (a.differenceLift hA)) := by
          rw [a.forget_differenceLift hA]
        _ = _ := (DFunLike.congr_fun hn (a.differenceLift hA)).symm
    have hrestriction : (DoubleSpace.relativeRestriction B hB).comp dPull =
        (relativeKZeroEnlarge B A hB hA hBA).comp
          (DoubleSpace.relativeRestriction A hA) := by
      change (relativeKZeroPullback B hB RB hRB (DoubleSpace.leftMap B)
        (DoubleSpace.left_mapsTo B)).comp (relativeKZeroPullback RB hRB RA hRA d hd) =
          (relativeKZeroPullback B hB A hA (ContinuousMap.id X) hBA).comp
            (relativeKZeroPullback A hA RA hRA (DoubleSpace.leftMap A)
              (DoubleSpace.left_mapsTo A))
      have hleft := relativeKZeroPullback_comp B hB RB hRB RA hRA
        (DoubleSpace.leftMap B) d (DoubleSpace.left_mapsTo B) hd
      have hright := relativeKZeroPullback_comp B hB A hA RA hRA
        (ContinuousMap.id X) (DoubleSpace.leftMap A) hBA (DoubleSpace.left_mapsTo A)
      rw [← hleft, ← hright]
      congr 1
    change DoubleSpace.relativeRestriction B hB (b.differenceLift hB) =
      relativeKZeroEnlarge B A hB hA hBA
        (DoubleSpace.relativeRestriction A hA (a.differenceLift hA))
    rw [hlift]
    exact DFunLike.congr_fun hrestriction (a.differenceLift hA)
  have nearIdentity (x : X) (S : Set X) (hN : S ∈ 𝓝 x) (n : ℕ)
      (C : Iso (Bundle.Trivial S (Fin n → ℂ)) (Bundle.Trivial S (Fin n → ℂ)))
      (hC : ∀ v, C.linearEquiv ⟨x, mem_of_mem_nhds hN⟩ v = v) :
      ∃ T : Set X, ∃ hT : IsClosed T, ∃ hTN : T ∈ 𝓝 x, ∃ hTS : T ⊆ S,
        letI := trivialTopology (X := I × T) (n := n)
        ∃ H : Iso (Bundle.Trivial (I × T) (Fin n → ℂ))
            (Bundle.Trivial (I × T) (Fin n → ℂ)),
          (∀ y v, H.linearEquiv (0, y) v = v) ∧
            (∀ y v, H.linearEquiv (1, y) v =
              C.linearEquiv ⟨y.val, hTS y.property⟩ v) := by
    classical
    let := trivialTopology (X := S) (n := n)
    let sx : S := ⟨x, mem_of_mem_nhds hN⟩
    let A (y : S) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
      (C.linearEquiv y).toContinuousLinearEquiv.toContinuousLinearMap
    have hA : Continuous A := by
      apply continuous_clm_apply.mpr
      intro v
      have hin : Continuous (fun y : S ↦
          (⟨y, v⟩ : TotalSpace Unit (Bundle.Trivial S (Fin n → ℂ)))) :=
        continuous_induced_rng.mpr (continuous_id.prodMk continuous_const)
      have hout : Continuous (fun z : TotalSpace Unit (Bundle.Trivial S (Fin n → ℂ)) ↦
          (z.proj, z.snd)) := continuous_induced_dom
      exact hout.snd.comp (C.continuous_total.comp hin)
    have hAx : A sx = 1 := by
      apply ContinuousLinearMap.ext
      intro v
      exact hC v
    let P (z : I × S) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
      1 + ((z.1 : ℝ) : ℂ) • (A z.2 - 1)
    have hP : Continuous P :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).smul
          ((hA.comp continuous_snd).sub continuous_const))
    let U : Set (I × S) := {z | (P z).IsInvertible}
    have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hP
    have hxU : Set.univ ×ˢ ({sx} : Set S) ⊆ U := by
      rintro ⟨t, y⟩ ⟨_, hy⟩
      rcases Set.mem_singleton_iff.mp hy with rfl
      have h : P (t, sx) = 1 := by simp [P, hAx]
      rw [show (t, sx) ∈ U ↔ (P (t, sx)).IsInvertible from Iff.rfl, h]
      exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ _)
    obtain ⟨J, V, _, hV, hJ, hxV, hJV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton hU hxU
    obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype S sx V).mp
      (hV.mem_nhds (hxV (Set.mem_singleton sx)))
    obtain ⟨T, hTN, hT, hTW⟩ := exists_mem_nhds_isClosed_subset (Filter.inter_mem hW hN)
    have hTS : T ⊆ S := fun y hy ↦ (hTW hy).2
    let k : I × T → I × S := fun z ↦ (z.1, ⟨z.2.val, hTS z.2.property⟩)
    have hk : Continuous k :=
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    have hPk (z : I × T) : (P (k z)).IsInvertible :=
      hJV ⟨hJ (Set.mem_univ z.1), hWV (hTW z.2.property).1⟩
    let := trivialTopology (X := I × T) (n := n)
    let := isFiniteRank_trivial (X := I × T) (n := n)
    let F : Hom (Bundle.Trivial (I × T) (Fin n → ℂ))
        (Bundle.Trivial (I × T) (Fin n → ℂ)) :=
      { linearMap := fun z ↦ (P (k z)).toLinearMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          have hc : Continuous (fun z : TotalSpace Unit
              (Bundle.Trivial (I × T) (Fin n → ℂ)) ↦ (z.proj, z.snd)) :=
            continuous_induced_dom
          exact hc.fst.prodMk (((hP.comp hk).comp hc.fst).clm_apply hc.snd) }
    have hb (z : I × T) : Function.Bijective (F.linearMap z) := by
      obtain ⟨e, he⟩ := hPk z
      change Function.Bijective (P (k z))
      rw [← he]
      exact e.bijective
    refine ⟨T, hT, hTN, hTS, F.toIso hb, ?_, ?_⟩
    · intro y v
      change (P (k (0, y))) v = v
      simp [P, k]
    · intro y v
      change (P (k (1, y))) v = C.linearEquiv ⟨y.val, hTS y.property⟩ v
      simp [P, k, A]
  -- Represent a on its original closed pair, then use the actual singleton restriction.
  obtain ⟨b, hb⟩ := bundleTriple_relativeClass_surjective S hS a
  have hxS : x ∈ S := mem_of_mem_nhds hN
  have hp : ({x} : Set X) ⊆ S := singleton_subset_of_mem_nhds x S hN
  let bp := BundleTriple.ofBoundary b.source b.target (b.boundary.restrict hp)
  have hbpzero : bp.relativeClass isClosed_singleton = 0 := by
    rw [changePair hS isClosed_singleton hp b, hb]
    exact ha
  obtain ⟨G, e, he⟩ := (bp.relativeClass_eq_zero_iff isClosed_singleton).mp hbpzero
  let b₀ := b.sum (BundleTriple.identity S G)
  have hepoint (v : b₀.source.Fiber x) :
      e.linearEquiv x v = b₀.boundary.linearEquiv ⟨x, hxS⟩ v := by
    have hv := congrArg (fun q : RelativeTriple b₀.source.Fiber b₀.target.Fiber
      ({x} : Set X) ↦ q.linearEquiv ⟨x, Set.mem_singleton x⟩ v) he
    change e.linearEquiv x v =
      (RelativeTriple.sum (b.boundary.restrict hp)
        (RelativeTriple.identity G.Fiber ({x} : Set X))).linearEquiv
          ⟨x, Set.mem_singleton x⟩ v at hv
    rw [RelativeTriple.sum_apply] at hv
    change e.linearEquiv x v =
      ((b.boundary.restrict hp).linearEquiv ⟨x, Set.mem_singleton x⟩ v.1, v.2) at hv
    calc
      e.linearEquiv x v =
          ((b.boundary.restrict hp).linearEquiv ⟨x, Set.mem_singleton x⟩ v.1, v.2) := hv
      _ = (b.boundary.linearEquiv ⟨x, hxS⟩ v.1, v.2) :=
        congrArg (fun w ↦ (w, v.2))
          (Iso.restrictTo_apply b.boundary hp ⟨x, Set.mem_singleton x⟩ v.1)
      _ = b₀.boundary.linearEquiv ⟨x, hxS⟩ v :=
        (RelativeTriple.sum_apply b.boundary
          (RelativeTriple.identity G.Fiber S) ⟨x, hxS⟩ v).symm
  -- Add a genuine finite complement on compact X, keeping the same global extension e.
  let p := idempotentPresentation (E := b₀.source.Fiber)
  let D := FiniteBundle.ofFamily (fun y : X ↦ p.complement.fiber y)
  let c := b₀.sum (BundleTriple.identity S D)
  let g : Iso c.source.Fiber c.target.Fiber := e.sum (Iso.refl D.Fiber)
  obtain ⟨u⟩ := nonempty_presentation_complement_iso (E := b₀.source.Fiber)
  have hgpoint (v : c.source.Fiber x) :
      g.linearEquiv x v = c.boundary.linearEquiv ⟨x, hxS⟩ v := by
    calc
      g.linearEquiv x v = (e.linearEquiv x v.1, v.2) := rfl
      _ = (b₀.boundary.linearEquiv ⟨x, hxS⟩ v.1, v.2) :=
        congrArg (fun w ↦ (w, v.2)) (hepoint v.1)
      _ = c.boundary.linearEquiv ⟨x, hxS⟩ v :=
        (RelativeTriple.sum_apply b₀.boundary
          (RelativeTriple.identity D.Fiber S) ⟨x, hxS⟩ v).symm
  let iS : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let uS : Iso (Restrict c.source.Fiber S) (Bundle.Trivial S (Fin p.size → ℂ)) :=
    (u.restrict S).trans (pullbackTrivialIso iS p.size)
  let vS : Iso (Restrict c.target.Fiber S) (Bundle.Trivial S (Fin p.size → ℂ)) :=
    ((g.restrict S).symm.trans (u.restrict S)).trans (pullbackTrivialIso iS p.size)
  have huS (y : S) (v : c.source.Fiber y.val) :
      uS.linearEquiv y v = u.linearEquiv y.val v :=
    pullbackTrivialIso_apply iS p.size y (u.linearEquiv y.val v)
  have hvS (y : S) (v : c.target.Fiber y.val) :
      vS.linearEquiv y v = u.linearEquiv y.val ((g.linearEquiv y.val).symm v) :=
    pullbackTrivialIso_apply iS p.size y (u.linearEquiv y.val ((g.linearEquiv y.val).symm v))
  have huSi (y : S) (v : Fin p.size → ℂ) :
      (uS.linearEquiv y).symm v = (u.linearEquiv y.val).symm v := by
    apply (uS.linearEquiv y).injective
    rw [LinearEquiv.apply_symm_apply, huS, LinearEquiv.apply_symm_apply]
  let C := uS.symm.trans (c.boundary.trans vS)
  have hC (y : S) (v : Fin p.size → ℂ) :
      C.linearEquiv y v = u.linearEquiv y.val
        ((g.linearEquiv y.val).symm
          (c.boundary.linearEquiv y ((u.linearEquiv y.val).symm v))) := by
    change vS.linearEquiv y (c.boundary.linearEquiv y ((uS.linearEquiv y).symm v)) = _
    rw [hvS, huSi]
  have hCx (v : Fin p.size → ℂ) :
      C.linearEquiv ⟨x, mem_of_mem_nhds hN⟩ v = v := by
    rw [hC, ← hgpoint, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  -- The normalized path is identity at x; compactness of I supplies one closed neighborhood.
  obtain ⟨T, hT, hTN, hTS, H, hH₀, hH₁⟩ := nearIdentity x S hN p.size C hCx
  let iT : C(T, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let tMap : C(I × T, T) := ⟨Prod.snd, continuous_snd⟩
  let uT : Iso (Restrict c.source.Fiber T) (Bundle.Trivial T (Fin p.size → ℂ)) :=
    (u.restrict T).trans (pullbackTrivialIso iT p.size)
  let vT : Iso (Restrict c.target.Fiber T) (Bundle.Trivial T (Fin p.size → ℂ)) :=
    ((g.restrict T).symm.trans (u.restrict T)).trans (pullbackTrivialIso iT p.size)
  let uI := (uT.pullback tMap).trans (pullbackTrivialIso tMap p.size)
  let vI := (vT.pullback tMap).trans (pullbackTrivialIso tMap p.size)
  have huI (z : I × T) (v : c.source.Fiber z.2.val) :
      uI.linearEquiv z v = u.linearEquiv z.2.val v := by
    change (pullbackTrivialIso tMap p.size).linearEquiv z
      ((pullbackTrivialIso iT p.size).linearEquiv z.2 (u.linearEquiv z.2.val v)) = _
    rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
  have hvI (z : I × T) (v : c.target.Fiber z.2.val) :
      vI.linearEquiv z v = u.linearEquiv z.2.val ((g.linearEquiv z.2.val).symm v) := by
    change (pullbackTrivialIso tMap p.size).linearEquiv z
      ((pullbackTrivialIso iT p.size).linearEquiv z.2
        (u.linearEquiv z.2.val ((g.linearEquiv z.2.val).symm v))) = _
    rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
  have hvIi (z : I × T) (v : Fin p.size → ℂ) :
      (vI.linearEquiv z).symm v =
        g.linearEquiv z.2.val ((u.linearEquiv z.2.val).symm v) := by
    apply (vI.linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, hvI, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  -- Transfer the same coordinate interpolation to the original two cylinder pullbacks.
  let K : IsoHomotopy (g.restrict T) (c.boundary.restrict hTS) :=
    { iso := uI.trans (H.trans vI.symm)
      map_zero := by
        intro y v
        change (vI.linearEquiv (0, y)).symm
          (H.linearEquiv (0, y) (uI.linearEquiv (0, y) v)) = _
        rw [hH₀, huI, hvIi, LinearEquiv.symm_apply_apply]
        rfl
      map_one := by
        intro y v
        change (vI.linearEquiv (1, y)).symm
          (H.linearEquiv (1, y) (uI.linearEquiv (1, y) v)) = _
        rw [hH₁, huI, hC, hvIi, LinearEquiv.symm_apply_apply,
          LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
        exact (Iso.restrictTo_apply c.boundary hTS y v).symm }
  let d := BundleTriple.ofBoundary c.source c.target (g.restrict T)
  have hd : d.IsIsomorphic (BundleTriple.identity T c.source) := by
    refine ⟨Iso.refl c.source.Fiber, g.symm, ?_⟩
    intro y v
    exact (g.linearEquiv y.val).symm_apply_apply v
  have hd0 : d.relativeClass hT = 0 :=
    (d.relativeClass_eq_of_isIsomorphic hT _ hd).trans
      (BundleTriple.relativeClass_identity hT c.source)
  have hc0 : (BundleTriple.ofBoundary c.source c.target
      (c.boundary.restrict hTS)).relativeClass hT = 0 :=
    (bundleTriple_relativeClass_eq_of_homotopy hT c.source c.target
      (g.restrict T) (c.boundary.restrict hTS) K).symm.trans hd0
  -- Descend through the actual double comparison; no injectivity is assumed on (X,T).
  rw [changePair hS hT hTS c] at hc0
  refine ⟨T, hT, hTN, hTS, ?_⟩
  simpa only [c, b₀, BundleTriple.relativeClass_sum,
    BundleTriple.relativeClass_identity, add_zero, hb] using hc0


set_option linter.unusedVariables false in
/-- Equality at the point is equality after restriction to a smaller closed neighborhood. -/
theorem relativeKZero_neighborhood_eventually_eq (x : X) (S : Set X) (hS : IsClosed S)
    (hN : S ∈ 𝓝 x) (a b : RelativeKZero S hS)
    (h : relativeKZeroNeighborhoodToPoint x S hS hN a =
      relativeKZeroNeighborhoodToPoint x S hS hN b) :
    ∃ T : Set X, ∃ hT : IsClosed T, ∃ hTN : T ∈ 𝓝 x, ∃ hTS : T ⊆ S,
      relativeKZeroEnlarge T S hT hS hTS a = relativeKZeroEnlarge T S hT hS hTS b := by
  /- Apply the eventual-zero statement to a minus b. The neighborhood map and the shrinking map
  are additive, so equality at the point is zero of the difference, and zero after shrinking
  is the asserted equality of the two restricted classes. -/
  have hzero : relativeKZeroNeighborhoodToPoint x S hS hN (a - b) = 0 := by
    rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hTN, hTS, heq⟩ :=
    relativeKZero_neighborhood_eventually_zero x S hS hN (a - b) hzero
  refine ⟨T, hT, hTN, hTS, ?_⟩
  exact sub_eq_zero.mp ((map_sub (relativeKZeroEnlarge T S hT hS hTS) a b).symm.trans heq)

end AtiyahSinger
