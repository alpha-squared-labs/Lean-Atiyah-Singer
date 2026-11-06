/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality

/-!
# Proper fiber maps and associated support descent

Public module ID: M1551.

The existing quotient map [p,x] mapped to [p,f(x)] is proper when the supplied
equivariant fiber map f is proper. Original principal charts identify it with
identity times f; no compactness or separation of the principal base is needed.
The original support-class descent then commutes with these actual proper maps.

Sources: HU IV.5--7 for the associated local products; SG I.9 and III.13,
KA II.2.33 and II.4.1--4.2 for bundle pullback and compact-support contravariance.
The explicit local properness and original-triple comparison are supplementary
arguments. Compact Hausdorff B and LCH fiber spaces enter only the existing
K-theory model. No compact G, global frames, or proper bundle projections are
assumed. The proofs below establish properness and the original compact-support
class and homomorphism comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- A proper equivariant fiber map induces a proper map of the original associated quotients. -/
theorem isProperMap_associatedBundleMap (hP : IsPrincipalBundle G projection)
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hf : IsProperMap f) : IsProperMap (associatedBundleMap (P := P) f heq) := by
  /- Use the ultrafilter criterion in one common principal chart. The original
  associated quotient map has fiber coordinate f in those charts. Properness
  supplies a limit for that coordinate, and the original inverse chart returns
  a limit in the source quotient. No separation or compactness is used. -/
  classical
  let a := associatedBundleMap (P := P) f heq
  let qX := associatedBundleProjection (F := X) hP
  let qY := associatedBundleProjection (F := Y) hP
  have hproj (z : AssociatedBundle G P X) : qY (a z) = qX z := by
    induction z using Quotient.inductionOn with
    | h w => rfl
  apply isProperMap_iff_ultrafilter.mpr
  refine ⟨a.continuous, ?_⟩
  intro U z hz
  -- The same principal chart controls both original associated quotients.
  let b := qY z
  obtain ⟨e, hb, he⟩ := hP.exists_trivialization b
  obtain ⟨eX, hXbase, hXcoord, hXinv⟩ :=
    exists_associatedBundleTrivialization (F := X) hP e he
  obtain ⟨eY, hYbase, hYcoord, hYinv⟩ :=
    exists_associatedBundleTrivialization (F := Y) hP e he
  have hzsource : z ∈ eY.source := eY.mem_source.mpr (hYbase.symm ▸ hb)
  have hbase : Filter.Tendsto qX U (nhds b) :=
    ((qY.continuous.tendsto z).comp hz).congr hproj
  have hevent : ∀ᶠ w in U, qX w ∈ e.baseSet := hbase (e.open_baseSet.mem_nhds hb)
  have hcoord (w : AssociatedBundle G P X) (hw : qX w ∈ e.baseSet) :
      f (eX w).2 = (eY (a w)).2 := by
    induction w using Quotient.inductionOn with
    | h w =>
      change projection w.1 ∈ e.baseSet at hw
      change f (eX (associatedBundleMk G P X w.1 w.2)).2 =
        (eY (associatedBundleMk G P Y w.1 (f w.2))).2
      rw [hXcoord w.1 w.2 hw, hYcoord w.1 (f w.2) hw]
      exact heq (e w.1).2 w.2
  -- The image fiber coordinate converges; properness of f lifts this exact ultrafilter.
  have hfiber : Filter.Tendsto (fun w : AssociatedBundle G P X ↦ f (eX w).2)
      U (nhds (eY z).2) := by
    have ht := Filter.Tendsto.comp (continuous_snd.tendsto (eY z))
      (Filter.Tendsto.comp (eY.toOpenPartialHomeomorph.continuousAt hzsource) hz)
    apply ht.congr'
    exact hevent.mono (fun w hw ↦ (hcoord w hw).symm)
  have hmapped : Filter.Tendsto f (Ultrafilter.map (fun w ↦ (eX w).2) U)
      (nhds (eY z).2) := by
    simpa only [Ultrafilter.coe_map, Filter.tendsto_map'_iff, Function.comp_def]
      using hfiber
  obtain ⟨x, hx, hxlimit⟩ := hf.ultrafilter_le_nhds_of_tendsto hmapped
  have hxlim : Filter.Tendsto (fun w : AssociatedBundle G P X ↦ (eX w).2)
      U (nhds x) := hxlimit
  have hfirst : Filter.Tendsto (fun w : AssociatedBundle G P X ↦ (eX w).1)
      U (nhds b) := by
    apply hbase.congr'
    exact hevent.mono (fun w hw ↦ (eX.coe_fst
      (eX.mem_source.mpr (hXbase.symm ▸ hw))).symm)
  let w := eX.toOpenPartialHomeomorph.symm (b, x)
  have htarget : (b, x) ∈ eX.target := eX.mem_target.mpr (hXbase.symm ▸ hb)
  refine ⟨w, ?_, ?_⟩
  · -- The inverse chart uses the same principal section, hence preserves the original quotient map.
    change a (eX.toOpenPartialHomeomorph.symm (b, x)) = z
    rw [hXinv b x hb]
    change associatedBundleMk G P Y (e.toOpenPartialHomeomorph.symm (b, 1)) (f x) = z
    rw [hx, ← hYinv b (eY z).2 hb]
    have hfst : (eY z).1 = b := eY.coe_fst hzsource
    have hpair : (b, (eY z).2) = eY z := Prod.ext hfst.symm rfl
    rw [hpair]
    exact eY.toOpenPartialHomeomorph.left_inv hzsource
  · -- Return through the continuous inverse chart, which agrees with identity eventually.
    have hinv := Filter.Tendsto.comp
      (eX.toOpenPartialHomeomorph.continuousAt_symm htarget) (hfirst.prodMk_nhds hxlim)
    change Filter.Tendsto id U (nhds w)
    apply hinv.congr'
    exact hevent.mono (fun v hv ↦ eX.toOpenPartialHomeomorph.left_inv
      (eX.mem_source.mpr (hXbase.symm ▸ hv)))

variable [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- The class of the actual descended pullback is the proper pullback of the original class. -/
theorem associatedSupportClass_pullback (hP : IsPrincipalBundle G projection)
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hf : IsProperMap f) (a : EquivariantSupportBundleTriple G Y) :
    letI := associatedBundle_t2Space (Y := X) hP
    letI := associatedBundle_locallyCompactSpace (Y := X) hP
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    associatedSupportClass hP (a.pullback f heq hf) =
      compactSupportKZeroPullback (associatedBundleMap (P := P) f heq)
        (isProperMap_associatedBundleMap hP f heq hf) (associatedSupportClass hP a) := by
  /- Stage 1: the comparison from the associated pulled family over [p,x]
  to the pulled associated family sends [p,(x,v)] to [p,(f(x),v)]. The same
  heq as in the original pulled action supplies its moving-fiber transport.
  Quotient representatives prove well-definedness and linear bijectivity;
  original principal and finite vector charts prove continuity both ways.
  Stage 2: associatedControl(f inverse K) is exactly the inverse image of
  associatedControl K under the specified associatedBundleMap. Check this
  on [p,x] with the original invariant-control membership theorem. Both
  triples therefore use the same compact control, with compactness certified
  by the stated proper maps. Their exterior square sends each original v
  to the same original boundary value at f(x), including its inverse.
  Stage 3: use these global bundle isomorphisms and the existing small-model
  comparisons to identify the actual support classes. Apply the original
  CompactSupportTriple.compactSupportClass_pullback for this very map.
  No free-action K equivalence or replacement support representative is used. -/
  classical
  let := associatedBundle_t2Space (Y := X) hP
  let := associatedBundle_locallyCompactSpace (Y := X) hP
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let q := associatedBundleMap (P := P) f heq
  -- The comparison uses the original pulled action and its same base equality heq.
  have comparison (E : Y → Type)
      [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
      [TopologicalSpace (Bundle.TotalSpace Unit E)] [IsFiniteRank E]
      (σ : EquivariantStructure G E) :
      letI := isFiniteRank_pullback (E := E) f
      letI := associatedEquivariantFiberAddCommGroup hP σ
      letI := associatedEquivariantFiberModule hP σ
      letI := associatedEquivariantTotalTopology hP σ
      letI := associatedEquivariantFiberAddCommGroup hP (σ.pullback f heq)
      letI := associatedEquivariantFiberModule hP (σ.pullback f heq)
      letI := associatedEquivariantTotalTopology hP (σ.pullback f heq)
      ∃ u : Iso (AssociatedEquivariantFiber hP (σ.pullback f heq))
          ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
            (AssociatedEquivariantFiber hP σ)),
        ∀ (p : P) (x : X) {z : AssociatedBundle G P X}
          (hz : associatedBundleMk G P X p x = z) (v : E (f x)),
          u.linearEquiv z
              (associatedEquivariantFiberMk hP (σ.pullback f heq) p x hz v) =
            associatedEquivariantFiberMk hP σ p (f x) (congrArg q hz) v := by
    let := isFiniteRank_pullback (E := E) f
    let := associatedEquivariantFiberAddCommGroup hP σ
    let := associatedEquivariantFiberModule hP σ
    let := associatedEquivariantTotalTopology hP σ
    let := associatedEquivariantFiberAddCommGroup hP (σ.pullback f heq)
    let := associatedEquivariantFiberModule hP (σ.pullback f heq)
    let := associatedEquivariantTotalTopology hP (σ.pullback f heq)
    let := isFiniteRank_associatedEquivariant hP σ
    let := isFiniteRank_associatedEquivariant hP (σ.pullback f heq)
    let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP σ) q
    let ρ := σ.pullback f heq
    let : MulAction G (Bundle.TotalSpace Unit E) := σ.toMulAction
    let : MulAction G (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) := ρ.toMulAction
    let : ContinuousSMul G (Bundle.TotalSpace Unit E) := ⟨σ.continuous_action⟩
    let : ContinuousSMul G (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) :=
      ⟨ρ.continuous_action⟩
    have htotal (g : G) (w : Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) :
        Bundle.Pullback.lift f (g • w) = g • Bundle.Pullback.lift f w := by
      have hcast (a b : Y) (hab : a = b) (L : E (f w.proj) →ₗ[ℂ] E b) :
          (⟨a, (Eq.mpr (congrArg (fun x ↦ E (f w.proj) →ₗ[ℂ] E x) hab) L) w.snd⟩ :
            Bundle.TotalSpace Unit E) = ⟨b, L w.snd⟩ := by
        subst b
        rfl
      exact hcast (f (g • w.proj)) (g • f w.proj) (heq g w.proj)
        (σ.linearMap g (f w.proj))
    let Q := associatedBundleMap (P := P)
      ⟨Bundle.Pullback.lift f, Pullback.continuous_lift Unit E f⟩ htotal
    have hproj (w : AssociatedBundle G P (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E))) :
        associatedEquivariantProjection σ (Q w) =
          q (associatedEquivariantProjection ρ w) := by
      induction w using Quotient.inductionOn with
      | h w => rfl
    let fiberMap (z : AssociatedBundle G P X) (v : AssociatedEquivariantFiber hP ρ z) :
        AssociatedEquivariantFiber hP σ (q z) :=
      ⟨Q v.val, (hproj v.val).trans (congrArg q v.property)⟩
    have hformula (p : P) (x : X) {z : AssociatedBundle G P X}
        (hz : associatedBundleMk G P X p x = z) (v : E (f x)) :
        fiberMap z (associatedEquivariantFiberMk hP ρ p x hz v) =
          associatedEquivariantFiberMk hP σ p (f x) (congrArg q hz) v := rfl
    -- Common original representatives prove linearity and bijectivity of this exact map.
    have hlinear (z : AssociatedBundle G P X) : IsLinearMap ℂ (fiberMap z) := by
      let p := (Quotient.out z).1
      let x := (Quotient.out z).2
      have hz : associatedBundleMk G P X p x = z := Quotient.out_eq z
      have hE := associatedEquivariantFiberMk_isLinear hP ρ p x hz
      have hF := associatedEquivariantFiberMk_isLinear hP σ p (f x) (congrArg q hz)
      have hsurj := (associatedEquivariantFiberMk_bijective hP ρ p x hz).2
      constructor
      · intro u v
        obtain ⟨u₀, rfl⟩ := hsurj u
        obtain ⟨v₀, rfl⟩ := hsurj v
        rw [← hE.map_add]
        exact (hformula p x hz (u₀ + v₀)).trans ((hF.map_add u₀ v₀).trans
          (congrArg₂ (· + ·) (hformula p x hz u₀).symm (hformula p x hz v₀).symm))
      · intro c v
        obtain ⟨v₀, rfl⟩ := hsurj v
        rw [← hE.map_smul]
        exact (hformula p x hz (c • v₀)).trans ((hF.map_smul c v₀).trans
          (congrArg (c • ·) (hformula p x hz v₀).symm))
    have hbij (z : AssociatedBundle G P X) : Function.Bijective (fiberMap z) := by
      let p := (Quotient.out z).1
      let x := (Quotient.out z).2
      have hz : associatedBundleMk G P X p x = z := Quotient.out_eq z
      have hE := associatedEquivariantFiberMk_bijective hP ρ p x hz
      have hF := associatedEquivariantFiberMk_bijective hP σ p (f x) (congrArg q hz)
      constructor
      · intro u v huv
        obtain ⟨u₀, rfl⟩ := hE.2 u
        obtain ⟨v₀, rfl⟩ := hE.2 v
        have hv := (hformula p x hz u₀).symm.trans (huv.trans (hformula p x hz v₀))
        exact congrArg (associatedEquivariantFiberMk hP ρ p x hz) (hF.1 hv)
      · intro v
        obtain ⟨v₀, rfl⟩ := hF.2 v
        exact ⟨associatedEquivariantFiberMk hP ρ p x hz v₀, hformula p x hz v₀⟩
    -- Native pullback topology records the base and the original associated total vector.
    let HE := associatedEquivariantTotalHomeomorph hP ρ
    let HF := associatedEquivariantTotalHomeomorph hP σ
    have hcontinuous : Continuous
        (fun w : Bundle.TotalSpace Unit (AssociatedEquivariantFiber hP ρ) ↦
          (⟨w.proj, fiberMap w.proj w.snd⟩ : Bundle.TotalSpace Unit
            ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
              (AssociatedEquivariantFiber hP σ)))) := by
      apply (inducing_pullbackTotalSpaceEmbedding Unit
        (AssociatedEquivariantFiber hP σ) q).continuous_iff.mpr
      apply (continuous_proj (E := AssociatedEquivariantFiber hP ρ)).prodMk
      have hc := HF.symm.continuous_toFun.comp (Q.continuous.comp HE.continuous_toFun)
      apply hc.congr
      intro w
      apply HF.injective
      exact HF.apply_symm_apply (Q w.snd.val)
    let u : Hom (AssociatedEquivariantFiber hP ρ)
        ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
          (AssociatedEquivariantFiber hP σ)) :=
      { linearMap z := IsLinearMap.mk' (fiberMap z) (hlinear z)
        continuous_total := hcontinuous }
    exact ⟨u.toIso hbij, hformula⟩

  let := isFiniteRank_pullback (E := a.1.source.Fiber) f
  let := isFiniteRank_pullback (E := a.1.target.Fiber) f
  let b := a.pullback f heq hf
  let := associatedEquivariantFiberAddCommGroup hP a.2.sourceAction
  let := associatedEquivariantFiberModule hP a.2.sourceAction
  let := associatedEquivariantTotalTopology hP a.2.sourceAction
  let := isFiniteRank_associatedEquivariant hP a.2.sourceAction
  let := associatedEquivariantFiberAddCommGroup hP a.2.targetAction
  let := associatedEquivariantFiberModule hP a.2.targetAction
  let := associatedEquivariantTotalTopology hP a.2.targetAction
  let := isFiniteRank_associatedEquivariant hP a.2.targetAction
  let := associatedEquivariantFiberAddCommGroup hP b.2.sourceAction
  let := associatedEquivariantFiberModule hP b.2.sourceAction
  let := associatedEquivariantTotalTopology hP b.2.sourceAction
  let := isFiniteRank_associatedEquivariant hP b.2.sourceAction
  let := associatedEquivariantFiberAddCommGroup hP b.2.targetAction
  let := associatedEquivariantFiberModule hP b.2.targetAction
  let := associatedEquivariantTotalTopology hP b.2.targetAction
  let := isFiniteRank_associatedEquivariant hP b.2.targetAction
  let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP a.2.sourceAction) q
  let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP a.2.targetAction) q
  obtain ⟨U, hU⟩ := comparison a.1.source.Fiber a.2.sourceAction
  obtain ⟨V, hV⟩ := comparison a.1.target.Fiber a.2.targetAction
  let d := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let pa := associatedSupportTriple hP b.1.datum b.2.sourceAction b.2.targetAction
    b.2.isEquivariant
  let hq : IsProperMap q := isProperMap_associatedBundleMap hP f heq hf
  let pb := d.pullback q hq
  -- Invariance identifies the exact inverse-image control, without a proper projection.
  have hcontrol : pa.control = pb.control := by
    ext z
    induction z using Quotient.inductionOn with
    | h w =>
      exact (associatedControl_mk_mem_iff b.1.datum.control
        b.2.isEquivariant.invariant_control w.1 w.2).trans
          (associatedControl_mk_mem_iff a.1.datum.control
            a.2.isEquivariant.invariant_control w.1 (f w.2)).symm
  let L := pa.control
  have hright : pb.control ⊆ L := hcontrol.symm.subset
  have boundaryX (p : P) (x : (b.1.datum.controlᶜ : Set X))
      {z : AssociatedBundle G P X} (hz : associatedBundleMk G P X p x = z)
      (hout : z ∈ pa.controlᶜ) (w : b.1.source.Fiber x) :
      pa.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP b.2.sourceAction p x hz w) =
        associatedEquivariantFiberMk hP b.2.targetAction p x hz
          (b.1.datum.boundary.linearEquiv x w) := by
    cases hz
    exact associatedSupportBoundary_apply hP b.1.datum b.2.sourceAction
      b.2.targetAction b.2.isEquivariant p x w
  have boundaryY (p : P) (y : (a.1.datum.controlᶜ : Set Y))
      {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z)
      (hout : z ∈ d.controlᶜ) (w : a.1.source.Fiber y) :
      d.boundary.linearEquiv ⟨z, hout⟩
          (associatedEquivariantFiberMk hP a.2.sourceAction p y hz w) =
        associatedEquivariantFiberMk hP a.2.targetAction p y hz
          (a.1.datum.boundary.linearEquiv y w) := by
    cases hz
    exact associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction
      a.2.targetAction a.2.isEquivariant p y w
  -- Both routes apply the original boundary at f(x) to the same fiber vector.
  have hsquare (z : (Lᶜ : Set (AssociatedBundle G P X)))
      (w : AssociatedEquivariantFiber hP b.2.sourceAction z) :
      V.linearEquiv z
          ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv z w) =
        (pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z
          (U.linearEquiv z w) := by
    let p := (Quotient.out z.val).1
    let x := (Quotient.out z.val).2
    have hz : associatedBundleMk G P X p x = z.val := Quotient.out_eq z.val
    have hx : x ∈ b.1.datum.controlᶜ := by
      intro hx
      exact z.property (hz ▸ (associatedControl_mk_mem_iff b.1.datum.control
        b.2.isEquivariant.invariant_control p x).mpr hx)
    let xb : (b.1.datum.controlᶜ : Set X) := ⟨x, hx⟩
    let ya : (a.1.datum.controlᶜ : Set Y) := ⟨f x, hx⟩
    let zb : (pb.controlᶜ : Set (AssociatedBundle G P X)) :=
      ⟨z, fun h ↦ z.property (hright h)⟩
    let zd : (d.controlᶜ : Set (AssociatedBundle G P Y)) :=
      ⟨q z, zb.property⟩
    obtain ⟨w₀, rfl⟩ :=
      (associatedEquivariantFiberMk_bijective hP b.2.sourceAction p x hz).2 w
    have hpa := boundaryX p xb hz z.property w₀
    have hda := boundaryY p ya (congrArg q hz) zd.property w₀
    have hpull := RelativeTriple.pullback_apply a.1.datum.boundary f xb w₀
    have hpb := RelativeTriple.pullback_apply d.boundary q zb
      (associatedEquivariantFiberMk hP a.2.sourceAction p (f x) (congrArg q hz) w₀)
    rw [pa.enlarge_apply L pa.isCompact_control (Set.Subset.refl _) z _,
      pb.enlarge_apply L pa.isCompact_control hright z _]
    exact (congrArg (V.linearEquiv z) hpa).trans
      ((hV p x hz (b.1.datum.boundary.linearEquiv xb w₀)).trans
        ((congrArg (associatedEquivariantFiberMk hP a.2.targetAction p (f x)
          (congrArg q hz)) hpull).trans (hda.symm.trans
            (hpb.symm.trans (congrArg (pb.boundary.linearEquiv zb) (hU p x hz w₀).symm)))))
  -- Conjugate the common exterior square, retaining the original small-model class maps.
  have htriple : (pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).congr U V =
      pb.enlarge L pa.isCompact_control hright := by
    change CompactSupportTriple.mk L pa.isCompact_control _ =
      CompactSupportTriple.mk L pa.isCompact_control _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    change V.linearEquiv z
      ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv z
        (U.symm.linearEquiv z w)) =
      (pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z w
    exact (hsquare z (U.symm.linearEquiv z w)).trans
      (congrArg ((pb.enlarge L pa.isCompact_control hright).boundary.linearEquiv z)
        ((U.linearEquiv z).apply_symm_apply w))
  change pa.compactSupportClass = compactSupportKZeroPullback q hq d.compactSupportClass
  calc
    pa.compactSupportClass =
        (pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).compactSupportClass :=
      (pa.compactSupportClass_enlarge L pa.isCompact_control (Set.Subset.refl _)).symm
    _ =
        ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).congr U V).compactSupportClass :=
      ((pa.enlarge L pa.isCompact_control (Set.Subset.refl _)).compactSupportClass_congr U V).symm
    _ = (pb.enlarge L pa.isCompact_control hright).compactSupportClass := congrArg _ htriple
    _ = pb.compactSupportClass := pb.compactSupportClass_enlarge L pa.isCompact_control hright
    _ = compactSupportKZeroPullback q hq d.compactSupportClass :=
      d.compactSupportClass_pullback q hq

/-- Associated descent is natural on the full original support group under proper fiber maps. -/
theorem associatedSupportKZero_pullback (hP : IsPrincipalBundle G projection)
    (f : C(X, Y)) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hf : IsProperMap f) :
    letI := associatedBundle_t2Space (Y := X) hP
    letI := associatedBundle_locallyCompactSpace (Y := X) hP
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    (associatedSupportKZero hP).comp (equivariantSupportTripleKZeroPullback f heq hf) =
      (compactSupportKZeroPullback (associatedBundleMap (P := P) f heq)
        (isProperMap_associatedBundleMap hP f heq hf)).comp (associatedSupportKZero hP) := by
  /- Evaluate both additive maps on each original equivariant triple generator.
  The two specified generator formulas reduce their equality to the preceding
  original-class comparison. Uniqueness in the existing group presentation
  extends equality to all virtual classes. Arbitrary topological G is allowed:
  no compact-group single-triple representative theorem is needed. -/
  let := associatedBundle_t2Space (Y := X) hP
  let := associatedBundle_locallyCompactSpace (Y := X) hP
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let left := (associatedSupportKZero hP).comp
    (equivariantSupportTripleKZeroPullback f heq hf)
  let right := (compactSupportKZeroPullback (associatedBundleMap (P := P) f heq)
    (isProperMap_associatedBundleMap hP f heq hf)).comp (associatedSupportKZero hP)
  -- The original free generators determine both additive maps on the same quotient.
  have heqgen : left.comp (QuotientAddGroup.mk'
        (equivariantSupportTripleKZeroRelations G Y)) =
      right.comp (QuotientAddGroup.mk'
        (equivariantSupportTripleKZeroRelations G Y)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change associatedSupportKZero hP
        (equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass) =
      compactSupportKZeroPullback (associatedBundleMap (P := P) f heq)
        (isProperMap_associatedBundleMap hP f heq hf)
        (associatedSupportKZero hP a.kZeroClass)
    rw [equivariantSupportTripleKZeroPullback_apply,
      associatedSupportKZero_class, associatedSupportKZero_class]
    exact associatedSupportClass_pullback hP f heq hf a
  -- Surjectivity of the actual quotient map extends this equality to every virtual class.
  change left = right
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G Y) z
  exact DFunLike.congr_fun heqgen w

end AtiyahSinger
