/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.AtlasNativeModel
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Topology.AssociatedCompactControl
public import AtiyahSinger.Topology.AssociatedEquivariantBundle

/-!
# Smooth descent of the original equivariant bundle

Public module ID: M1067.

Principal charts and the given sphere bundle charts define local coordinates on
its actual associated quotient fibers. Their transition columns use the given
jointly smooth action. The topology, fiber operations and quotient maps are the
original ones; the construction does not replace descent by a rank comparison.

The local chart theorem records all original representatives, which is also the
coordinate formula needed to descend vertical operators and their kernels.
Sources: SG III.13.6 and the usual local description of associated vector bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology

section QuotientChart

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option maxHeartbeats 1200000 in
-- The actual quotient and fiber charts carry nested dependent projections.
/-- The specified principal and fiber charts give linear coordinates on the original quotient. -/
theorem exists_associatedEquivariant_chart (hP : IsPrincipalBundle G projection)
    (σ : EquivariantStructure G E) (e : Trivialization G projection)
    (he : ∀ (g : G) (p : P), projection p ∈ e.baseSet →
      (e (MulOpposite.op g • p)).2 = (e p).2 * g)
    {r : ℕ} (d : Trivialization (Fin r → ℂ) (π Unit E))
    (hdlin : ∀ y : Y, y ∈ d.baseSet →
      IsLinearMap ℂ (fun v : E y ↦ (d ⟨y, v⟩).2)) :
    let eB := (exists_associatedBundleTrivialization (F := Y) hP e he).choose
    ∃ t : Trivialization (Fin r → ℂ) (π Unit (AssociatedEquivariantFiber hP σ)),
      t.baseSet = eB.source ∩ eB ⁻¹' (Set.univ ×ˢ d.baseSet) ∧
        (∀ z, z ∈ t.baseSet → IsLinearMap ℂ
          (fun v : AssociatedEquivariantFiber hP σ z ↦ (t ⟨z, v⟩).2)) ∧
        ∀ (p : P) (y : Y) (z : AssociatedBundle G P Y)
          (hz : associatedBundleMk G P Y p y = z) (v : E y),
          projection p ∈ e.baseSet →
            (t ⟨z, associatedEquivariantFiberMk hP σ p y hz v⟩).2 =
              (d ⟨(e p).2 • y, σ.linearMap (e p).2 y v⟩).2 := by
  -- Compose the actual two quotient charts with the original finite vector chart.
  classical
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : ContinuousSMul G (TotalSpace Unit E) := ⟨σ.continuous_action⟩
  let H := associatedEquivariantTotalHomeomorph hP σ
  let pA := associatedEquivariantProjection (P := P) σ
  let pB := associatedBundleProjection (F := Y) hP
  have hproj (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ)) :
      pA (H w) = w.proj := w.snd.property
  have hprojB (q : AssociatedBundle G P (TotalSpace Unit E)) :
      associatedBundleProjection (F := TotalSpace Unit E) hP q = pB (pA q) := by
    induction q using Quotient.inductionOn with
    | h t => rfl
  have hcontinuousProj : Continuous (π Unit (AssociatedEquivariantFiber hP σ)) :=
    (pA.continuous.comp H.continuous_toFun).congr hproj
  let eB := (exists_associatedBundleTrivialization (F := Y) hP e he).choose
  obtain ⟨hBb, hBf, hBi⟩ :=
    (exists_associatedBundleTrivialization (F := Y) hP e he).choose_spec
  obtain ⟨eT, hTb, hTf, hTi⟩ :=
    exists_associatedBundleTrivialization (F := TotalSpace Unit E) hP e he
  -- The two quotient charts use the same principal chart and commute with the original projection.
  have hcomm (q : AssociatedBundle G P (TotalSpace Unit E))
      (hq : associatedBundleProjection (F := TotalSpace Unit E) hP q ∈ e.baseSet) :
      eB (pA q) = ((eT q).1, (eT q).2.proj) := by
    induction q using Quotient.inductionOn with
    | h t =>
      rcases t with ⟨p, v⟩
      change eB (associatedBundleMk G P Y p v.proj) = _
      exact (hBf p v.proj hq).trans
        (congrArg (fun t : B × TotalSpace Unit E ↦ (t.1, t.2.proj)) (hTf p v hq)).symm
  have hinverseProj (b : B) (v : TotalSpace Unit E) (hb : b ∈ e.baseSet) :
      pA (eT.toOpenPartialHomeomorph.symm (b, v)) =
        eB.toOpenPartialHomeomorph.symm (b, v.proj) := by
    rw [hTi b v hb, hBi b v.proj hb]
    rfl
  let V : Set (AssociatedBundle G P Y) := eB.source ∩ eB ⁻¹' (Set.univ ×ˢ d.baseSet)
  have hV : IsOpen V := eB.toOpenPartialHomeomorph.isOpen_inter_preimage
    (isOpen_univ.prod d.open_baseSet)
  have hb (z : AssociatedBundle G P Y) (hz : z ∈ V) : (eB z).1 ∈ e.baseSet :=
    hBb ▸ eB.mem_target.mp (eB.map_source hz.1)
  have hsource (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ eB.source) : H w ∈ eT.source := by
    apply eT.mem_source.mpr
    rw [hTb, hprojB, hproj]
    exact hBb ▸ eB.mem_source.mp hw
  have hcommTotal (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ eB.source) :
      eB w.proj = ((eT (H w)).1, (eT (H w)).2.proj) := by
    rw [← hproj w]
    exact hcomm (H w) (hTb ▸ eT.mem_source.mp (hsource w hw))
  have hdsource (w : TotalSpace Unit (AssociatedEquivariantFiber hP σ))
      (hw : w.proj ∈ V) : (eT (H w)).2 ∈ d.source := by
    apply d.mem_source.mpr
    have hc : (eB w.proj).2 = (eT (H w)).2.proj :=
      congrArg Prod.snd (hcommTotal w hw.1)
    exact hc ▸ hw.2.2
  let inverse (y : AssociatedBundle G P Y × (Fin r → ℂ)) :
      TotalSpace Unit (AssociatedEquivariantFiber hP σ) :=
    H.symm (eT.toOpenPartialHomeomorph.symm
      ((eB y.1).1, d.toOpenPartialHomeomorph.symm ((eB y.1).2, y.2)))
  have hinverseBase (y : AssociatedBundle G P Y × (Fin r → ℂ)) (hy : y.1 ∈ V) :
      (inverse y).proj = y.1 := by
    change pA (eT.toOpenPartialHomeomorph.symm
      ((eB y.1).1, d.toOpenPartialHomeomorph.symm ((eB y.1).2, y.2))) = y.1
    rw [hinverseProj _ _ (hb y.1 hy), d.proj_symm_apply' hy.2.2]
    exact eB.left_inv hy.1
  -- Compose these charts on their actual open domains in the unchanged total topology.
  let t : Trivialization (Fin r → ℂ) (π Unit (AssociatedEquivariantFiber hP σ)) :=
    { toFun := fun w ↦ (w.proj, (d (eT (H w)).2).2)
      invFun := inverse
      source := π Unit (AssociatedEquivariantFiber hP σ) ⁻¹' V
      target := V ×ˢ Set.univ
      baseSet := V
      map_source' := fun _ hw ↦ ⟨hw, Set.mem_univ _⟩
      map_target' := by
        intro y hy
        change (inverse y).proj ∈ V
        rw [hinverseBase y hy.1]
        exact hy.1
      left_inv' := by
        intro w hw
        change H.symm (eT.toOpenPartialHomeomorph.symm
          ((eB w.proj).1,
            d.toOpenPartialHomeomorph.symm ((eB w.proj).2, (d (eT (H w)).2).2))) = w
        rw [hcommTotal w hw.1, d.symm_apply_mk_proj (hdsource w hw)]
        change H.symm (eT.toOpenPartialHomeomorph.symm (eT (H w))) = w
        exact (congrArg H.symm (eT.left_inv (hsource w hw.1))).trans
          (H.symm_apply_apply w)
      right_inv' := by
        intro y hy
        apply Prod.ext
        · exact hinverseBase y hy.1
        · change (d (eT (H (inverse y))).2).2 = y.2
          dsimp only [inverse]
          rw [H.apply_symm_apply, eT.apply_symm_apply' (hTb.symm ▸ hb y.1 hy.1)]
          rw [d.apply_symm_apply' hy.1.2.2]
      open_source := hV.preimage hcontinuousProj
      open_target := hV.prod isOpen_univ
      open_baseSet := hV
      continuousOn_toFun := by
        apply hcontinuousProj.continuousOn.prodMk
        apply continuous_snd.comp_continuousOn
        apply d.toOpenPartialHomeomorph.continuousOn.comp
        · exact continuous_snd.comp_continuousOn
            (eT.toOpenPartialHomeomorph.continuousOn.comp H.continuous_toFun.continuousOn
              (fun w hw ↦ hsource w hw.1))
        · exact fun w hw ↦ hdsource w hw
      continuousOn_invFun := by
        have hcB : ContinuousOn (fun y : AssociatedBundle G P Y × (Fin r → ℂ) ↦ eB y.1)
            (V ×ˢ Set.univ) :=
          eB.toOpenPartialHomeomorph.continuousOn.comp continuous_fst.continuousOn
            (fun y hy ↦ hy.1.1)
        apply H.symm.continuous_toFun.comp_continuousOn
        apply eT.toOpenPartialHomeomorph.continuousOn_symm.comp
        · exact (continuous_fst.comp_continuousOn hcB).prodMk
            (d.toOpenPartialHomeomorph.continuousOn_symm.comp
              ((continuous_snd.comp_continuousOn hcB).prodMk continuous_snd.continuousOn)
              (fun y hy ↦ d.mem_target.mpr hy.1.2.2))
        · exact fun y hy ↦ eT.mem_target.mpr (hTb.symm ▸ hb y.1 hy.1)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  refine ⟨t, rfl, ?_, ?_⟩
  · intro z hz
    -- Representative linearity uses the same algebra; the inverse section gives linear charts.
    let b := (eB z).1
    let y := (eB z).2
    let p₀ := e.toOpenPartialHomeomorph.symm (b, 1)
    have hzrep : associatedBundleMk G P Y p₀ y = z :=
      (hBi b y (hb z hz)).symm.trans (eB.left_inv hz.1)
    let mk := associatedEquivariantFiberMk hP σ p₀ y hzrep
    have hmk := associatedEquivariantFiberMk_isLinear hP σ p₀ y hzrep
    have hsurj := (associatedEquivariantFiberMk_bijective hP σ p₀ y hzrep).2
    have hformula (v : E y) : (t ⟨z, mk v⟩).2 = (d ⟨y, v⟩).2 := by
      change (d (eT (associatedBundleMk G P (TotalSpace Unit E) p₀ ⟨y, v⟩)).2).2 = _
      rw [← hTi b ⟨y, v⟩ (hb z hz), eT.apply_symm_apply' (hTb.symm ▸ hb z hz)]
    constructor
    · intro u v
      obtain ⟨u₀, rfl⟩ := hsurj u
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hmk.map_add, hformula, hformula, hformula]
      exact (hdlin y hz.2.2).map_add u₀ v₀
    · intro c v
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hmk.map_smul, hformula, hformula]
      exact (hdlin y hz.2.2).map_smul c v₀
  · intro p y z hz v hp
    change (d (eT (associatedBundleMk G P (TotalSpace Unit E) p ⟨y, v⟩)).2).2 = _
    rw [hTf p ⟨y, v⟩ hp]
    rfl

end QuotientChart

section SphereDescent

open scoped Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "AssocFiber" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

/-- The original principal chart composed with the specified original sphere-bundle chart. -/
def associatedSphereBundleChart (i : B × A.Index) :
    Trivialization (Fin (A.rank i.2) → ℂ) (π Unit AssocFiber) :=
  (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
    (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2) (A.linear i.2)).choose

set_option maxHeartbeats 1600000 in
-- The quotient transition and two original atlases have nested dependent fiber coordinates.
/-- Joint smooth equivariance gives the associated smooth atlas on the actual quotient fibers. -/
def associatedSphereSmoothBundleAtlas
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    SmoothComplexBundleAtlas (n := n + r) AssocFiber := by
  classical
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let T := associatedSphereBundleChart S A σ
  let t (b : B) := associatedSphereTrivialization S b
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let τ (i j b : B) : G :=
    (S.trivialization j ((S.trivialization i).toOpenPartialHomeomorph.symm (b, 1))).2
  have hbase (b : B) : (t b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hforward (b : B) (p : P) (y : OrthogonalSphere r)
      (hp : projection p ∈ (S.trivialization b).baseSet) :
      t b (associatedBundleMk G P (OrthogonalSphere r) p y) =
        (projection p, (S.trivialization b p).2 • y) :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
  have hinverse (b x : B) (y : OrthogonalSphere r)
      (hx : x ∈ (S.trivialization b).baseSet) :
      (t b).toOpenPartialHomeomorph.symm (x, y) =
        associatedBundleMk G P (OrthogonalSphere r)
          ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)) y :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.2 x y hx
  have hchart (i : B × A.Index) :
      (T i).baseSet = (t i.1).source ∩
        (t i.1) ⁻¹' (Set.univ ×ˢ (A.chart i.2).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2) (A.linear i.2)).choose_spec.1
  have hrep (i : B × A.Index) (p : P) (y : OrthogonalSphere r) (z : Z)
      (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z) (v : E y)
      (hp : projection p ∈ (S.trivialization i.1).baseSet) :
      (T i ⟨z, associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hz v⟩).2 =
        (A.chart i.2 ⟨(S.trivialization i.1 p).2 • y,
          σ.linearMap (S.trivialization i.1 p).2 y v⟩).2 :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2) (A.linear i.2)).choose_spec.2.2
      p y z hz v hp
  have hcoord (b : B) : ContMDiffOn (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞
      (t b) (t b).source :=
    ((exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b).1.comp
      d.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  -- Matrix-entry smoothness gives smoothness in the actual orthogonal Lie atlas.
  have hτ (i j : B) : ContMDiffOn (𝓡 n) 𝓘(ℝ, OrthogonalGroupModel r) ∞
      (τ i j) ((S.trivialization i).baseSet ∩ (S.trivialization j).baseSet) := by
    let U : TopologicalSpace.Opens B :=
      ⟨_, (S.trivialization i).open_baseSet.inter (S.trivialization j).open_baseSet⟩
    have hm : ContMDiff (𝓡 n) 𝓘(ℝ, Fin r → Fin r → ℝ) ∞
        (fun b : U ↦ fun k l ↦ (τ i j b).val k l) := by
      intro b
      exact ((S.contMDiffOn_transition i j).contMDiffAt
        (U.isOpen.mem_nhds b.property)).comp b contMDiff_subtype_val.contMDiffAt
    have hg : ContMDiff (𝓡 n) 𝓘(ℝ, OrthogonalGroupModel r) ∞
        (fun b : U ↦ τ i j b) := by
      apply (contMDiff_orthogonalGroup_iff (𝓡 n) r ∞ _).mpr
      intro k l
      exact (contMDiff_pi_space.mp (contMDiff_pi_space.mp hm k) l)
    intro b hb
    exact (contMDiffAt_subtype_iff.mp (hg ⟨b, hb⟩)).contMDiffWithinAt
  refine
    { Index := B × A.Index
      rank := fun i ↦ A.rank i.2
      chart := T
      covers := ?_
      linear := ?_
      contMDiffOn_coordChange := ?_ }
  · intro z
    obtain ⟨i, hi⟩ := A.covers (t (q z) z).2
    refine ⟨(q z, i), ?_⟩
    rw [hchart]
    exact ⟨(t (q z)).mem_source.mpr ((hbase _).symm ▸ S.mem_baseSet _),
      Set.mem_univ _, hi⟩
  · intro i
    exact (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization i.1) (S.equivariant i.1) (A.chart i.2)
      (A.linear i.2)).choose_spec.2.1
  · intro i j a
    let U := (T i).baseSet ∩ (T j).baseSet
    have hi (z : Z) (hz : z ∈ U) :
        z ∈ (t i.1).source ∧ (t i.1 z).2 ∈ (A.chart i.2).baseSet := by
      have h := (hchart i) ▸ hz.1
      exact ⟨h.1, h.2.2⟩
    have hj (z : Z) (hz : z ∈ U) :
        z ∈ (t j.1).source ∧ (t j.1 z).2 ∈ (A.chart j.2).baseSet := by
      have h := (hchart j) ▸ hz.2
      exact ⟨h.1, h.2.2⟩
    have hb (z : Z) (hz : z ∈ U) :
        (t i.1 z).1 ∈ (S.trivialization i.1).baseSet ∩
          (S.trivialization j.1).baseSet := by
      rw [(t i.1).coe_fst (hi z hz).1]
      exact ⟨hbase i.1 ▸ (t i.1).mem_source.mp (hi z hz).1,
        hbase j.1 ▸ (t j.1).mem_source.mp (hj z hz).1⟩
    have hpr (z : Z) (hz : z ∈ U) :
        associatedBundleMk G P (OrthogonalSphere r)
          ((S.trivialization i.1).toOpenPartialHomeomorph.symm ((t i.1 z).1, 1))
          (t i.1 z).2 = z :=
      (hinverse i.1 _ _ (hb z hz).1).symm.trans ((t i.1).left_inv (hi z hz).1)
    have htrans (z : Z) (hz : z ∈ U) :
        (t j.1 z).2 = τ i.1 j.1 (t i.1 z).1 • (t i.1 z).2 := by
      have hp := (S.trivialization i.1).proj_symm_apply' (x := (1 : G)) (hb z hz).1
      have hf := hforward j.1 _ (t i.1 z).2 (hp.symm ▸ (hb z hz).2)
      rw [hpr z hz] at hf
      exact congrArg Prod.snd hf
    -- The actual inverse fiber chart is represented in the same principal local section.
    have hinv (z : Z) (hz : z ∈ U) (v : Fin (A.rank i.2) → ℂ) :
        (T i).toPartialEquiv.symm (z, v) =
          ⟨z, associatedEquivariantFiberMk S.toIsPrincipalBundle σ
            ((S.trivialization i.1).toOpenPartialHomeomorph.symm ((t i.1 z).1, 1))
            (t i.1 z).2 (hpr z hz)
            ((A.frameLinearEquiv i.2 (t i.1 z).2 (hi z hz).2).symm v)⟩ := by
      let p := (S.trivialization i.1).toOpenPartialHomeomorph.symm ((t i.1 z).1, 1)
      let w := (A.frameLinearEquiv i.2 (t i.1 z).2 (hi z hz).2).symm v
      let W : TotalSpace Unit AssocFiber :=
        ⟨z, associatedEquivariantFiberMk S.toIsPrincipalBundle σ p
          (t i.1 z).2 (hpr z hz) w⟩
      have hp : projection p = (t i.1 z).1 :=
        (S.trivialization i.1).proj_symm_apply' (hb z hz).1
      have hc : (T i W).2 = v := by
        rw [hrep i p _ z (hpr z hz) w (hp.symm ▸ (hb z hz).1)]
        rw [(S.trivialization i.1).apply_symm_apply' (hb z hz).1]
        rw [σ.one_map]
        exact (A.frameLinearEquiv i.2 (t i.1 z).2 (hi z hz).2).apply_symm_apply v
      calc
        (T i).toPartialEquiv.symm (z, v) =
            (T i).toPartialEquiv.symm (W.proj, (T i W).2) := by rw [hc]
        _ = W := (T i).symm_apply_mk_proj ((T i).mem_source.mpr hz.1)
    -- Compose the given joint action columns with these same moving base coordinates.
    have hs := (hcoord i.1).mono (fun z hz ↦ (hi z hz).1)
    have harg : ContMDiffOn (𝓡 (n + r))
        (𝓘(ℝ, OrthogonalGroupModel r).prod (𝓡 r)) ∞
        (fun z : Z ↦ (τ i.1 j.1 (t i.1 z).1, (t i.1 z).2)) U :=
      ((hτ i.1 j.1).comp (contMDiff_fst.comp_contMDiffOn hs)
        (fun z hz ↦ hb z hz)).prodMk (contMDiff_snd.comp_contMDiffOn hs)
    have h := (hσ i.2 j.2 a).comp harg (by
      intro z hz
      exact ⟨(hi z hz).2, (htrans z hz) ▸ (hj z hz).2⟩)
    apply h.congr
    intro z hz
    rw [hinv z hz]
    rw [hrep j _ _ z (hpr z hz) _
      ((S.trivialization i.1).proj_symm_apply' (x := (1 : G)) (hb z hz).1 |>.symm ▸
        (hb z hz).2)]
    dsimp only [Function.comp_def]
    rw [dite_eq_left (hi z hz).2]

variable [CompactSpace B] [T2Space B]

set_option maxSynthPendingDepth 30 in
/-- A constant-rank descended atlas has a native model with both actual comparison maps smooth. -/
theorem exists_associatedSphere_nativeBundle
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (k : ℕ)
    (hrank : ∀ y : OrthogonalSphere r, Module.finrank ℂ (E y) = k) :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let D := associatedSphereSmoothBundleAtlas S A σ hσ
    ∃ V : SmoothFiniteComplexBundle (n := n + r) Z, V.rank = k ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin V.rank)) V.Fiber
      ∃ e : Iso AssocFiber V.Fiber,
        IsSmoothAtlasBundleMap D
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := V.rank) V.Fiber)
          e.toHom.linearMap ∧
        IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n + r) (r := V.rank) V.Fiber) D
          e.symm.toHom.linearMap := by
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let D := associatedSphereSmoothBundleAtlas S A σ hσ
  -- Compactness is for the original associated quotient and its original topology.
  let : T2Space Z := associatedBundle_t2Space S.toIsPrincipalBundle
  have hcontrol : associatedControl G P (OrthogonalSphere r) Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with
    | h v => exact ⟨v, ⟨Set.mem_univ v.1, Set.mem_univ v.2⟩, rfl⟩
  let : CompactSpace Z := ⟨by
    rw [← hcontrol]
    exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
      (fun _ _ ↦ Iff.rfl)⟩
  -- Rank and both smooth maps are transported through the same actual quotient coordinates.
  have hr (z : Z) : Module.finrank ℂ (AssocFiber z) = k :=
    (associatedEquivariantFiberLinearEquiv S.toIsPrincipalBundle σ z).finrank_eq.trans
      (hrank (Quotient.out z).2)
  exact D.exists_native_model_with_atlasMaps k hr

end SphereDescent

end AtiyahSinger
