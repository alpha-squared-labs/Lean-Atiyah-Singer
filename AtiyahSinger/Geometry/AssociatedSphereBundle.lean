/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphereParametric
public import AtiyahSinger.Geometry.SmoothOrthogonalPrincipalBundle
public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.Geometry.Manifold.Submersion

-- Access the complementary submersion definition for the explicit local projection form.
import all Mathlib.Geometry.Manifold.Submersion

/-!
# The smooth sphere bundle on the original associated quotient

Public module ID: M1068.

The standard smooth orthogonal principal transition atlas induces a smooth
atlas on the original associated sphere quotient. Its topology, action,
projection and local trivializations are the existing topological objects.
One witness supplies the total atlas, its manifold certificate, smoothness and
the submersion property of the original projection, smooth local coordinates
in both directions, and smoothness of each original fiber inclusion.

The chosen total model is the full real product `E × EuclideanSpace ℝ (Fin r)`.
Local trivializations take values in the native product of the original base
and sphere. Their product model is compared with that full model using
`modelWithCornersSelf_prod`, without choosing a second total atlas. This
allows the actual projection to feed the existing vertical-kernel construction.

Sources: SG II.3 and Appendix A for smooth associated bundles, and III.13,
p.251, for the sphere bundle of the orthogonal representation plus a trivial
line. The explicit native-atlas and submersion certificates are the standard
coordinate argument spelled out as a project supplement. No smooth target
atlas is assumed in the principal-atlas definition. The proof constructs one
atlas and proves every stated property for that same choice.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] continuousSMul_orthogonalSphere

variable {r : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [hE : FiniteDimensional ℝ E]
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B] [ChartedSpace E B]
  [hB : IsManifold 𝓘(ℝ, E) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B}
  (S : SmoothOrthogonalPrincipalAtlas r 𝓘(ℝ, E) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Rr" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

/-- The original associated trivialization induced by the selected actual principal chart. -/
def associatedSphereTrivialization (b : B) :
    Trivialization (OrthogonalSphere r)
      (associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) :=
  (exists_associatedBundleTrivialization S.toIsPrincipalBundle
    (S.trivialization b) (S.equivariant b)).choose

-- Finite-dimensional manifold charts give the local projection normal form.
include hE hB in
set_option linter.unusedSectionVars false in
/-- A smooth principal atlas gives the original associated sphere its compatible smooth atlas. -/
theorem exists_associatedSphere_atlas :
    ∃ hC : ChartedSpace (E × Rr) Z,
      letI := hC
      IsManifold 𝓘(ℝ, E × Rr) ∞ Z ∧
        ContMDiff 𝓘(ℝ, E × Rr) 𝓘(ℝ, E) ∞
          (associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) ∧
        Manifold.IsSubmersion 𝓘(ℝ, E × Rr) 𝓘(ℝ, E) ∞
          (associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) ∧
        (∀ b : B,
          ContMDiffOn 𝓘(ℝ, E × Rr) (𝓘(ℝ, E).prod (𝓡 r)) ∞
              (associatedSphereTrivialization S b) (associatedSphereTrivialization S b).source ∧
            ContMDiffOn (𝓘(ℝ, E).prod (𝓡 r)) 𝓘(ℝ, E × Rr) ∞
              (associatedSphereTrivialization S b).toOpenPartialHomeomorph.symm
              (associatedSphereTrivialization S b).target) ∧
        ∀ p : P, ContMDiff (𝓡 r) 𝓘(ℝ, E × Rr) ∞
          (fun y : OrthogonalSphere r ↦ associatedBundleMk G P (OrthogonalSphere r) p y) := by
  /- Stage 1: use the selected original principal trivializations. The existing
  associated trivialization sends [p,y] to (projection p, gamma_i(p)*y), with
  inverse (b,y) mapped to [e_i.symm(b,1),y]. These formulas refer to the actual
  quotient topology and the same principal right action, not abstract copies.
  Stage 2: from chart i to chart j the fiber coordinate changes by
  a_ji(b)=gamma_j(e_i.symm(b,1)). The supplied principal atlas makes its actual
  matrix entries smooth on the overlap. Apply the parametric sphere-action
  theorem on that overlap times the whole sphere. The reverse transition uses
  the reversed principal chart pair. Thus both coordinate changes are smooth;
  fixed-element smoothness alone would not suffice for this step.
  Stage 3: compose these actual local products with the original base charts
  and native sphere charts. Their open domains cover the quotient and their
  transitions are smooth, giving one ChartedSpace and IsManifold certificate.
  All coordinate maps are homeomorphisms for the existing quotient topology.
  Use the same charts with the full real product model E times Rr; the equality
  modelWithCornersSelf_prod compares it with the native local product model.
  No second atlas or replacement topology is introduced by this model adapter.
  Stage 4: the original associated projection is first coordinate in every
  such local product. It is smooth and has the actual local projection normal
  form required by IsSubmersion, with complementary model Rr. The associated
  trivializations and their inverses are smooth on exactly their original
  source and target sets, for this same selected total atlas.
  Stage 5: fix p and a selected principal chart over projection p. The original
  fiber inclusion y mapped to [p,y] has local formula
  y mapped to (projection p, gamma_i(p)*y). Its group element is fixed, so native
  sphere smoothness gives smoothness of the entire inclusion for the same atlas.
  No smooth structure on P, Lie-group atlas, metric choice, separation,
  paracompactness, compactness, positive rank or nonempty base is required. -/
  classical
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let T (b : B) := associatedSphereTrivialization S b
  let I := 𝓘(ℝ, E × Rr)
  let J := 𝓘(ℝ, E).prod (𝓡 r)
  have hIJ : J = I := modelWithCornersSelf_prod.symm
  have hbase (b : B) : (T b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hforward (b : B) (p : P) (y : OrthogonalSphere r)
      (hp : projection p ∈ (S.trivialization b).baseSet) :
      T b (associatedBundleMk G P (OrthogonalSphere r) p y) =
        (projection p, (S.trivialization b p).2 • y) :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
  have hinverse (b b' : B) (y : OrthogonalSphere r)
      (hb' : b' ∈ (S.trivialization b).baseSet) :
      (T b).toOpenPartialHomeomorph.symm (b', y) =
        associatedBundleMk G P (OrthogonalSphere r)
          ((S.trivialization b).toOpenPartialHomeomorph.symm (b', 1)) y :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.2 b' y hb'
  -- First identify the actual quotient transition with the supplied smooth matrix action.
  have htransition (b c : B) :
      ContMDiffOn J J ∞
        ((T b).toOpenPartialHomeomorph.symm.trans (T c).toOpenPartialHomeomorph)
        ((T b).toOpenPartialHomeomorph.symm.trans (T c).toOpenPartialHomeomorph).source := by
    let A (x : B) : G :=
      (S.trivialization c ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1))).2
    let U := (S.trivialization b).baseSet ∩ (S.trivialization c).baseSet
    have hsource :
        ((T b).toOpenPartialHomeomorph.symm.trans (T c).toOpenPartialHomeomorph).source =
          U ×ˢ Set.univ := by
      ext z
      change (z ∈ (T b).target ∧ (T b).toOpenPartialHomeomorph.symm z ∈ (T c).source) ↔ _
      rw [(T b).mem_target, (T c).mem_source]
      constructor
      · rintro ⟨hb, hc⟩
        rw [(T b).proj_symm_apply' hb] at hc
        exact ⟨⟨(hbase b) ▸ hb, (hbase c) ▸ hc⟩, Set.mem_univ _⟩
      · rintro ⟨⟨hb, hc⟩, _⟩
        have hb' : z.1 ∈ (T b).baseSet := (hbase b).symm ▸ hb
        exact ⟨hb', by rw [(T b).proj_symm_apply' hb', hbase c]; exact hc⟩
    have hact : ContMDiffOn J (𝓡 r) ∞
        (fun z : B × OrthogonalSphere r ↦ A z.1 • z.2) (U ×ˢ Set.univ) :=
      contMDiffOn_orthogonalSphere_parametric_smul 𝓘(ℝ, E) r (fun x ↦ (A x).val) U
        (S.contMDiffOn_transition b c) (fun x ↦ (A x).property)
    rw [hsource]
    apply (contMDiffOn_fst.prodMk hact).congr
    rintro ⟨x, y⟩ hxy
    change T c ((T b).toOpenPartialHomeomorph.symm (x, y)) = (x, A x • y)
    rw [hinverse b x y hxy.1.1]
    have hp : projection ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)) = x :=
      (S.trivialization b).proj_symm_apply' hxy.1.1
    have hp' : projection ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)) ∈
        (S.trivialization c).baseSet := by rw [hp]; exact hxy.1.2
    rw [hforward c _ y hp', hp]
  -- Compose these original local products with the existing native product charts.
  let localCharts : ChartedSpace (B × OrthogonalSphere r) Z :=
    { atlas := Set.range fun b ↦ (T b).toOpenPartialHomeomorph
      chartAt := fun z ↦ (T (q z)).toOpenPartialHomeomorph
      mem_chart_source := fun z ↦ (T (q z)).mem_source.mpr
        ((hbase (q z)).symm ▸ S.mem_baseSet (q z))
      chart_mem_atlas := fun z ↦ ⟨q z, rfl⟩ }
  let : ChartedSpace (B × OrthogonalSphere r) Z := localCharts
  let hC := ChartedSpace.comp (ModelProd E Rr) (B × OrthogonalSphere r) Z
  let : ChartedSpace (ModelProd E Rr) Z := hC
  have hmanJ : IsManifold J ∞ Z := by
    refine { compatible := ?_ }
    rintro _ _ ⟨_, ⟨b, rfl⟩, c, hc, rfl⟩ ⟨_, ⟨b', rfl⟩, c', hc', rfl⟩
    have h := symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
      (I := J) (StructureGroupoid.subset_maximalAtlas _ hc)
      (StructureGroupoid.subset_maximalAtlas _ hc') (htransition b b') (htransition b' b)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using h
  let : IsManifold J ∞ Z := hmanJ
  have hchart (b : B) (c : OpenPartialHomeomorph (B × OrthogonalSphere r) (ModelProd E Rr))
      (hc : c ∈ atlas (ModelProd E Rr) (B × OrthogonalSphere r)) :
      (T b).toOpenPartialHomeomorph.trans c ∈ IsManifold.maximalAtlas J ∞ Z :=
    IsManifold.subset_maximalAtlas ⟨_, ⟨b, rfl⟩, c, hc, rfl⟩
  -- Each original trivialization is smooth in both directions for this one total atlas.
  have hsmooth (b : B) :
      ContMDiffOn J J ∞ (T b) (T b).source ∧
        ContMDiffOn J J ∞ (T b).toOpenPartialHomeomorph.symm (T b).target := by
    constructor
    · intro z hz
      let c := chartAt (ModelProd E Rr) (T b z)
      let d := (T b).toOpenPartialHomeomorph.trans c
      have hc : c ∈ IsManifold.maximalAtlas J ∞ (B × OrthogonalSphere r) :=
        IsManifold.chart_mem_maximalAtlas (T b z)
      have hd := hchart b c (chart_mem_atlas _ _)
      have hdz : z ∈ d.source := by
        refine ⟨hz, ?_⟩
        change T b z ∈ c.source
        exact mem_chart_source _ _
      have hcz : d z ∈ c.target := c.map_source (mem_chart_source _ _)
      have h := (contMDiffAt_symm_of_mem_maximalAtlas hc hcz).comp z
        (contMDiffAt_of_mem_maximalAtlas hd hdz)
      apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [d.open_source.mem_nhds hdz] with z' hz'
      exact (c.left_inv hz'.2).symm
    · intro y hy
      let c := chartAt (ModelProd E Rr) y
      let d := (T b).toOpenPartialHomeomorph.trans c
      have hc : c ∈ IsManifold.maximalAtlas J ∞ (B × OrthogonalSphere r) :=
        IsManifold.chart_mem_maximalAtlas y
      have hd := hchart b c (chart_mem_atlas _ _)
      have hcy : y ∈ c.source := mem_chart_source _ _
      have hdy : c y ∈ d.target := by
        refine ⟨c.map_source hcy, ?_⟩
        change c.symm (c y) ∈ (T b).target
        rw [c.left_inv hcy]
        exact hy
      have h := (contMDiffAt_symm_of_mem_maximalAtlas hd hdy).comp y
        (contMDiffAt_of_mem_maximalAtlas hc hcy)
      apply (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [c.open_source.mem_nhds hcy] with y' hy'
      change (T b).toOpenPartialHomeomorph.symm y' =
        (T b).toOpenPartialHomeomorph.symm (c.symm (c y'))
      rw [c.left_inv hy']
  -- The projection is locally the first coordinate of the very same product chart.
  have hproj : ContMDiff J 𝓘(ℝ, E) ∞ q := by
    intro z
    let b := q z
    have hz : z ∈ (T b).source := (T b).mem_source.mpr
      ((hbase b).symm ▸ S.mem_baseSet b)
    have h := contMDiffAt_fst.comp z
      ((hsmooth b).1.contMDiffAt ((T b).open_source.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [(T b).open_source.mem_nhds hz] with z' hz'
    exact ((T b).coe_fst hz').symm
  have hsub : Manifold.IsSubmersion J 𝓘(ℝ, E) ∞ q := by
    apply Manifold.IsSubmersionOfComplement.isSubmersion (F := Rr)
    change ∀ z : Z, Manifold.IsSubmersionAtOfComplement Rr J 𝓘(ℝ, E) ∞ q z
    intro z
    let b := q z
    let cB := chartAt E b
    let cF := chartAt Rr (T b z).2
    let c := cB.prod cF
    let d := (T b).toOpenPartialHomeomorph.trans c
    have hz : z ∈ (T b).source := (T b).mem_source.mpr
      ((hbase b).symm ▸ S.mem_baseSet b)
    have hcz : T b z ∈ c.source := by
      refine ⟨?_, mem_chart_source _ _⟩
      rw [(T b).coe_fst hz]
      exact mem_chart_source _ _
    have hc : c ∈ atlas (ModelProd E Rr) (B × OrthogonalSphere r) :=
      ⟨cB, chart_mem_atlas _ _, cF, chart_mem_atlas _ _, rfl⟩
    apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (I := J) (J := 𝓘(ℝ, E))
      (ContinuousLinearEquiv.refl ℝ (E × Rr)) d cB ⟨hz, hcz⟩
      (mem_chart_source _ _) (hchart b c hc) (IsManifold.chart_mem_maximalAtlas b)
    · intro z' hz'
      change q z' ∈ cB.source
      rw [← (T b).coe_fst hz'.1]
      exact hz'.2.1
    · intro w hw
      rw [hIJ] at hw ⊢
      have hw' : w ∈ d.target := by
        rw [OpenPartialHomeomorph.extend_target] at hw
        exact hw.1
      change cB (q ((T b).toOpenPartialHomeomorph.symm (c.symm w))) = w.1
      rw [(T b).proj_symm_apply hw'.2]
      exact cB.right_inv hw'.1.1
  -- A fixed principal point gives its original quotient fiber inclusion, in the same charts.
  have hfiber (p : P) :
      ContMDiff (𝓡 r) J ∞ (fun y ↦ associatedBundleMk G P (OrthogonalSphere r) p y) := by
    let b := projection p
    let g (y : OrthogonalSphere r) := (b, (S.trivialization b p).2 • y)
    have hg : ContMDiff (𝓡 r) J ∞ g :=
      contMDiff_const.prodMk (contMDiff_orthogonalSphere_smul r (S.trivialization b p).2)
    have hgt (y : OrthogonalSphere r) : g y ∈ (T b).target :=
      (T b).mem_target.mpr ((hbase b).symm ▸ S.mem_baseSet b)
    have h : ContMDiff (𝓡 r) J ∞ ((T b).toOpenPartialHomeomorph.symm ∘ g) :=
      fun y ↦ ((hsmooth b).2.contMDiffAt
        ((T b).open_target.mem_nhds (hgt y))).comp y (hg y)
    apply h.congr
    intro y
    have hsource : associatedBundleMk G P (OrthogonalSphere r) p y ∈ (T b).source :=
      (T b).mem_source.mpr ((hbase b).symm ▸ S.mem_baseSet b)
    change associatedBundleMk G P (OrthogonalSphere r) p y =
      (T b).toOpenPartialHomeomorph.symm (g y)
    rw [show g y = T b (associatedBundleMk G P (OrthogonalSphere r) p y) from
      (hforward b p y (S.mem_baseSet b)).symm]
    exact ((T b).toOpenPartialHomeomorph.left_inv hsource).symm
  let : ChartedSpace (E × Rr) Z := hC
  refine ⟨hC, ?_⟩
  change IsManifold I ∞ Z ∧ ContMDiff I 𝓘(ℝ, E) ∞ q ∧
    Manifold.IsSubmersion I 𝓘(ℝ, E) ∞ q ∧
      (∀ b, ContMDiffOn I J ∞ (T b) (T b).source ∧
        ContMDiffOn J I ∞ (T b).toOpenPartialHomeomorph.symm (T b).target) ∧
      ∀ p, ContMDiff (𝓡 r) I ∞ (fun y ↦ associatedBundleMk G P (OrthogonalSphere r) p y)
  rw [← hIJ]
  exact ⟨hmanJ, hproj, hsub, hsmooth, hfiber⟩

/-- The total atlas selected from the single original associated-sphere existence witness. -/
@[reducible]
def associatedSphereChartedSpace : ChartedSpace (E × Rr) Z :=
  (exists_associatedSphere_atlas S).choose

/-- Smoothness of the total manifold uses precisely the selected associated atlas. -/
instance associatedSphereIsManifold :
    letI := associatedSphereChartedSpace S
    IsManifold 𝓘(ℝ, E × Rr) ∞ Z :=
  (exists_associatedSphere_atlas S).choose_spec.1

/-- The original quotient projection, bundled with smoothness for the selected total atlas. -/
def smoothAssociatedSphereProjection :
    letI := associatedSphereChartedSpace S
    ContMDiffMap 𝓘(ℝ, E × Rr) 𝓘(ℝ, E) Z B ∞ :=
  ⟨associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle,
    (exists_associatedSphere_atlas S).choose_spec.2.1⟩

set_option linter.defProp false in
/-- The submersion certificate for that exact projection and that same selected total atlas. -/
def associatedSphereProjection_isSubmersion :
    letI := associatedSphereChartedSpace S
    Manifold.IsSubmersion 𝓘(ℝ, E × Rr) 𝓘(ℝ, E) ∞ (smoothAssociatedSphereProjection S) :=
  (exists_associatedSphere_atlas S).choose_spec.2.2.1

/-- The actual map y mapped to [p,y], smooth for the one selected associated total atlas. -/
def smoothAssociatedSphereFiberInclusion (p : P) :
    letI := associatedSphereChartedSpace S
    ContMDiffMap (𝓡 r) 𝓘(ℝ, E × Rr) (OrthogonalSphere r) Z ∞ :=
  ⟨fun y ↦ associatedBundleMk G P (OrthogonalSphere r) p y,
    (exists_associatedSphere_atlas S).choose_spec.2.2.2.2 p⟩

end AtiyahSinger
