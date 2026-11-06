/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.OrthogonalFrameBundle
public import Mathlib.Geometry.Manifold.SmoothEmbedding

import AtiyahSinger.Geometry.CompactEuclideanEmbedding

/-!
# The frame-associated sphere is the original fiberwise sphere compactification

Public module ID: M1242.

The sphere compactification of V is the unit sphere of V plus a real line.
Its carrier below is a subtype of the original bundle total space times the
real line, with the sum of squared norms condition. The product's max norm
is not used to define this sphere. This is a fiberwise compactification,
not the one-point compactification of the whole total space.

For the actual orthogonal frame bundle, the associated sphere quotient maps
by [p,(u,t)] to (p(u),t). The specified original principal atlas supplies the
source smooth structure. Smoothness of its local frame columns in the original
vector bundle is essential: the same evaluation is a smooth embedding into
the original total space times the line. The rank-zero case gives two points
in each fiber and retains the original base topology.

Sources: SG Appendix A, pp.370--372, for reconstruction from frames, and
III.13, p.251, for S^r with the block O(r) action and the sphere compactification.
The exact native-topology and smooth-embedding formulation is a standard
geometric supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The unit sphere of the original real bundle plus a line, with its subspace topology. -/
abbrev SphereCompactification (r : ℕ) {B : Type*} (V : B → Type*)
    [∀ x, NormedAddCommGroup (V x)] : Type _ :=
  {z : TotalSpace (EuclideanSpace ℝ (Fin r)) V × ℝ |
    ‖z.1.snd‖ ^ 2 + z.2 ^ 2 = 1}

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [hEB : FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [hB : IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [hV : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [hMetric : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "Rr" => EuclideanSpace ℝ (Fin r)

include hEB hB hV hMetric

/-- Frame evaluation identifies the original associated sphere with the original sphere bundle. -/
theorem exists_frameSphereHomeomorph :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    ∃ e : Z ≃ₜ SphereCompactification r V,
      (∀ (p : P) (y : OrthogonalSphere r),
        (e (associatedBundleMk G P (OrthogonalSphere r) p y)).val =
          ((⟨p.1, p.2 y.val.fst⟩ : TotalSpace Rr V), y.val.snd)) ∧
      Manifold.IsSmoothEmbedding 𝓘(ℝ, EB × Rr)
        ((𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : Z ↦ (e z).val) := by
  /- Stage 1: evaluate the actual frame p on the horizontal coordinate and
  keep the vertical coordinate t. The L2 sphere equation is exactly the sum
  of the two squared norms, and p is an isometry. Thus the value lies in the
  displayed original subtype. The right frame action is precomposition by A,
  whereas the diagonal quotient changes y by A inverse; these cancel. Hence
  this precise formula descends to the existing associated quotient.
  Stage 2: on each original principal chart, choose its canonical frame s(x).
  The inverse sends (v,t) over x to [s(x),(s(x) inverse(v),t)]. Different frames
  differ by the same orthogonal transition used in the quotient, so these
  local inverses agree. Both maps are continuous for the original total and
  quotient topologies, and are inverse on every fiber. They give a homeomorphism
  to the whole displayed subtype; no independent target topology is selected.
  Stage 3: the chosen frame atlas has smooth columns in the original bundle.
  Consequently (x,u,t) mapped to (s(x)u,t) is smooth in the original local
  vector-bundle coordinates. Its inverse ambient local map is smooth as well:
  the matrix entries of s(x) inverse are the original smooth metric pairings
  with those columns. The source associated atlas is the specified one built
  from this very same principal atlas, so its local sphere coordinates agree.
  Stage 4: in these local ambient coordinates, evaluation is the product of
  the identity on the base with the native unit-sphere inclusion into R^(r+1).
  That inclusion is a smooth immersion and a topological embedding. Therefore
  the global evaluation is a smooth embedding in the original total times R.
  At rank zero the sphere is the two poles, the local immersion has zero fiber
  dimension, and the retained base coordinate supplies the base topology.
  Neither compactness, orientation, positive rank nor a global frame is used. -/
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let I := 𝓘(ℝ, EB)
  let Q := 𝓘(ℝ, EB × Rr)
  let J := I.prod (𝓡 r)
  let K := (I.prod 𝓘(ℝ, Rr)).prod 𝓘(ℝ, ℝ)
  let t (b : B) := S.trivialization b
  let U (b : B) := (t b).baseSet
  let T (b : B) := associatedSphereTrivialization S b
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  have hbase (b : B) : (T b).baseSet = U b :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (t b) (S.equivariant b)).choose_spec.1
  have hforward (b : B) (p : P) (y : OrthogonalSphere r) (hp : p.1 ∈ U b) :
      T b (associatedBundleMk G P (OrthogonalSphere r) p y) =
        (p.1, (t b p).2 • y) :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (t b) (S.equivariant b)).choose_spec.2.1 p y hp
  have hinverse (b x : B) (y : OrthogonalSphere r) (hx : x ∈ U b) :
      (T b).toOpenPartialHomeomorph.symm (x, y) =
        associatedBundleMk G P (OrthogonalSphere r)
          ((t b).toOpenPartialHomeomorph.symm (x, 1)) y :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (t b) (S.equivariant b)).choose_spec.2.2 x y hx
  -- The local frame is the unit section of the already specified principal atlas.
  -- Outside its domain the atlas at x only supplies a harmless total extension.
  let p (b x : B) : P := if x ∈ U b then
    (t b).toOpenPartialHomeomorph.symm (x, 1)
    else (t x).toOpenPartialHomeomorph.symm (x, 1)
  have hp (b x : B) : (p b x).1 = x := by
    dsimp [p]
    split_ifs with hx
    · exact (t b).proj_symm_apply' hx
    · exact (t x).proj_symm_apply' (S.mem_baseSet x)
  let s (b x : B) : Rr ≃ₗᵢ[ℝ] V x := (hp b x) ▸ (p b x).2
  have htransport {x y : B} (h : x = y) (f : Rr ≃ₗᵢ[ℝ] V x) :
      (⟨x, f⟩ : P) = ⟨y, h ▸ f⟩ := by
    subst y
    rfl
  have hps (b x : B) : p b x = ⟨x, s b x⟩ :=
    htransport (hp b x) (p b x).2
  have hsection (b x : B) (hx : x ∈ U b) :
      (t b).toOpenPartialHomeomorph.symm (x, 1) = ⟨x, s b x⟩ := by
    rw [← hps]
    dsimp [p]
    rw [ite_eq_left hx]
  have hcolumn (b : B) (i : Fin r) :
      ContMDiffOn I (I.prod 𝓘(ℝ, Rr)) ∞
        (fun x ↦ (⟨x, s b x (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
          TotalSpace Rr V)) (U b) := by
    apply (contMDiffOn_orthogonalFrameAtlas_columns r V I b i).congr
    intro x hx
    exact congrArg (fun a : P ↦
      (⟨a.1, a.2 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ : TotalSpace Rr V))
      (hsection b x hx).symm
  -- The norm equation uses the Euclidean direct sum, retaining the actual real coordinate.
  have hsphere (y : OrthogonalSphere r) : ‖y.val.fst‖ ^ 2 + y.val.snd ^ 2 = 1 := by
    have hy := norm_eq_of_mem_sphere y
    have hnorm := WithLp.prod_norm_sq_eq_of_L2 y.val
    rw [hy] at hnorm
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using hnorm.symm
  let raw (a : P) (y : OrthogonalSphere r) : SphereCompactification r V :=
    ⟨((⟨a.1, a.2 y.val.fst⟩ : TotalSpace Rr V), y.val.snd), by
      change ‖a.2 y.val.fst‖ ^ 2 + y.val.snd ^ 2 = 1
      rw [a.2.norm_map]
      exact hsphere y⟩
  let e₀ : Z → SphereCompactification r V :=
    Quotient.lift (fun a : P × OrthogonalSphere r ↦ raw a.1 a.2) (by
      intro a c hac
      rcases hac with ⟨g, rfl⟩
      rcases a with ⟨⟨x, f⟩, y⟩
      apply Subtype.ext
      change ((⟨x, f y.val.fst⟩ : TotalSpace Rr V), y.val.snd) =
        ((⟨x, f ((orthogonalEuclideanIsometry r g)
          ((orthogonalEuclideanIsometry r g⁻¹) y.val.fst))⟩ : TotalSpace Rr V),
          y.val.snd)
      rw [map_inv, LinearIsometryEquiv.inv_def,
        LinearIsometryEquiv.apply_symm_apply])
  have he₀ (a : P) (y : OrthogonalSphere r) :
      (e₀ (associatedBundleMk G P (OrthogonalSphere r) a y)).val =
        ((⟨a.1, a.2 y.val.fst⟩ : TotalSpace Rr V), y.val.snd) := rfl
  have he₀_base (z : Z) : (e₀ z).val.1.proj = q z := by
    induction z using Quotient.inductionOn with
    | h a => rfl
  have hinj : Function.Injective e₀ := by
    intro z w hzw
    induction z using Quotient.inductionOn with
    | h a =>
      induction w using Quotient.inductionOn with
      | h c =>
        obtain ⟨g, hg, _⟩ := S.toIsPrincipalBundle.existsUnique_smul a.1 c.1
          (congrArg (fun y : SphereCompactification r V ↦ y.val.1.proj) hzw)
        have heq : e₀ (associatedBundleMk G P (OrthogonalSphere r) a.1 a.2) =
            e₀ (associatedBundleMk G P (OrthogonalSphere r) a.1 (g • c.2)) := by
          rw [← associatedBundleMk_smul, hg]
          exact hzw
        have hy : a.2 = g • c.2 := by
          apply Subtype.ext
          apply WithLp.ofLp_injective 2
          apply Prod.ext
          · apply a.1.2.injective
            exact TotalSpace.mk_injective a.1.1
              (congrArg (fun y : SphereCompactification r V ↦ y.val.1) heq)
          · exact congrArg (fun y : SphereCompactification r V ↦ y.val.2) heq
        change associatedBundleMk G P (OrthogonalSphere r) a.1 a.2 =
          associatedBundleMk G P (OrthogonalSphere r) c.1 c.2
        rw [hy, ← associatedBundleMk_smul, hg]
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨⟨⟨x, v⟩, a⟩, ha⟩
    let f := s x x
    let y : OrthogonalSphere r := ⟨WithLp.toLp 2 (f.symm v, a), by
      rw [Metric.mem_sphere, dist_zero_right]
      have hnorm := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (f.symm v, a))
      change ‖WithLp.toLp 2 (f.symm v, a)‖ ^ 2 = ‖f.symm v‖ ^ 2 + ‖a‖ ^ 2 at hnorm
      simp only [LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs] at hnorm
      change ‖v‖ ^ 2 + a ^ 2 = 1 at ha
      have hnonneg := norm_nonneg (WithLp.toLp 2 (f.symm v, a))
      nlinarith⟩
    refine ⟨associatedBundleMk G P (OrthogonalSphere r) ⟨x, f⟩ y, ?_⟩
    apply Subtype.ext
    change ((⟨x, f (f.symm v)⟩ : TotalSpace Rr V), a) = ((⟨x, v⟩ : TotalSpace Rr V), a)
    rw [f.apply_symm_apply]
  let e := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩
  have he_local (b x : B) (y : OrthogonalSphere r) (hx : x ∈ U b) :
      (e ((T b).toOpenPartialHomeomorph.symm (x, y))).val =
        ((⟨x, s b x y.val.fst⟩ : TotalSpace Rr V), y.val.snd) := by
    change (e₀ ((T b).toOpenPartialHomeomorph.symm (x, y))).val = _
    rw [hinverse b x y hx, hsection b x hx]
    rfl
  have he_chart (b : B) (z : Z) (hz : z ∈ (T b).source) :
      (e z).val =
        ((⟨(T b z).1, s b (T b z).1 (T b z).2.val.fst⟩ : TotalSpace Rr V),
          (T b z).2.val.snd) := by
    have hTw : (T b z).1 ∈ U b := by
      rw [(T b).coe_fst hz, ← hbase b]
      exact (T b).mem_source.mp hz
    have hformula := he_local b (T b z).1 (T b z).2 hTw
    have hinv : (T b).toOpenPartialHomeomorph.symm ((T b z).1, (T b z).2) = z :=
      (T b).toOpenPartialHomeomorph.left_inv hz
    rwa [hinv] at hformula
  -- Smoothness of frame evaluation follows from the finite expansion in the same smooth columns.
  have hexpand (b x : B) (v : Rr) :
      s b x v = Finset.univ.sum (fun i : Fin r ↦
        v i • s b x (EuclideanSpace.basisFun (Fin r) ℝ i)) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin r) ℝ).sum_repr v]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr]
  have hlinear (b : B) :
      ContMDiffOn (I.prod 𝓘(ℝ, Rr)) (I.prod 𝓘(ℝ, Rr)) ∞
        (fun a : B × Rr ↦ (⟨a.1, s b a.1 a.2⟩ : TotalSpace Rr V))
        (U b ×ˢ Set.univ) := by
    intro a ha
    let eV := trivializationAt Rr V a.1
    have haV : a.1 ∈ eV.baseSet := mem_baseSet_trivializationAt Rr V a.1
    apply (eV.contMDiffWithinAt_iff ((eV.mem_source).mpr haV)).mpr
    refine ⟨contMDiffWithinAt_fst, ?_⟩
    have hsum : ContMDiffWithinAt (I.prod 𝓘(ℝ, Rr)) 𝓘(ℝ, Rr) ∞
        (fun z : B × Rr ↦ Finset.univ.sum (fun i : Fin r ↦
          z.2 i • (eV (⟨z.1, s b z.1 (EuclideanSpace.basisFun (Fin r) ℝ i)⟩ :
            TotalSpace Rr V)).2)) (U b ×ˢ Set.univ) a := by
      apply contMDiffWithinAt_finsetSum
      intro i _
      have hfst : ContMDiffOn (I.prod 𝓘(ℝ, Rr)) I ∞
          (fun z : B × Rr ↦ z.1) (U b ×ˢ Set.univ) := contMDiffOn_fst
      have hcol := ((hcolumn b i).comp hfst
        (fun _ hz ↦ hz.1)) a ha
      have hcol' := ((eV.contMDiffWithinAt_iff ((eV.mem_source).mpr haV)).mp hcol).2
      have hsnd : ContMDiffWithinAt (I.prod 𝓘(ℝ, Rr)) 𝓘(ℝ, Rr) ∞
          (fun z : B × Rr ↦ z.2) (U b ×ˢ Set.univ) a := contMDiffWithinAt_snd
      exact ((EuclideanSpace.proj i).contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt
        a hsnd).smul hcol'
    apply hsum.congr_of_eventuallyEq_of_mem _ ha
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      ((eV.open_baseSet.preimage continuous_fst).mem_nhds haV)] with z hz
    rw [hexpand b z.1 z.2]
    change (eV.linearEquivAt ℝ z.1 hz) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact map_smul (eV.linearEquivAt ℝ z.1 hz) (z.2 i) _
  have hcharts (b : B) :
      ContMDiffOn Q J ∞ (T b) (T b).source ∧
        ContMDiffOn J Q ∞ (T b).toOpenPartialHomeomorph.symm (T b).target :=
    (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
  let split := WithLp.prodContinuousLinearEquiv 2 ℝ Rr ℝ
  have hhoriz : ContMDiff J 𝓘(ℝ, Rr) ∞
      (fun a : B × OrthogonalSphere r ↦ a.2.val.fst) :=
    (ContinuousLinearMap.fst ℝ Rr ℝ).contDiff.contMDiff.comp
      (split.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp contMDiff_snd))
  have hvert : ContMDiff J 𝓘(ℝ, ℝ) ∞
      (fun a : B × OrthogonalSphere r ↦ a.2.val.snd) :=
    (ContinuousLinearMap.snd ℝ Rr ℝ).contDiff.contMDiff.comp
      (split.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp contMDiff_snd))
  have hlocal_smooth (b : B) : ContMDiffOn J K ∞
      (fun a : B × OrthogonalSphere r ↦
        ((⟨a.1, s b a.1 a.2.val.fst⟩ : TotalSpace Rr V), a.2.val.snd))
      (U b ×ˢ Set.univ) :=
    ((hlinear b).comp (contMDiffOn_fst.prodMk hhoriz.contMDiffOn)
      (fun _ hz ↦ ⟨hz.1, Set.mem_univ _⟩)).prodMk hvert.contMDiffOn
  have he_smooth : ContMDiff Q K ∞ (fun z : Z ↦ (e z).val) := by
    intro z
    let b := q z
    have hz : z ∈ (T b).source := (T b).mem_source.mpr
      ((hbase b).symm ▸ S.mem_baseSet b)
    have ht : T b z ∈ U b ×ˢ Set.univ := by
      change (T b z).1 ∈ U b ∧ _
      rw [(T b).coe_fst hz]
      rw [← hbase b]
      exact ⟨(T b).mem_source.mp hz, Set.mem_univ _⟩
    have h := ((hlocal_smooth b).contMDiffAt
      (((t b).open_baseSet.prod isOpen_univ).mem_nhds ht)).comp z
        ((hcharts b).1.contMDiffAt ((T b).open_source.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [(T b).open_source.mem_nhds hz] with w hw
    exact he_chart b w hw
  -- The inverse frame coordinates are metric pairings with the original smooth columns.
  have hcoord (b x : B) (v : V x) (i : Fin r) :
      (s b x).symm v i =
        inner ℝ (s b x (EuclideanSpace.basisFun (Fin r) ℝ i)) v := by
    rw [LinearIsometryEquiv.inner_map_eq_flip, EuclideanSpace.basisFun_inner]
  let W := OrthogonalSphereAmbient r
  let L := I.prod 𝓘(ℝ, W)
  let D (b : B) := {a : TotalSpace Rr V × ℝ | a.1.proj ∈ U b}
  let back (b : B) (a : TotalSpace Rr V × ℝ) : B × W :=
    (a.1.proj, split.symm ((s b a.1.proj).symm a.1.snd, a.2))
  have hproj : ContMDiff K I ∞ (fun a : TotalSpace Rr V × ℝ ↦ a.1.proj) :=
    (Bundle.contMDiff_proj V).comp contMDiff_fst
  have hopenD (b : B) : IsOpen (D b) :=
    (t b).open_baseSet.preimage hproj.continuous
  have hback_smooth (b : B) : ContMDiffOn K L ∞ (back b) (D b) := by
    apply hproj.contMDiffOn.prodMk
    have hcoord_smooth (i : Fin r) : ContMDiffOn K 𝓘(ℝ, ℝ) ∞
        (fun a : TotalSpace Rr V × ℝ ↦ (s b a.1.proj).symm a.1.snd i) (D b) := by
      have hcol := (hcolumn b i).comp hproj.contMDiffOn (fun _ hz ↦ hz)
      have hfirst : ContMDiffOn K (I.prod 𝓘(ℝ, Rr)) ∞
          (fun a : TotalSpace Rr V × ℝ ↦ a.1) (D b) := contMDiffOn_fst
      apply (hcol.inner_bundle hfirst).congr
      intro a _
      exact hcoord b a.1.proj a.1.snd i
    have hvector : ContMDiffOn K 𝓘(ℝ, Rr) ∞
        (fun a : TotalSpace Rr V × ℝ ↦ (s b a.1.proj).symm a.1.snd) (D b) := by
      have hpi : ContMDiffOn K 𝓘(ℝ, Fin r → ℝ) ∞
          (fun a i ↦ (s b a.1.proj).symm a.1.snd i) (D b) :=
        contMDiffOn_pi_space.mpr hcoord_smooth
      exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℝ)).symm.contDiff.contMDiff
        |>.comp_contMDiffOn hpi
    exact split.symm.contDiff.contMDiff.comp_contMDiffOn
      (hvector.prodMk_space contMDiffOn_snd)
  have hback_eval (b : B) (z : Z) (hz : z ∈ (T b).source) :
      back b (e z).val = ((T b z).1, (T b z).2.val) := by
    rw [he_chart b z hz]
    dsimp [back]
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hcontinuous : Continuous e := by
    exact he_smooth.continuous.subtype_mk _
  have hinvcontinuous : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro v
    let b := v.val.1.proj
    let g (w : SphereCompactification r V) : B × OrthogonalSphere r :=
      (w.val.1.proj, ⟨(back b w.val).2, by
        rw [Metric.mem_sphere, dist_zero_right]
        have hnorm := WithLp.prod_norm_sq_eq_of_L2 (back b w.val).2
        change ‖(back b w.val).2‖ ^ 2 =
          ‖(s b w.val.1.proj).symm w.val.1.snd‖ ^ 2 + ‖w.val.2‖ ^ 2 at hnorm
        simp only [LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs] at hnorm
        have heq := w.property
        change ‖w.val.1.snd‖ ^ 2 + w.val.2 ^ 2 = 1 at heq
        have hnonneg := norm_nonneg (back b w.val).2
        nlinarith⟩)
    have hvD : v.val ∈ D b := S.mem_baseSet b
    have hbackAt := (hback_smooth b).contMDiffAt ((hopenD b).mem_nhds hvD)
    have hg : ContinuousAt g v := by
      exact (hproj.continuous.continuousAt.comp continuous_subtype_val.continuousAt).prodMk
        (tendsto_subtype_rng.mpr
          (hbackAt.continuousAt.comp continuous_subtype_val.continuousAt).snd)
    have hgv : g v ∈ (T b).target := (T b).mem_target.mpr
      ((hbase b).symm ▸ S.mem_baseSet b)
    have h := ((T b).toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      ((T b).open_target.mem_nhds hgv)).comp hg
    apply h.congr_of_eventuallyEq
    filter_upwards [((hproj.continuous.comp continuous_subtype_val).isOpen_preimage _
      (t b).open_baseSet).mem_nhds hvD] with w hw
    apply e.injective
    change e (e.symm w) = e ((T b).toOpenPartialHomeomorph.symm (g w))
    rw [e.apply_symm_apply]
    apply Subtype.ext
    have hformula := he_local b w.val.1.proj (g w).2 hw
    change (e ((T b).toOpenPartialHomeomorph.symm (g w))).val =
      ((⟨w.val.1.proj, s b w.val.1.proj ((s b w.val.1.proj).symm w.val.1.snd)⟩ :
        TotalSpace Rr V), w.val.2) at hformula
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hformula.symm
  let homeo : Z ≃ₜ SphereCompactification r V :=
    { e with continuous_toFun := hcontinuous, continuous_invFun := hinvcontinuous }
  have hsmooth : ContMDiff Q K ∞ (fun z : Z ↦ (homeo z).val) := by
    exact he_smooth
  have hderiv (z : Z) :
      Function.Injective (mfderiv Q K (fun z : Z ↦ (homeo z).val) z) := by
    -- On the same chart the smooth inverse ambient coordinates recover the native sphere inclusion.
    let b := q z
    let inc : B × OrthogonalSphere r → B × W := fun a ↦ (a.1, a.2.val)
    have hinc : ContMDiff J L ∞ inc := contMDiff_fst.prodMk
      (contMDiff_coe_sphere.comp contMDiff_snd)
    have hinc_inj (a : B × OrthogonalSphere r) :
        Function.Injective (mfderiv J L inc a) := by
      change Function.Injective
        (mfderiv J L (Prod.map (id : B → B) (Subtype.val : OrthogonalSphere r → W)) a)
      rw [mfderiv_prodMap mdifferentiableAt_id
        ((contMDiff_coe_sphere (m := ∞) a.2).mdifferentiableAt (by simp)), mfderiv_id]
      change Function.Injective
        (fun u : EB × Rr ↦ (u.1, (mvfderiv (𝓡 r) Subtype.val a.2) u.2))
      intro u v huv
      apply Prod.ext
      · exact congrArg (fun w : EB × W ↦ w.1) huv
      · exact injective_mvfderiv_subtypeVal_sphere a.2
          (congrArg (fun w : EB × W ↦ w.2) huv)
    have hz : z ∈ (T b).source := (T b).mem_source.mpr
      ((hbase b).symm ▸ S.mem_baseSet b)
    have hdT := ((hcharts b).1.contMDiffAt
      ((T b).open_source.mem_nhds hz)).mdifferentiableAt (by simp)
    have htrivialization : (T b).toOpenPartialHomeomorph.MDifferentiable Q J :=
      ⟨(hcharts b).1.mdifferentiableOn (by simp),
        (hcharts b).2.mdifferentiableOn (by simp)⟩
    have hTinj : Function.Injective (mfderiv Q J (T b) z) := by
      exact htrivialization.mfderiv_injective hz
    have hvD : (homeo z).val ∈ D b := by
      change (e₀ z).val.1.proj ∈ U b
      rw [he₀_base]
      exact S.mem_baseSet b
    have hdback := ((hback_smooth b).contMDiffAt
      ((hopenD b).mem_nhds hvD)).mdifferentiableAt (by simp)
    have hsame : (back b ∘ (fun w : Z ↦ (homeo w).val)) =ᶠ[nhds z] (inc ∘ T b) := by
      filter_upwards [(T b).open_source.mem_nhds hz] with w hw
      exact hback_eval b w hw
    have hd_same :
        (mfderiv K L (back b) (homeo z).val).comp
          (mfderiv Q K (fun w : Z ↦ (homeo w).val) z) =
        (tangentSpaceCast L (inc (T b z)) (back b (homeo z).val)).toContinuousLinearMap.comp
          ((mfderiv J L inc (T b z)).comp (mfderiv Q J (T b) z)) := by
      rw [← mfderiv_comp z hdback ((hsmooth z).mdifferentiableAt (by simp)),
        hsame.mfderiv_eq,
        mfderiv_comp z ((hinc (T b z)).mdifferentiableAt (by simp)) hdT]
      rfl
    intro u v huv
    apply hTinj
    apply hinc_inj (T b z)
    apply (tangentSpaceCast L (inc (T b z)) (back b (homeo z).val)).injective
    have heq := congrArg (mfderiv K L (back b) (homeo z).val) huv
    change ((mfderiv K L (back b) (homeo z).val).comp
      (mfderiv Q K (fun w : Z ↦ (homeo w).val) z)) u =
        ((mfderiv K L (back b) (homeo z).val).comp
          (mfderiv Q K (fun w : Z ↦ (homeo w).val) z)) v at heq
    rw [hd_same] at heq
    exact heq
  refine ⟨homeo, he₀, ?_⟩
  let : ChartedSpace ((EB × Rr) × ℝ) (TotalSpace Rr V × ℝ) :=
    inferInstanceAs
      (ChartedSpace (ModelProd (ModelProd EB Rr) ℝ) (TotalSpace Rr V × ℝ))
  let : IsManifold 𝓘(ℝ, (EB × Rr) × ℝ) ∞ (TotalSpace Rr V × ℝ) := by
    simpa only [modelWithCornersSelf_prod] using
      (inferInstance : IsManifold K ∞ (TotalSpace Rr V × ℝ))
  have hmodel : K =
      𝓘(ℝ, (EB × Rr) × ℝ) := by
    dsimp [K, I]
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
  refine ⟨?_, Topology.IsEmbedding.subtypeVal.comp homeo.isEmbedding⟩
  change Manifold.IsImmersion Q K ∞ (fun z : Z ↦ (homeo z).val)
  rw [hmodel] at hsmooth hderiv ⊢
  exact isImmersion_of_injective_mfderiv ⟨_, hsmooth⟩ hderiv

/-- The homeomorphism selected with its original frame formula and smooth embedding certificate. -/
def frameSphereHomeomorph : Z ≃ₜ SphereCompactification r V :=
  (exists_frameSphereHomeomorph (EB := EB) r V).choose

/-- The selected identification retains both its original formula and its smooth geometry. -/
theorem frameSphereHomeomorph_spec :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    (∀ (p : P) (y : OrthogonalSphere r),
      (frameSphereHomeomorph (EB := EB) r V
        (associatedBundleMk G P (OrthogonalSphere r) p y)).val =
          ((⟨p.1, p.2 y.val.fst⟩ : TotalSpace Rr V), y.val.snd)) ∧
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EB × Rr)
      ((𝓘(ℝ, EB).prod 𝓘(ℝ, Rr)).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : Z ↦ (frameSphereHomeomorph (EB := EB) r V z).val) := by
  /- Use both components of the same existence witness used by the selector.
  In particular, the source atlas and the original target total topology have
  not changed between the exact formula and the smooth-embedding assertion. -/
  exact (exists_frameSphereHomeomorph (EB := EB) r V).choose_spec

end AtiyahSinger
