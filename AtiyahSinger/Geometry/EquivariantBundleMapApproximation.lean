/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleMapAverage
public import AtiyahSinger.Geometry.HermitianMetric
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Topology.BundleIsoHomotopy

import Mathlib.Analysis.Convex.Integral

/-!
# Equivariant smoothing of maps between the original smooth bundles

Public module ID: M1174.

For a compact group with jointly smooth actions on a compact smooth base
and the given complex bundles, continuous equivariant maps admit arbitrarily
close smooth equivariant approximations.
The error is measured by specified smooth Hermitian forms, without replacing
the original fiber norms. These forms need not be invariant. Local constant
matrices are chosen close before every group translate, using compactness
of the group and model unit sphere. A finite smooth partition glues them
before taking the actual Haar average.

A continuous equivariant bundle isomorphism can therefore be joined to a smooth
one through actual continuous equivariant bundle isomorphisms. The initial map
is only continuous, so the resulting cylinder is not asserted to be smooth.
Both endpoints, all intermediate maps and the original actions are retained.

Sources: SG Appendix A, Remark A.1, for ordinary smooth bundle classification;
SG III.9 for the averaging method. The quantitative map approximation and the
fixed-bundle equivariant homotopy are explicit standard supplements. This file
assumes the bundles and their actions are already smooth. It does not smooth a
continuous bundle action, remove locally varying ranks, or realize an arbitrary
equivariant K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle MeasureTheory TopologicalSpace Topology
open scoped Manifold ContDiff unitInterval

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

variable
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hC hE hF hG hGC hGT hAction hσE hσF

set_option linter.unusedSectionVars false in
/-- Continuous equivariant bundle maps admit smooth equivariant approximations in given metrics. -/
theorem Hom.exists_equivariant_smooth_approximation
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Hom E F)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.IsEquivariant σE σF)
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F) (ε : ℝ) (hε : 0 < ε) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ b : Hom E F, IsSmoothBundleMap (n := n) (r := r) (q := q) b.linearMap ∧
      b.IsEquivariant σE σF ∧ ∀ (x : M) (v : E x),
        (k.pairing x (b.linearMap x v - a.linearMap x v)
          (b.linearMap x v - a.linearMap x v)).re ≤
            ε ^ 2 * (h.pairing x v v).re := by
  /- Stage 1: express the original map in its smooth local frames. The
  constant matrix fixed at each base point agrees with the map there.
  Continuity of the given metric forms and original actions, and
  compactness of G times the model unit sphere, give a neighborhood
  where its error is small before every group translate. Rescaling
  gives the bound for every vector, with the zero vector handled directly.
  No continuous variation of the original fiber norms is assumed.
  Stage 2: take a finite subcover of the compact base and a subordinate
  smooth partition of unity. Glue these local constant matrices. Smooth
  original transitions give smoothness in arbitrary original frames;
  convexity of the metric error balls preserves every translated bound.
  The specified metrics need not be invariant.
  Stage 3: take the normalized Haar average of this same smooth map.
  Use its smooth-preservation theorem and Haar equivariance. The original
  action square for a identifies each conjugated error with an error
  at the same base point; convexity of the closed metric ball bounds
  their integral. Continuous group inversion suffices; no LieGroup
  premise is used.
  Stage 4: square the nonnegative metric estimate. This includes the
  zero vector, so the conclusion uses ≤. No norm on the space of all
  bundle maps is introduced. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  let : ∀ x, NormedSpace ℝ (F x) := fun x ↦ NormedSpace.restrictScalars ℝ ℂ (F x)
  let : ∀ x, IsScalarTower ℝ ℂ (F x) := fun x ↦
    IsScalarTower.restrictScalars ℝ ℂ (F x)
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  -- The original smooth Gram matrices give continuity without replacing any fiber norm.
  have hHquad : Continuous (fun z : TotalSpace Unit E ↦
      (h.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin r)) E
    have hb : Continuous (fun z : TotalSpace Unit E ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin r)) E
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.proj
    let U : Set (TotalSpace Unit E) := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit E ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin r) : ContinuousOn
        (fun w : TotalSpace Unit E ↦ h.gramMatrix e w.proj i j) U :=
      (h.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit E ↦
        (∑ i : Fin r, ∑ j : Fin r,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * h.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (h.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  have hKquad : Continuous (fun z : TotalSpace Unit F ↦
      (k.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin q)) F
    have hb : Continuous (fun z : TotalSpace Unit F ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin q)) F
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj
    let U : Set (TotalSpace Unit F) := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit F ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin q) : ContinuousOn
        (fun w : TotalSpace Unit F ↦ k.gramMatrix e w.proj i j) U :=
      (k.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit F ↦
        (∑ i : Fin q, ∑ j : Fin q,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * k.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (k.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  let H (x : M) : Seminorm ℂ (E x) := by
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact @normSeminorm ℂ (E x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  let K (x : M) : Seminorm ℂ (F x) := by
    let : InnerProductSpace.Core ℂ (F x) := k.toCore x
    exact @normSeminorm ℂ (F x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  have hH (x : M) (v : E x) : H x v = Real.sqrt (h.pairing x v v).re := rfl
  have hK (x : M) (v : F x) : K x v = Real.sqrt (k.pairing x v v).re := rfl
  have hHc : Continuous (fun z : TotalSpace Unit E ↦ H z.proj z.snd) :=
    hHquad.sqrt
  have hKc : Continuous (fun z : TotalSpace Unit F ↦ K z.proj z.snd) :=
    hKquad.sqrt
  -- Local constant matrices are arbitrarily close before every original group translate.
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  let A (x : M) : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    ((f x).linearMapAt ℂ x |>.comp
      ((a.linearMap x).comp ((e x).symmL ℂ x).toLinearMap)).toContinuousLinearMap
  let S (x y : M) : E y →ₗ[ℂ] F y :=
    ((f x).symmL ℂ y).toLinearMap.comp
      ((A x).toLinearMap.comp ((e x).linearMapAt ℂ y))
  have hSself (x : M) : S x x = a.linearMap x := by
    ext v
    have he : x ∈ (e x).baseSet := mem_baseSet_trivializationAt _ _ _
    have hf : x ∈ (f x).baseSet := mem_baseSet_trivializationAt _ _ _
    change (f x).symmL ℂ x ((f x).continuousLinearMapAt ℂ x
      (a.linearMap x ((e x).symmL ℂ x ((e x).continuousLinearMapAt ℂ x v)))) = _
    rw [(e x).symmL_continuousLinearMapAt (R := ℂ) he,
      (f x).symmL_continuousLinearMapAt (R := ℂ) hf]
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (e x).baseSet ∩ (f x).baseSet ∧
      ∀ y ∈ U, ∀ (g : G) (v : E y),
        K (g • y) (σF.linearMap g y ((S x y - a.linearMap y) v)) ≤
          ε * H (g • y) (σE.linearMap g y v) := by
    let W : Set M := (e x).baseSet ∩ (f x).baseSet
    have hW : IsOpen W := (e x).open_baseSet.inter (f x).open_baseSet
    have hx : x ∈ W := ⟨mem_baseSet_trivializationAt _ _ _,
      mem_baseSet_trivializationAt _ _ _⟩
    let x₀ : W := ⟨x, hx⟩
    let T := W × (G × EuclideanSpace ℂ (Fin r))
    let v (p : T) : E p.1.val := (e x).symmL ℂ p.1.val p.2.2
    have hv : Continuous (fun p : T ↦ (⟨p.1.val, v p⟩ : TotalSpace Unit E)) := by
      apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin r)) E _).mpr
      have hc := (e x).continuousOn_symm.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd.snd)
        (fun p : T ↦ ⟨p.1.property.1, Set.mem_univ _⟩)
      apply hc.congr
      intro p
      change (⟨p.1.val, (e x).symm p.1.val p.2.2⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨p.1.val, v p⟩
      exact congrArg (fun w : E p.1.val ↦
        (⟨p.1.val, w⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
        ((e x).symmL_apply p.1.property.1 p.2.2).symm
    have hac := a.continuous_total.comp hv
    have hcoord : Continuous (fun p : T ↦
        ((f x) ⟨p.1.val, a.linearMap p.1.val (v p)⟩).2) := by
      exact ((f x).continuousOn.comp_continuous
        ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp hac)
        (fun p ↦ (f x).mem_source.mpr p.1.property.2)).snd
    have hdiff : Continuous (fun p : T ↦
        (⟨p.1.val, (S x p.1.val - a.linearMap p.1.val) (v p)⟩ :
          TotalSpace Unit F)) := by
      apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
      have hc := (f x).continuousOn_symm.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (((A x).continuous.comp continuous_snd.snd).sub hcoord))
        (fun p : T ↦ ⟨p.1.property.2, Set.mem_univ _⟩)
      apply hc.congr
      intro p
      change (⟨p.1.val, (f x).symm p.1.val
        (A x p.2.2 - ((f x) ⟨p.1.val, a.linearMap p.1.val (v p)⟩).2)⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin q)) F) = _
      apply congrArg (fun w : F p.1.val ↦
        (⟨p.1.val, w⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F))
      rw [← (f x).symmL_apply (R := ℂ) p.1.property.2]
      rw [← (f x).continuousLinearMapAt_apply_of_mem ℂ p.1.property.2]
      change (f x).symmL ℂ p.1.val
          (A x p.2.2 - (f x).continuousLinearMapAt ℂ p.1.val
            (a.linearMap p.1.val (v p))) =
        (f x).symmL ℂ p.1.val (A x ((e x).continuousLinearMapAt ℂ p.1.val
          ((e x).symmL ℂ p.1.val p.2.2))) - a.linearMap p.1.val (v p)
      rw [map_sub, (f x).symmL_continuousLinearMapAt (R := ℂ) p.1.property.2,
        (e x).continuousLinearMapAt_symmL (R := ℂ) p.1.property.1]
    let d (p : T) : ℝ :=
      ε * H (p.2.1 • p.1.val) (σE.linearMap p.2.1 p.1.val (v p)) -
        K (p.2.1 • p.1.val)
          (σF.linearMap p.2.1 p.1.val ((S x p.1.val - a.linearMap p.1.val) (v p)))
    have hd : Continuous d :=
      (continuous_const.mul (hHc.comp (σE.continuous_action.comp
        (continuous_snd.fst.prodMk hv)))).sub
        (hKc.comp (σF.continuous_action.comp (continuous_snd.fst.prodMk hdiff)))
    have hpos (p : G × EuclideanSpace ℂ (Fin r))
        (hp : p ∈ Set.univ ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) :
        0 < d (x₀, p) := by
      have hu : p.2 ≠ 0 := by
        intro hu
        simpa [hu] using hp.2
      have hv₀ : v (x₀, p) ≠ 0 := by
        intro hz
        apply hu
        have he := (e x).continuousLinearMapAt_symmL (R := ℂ) hx.1 p.2
        rw [show (e x).symmL ℂ x p.2 = 0 from hz, map_zero] at he
        exact he.symm
      have hs : σE.linearMap p.1 x (v (x₀, p)) ≠ 0 :=
        by
          simpa only [map_zero] using (σE.linearMap_bijective p.1 x).1.ne_iff.mpr hv₀
      have hh : 0 < H (p.1 • x) (σE.linearMap p.1 x (v (x₀, p))) := by
        rw [hH, Real.sqrt_pos]
        exact h.pairing_self_pos _ _ hs
      simpa [d, x₀, hSself, sub_self, map_zero] using mul_pos hε hh
    have hcompact := isCompact_univ (X := G) |>.prod
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1)
    have hevent : ∀ᶠ y : W in 𝓝 x₀,
        ∀ p ∈ Set.univ ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1,
          0 < d (y, p) :=
      hcompact.eventually_forall_of_forall_eventually
        (fun p hp ↦ (hd.continuousAt (x := (x₀, p))).eventually (Ioi_mem_nhds (hpos p hp)))
    obtain ⟨V, hsub, hV, hxV⟩ := mem_nhds_iff.mp hevent
    have hVo : IsOpen ((Subtype.val : W → M) '' V) :=
      hW.isOpenMap_subtype_val _ hV
    refine ⟨Subtype.val '' V, hVo, ⟨x₀, hxV, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨y, _, rfl⟩
      exact y.property
    · rintro y ⟨y', hy', rfl⟩ g w
      by_cases hw : w = 0
      · simp [hw]
      let u := (e x) ⟨y'.val, w⟩ |>.2
      have hu : u ≠ 0 := by
        intro hz
        apply hw
        have he := (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property.1 w
        rw [(e x).continuousLinearMapAt_apply_of_mem ℂ y'.property.1] at he
        change (e x).symmL ℂ y'.val u = w at he
        rw [hz, map_zero] at he
        exact he.symm
      let u₀ := (‖u‖⁻¹ : ℂ) • u
      have hu₀ : u₀ ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1 := by
        simpa [u₀, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hu
      have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hrecover : (‖u‖ : ℂ) • v (y', (g, u₀)) = w := by
        dsimp only [v, u₀]
        rw [map_smul, smul_smul]
        rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu_norm.ne'), one_smul]
        dsimp only [u]
        rw [← (e x).continuousLinearMapAt_apply_of_mem ℂ y'.property.1]
        exact (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property.1 w
      have hbound := le_of_lt (sub_pos.mp (hsub hy' (g, u₀) ⟨Set.mem_univ _, hu₀⟩))
      conv_lhs => rw [← hrecover]
      conv_rhs => rw [← hrecover]
      simp only [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu_norm.le]
      nlinarith [mul_le_mul_of_nonneg_left hbound hu_norm.le]
  choose U hUopen hxU hUframe hUerror using hlocal
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  have hfinitecover : Set.univ ⊆ ⋃ j : s, U j := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ
      (fun j : s ↦ U j) (fun j ↦ hUopen j) hfinitecover
  let C (x : M) : E x →ₗ[ℂ] F x := ∑ j : s, ((ρ j x : ℝ) : ℂ) • S j x
  have hsumρ (x : M) : ∑ j : s, ρ j x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
  -- In arbitrary original frames, the supported constant matrices have smooth transitions.
  have hCsmooth : IsSmoothBundleMap (n := n) (r := r) (q := q) C := by
    intro d hd t ht col x hx
    let := hd
    let := ht
    let Q (j : s) (y : M) :=
      (t ⟨y, S j y (d.symmL ℂ y (EuclideanSpace.single col 1))⟩).2
    have hsmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
        (fun y ↦ ∑ᶠ j : s, ρ j y • Q j y) x := by
      apply ρ.contMDiffAt_finsum
      intro j hj
      have hframes := hUframe j (hρ j hj)
      have hinput := (IsSmoothComplexBundle.contMDiffOn_coordChange
        (n := n) (E := E) d (e j)).contMDiffAt
          ((d.open_baseSet.inter (e j).open_baseSet).mem_nhds ⟨hx.1, hframes.1⟩)
      have houtput := (IsSmoothComplexBundle.contMDiffOn_coordChange
        (n := n) (E := F) (f j) t).contMDiffAt
          (((f j).open_baseSet.inter t.open_baseSet).mem_nhds ⟨hframes.2, hx.2⟩)
      have heval : ContDiff ℝ ∞
          (fun p : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
              (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦
            p.2 (A j (p.1 (EuclideanSpace.single col 1)))) :=
        (show ContDiff ℂ ∞ _ from contDiff_snd.clm_apply
          ((A j).contDiff.comp (contDiff_fst.clm_apply contDiff_const))).restrict_scalars ℝ
      have hc := heval.comp_contMDiffAt (hinput.prodMk_space houtput)
      apply hc.congr_of_eventuallyEq
      filter_upwards [d.open_baseSet.mem_nhds hx.1,
        t.open_baseSet.mem_nhds hx.2, (e j).open_baseSet.mem_nhds hframes.1,
        (f j).open_baseSet.mem_nhds hframes.2] with y hyd hyt hye hyf
      dsimp only [Q, S, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      dsimp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [d.coordChangeL_apply (R := ℂ) (e j) ⟨hyd, hye⟩,
        (f j).coordChangeL_apply (R := ℂ) t ⟨hyf, hyt⟩,
        d.symmL_apply hyd, (f j).symmL_apply hyf,
        (e j).coe_linearMapAt_of_mem hye]
    have heq (y : M) (hy : y ∈ d.baseSet ∩ t.baseSet) :
        (t ⟨y, C y (d.symmL ℂ y (EuclideanSpace.single col 1))⟩).2 =
          ∑ᶠ j : s, ρ j y • Q j y := by
      rw [finsum_eq_sum_of_fintype,
        ← t.continuousLinearMapAt_apply_of_mem ℂ hy.2]
      simp only [C, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
        t.continuousLinearMapAt_apply_of_mem ℂ hy.2]
      rfl
    apply (hsmooth.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(d.open_baseSet.inter t.open_baseSet).mem_nhds hx] with y hy
    exact heq y hy
  have hCcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, C z.proj z.snd⟩ : TotalSpace Unit F)) := by
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt, ?_⟩
    let d := e z.proj
    let t := f z.proj
    have hyd : z.proj ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
    have hyt : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt _ _ _
    let L (y : M) : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
      ∑ j : Fin r, ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
          ((t ⟨y, C y (d.symmL ℂ y (EuclideanSpace.single j 1))⟩).2)
    have hL : ContinuousOn L (d.baseSet ∩ t.baseSet) := by
      apply continuousOn_finsetSum
      intro j _
      exact (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).continuous
          |>.comp_continuousOn (hCsmooth d t j).continuousOn
    have hLc := (hL.continuousAt
      ((d.open_baseSet.inter t.open_baseSet).mem_nhds ⟨hyd, hyt⟩)).comp
        (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt
    have hdc := ((d.continuousAt (d.mem_source.mpr hyd)).comp
      (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).continuousAt).snd
    apply (hLc.clm_apply hdc).congr_of_eventuallyEq
    filter_upwards [((d.open_baseSet.inter t.open_baseSet).preimage
      (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E)).mem_nhds ⟨hyd, hyt⟩]
      with w hw
    let B := (t.linearMapAt ℂ w.proj).comp
      ((C w.proj).comp (d.symmL ℂ w.proj).toLinearMap)
    have hmap := congrArg B ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr
      (d ⟨w.proj, w.snd⟩).2)
    simpa [L, B, d, t, e, f, unitTotalEquiv, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, t.coe_linearMapAt_of_mem hw.2,
      d.symmL_apply hw.1, d.symm_apply_apply_mk hw.1] using hmap.symm
  let c : Hom E F := ⟨C, hCcontinuous⟩
  have hCerror (x : M) (g : G) (v : E x) :
      K (g • x) (σF.linearMap g x ((C x - a.linearMap x) v)) ≤
        ε * H (g • x) (σE.linearMap g x v) := by
    let B : Set (F (g • x)) :=
      (K (g • x)).closedBall 0 (ε * H (g • x) (σE.linearMap g x v))
    have hmem : ∑ᶠ j : s, ρ j x •
        σF.linearMap g x ((S j x - a.linearMap x) v) ∈ B := by
      apply ((K (g • x)).convex_closedBall 0 _).finsum_mem
        (fun j ↦ ρ.nonneg j x) (ρ.sum_eq_one (Set.mem_univ x))
      intro j hj
      rw [Seminorm.mem_closedBall, sub_zero]
      exact hUerror j x (hρ j (subset_closure (Function.mem_support.mpr hj))) g v
    have heq : (∑ᶠ j : s, ρ j x •
        σF.linearMap g x ((S j x - a.linearMap x) v)) =
          σF.linearMap g x ((C x - a.linearMap x) v) := by
      rw [finsum_eq_sum_of_fintype]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), C,
        LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        map_sub, map_smul, map_sum, smul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_smul]
      have hw : (∑ j : s, (ρ j x : ℂ)) = (1 : ℂ) := by exact_mod_cast hsumρ x
      exact (congrArg (fun z : ℂ ↦ z • σF.linearMap g x (a.linearMap x v)) hw).trans
        (one_smul ℂ _)
    rw [heq, Seminorm.mem_closedBall, sub_zero] at hmem
    exact hmem
  -- Average this same smooth map, using normalized Haar in each original target fiber.
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  let b := c.equivariantAverage σE σF
  refine ⟨b, c.isSmoothBundleMap_equivariantAverage σE σF IG hσE hσF hCsmooth,
    c.isEquivariant_equivariantAverage σE σF, ?_⟩
  intro x v
  let Z (g : G) : F x := (smul_inv_smul g x) ▸
    (σF.linearMap g (g⁻¹ • x)
      (c.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v)))
  have hZtotal (g : G) : (⟨x, Z g⟩ : TotalSpace Unit F) =
      g • c.totalMap (g⁻¹ • (⟨x, v⟩ : TotalSpace Unit E)) := by
    change (⟨x, Z g⟩ : TotalSpace Unit F) =
      ⟨g • (g⁻¹ • x), σF.linearMap g (g⁻¹ • x)
        (c.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))⟩
    simpa only [Z, eqRec_eq_cast] using
      (TotalSpace.mk_cast (F := Unit) (smul_inv_smul g x)
        (σF.linearMap g (g⁻¹ • x)
          (c.linearMap (g⁻¹ • x) (σE.linearMap g⁻¹ x v))))
  have hZcontinuous : Continuous Z := by
    apply (FiberBundle.totalSpaceMk_isEmbedding (EuclideanSpace ℂ (Fin q)) F x)
      |>.continuous_iff.mpr
    have ht : Continuous (fun g ↦ (⟨x, Z g⟩ : TotalSpace Unit F)) := by
      have hc : Continuous (fun g : G ↦
          g • c.totalMap (g⁻¹ • (⟨x, v⟩ : TotalSpace Unit E))) :=
        σF.continuous_action.comp (continuous_id.prodMk
        (c.continuous_total.comp (σE.continuous_action.comp
          (continuous_id.inv.prodMk continuous_const))))
      exact hc.congr (fun g ↦ (hZtotal g).symm)
    exact (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp ht
  have hZintegrable : Integrable Z μ :=
    hZcontinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have herror (g : G) : K x (Z g - a.linearMap x v) ≤ ε * H x v := by
    -- Cancel the same original group element on the base and in the source fiber.
    obtain ⟨y, hy⟩ := (MulAction.surjective g) x
    subst x
    obtain ⟨w, hw⟩ := (σE.linearMap_bijective g y).2 v
    subst v
    have hZ : Z g = σF.linearMap g y (C y w) := by
      apply TotalSpace.mk_injective (F := Unit) (g • y)
      rw [hZtotal]
      change g • c.totalMap (g⁻¹ • (g • (⟨y, w⟩ : TotalSpace Unit E))) = _
      rw [inv_smul_smul]
      rfl
    rw [hZ, ha g y w, ← map_sub]
    exact hCerror y g w
  let B : Set (F x) := (K x).closedBall 0 (ε * H x v)
  have hBclosed : IsClosed B := by
    have hKfiber : Continuous (K x) :=
      (Complex.continuous_re.comp ((k.continuous_pairing x).comp
        (continuous_id.prodMk continuous_id))).sqrt
    change IsClosed {w : F x | K x (w - 0) ≤ ε * H x v}
    simpa only [sub_zero] using isClosed_le hKfiber continuous_const
  have hBmem : (∫ g, Z g - a.linearMap x v ∂μ) ∈ B := by
    apply ((K x).convex_closedBall 0 _).integral_mem hBclosed
      (Filter.Eventually.of_forall ?_) (hZintegrable.sub (integrable_const _))
    intro g
    rw [Seminorm.mem_closedBall, sub_zero]
    exact herror g
  have havg : (∫ g, Z g - a.linearMap x v ∂μ) = b.linearMap x v - a.linearMap x v := by
    rw [integral_sub hZintegrable (integrable_const _), integral_const, probReal_univ, one_smul]
    exact congrArg (fun w : F x ↦ w - a.linearMap x v)
      (c.equivariantAverage_apply σE σF x v).symm
  rw [havg, Seminorm.mem_closedBall, sub_zero] at hBmem
  -- Squaring the nonnegative metric norm estimate includes every zero vector and zero rank.
  have hsquare := (sq_le_sq₀ (apply_nonneg (K x) _) (mul_nonneg hε.le
    (apply_nonneg (H x) v))).mpr hBmem
  have hkpos : 0 ≤ (k.pairing x (b.linearMap x v - a.linearMap x v)
      (b.linearMap x v - a.linearMap x v)).re := (k.toCore x).re_inner_nonneg _
  have hhpos : 0 ≤ (h.pairing x v v).re := (h.toCore x).re_inner_nonneg _
  rw [hK, hH, mul_pow, Real.sq_sqrt hkpos, Real.sq_sqrt hhpos] at hsquare
  exact hsquare

/-- A continuous equivariant isomorphism is equivariantly homotopic to a smooth isomorphism. -/
theorem Iso.exists_equivariant_smooth_homotopy
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Iso E F)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.IsEquivariant σE σF) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ b : Iso E F, IsSmoothBundleMap (n := n) (r := r) (q := q) b.toHom.linearMap ∧
      b.IsEquivariant σE σF ∧ ∃ H : IsoHomotopy a b,
        ∀ (t : I) (g : G) (x : M) (v : E x),
          H.iso.linearEquiv (t, g • x) (σE.linearMap g x v) =
            σF.linearMap g x (H.iso.linearEquiv (t, x) v) := by
  /- Stage 1: choose smooth Hermitian metrics on the two given smooth bundles.
  Continuity of the original inverse of a and compactness of the base give a
  uniform positive lower bound for its least metric singular value, using
  finitely many local frames. Rank-zero fibers have the unique isomorphism and
  require no minimum over an empty unit sphere; the empty base is vacuous.
  Stage 2: apply the preceding equivariant approximation theorem to a.toHom
  with error smaller than that positive invertibility margin. Let b be the
  resulting actual fiber map. Every affine interpolation (1-t)*a+t*b remains
  invertible in the original fibers. Hom.toIso supplies continuous
  inverses from these fiberwise bijectivity certificates.
  Stage 3: package b as the original continuous Iso, keeping its actual forward
  fiber maps. Package the affine interpolation and its continuous inverse on
  the two original cylinder pullbacks as IsoHomotopy a b. Its endpoint equations
  are exact. Both a and b intertwine the same original actions; their affine
  interpolation therefore does too at every time, since G fixes that time.
  This is a continuous equivariant path of isomorphisms, not a jointly smooth
  cylinder whose initial slice would incorrectly force a to be smooth. It
  changes no bundle, rank, total topology or prescribed group action. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  obtain ⟨h⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  obtain ⟨k⟩ := nonempty_smoothHermitianMetric (n := n) (r := q) F
  -- The original smooth Gram matrices give continuity without replacing any fiber norm.
  have hHquad : Continuous (fun z : TotalSpace Unit E ↦
      (h.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin r)) E
    have hb : Continuous (fun z : TotalSpace Unit E ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin r)) E
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.proj
    let U : Set (TotalSpace Unit E) := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit E ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin r) : ContinuousOn
        (fun w : TotalSpace Unit E ↦ h.gramMatrix e w.proj i j) U :=
      (h.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit E ↦
        (∑ i : Fin r, ∑ j : Fin r,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * h.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (h.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  have hKquad : Continuous (fun z : TotalSpace Unit F ↦
      (k.pairing z.proj z.snd z.snd).re) := by
    let := modelTopology (EuclideanSpace ℂ (Fin q)) F
    have hb : Continuous (fun z : TotalSpace Unit F ↦ z.proj) :=
      continuous_model_proj (EuclideanSpace ℂ (Fin q)) F
    apply continuous_iff_continuousAt.mpr
    intro z
    let e := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj
    let U : Set (TotalSpace Unit F) := {w | w.proj ∈ e.baseSet}
    have hU : IsOpen U := e.open_baseSet.preimage hb
    have hz : z ∈ U := mem_baseSet_trivializationAt _ _ _
    have hc : ContinuousOn
        (fun w : TotalSpace Unit F ↦ (e ⟨w.proj, w.snd⟩).2) U := by
      exact (e.continuousOn.comp
        (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).continuousOn
        (fun w hw ↦ e.mem_source.mpr hw)).snd
    have hg (i j : Fin q) : ContinuousOn
        (fun w : TotalSpace Unit F ↦ k.gramMatrix e w.proj i j) U :=
      (k.contMDiffOn_gram e i j).continuousOn.comp hb.continuousOn (fun _ hw ↦ hw)
    have hsum : ContinuousOn (fun w : TotalSpace Unit F ↦
        (∑ i : Fin q, ∑ j : Fin q,
          starRingEnd ℂ ((e ⟨w.proj, w.snd⟩).2 i) * k.gramMatrix e w.proj i j *
            (e ⟨w.proj, w.snd⟩).2 j).re) U := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact (((Complex.continuous_conj.comp_continuousOn
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).continuous.comp_continuousOn hc)).mul
          (hg i j)).mul
        ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) j).continuous.comp_continuousOn hc))
    apply (hsum.congr ?_).continuousAt (hU.mem_nhds hz)
    intro w hw
    exact congrArg Complex.re (k.pairing_eq_gramMatrix e w.proj hw w.snd w.snd)
  let H (x : M) : Seminorm ℂ (E x) := by
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact @normSeminorm ℂ (E x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  let K (x : M) : Seminorm ℂ (F x) := by
    let : InnerProductSpace.Core ℂ (F x) := k.toCore x
    exact @normSeminorm ℂ (F x) _
      InnerProductSpace.Core.toNormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.Core.toNormedSpace
  have hH (x : M) (v : E x) : H x v = Real.sqrt (h.pairing x v v).re := rfl
  have hK (x : M) (v : F x) : K x v = Real.sqrt (k.pairing x v v).re := rfl
  have hHc : Continuous (fun z : TotalSpace Unit E ↦ H z.proj z.snd) :=
    hHquad.sqrt
  have hKc : Continuous (fun z : TotalSpace Unit F ↦ K z.proj z.snd) :=
    hKquad.sqrt
  -- A compact model sphere gives a positive local lower bound, including empty spheres.
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hlocal (x : M) : ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set M,
      IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ v : E y,
        δ * H y v ≤ K y (a.linearEquiv y v) := by
    let W : Set M := (e x).baseSet
    have hW : IsOpen W := (e x).open_baseSet
    have hx : x ∈ W := mem_baseSet_trivializationAt _ _ _
    let x₀ : W := ⟨x, hx⟩
    let T := W × EuclideanSpace ℂ (Fin r)
    let v (p : T) : E p.1.val := (e x).symmL ℂ p.1.val p.2
    have hv : Continuous (fun p : T ↦ (⟨p.1.val, v p⟩ : TotalSpace Unit E)) := by
      apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin r)) E _).mpr
      have hc := (e x).continuousOn_symm.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p : T ↦ ⟨p.1.property, Set.mem_univ _⟩)
      apply hc.congr
      intro p
      change (⟨p.1.val, (e x).symm p.1.val p.2⟩ :
        TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨p.1.val, v p⟩
      exact congrArg (fun w : E p.1.val ↦
        (⟨p.1.val, w⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
        ((e x).symmL_apply p.1.property p.2).symm
    have hH₀ : Continuous (fun u : EuclideanSpace ℂ (Fin r) ↦ H x (v (x₀, u))) :=
      (hHc.comp hv).comp (continuous_const.prodMk continuous_id)
    have hK₀ : Continuous (fun u : EuclideanSpace ℂ (Fin r) ↦
        K x (a.linearEquiv x (v (x₀, u)))) :=
      (hKc.comp (a.continuous_total.comp hv)).comp
        ((continuous_const (y := x₀)).prodMk continuous_id)
    have hvpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) : v (x₀, u) ≠ 0 := by
      have hu₀ : u ≠ 0 := by
        intro hz
        simp [hz] at hu
      intro hz
      apply hu₀
      have he := (e x).continuousLinearMapAt_symmL (R := ℂ) hx u
      rw [show (e x).symmL ℂ x u = 0 from hz, map_zero] at he
      exact he.symm
    have hHpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) :
        0 < H x (v (x₀, u)) := by
      rw [hH, Real.sqrt_pos]
      exact h.pairing_self_pos _ _ (hvpos u hu)
    have hKpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) :
        0 < K x (a.linearEquiv x (v (x₀, u))) := by
      rw [hK, Real.sqrt_pos]
      apply k.pairing_self_pos
      simpa only [map_zero] using (a.linearEquiv x).injective.ne_iff.mpr (hvpos u hu)
    obtain ⟨c, hc, hcBound⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1).exists_forall_le'
        (hK₀.continuousOn.div hH₀.continuousOn (fun u hu ↦ (hHpos u hu).ne'))
        (fun u hu ↦ div_pos (hKpos u hu) (hHpos u hu))
    let δ := c / 2
    have hδ : 0 < δ := half_pos hc
    let d (p : T) : ℝ := K p.1.val (a.linearEquiv p.1.val (v p)) - δ * H p.1.val (v p)
    have hd : Continuous d := (hKc.comp (a.continuous_total.comp hv)).sub
      (continuous_const.mul (hHc.comp hv))
    have hpos (u : EuclideanSpace ℂ (Fin r))
        (hu : u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1) : 0 < d (x₀, u) := by
      have hb := (le_div_iff₀ (hHpos u hu)).mp (hcBound u hu)
      have hp := hHpos u hu
      change 0 < K x (a.linearEquiv x (v (x₀, u))) - δ * H x (v (x₀, u))
      dsimp only [δ]
      nlinarith
    have hevent : ∀ᶠ y : W in 𝓝 x₀,
        ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1, 0 < d (y, u) :=
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1).eventually_forall_of_forall_eventually
          (fun u hu ↦ (hd.continuousAt (x := (x₀, u))).eventually
            (Ioi_mem_nhds (hpos u hu)))
    obtain ⟨V, hsub, hV, hxV⟩ := mem_nhds_iff.mp hevent
    have hVo : IsOpen ((Subtype.val : W → M) '' V) := hW.isOpenMap_subtype_val _ hV
    refine ⟨δ, hδ, Subtype.val '' V, hVo, ⟨x₀, hxV, rfl⟩, ?_⟩
    rintro y ⟨y', hy', rfl⟩ w
    by_cases hw : w = 0
    · simp [hw]
    let u := (e x) ⟨y'.val, w⟩ |>.2
    have hu : u ≠ 0 := by
      intro hz
      apply hw
      have he := (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property w
      rw [(e x).continuousLinearMapAt_apply_of_mem ℂ y'.property] at he
      change (e x).symmL ℂ y'.val u = w at he
      rw [hz, map_zero] at he
      exact he.symm
    let u₀ := (‖u‖⁻¹ : ℂ) • u
    have hu₀ : u₀ ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1 := by
      simpa [u₀, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hu
    have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hrecover : (‖u‖ : ℂ) • v (y', u₀) = w := by
      dsimp only [v, u₀]
      rw [map_smul, smul_smul]
      rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu_norm.ne'), one_smul]
      dsimp only [u]
      rw [← (e x).continuousLinearMapAt_apply_of_mem ℂ y'.property]
      exact (e x).symmL_continuousLinearMapAt (R := ℂ) y'.property w
    have hbound := le_of_lt (sub_pos.mp (hsub hy' u₀ hu₀))
    conv_lhs => rw [← hrecover]
    conv_rhs => rw [← hrecover]
    simp only [map_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu_norm.le]
    nlinarith [mul_le_mul_of_nonneg_left hbound hu_norm.le]
  choose δ hδ U hUopen hxU hUbound using hlocal
  have hcover : Set.univ ⊆ ⋃ x, U x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hcover
  obtain ⟨d, hd, hdBound⟩ := (s.finite_toSet.image δ).isCompact.exists_forall_le'
    continuousOn_id (fun c hc ↦ by
      obtain ⟨x, _, rfl⟩ := hc
      exact hδ x)
  have hmargin (x : M) (v : E x) : d * H x v ≤ K x (a.linearEquiv x v) := by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact (mul_le_mul_of_nonneg_right (hdBound (δ y) ⟨y, hy, rfl⟩)
      (apply_nonneg (H x) v)).trans (hUbound y x hxy v)
  -- Approximate the same original map more finely than this invertibility margin.
  obtain ⟨b, hbsmooth, hbequiv, hbclose⟩ :=
    a.toHom.exists_equivariant_smooth_approximation IG σE σF hσE hσF ha h k (d / 2)
      (half_pos hd)
  have herror (x : M) (v : E x) :
      K x (b.linearMap x v - a.linearEquiv x v) ≤ d / 2 * H x v := by
    apply (sq_le_sq₀ (apply_nonneg (K x) _) (mul_nonneg (half_pos hd).le
      (apply_nonneg (H x) v))).mp
    have hkpos : 0 ≤ (k.pairing x (b.linearMap x v - a.linearEquiv x v)
        (b.linearMap x v - a.linearEquiv x v)).re := (k.toCore x).re_inner_nonneg _
    have hhpos : 0 ≤ (h.pairing x v v).re := (h.toCore x).re_inner_nonneg _
    rw [hK, hH, mul_pow, Real.sq_sqrt hkpos, Real.sq_sqrt hhpos]
    exact hbclose x v
  let L (t : I) (x : M) : E x →ₗ[ℂ] F x :=
    a.toHom.linearMap x + (((t : ℝ) : ℂ) • (b.linearMap x - a.toHom.linearMap x))
  have hLzero (x : M) (v : E x) : L 0 x v = a.linearEquiv x v := by
    simp [L, Iso.toHom]
  have hLone (x : M) (v : E x) : L 1 x v = b.linearMap x v := by
    simp [L]
  have hLinj (t : I) (x : M) : Function.Injective (L t x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hv₀
    have hHpos : 0 < H x v := by
      rw [hH, Real.sqrt_pos]
      exact h.pairing_self_pos x v hv₀
    have hav : a.linearEquiv x v = -(((t : ℝ) : ℂ) •
        (b.linearMap x v - a.linearEquiv x v)) := by
      change a.linearEquiv x v + (((t : ℝ) : ℂ) •
        (b.linearMap x v - a.linearEquiv x v)) = 0 at hv
      exact eq_neg_of_add_eq_zero_left hv
    have hupper : K x (a.linearEquiv x v) ≤ d / 2 * H x v := by
      calc
        K x (a.linearEquiv x v) = (t : ℝ) *
            K x (b.linearMap x v - a.linearEquiv x v) := by
          conv_lhs => rw [hav]
          rw [map_neg_eq_map, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg t.property.1]
        _ ≤ K x (b.linearMap x v - a.linearEquiv x v) :=
          mul_le_of_le_one_left (apply_nonneg (K x) _) t.property.2
        _ ≤ d / 2 * H x v := herror x v
    have hlower := hmargin x v
    nlinarith
  have hLbij (t : I) (x : M) : Function.Bijective (L t x) := by
    refine ⟨hLinj t x, ?_⟩
    let A : E x →ₗ[ℂ] E x := (a.linearEquiv x).symm.toLinearMap.comp (L t x)
    have hAinj : Function.Injective A := (a.linearEquiv x).symm.injective.comp (hLinj t x)
    have hAsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hAinj
    intro w
    obtain ⟨v, hv⟩ := hAsurj ((a.linearEquiv x).symm w)
    refine ⟨v, (a.linearEquiv x).symm.injective hv⟩
  -- Keep the actual affine cylinder, and test its joint continuity in original frames.
  let p : I × M → M := Prod.snd
  let : IsFiniteRank (p *ᵖ E) := isFiniteRank_pullback (E := E) ⟨p, continuous_snd⟩
  let : IsFiniteRank (p *ᵖ F) := isFiniteRank_pullback (E := F) ⟨p, continuous_snd⟩
  have hLcontinuous : Continuous (fun z : TotalSpace Unit (p *ᵖ E) ↦
      (⟨z.proj.2, L z.proj.1 z.proj.2 z.snd⟩ : TotalSpace Unit F)) := by
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    apply continuous_iff_continuousAt.mpr
    intro z
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj.2
    have hz : z.proj.2 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hbase : Continuous (fun w : TotalSpace Unit (p *ᵖ E) ↦ w.proj.2) :=
      (Pullback.continuous_proj Unit E p).snd
    apply f.continuousAt_of_comp_left hbase.continuousAt hz
    have hac := ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp
      (a.continuous_total.comp (Pullback.continuous_lift Unit E p))).continuousAt (x := z)
    have hbc := ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).comp
      (b.continuous_total.comp (Pullback.continuous_lift Unit E p))).continuousAt (x := z)
    have hca := ((f.continuousAt (f.mem_source.mpr hz)).comp hac).snd
    have hcb := ((f.continuousAt (f.mem_source.mpr hz)).comp hbc).snd
    have htime : Continuous (fun w : TotalSpace Unit (p *ᵖ E) ↦ ((w.proj.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp (Pullback.continuous_proj Unit E p).fst)
    have hcoord := hca.add (htime.continuousAt.smul (hcb.sub hca))
    apply (hbase.continuousAt.prodMk hcoord).congr_of_eventuallyEq
    filter_upwards [(f.open_baseSet.preimage hbase).mem_nhds hz] with w hw
    refine Prod.ext (f.proj_toFun _ (f.mem_source.mpr hw)) ?_
    change (f ⟨w.proj.2, a.linearEquiv w.proj.2 w.snd + ((w.proj.1 : ℝ) : ℂ) •
        (b.linearMap w.proj.2 w.snd - a.linearEquiv w.proj.2 w.snd)⟩).2 =
      (f ⟨w.proj.2, a.linearEquiv w.proj.2 w.snd⟩).2 + ((w.proj.1 : ℝ) : ℂ) •
        ((f ⟨w.proj.2, b.linearMap w.proj.2 w.snd⟩).2 -
          (f ⟨w.proj.2, a.linearEquiv w.proj.2 w.snd⟩).2)
    simp only [← f.continuousLinearMapAt_apply_of_mem ℂ hw]
    rw [map_add, map_smul, map_sub]
  let c : Hom (p *ᵖ E) (p *ᵖ F) :=
    { linearMap y := L y.1 y.2
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
        exact (Pullback.continuous_proj Unit E p).prodMk hLcontinuous }
  let B : Iso E F := b.toIso (fun x ↦ by
    have heq : L 1 x = b.linearMap x := LinearMap.ext (hLone x)
    have hi := hLbij 1 x
    rwa [heq] at hi)
  let Hpath : IsoHomotopy a B :=
    { iso := c.toIso (fun y ↦ hLbij y.1 y.2)
      map_zero := hLzero
      map_one := hLone }
  refine ⟨B, hbsmooth, hbequiv, Hpath, ?_⟩
  intro t g x v
  change L t (g • x) (σE.linearMap g x v) = σF.linearMap g x (L t x v)
  simp only [L, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    ha g x v, hbequiv g x v, map_add, map_smul, map_sub]

end AtiyahSinger.ComplexBundle
