/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantFineApproximation
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Topology.BundleIsoHomotopy
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Equivariant relative smoothing of actual bundle isomorphisms

Public module ID: M1200.

Fine approximation and one prescribed invariant smooth cutoff give a smooth
intertwining isomorphism, connected to the original one by an equivariant
isomorphism homotopy fixed on the specified region. Neither compactness of the
base nor a uniform inverse bound is needed. The cutoff exposes the precise
buffer required in applications to invariant exterior regions.

This extends the relative argument in `RelativeBundleSmoothing` to the original
compact group actions, using `EquivariantFineApproximation`. The ordinary
smoothing source is SG Appendix A, Remark A.1; retaining the same equivariant
relative cylinder is a project supplement for analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace Topology
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
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hE hF hG hGC hGT hAction hσE hσF

set_option maxHeartbeats 1000000 in
-- Retain the original local inverse margins and the full equivariant affine cylinder.

/-- Smooth a continuous equivariant bundle isomorphism through isomorphisms fixed
on a specified region. The given invariant smooth cutoff equals one there and
has closed support in an open set where the initial map is smooth. -/
theorem Iso.exists_equivariant_smooth_homotopy_relative
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Iso E F)
    (haEq : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.IsEquivariant σE σF)
    (A : Set M) (U : Opens M)
    (χ : M → ℝ) (hχsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ (U : Set M))
    (hχA : ∀ x ∈ A, χ x = 1)
    (hχbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχinv : ∀ (g : G) (x : M), χ (g • x) = χ x)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
      (E := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      (F := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F)
      (fun x ↦ (a.linearEquiv x.val).toLinearMap)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ b : Iso E F, IsSmoothBundleMap (n := n) (r := r) (q := q) b.toHom.linearMap ∧
      b.IsEquivariant σE σF ∧
      ∃ H : IsoHomotopy a b,
        (∀ (t : unitInterval) (g : G) (x : M) (v : E x),
          H.iso.linearEquiv (t, g • x) (σE.linearMap g x v) =
            σF.linearMap g x (H.iso.linearEquiv (t, x) v)) ∧
        (∀ (t : unitInterval) (x : M), x ∈ A →
          ∀ v : E x, H.iso.linearEquiv (t, x) v = a.linearEquiv x v) := by
  /- Choose a positive local invertibility margin and approximate equivariantly.
  The prescribed invariant cutoff keeps the original map wherever it is one;
  the complementary weight contracts the approximation error. Closed support
  inside the smooth-input region makes the new map smooth everywhere. The
  same affine cylinder is invertible, equivariant and fixed on A at every time. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  have haIntertwines (g : G) (x : M) (v : E x) :
      a.linearEquiv (g • x) (σE.linearMap g x v) =
        σF.linearMap g x (a.linearEquiv x v) := haEq g x v
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
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
    let O : Set M := (e x).baseSet
    have hW : IsOpen O := (e x).open_baseSet
    have hx : x ∈ O := mem_baseSet_trivializationAt _ _ _
    let x₀ : O := ⟨x, hx⟩
    let T := O × EuclideanSpace ℂ (Fin r)
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
    have hevent : ∀ᶠ y : O in 𝓝 x₀,
        ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1, 0 < d (y, u) :=
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin r)) 1).eventually_forall_of_forall_eventually
          (fun u hu ↦ (hd.continuousAt (x := (x₀, u))).eventually
            (Ioi_mem_nhds (hpos u hu)))
    obtain ⟨V, hsub, hV, hxV⟩ := mem_nhds_iff.mp hevent
    have hVo : IsOpen ((Subtype.val : O → M) '' V) := hW.isOpenMap_subtype_val _ hV
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
  choose δ hδ O hOopen hxO hObound using hlocal
  have hcover : Set.univ ⊆ ⋃ x, O x := fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxO x⟩
  -- Locally finite convex averaging gives a positive continuous pointwise margin.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ O hOopen hcover
  let d (x : M) : ℝ := ∑ᶠ j : M, ρ j x * δ j
  have hdsum (x : M) : d x = ∑ j ∈ ρ.finsupport x, ρ j x * δ j := by
    exact (ρ.sum_finsupport_smul_eq_finsum x (fun j _ ↦ δ j)).symm
  have hdc : Continuous d := by
    exact (ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (fun j _ _ ↦ contMDiffAt_const)).continuous
  have hd (x : M) : 0 < d x := by
    rw [hdsum]
    obtain ⟨j, hj⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (ρ.nonneg j x) (hδ j).le
    · exact ⟨j, (ρ.mem_finsupport x).mpr hj.ne', mul_pos hj (hδ j)⟩
  have hmargin (x : M) (v : E x) : d x * H x v ≤ K x (a.linearEquiv x v) := by
    rw [hdsum, Finset.sum_mul]
    calc
      (∑ j ∈ ρ.finsupport x, ρ j x * δ j * H x v) ≤
          ∑ j ∈ ρ.finsupport x, ρ j x * K x (a.linearEquiv x v) := by
        apply Finset.sum_le_sum
        intro j hj
        have hnz : ρ j x ≠ 0 := (ρ.mem_finsupport x).mp hj
        have hxU := hρ j (subset_tsupport (ρ j) hnz)
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hObound j x hxU v) (ρ.nonneg j x)
      _ = K x (a.linearEquiv x v) := by
        rw [← Finset.sum_mul, ρ.sum_finsupport x (Set.mem_univ x), one_mul]
  -- Approximate the actual original intertwiner within its local inverse margin.
  let ε : C(M, ℝ) := ⟨fun x ↦ d x / 2, hdc.div_const 2⟩
  obtain ⟨c, hcsmooth, hcequiv, hcclose⟩ :=
    a.toHom.exists_equivariant_smooth_fine_approximation
      IG σE σF hσE hσF haEq h k ε (fun x ↦ half_pos (hd x))
  -- The prescribed invariant cutoff retains the original map on the fixed region.
  let Bmap (x : M) : E x →ₗ[ℂ] F x :=
    ((χ x : ℝ) : ℂ) • a.toHom.linearMap x +
      (((1 - χ x : ℝ) : ℂ) • c.linearMap x)
  -- Over U, the original native pullback smoothness gives the original smooth columns.
  have haLocal (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e]
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F)) [MemTrivializationAtlas f]
      (j : Fin r) (x : M) (hx : x ∈ e.baseSet ∩ f.baseSet) (hxU : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
        (fun y ↦ (f ⟨y, a.linearEquiv y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2) x := by
    let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
    let x' : U := ⟨x, hxU⟩
    let : MemTrivializationAtlas (e.pullback i) := ⟨e, inferInstance, rfl⟩
    let : MemTrivializationAtlas (f.pullback i) := ⟨f, inferInstance, rfl⟩
    have hx' : x' ∈ (e.pullback i).baseSet ∩ (f.pullback i).baseSet := hx
    have hlocal := (ha (e.pullback i) (f.pullback i) j).contMDiffAt
      (((e.pullback i).open_baseSet.inter (f.pullback i).open_baseSet).mem_nhds hx')
    apply (contMDiffAt_subtype_iff (U := U) (x := x')).mp
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [((e.pullback i).open_baseSet.inter
      (f.pullback i).open_baseSet).mem_nhds hx'] with y hy
    have heq : (e.pullback i).symmL ℂ y (EuclideanSpace.single j 1) =
        e.symmL ℂ y.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hy.1]
      change (e.pullback i).symm y (EuclideanSpace.single j 1) =
        e.symmL ℂ (i y) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) hy.1, (e.pullback i).symm_apply hy.1]
      rfl
    change (f ⟨y.val, a.linearEquiv y.val
      (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2 =
        (f ⟨y.val, a.linearEquiv y.val
          ((e.pullback i).symmL ℂ y (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  -- The closed support lies inside U, so the nonsmooth map is absent locally elsewhere.
  have hBsmooth : IsSmoothBundleMap (n := n) (r := r) (q := q) Bmap := by
    intro e he f hf j x hx
    let := he
    let := hf
    by_cases hxχ : x ∈ tsupport χ
    · have haCol := haLocal e f j x hx (hχU hxχ)
      have hcCol := (hcsmooth e f j).contMDiffAt
        ((e.open_baseSet.inter f.open_baseSet).mem_nhds hx)
      have hχC := Complex.ofRealCLM.contMDiff.comp hχsmooth
      have hχD := Complex.ofRealCLM.contMDiff.comp
        ((contMDiff_const (c := (1 : ℝ))).sub hχsmooth)
      have hsmul : ContDiff ℝ ∞
          (fun p : ℂ × EuclideanSpace ℂ (Fin q) ↦ p.1 • p.2) := contDiff_smul
      have hc := (hsmul.comp_contMDiffAt
        (hχC.contMDiffAt.prodMk_space haCol)).add
          (hsmul.comp_contMDiffAt (hχD.contMDiffAt.prodMk_space hcCol))
      apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(e.open_baseSet.inter f.open_baseSet).mem_nhds hx] with y hy
      change (f ⟨y, Bmap y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
        (χ y : ℂ) • (f ⟨y, a.linearEquiv y
          (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 +
        (((1 - χ y : ℝ) : ℂ) • (f ⟨y, c.linearMap y
          (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2)
      simp only [Bmap, LinearMap.add_apply, LinearMap.smul_apply,
        ← f.continuousLinearMapAt_apply_of_mem ℂ hy.2, map_add, map_smul]
      rfl
    · have hc := (hcsmooth e f j).contMDiffAt
        ((e.open_baseSet.inter f.open_baseSet).mem_nhds hx)
      apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ]
        with y hy
      have hz : χ y = 0 := notMem_tsupport_iff_eventuallyEq.mp hy |>.self_of_nhds
      simp [Bmap, hz]
  have hBcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, Bmap z.proj z.snd⟩ : TotalSpace Unit F)) := by
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt, ?_⟩
    let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.proj
    let t := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj
    have hyd : z.proj ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
    have hyt : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt _ _ _
    let L (y : M) : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
      ∑ j : Fin r, ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
          ((t ⟨y, Bmap y (d.symmL ℂ y (EuclideanSpace.single j 1))⟩).2)
    have hL : ContinuousOn L (d.baseSet ∩ t.baseSet) := by
      apply continuousOn_finsetSum
      intro j _
      exact (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).continuous
          |>.comp_continuousOn (hBsmooth d t j).continuousOn
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
      ((Bmap w.proj).comp (d.symmL ℂ w.proj).toLinearMap)
    have hmap := congrArg B ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr
      (d ⟨w.proj, w.snd⟩).2)
    simpa [L, B, d, t, unitTotalEquiv, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, t.coe_linearMapAt_of_mem hw.2,
      d.symmL_apply hw.1, d.symm_apply_apply_mk hw.1] using hmap.symm
  let b : Hom E F := ⟨Bmap, hBcontinuous⟩
  have hbEq : b.IsEquivariant σE σF := by
    intro g x v
    change (χ (g • x) : ℂ) • a.linearEquiv (g • x) (σE.linearMap g x v) +
        (((1 - χ (g • x) : ℝ) : ℂ) • c.linearMap (g • x) (σE.linearMap g x v)) =
      σF.linearMap g x ((χ x : ℂ) • a.linearEquiv x v +
        (((1 - χ x : ℝ) : ℂ) • c.linearMap x v))
    rw [hχinv, haIntertwines g x v, hcequiv g x v, map_add, map_smul, map_smul]
  -- The complementary weight 1 - χ contracts the original fine approximation error.
  have herror (x : M) (v : E x) :
      K x (b.linearMap x v - a.linearEquiv x v) ≤ d x / 2 * H x v := by
    have hcerror : K x (c.linearMap x v - a.linearEquiv x v) ≤ d x / 2 * H x v := by
      apply (sq_le_sq₀ (apply_nonneg (K x) _) (mul_nonneg (half_pos (hd x)).le
        (apply_nonneg (H x) v))).mp
      have hkpos : 0 ≤ (k.pairing x (c.linearMap x v - a.linearEquiv x v)
          (c.linearMap x v - a.linearEquiv x v)).re := (k.toCore x).re_inner_nonneg _
      have hhpos : 0 ≤ (h.pairing x v v).re := (h.toCore x).re_inner_nonneg _
      rw [hK, hH, mul_pow, Real.sq_sqrt hkpos, Real.sq_sqrt hhpos]
      exact hcclose x v
    have heq : b.linearMap x v - a.linearEquiv x v =
        (((1 - χ x : ℝ) : ℂ) • (c.linearMap x v - a.linearEquiv x v)) := by
      change (χ x : ℂ) • a.linearEquiv x v +
        (((1 - χ x : ℝ) : ℂ) • c.linearMap x v) - a.linearEquiv x v = _
      rw [Complex.ofReal_sub, Complex.ofReal_one, smul_sub, sub_smul,
        sub_smul, one_smul, one_smul]
      abel
    rw [heq, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hχbounds x).2)]
    exact (mul_le_of_le_one_left (apply_nonneg (K x) _)
      (by linarith [(hχbounds x).1])).trans hcerror
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
    have hupper : K x (a.linearEquiv x v) ≤ d x / 2 * H x v := by
      calc
        K x (a.linearEquiv x v) = (t : ℝ) *
            K x (b.linearMap x v - a.linearEquiv x v) := by
          conv_lhs => rw [hav]
          rw [map_neg_eq_map, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg t.property.1]
        _ ≤ K x (b.linearMap x v - a.linearEquiv x v) :=
          mul_le_of_le_one_left (apply_nonneg (K x) _) t.property.2
        _ ≤ d x / 2 * H x v := herror x v
    have hlower := hmargin x v
    have hdpos := hd x
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
  refine ⟨B, hBsmooth, hbEq, Hpath, ?_, ?_⟩
  · intro t g x v
    change a.linearEquiv (g • x) (σE.linearMap g x v) + ((t : ℝ) : ℂ) •
        (b.linearMap (g • x) (σE.linearMap g x v) -
          a.linearEquiv (g • x) (σE.linearMap g x v)) =
      σF.linearMap g x (a.linearEquiv x v + ((t : ℝ) : ℂ) •
        (b.linearMap x v - a.linearEquiv x v))
    rw [haIntertwines g x v, hbEq g x v, map_add, map_smul, map_sub]
  · intro t x hx v
    have hfixed : b.linearMap x v = a.linearEquiv x v := by
      simp [b, Bmap, hχA x hx, Iso.toHom]
    change L t x v = a.linearEquiv x v
    change a.linearEquiv x v + ((t : ℝ) : ℂ) •
      (b.linearMap x v - a.linearEquiv x v) = a.linearEquiv x v
    rw [hfixed, sub_self, smul_zero, add_zero]

end AtiyahSinger.ComplexBundle
