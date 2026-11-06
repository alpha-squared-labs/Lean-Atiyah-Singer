/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphRepresentation
public import AtiyahSinger.Analysis.EquivariantCoordinateCutoffIndex
public import AtiyahSinger.Analysis.EquivariantNativeSumL2
public import AtiyahSinger.Analysis.GradedBundleL2Realization
public import AtiyahSinger.Analysis.SmoothSectionBundleSum
public import AtiyahSinger.Analysis.SobolevBundleSum

/-!
# Averaged native graded cutoffs on the specified Hilbert graph

Public module ID: M0516.

The specified smooth source and target sums give fixed native Sobolev and
integral L² coordinates. A signed four-block cutoff close to the original
graph realization has, after actual elliptic averaging, that graph's full
representation-valued index. All metrics, actions, smooth projections and
presentations are retained; the native sum metrics need not be orthogonal.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory PseudodifferentialOperator
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : Fin 2 → SmoothFiniteComplexBundle (n := n) M)
  (σ : (i : Fin 2) →
    letI := modelTopology (EuclideanSpace ℂ (Fin (A i).rank)) (A i).Fiber
    EquivariantStructure G (A i).Fiber)
  (hσ : ∀ i : Fin 2, (σ i).IsSmooth (n := n) (r := (A i).rank) IG)
  (τ : (i : Fin 2) →
    letI := modelTopology (EuclideanSpace ℂ (Fin (B i).rank)) (B i).Fiber
    EquivariantStructure G (B i).Fiber)
  (hτ : ∀ i : Fin 2, (τ i).IsSmooth (n := n) (r := (B i).rank) IG)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (h : (i : Fin 2) → SmoothHermitianMetric (n := n) (r := (A i).rank) (A i).Fiber)
  (hInvariant : ∀ i : Fin 2,
    letI := modelTopology (EuclideanSpace ℂ (Fin (A i).rank)) (A i).Fiber
    ∀ (g : G) (x : M) (u v : (A i).Fiber x),
      (h i).pairing (g • x) ((σ i).linearMap g x u) ((σ i).linearMap g x v) =
        (h i).pairing x u v)
  (k : (i : Fin 2) → SmoothHermitianMetric (n := n) (r := (B i).rank) (B i).Fiber)
  (kInvariant : ∀ i : Fin 2,
    letI := modelTopology (EuclideanSpace ℂ (Fin (B i).rank)) (B i).Fiber
    ∀ (g : G) (x : M) (u v : (B i).Fiber x),
      (k i).pairing (g • x) ((τ i).linearMap g x u) ((τ i).linearMap g x v) =
        (k i).pairing x u v)
  (hE : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (hEInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    ∀ (g : G) (x : M) (u v : E.Fiber x),
      hE.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) =
        hE.pairing x u v)
  (hF : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (hFInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : G) (x : M) (u v : F.Fiber x),
      hF.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) =
        hF.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
  (e : ∀ x, ((A 0).Fiber x × (A 1).Fiber x) ≃ₗ[ℂ] E.Fiber x)
  (he₀ : IsSmoothBundleMap (n := n) (r := (A 0).rank) (q := E.rank)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
  (he₁ : IsSmoothBundleMap (n := n) (r := (A 1).rank) (q := E.rank)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
  (he : letI := modelTopology (EuclideanSpace ℂ (Fin (A 0).rank)) (A 0).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin (A 1).rank)) (A 1).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    ∀ (g : G) (x : M) (v : (A 0).Fiber x × (A 1).Fiber x),
      e (g • x) ((σ 0).linearMap g x v.1, (σ 1).linearMap g x v.2) =
        σE.linearMap g x (e x v))
  (f : ∀ x, ((B 0).Fiber x × (B 1).Fiber x) ≃ₗ[ℂ] F.Fiber x)
  (hf₀ : IsSmoothBundleMap (n := n) (r := (B 0).rank) (q := F.rank)
    (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
  (hf₁ : IsSmoothBundleMap (n := n) (r := (B 1).rank) (q := F.rank)
    (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
  (hf : letI := modelTopology (EuclideanSpace ℂ (Fin (B 0).rank)) (B 0).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin (B 1).rank)) (B 1).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : G) (x : M) (v : (B 0).Fiber x × (B 1).Fiber x),
      f (g • x) ((τ 0).linearMap g x v.1, (τ 1).linearMap g x v.2) =
        σF.linearMap g x (f x v))

include hEInvariant hFInvariant he hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3500000 in
-- Use the same native sums and fixed graph before selecting the four-block cutoff.
/-- Close native graded cutoffs have the full index of their specified invariant graph. -/
theorem exists_radius_smoothEquivariantAnalyticIndex_average_eq_of_graded_graph :
    let Even := WithLp 2 ((h 0).L2SectionSpace μ × (h 1).L2SectionSpace μ)
    let Odd := WithLp 2 ((k 0).L2SectionSpace μ × (k 1).L2SectionSpace μ)
    let R (i : Fin 2) := (h i).l2ContRepresentation μ IG (σ i) (hσ i) (hInvariant i) hμInvariant
    let S (i : Fin 2) := (k i).l2ContRepresentation μ IG (τ i) (hτ i) (kInvariant i) hμInvariant
    let Φs := smoothSectionSumEquiv e he₀ he₁
    let Ψs := smoothSectionSumEquiv f hf₀ hf₁
    ∀ (ρ : ContRepresentation ℂ G Even) (η : ContRepresentation ℂ G Odd)
      (_hρ : Continuous (fun p : G × Even ↦ ρ p.1 p.2))
      (hη : Continuous (fun p : G × Odd ↦ η p.1 p.2))
      (_hρapp : ∀ g v, ρ g v = WithLp.toLp 2
        (R 0 g (WithLp.ofLp v).1, R 1 g (WithLp.ofLp v).2))
      (_hηapp : ∀ g v, η g v = WithLp.toLp 2
        (S 0 g (WithLp.ofLp v).1, S 1 g (WithLp.ofLp v).2))
      (D : Even →ₗ.[ℂ] Odd) (_hD : D.IsClosed)
      (C : (i : Fin 2) → SmoothBundlePresentation (n := n) (r := (A i).rank) (A i).Fiber)
      (H : (i : Fin 2) → SmoothBundlePresentation (n := n) (r := (B i).rank) (B i).Fiber)
      (_AE : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
      (_AF : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber)
      (T : WithLp 2 ((C 0).SobolevSpace 1 × (C 1).SobolevSpace 1) →L[ℂ] Odd),
    let J₀ := ((h 0).sobolevZeroEquivL2 (μ := μ) (C 0)).toContinuousLinearMap.comp
      ((C 0).sobolevInclusion 1 0 (by norm_num))
    let J₁ := ((h 1).sobolevZeroEquivL2 (μ := μ) (C 1)).toContinuousLinearMap.comp
      ((C 1).sobolevInclusion 1 0 (by norm_num))
    let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
      ((J₀.prodMap J₁).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
    let Γ := D.graph.comap (WithLp.linearEquiv 2 ℂ (Even × Odd)).toLinearMap
    let FΓ := (WithLp.sndL 2 ℂ Even Odd).comp Γ.subtypeL
    ∀ (γ : ContRepresentation ℂ G Γ)
      (hγ : Continuous (fun p : G × Γ ↦ γ p.1 p.2))
      (γI : G →* (Γ ≃ₗᵢ[ℂ] Γ)) (_hγI : ∀ g v, γI g v = γ g v)
      (_hγv : ∀ g v, (γ g v).val = WithLp.toLp 2
        (ρ g (WithLp.ofLp v.val).1, η g (WithLp.ofLp v.val).2))
      (Φ : WithLp 2 ((C 0).SobolevSpace 1 × (C 1).SobolevSpace 1) ≃L[ℂ] Γ)
      (_hΦ : ∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x))
      (hFg : ∀ g, FΓ.comp (γ g) = (η g).comp FΓ) (hFred : FΓ.IsFredholm),
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (U : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
          (A 0).Fiber (B 0).Fiber μ 1)
        (V : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
          (A 0).Fiber (B 1).Fiber μ 1)
        (W : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 0).rank)
          (A 1).Fiber (B 0).Fiber μ 1)
        (Z : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 1).rank)
          (A 1).Fiber (B 1).Fiber μ 1)
        (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber μ 1)
        (_hK : ∀ u v, K.toLinearMap (Φs (u, v)) =
          Ψs (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v))
        (hKell : (K.average IG σE σF hσE hσF).IsElliptic),
        ‖gradedBlockOperator
          (((k 0).sobolevZeroEquivL2 (μ := μ) (H 0)).toContinuousLinearMap.comp
            (U.sobolevRealization (C 0) (H 0) 1 0 (by norm_num)))
          (((k 1).sobolevZeroEquivL2 (μ := μ) (H 1)).toContinuousLinearMap.comp
            (V.sobolevRealization (C 0) (H 1) 1 0 (by norm_num)))
          (((k 0).sobolevZeroEquivL2 (μ := μ) (H 0)).toContinuousLinearMap.comp
            (W.sobolevRealization (C 1) (H 0) 1 0 (by norm_num)))
          (((k 1).sobolevZeroEquivL2 (μ := μ) (H 1)).toContinuousLinearMap.comp
            (Z.sobolevRealization (C 1) (H 1) 1 0 (by norm_num))) - T‖ < ε →
          (K.average IG σE σF hσE hσF).smoothEquivariantAnalyticIndex IG σE σF hσE hσF
            (K.isEquivariant_average IG σE σF hσE hσF) hKell =
              equivariantFredholmIndex γ η hγ hη FΓ hFg hFred := by
  classical
  let Even := WithLp 2 ((h 0).L2SectionSpace μ × (h 1).L2SectionSpace μ)
  let Odd := WithLp 2 ((k 0).L2SectionSpace μ × (k 1).L2SectionSpace μ)
  let R (i : Fin 2) := (h i).l2ContRepresentation μ IG (σ i) (hσ i) (hInvariant i) hμInvariant
  let S (i : Fin 2) := (k i).l2ContRepresentation μ IG (τ i) (hτ i) (kInvariant i) hμInvariant
  let Φs := smoothSectionSumEquiv e he₀ he₁
  let Ψs := smoothSectionSumEquiv f hf₀ hf₁
  dsimp only
  intro ρ η hρ hη hρapp hηapp D hD C H AE AF T
  let J₀ := ((h 0).sobolevZeroEquivL2 (μ := μ) (C 0)).toContinuousLinearMap.comp
    ((C 0).sobolevInclusion 1 0 (by norm_num))
  let J₁ := ((h 1).sobolevZeroEquivL2 (μ := μ) (C 1)).toContinuousLinearMap.comp
    ((C 1).sobolevInclusion 1 0 (by norm_num))
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toContinuousLinearMap.comp
    ((J₀.prodMap J₁).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap)
  let Γ := D.graph.comap (WithLp.linearEquiv 2 ℂ (Even × Odd)).toLinearMap
  let FΓ := (WithLp.sndL 2 ℂ Even Odd).comp Γ.subtypeL
  intro γ hγ γI hγI hγv Φ hΦ hFg hFred
  -- Choose all three actual native coordinate equivalences before the cutoff radius.
  obtain ⟨I₀, hI₀⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ) e he₀ he₁
    (C 0) (C 1) AE 1
  obtain ⟨U₀, hU₀⟩ := exists_l2Equiv_of_smoothBundleSum (μ := μ) e he₀ he₁ (h 0) (h 1) hE
  obtain ⟨O₀, hO₀⟩ := exists_l2Equiv_of_smoothBundleSum (μ := μ) f hf₀ hf₁ (k 0) (k 1) hF
  let I := I₀.trans (WithLp.prodContinuousLinearEquiv 2 ℂ
    ((C 0).SobolevSpace 1) ((C 1).SobolevSpace 1)).symm
  let U := U₀.trans (WithLp.prodContinuousLinearEquiv 2 ℂ
    ((h 0).L2SectionSpace μ) ((h 1).L2SectionSpace μ)).symm
  let O := O₀.trans (WithLp.prodContinuousLinearEquiv 2 ℂ
    ((k 0).L2SectionSpace μ) ((k 1).L2SectionSpace μ)).symm
  have hI (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      I (AE.smoothToSobolev 1 (Φs (u, v))) =
        WithLp.toLp 2 ((C 0).smoothToSobolev 1 u, (C 1).smoothToSobolev 1 v) := by
    have hu := hI₀ (Φs (u, v))
    change I₀ (AE.smoothToSobolev 1 (Φs (u, v))) =
      ((C 0).smoothToSobolev 1 ((Φs.symm (Φs (u, v))).1),
        (C 1).smoothToSobolev 1 ((Φs.symm (Φs (u, v))).2)) at hu
    rw [Φs.symm_apply_apply] at hu
    exact congrArg (WithLp.toLp 2) hu
  have hO (u : smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber)
      (v : smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) :
      O (hF.smoothToL2 μ (Ψs (u, v))) =
        WithLp.toLp 2 ((k 0).smoothToL2 μ u, (k 1).smoothToL2 μ v) := by
    have hu := hO₀ (Ψs (u, v))
    change O₀ (hF.smoothToL2 μ (Ψs (u, v))) =
      ((k 0).smoothToL2 μ ((Ψs.symm (Ψs (u, v))).1),
        (k 1).smoothToL2 μ ((Ψs.symm (Ψs (u, v))).2)) at hu
    rw [Ψs.symm_apply_apply] at hu
    exact congrArg (WithLp.toLp 2) hu
  have hUg := l2Equiv_intertwines_of_smoothBundleSum IG (σ 0) (σ 1) σE
    (hσ 0) (hσ 1) hσE (h 0) (h 1) hE (hInvariant 0) (hInvariant 1) hEInvariant
    hμInvariant e he₀ he₁ he U₀ hU₀
  have hOg := l2Equiv_intertwines_of_smoothBundleSum IG (τ 0) (τ 1) σF
    (hτ 0) (hτ 1) hσF (k 0) (k 1) hF (kInvariant 0) (kInvariant 1) hFInvariant
    hμInvariant f hf₀ hf₁ hf O₀ hO₀
  have hΓclosed : IsClosed (Γ : Set (WithLp 2 (Even × Odd))) :=
    hD.preimage (WithLp.prod_continuous_ofLp 2 Even Odd)
  let : CompleteSpace Γ := hΓclosed.completeSpace_coe
  let JΓ := (WithLp.fstL 2 ℂ Even Odd).comp Γ.subtypeL
  have hJΓ : Function.Injective JΓ := by
    intro x y hxy
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact Prod.ext hxy (D.mem_graph_snd_inj' x.property y.property hxy)
  have hJΓg (g : G) (x : Γ) : JΓ (γ g x) = U
      (hE.l2ContRepresentation μ IG σE hσE hEInvariant hμInvariant g (U.symm (JΓ x))) := by
    have hu := hUg g (U.symm (JΓ x))
    have hleft : JΓ (γ g x) = ρ g (JΓ x) := congrArg
      (fun z : WithLp 2 (Even × Odd) ↦ (WithLp.ofLp z).1) (hγv g x)
    rw [hleft, hρapp]
    have hu' := congrArg (WithLp.toLp 2) hu
    change U (hE.l2ContRepresentation μ IG σE hσE hEInvariant hμInvariant g
      (U.symm (JΓ x))) = WithLp.toLp 2
        (R 0 g (WithLp.ofLp (U (U.symm (JΓ x)))).1,
          R 1 g (WithLp.ofLp (U (U.symm (JΓ x)))).2) at hu'
    rw [U.apply_symm_apply] at hu'
    exact hu'.symm
  have hJΓsmooth (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      JΓ (Φ (I (AE.smoothToSobolev 1 u))) = U (hE.smoothToL2 μ u) := by
    have hfirst := congrArg (fun z : WithLp 2 (Even × Odd) ↦ (WithLp.ofLp z).1)
      (hΦ (I (AE.smoothToSobolev 1 u)))
    change JΓ (Φ (I (AE.smoothToSobolev 1 u))) = J (I (AE.smoothToSobolev 1 u)) at hfirst
    rw [hfirst]
    apply WithLp.ofLp_injective
    change (J₀ (I₀ (AE.smoothToSobolev 1 u)).1, J₁ (I₀ (AE.smoothToSobolev 1 u)).2) =
      U₀ (hE.smoothToL2 μ u)
    rw [hI₀, hU₀]
    apply Prod.ext
    · change (h 0).sobolevZeroEquivL2 (C 0)
        ((C 0).sobolevInclusion 1 0 (by norm_num) ((C 0).smoothToSobolev 1 _)) = _
      rw [SmoothBundlePresentation.sobolevInclusion_smoothToSobolev,
        SmoothHermitianMetric.sobolevZeroEquivL2_smooth]
    · change (h 1).sobolevZeroEquivL2 (C 1)
        ((C 1).sobolevInclusion 1 0 (by norm_num) ((C 1).smoothToSobolev 1 _)) = _
      rw [SmoothBundlePresentation.sobolevInclusion_smoothToSobolev,
        SmoothHermitianMetric.sobolevZeroEquivL2_smooth]
  have hOη (g : G) (y : hF.L2SectionSpace μ) :
      O (hF.l2ContRepresentation μ IG σF hσF hFInvariant hμInvariant g y) = η g (O y) := by
    rw [hηapp]
    exact congrArg (WithLp.toLp 2) (hOg g y)
  obtain ⟨ε, hε, hstable⟩ :=
    exists_radius_smoothEquivariantAnalyticIndex_average_eq_of_coordinates
      IG σE σF hσE hσF hE hF hEInvariant hFInvariant hμInvariant AE AF
      γ hγ γI hγI η hη I Φ U O JΓ hJΓ hJΓg hJΓsmooth hOη FΓ hFg hFred
  refine ⟨ε, hε, ?_⟩
  intro U' V' W' Z' K hK hKell hclose
  have hmatrix := gradedBundleL2Realization_eq E F A B U' V' W' Z' K Φs Ψs hK
    C H AE AF (k 0) (k 1) hF 1 (by norm_num) I O hI hO
  have hFΦ : FΓ.comp Φ.toContinuousLinearMap = T := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun z : WithLp 2 (Even × Odd) ↦ (WithLp.ofLp z).2) (hΦ x)
  apply hstable K hKell
  change ‖(O.toContinuousLinearMap.comp
    ((hF.sobolevZeroEquivL2 (μ := μ) AF).toContinuousLinearMap.comp
      (K.sobolevRealization AE AF 1 0 (by norm_num)))).comp I.symm.toContinuousLinearMap -
    FΓ.comp Φ.toContinuousLinearMap‖ < ε
  have hII : I.toContinuousLinearMap.comp I.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (WithLp 2 ((C 0).SobolevSpace 1 × (C 1).SobolevSpace 1)) := by
    apply ContinuousLinearMap.ext
    intro x
    exact I.apply_symm_apply x
  rw [hmatrix, ContinuousLinearMap.comp_assoc, hII, ContinuousLinearMap.comp_id, hFΦ]
  exact hclose

end AtiyahSinger
