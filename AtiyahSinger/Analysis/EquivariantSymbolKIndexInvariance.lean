/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantContinuousSymbolHomotopy
public import AtiyahSinger.Analysis.EquivariantSymbolGermIndex
public import AtiyahSinger.Analysis.EquivariantSymbolIndexBundle
public import AtiyahSinger.Analysis.EquivariantSymbolIndexOperations
public import AtiyahSinger.Analysis.EquivariantSymbolIndexSum
public import AtiyahSinger.Analysis.EquivariantSymbolStabilization
public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantCotangentStabilization
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

/-!
# The full homogeneous symbol index depends on the original equivariant K class

Public module ID: M0599.

Equality of the original compact-support equivariant symbol classes implies
equality of the full canonical representation-valued indices, even when the
two original pairs of smooth bundles differ. The premise is equality before
forgetting the group action. No arbitrary-class index function is assumed.

The original stable relation permits arbitrary locally finite-rank stabilizers
on the cotangent total space. They are first reduced equivariantly to the zero
section. A common finite-representation complement and a common extra trivial
summand then give constant-rank stabilizers on both sides; their original
ranks need not be constant. Only these actual stabilized bundles are smoothed.
The resulting original global square gives a continuous elliptic symbol path,
which is handled by the endpoint-preserving equivariant smoothing theorem.

Sources: SG III.13, printed pp.246--247, gives the ordinary index descent
through homotopy and elementary stabilization; SG III.9, Theorem 9.7, p.214,
gives equivariant regular-homotopy invariance. Karoubi I.9.31(d),(g) supplies
finite-representation complements. The complete equivariant stable-germ,
zero-section, smoothing and original full-index comparison is a project
supplement; these passages do not separately state that complete comparison.

The finite-dimensional standard Lie-group model is explicit because the
existing equivariant smooth-bundle replacement requires it. The original
K-class construction also requires small fibers. All four model ranks remain
independent; no connectedness, nonempty-base or positive-dimension hypothesis
is imposed. This comparison does not supply a representative for every K
class, prove partition-independent assembly, or define a homomorphism on all
K classes. The proof below uses the original stable square and keeps its common
stabilization witnesses throughout the geometric index comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  {E' : M → Type}
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) E']
  {F' : M → Type}
  [∀ x, NormedAddCommGroup (F' x)] [∀ x, NormedSpace ℂ (F' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) F']
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := r') E']
  [IsSmoothComplexBundle (n := n) (r := q') F']

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')
  (hσE : σE.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := q) 𝓘(ℝ, VG))
  (hσE' : σE'.IsSmooth (n := n) (r := r') 𝓘(ℝ, VG))
  (hσF' : σF'.IsSmooth (n := n) (r := q') 𝓘(ℝ, VG))

include hDim

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

set_option maxHeartbeats 2400000 in
-- The original stable square retains every dependent bundle and specified action.
/-- Equal original equivariant symbol K classes have equal full canonical analytic indices. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_equivariantSymbolKClass_eq
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol E' F' t.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ = s.val x ξ)
    (ht : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE' σF' g t.val x ξ = t.val x ξ)
    (hK : equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE σF 0 s hi hs =
      equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σE' σF' 0 t hj ht) :
    equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF s hi hs =
      equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE' σF' hσE' hσF' t hj ht :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r')) E'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q')) F'
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let πM := cotangentProjection (n := n) (M := M)
  let a := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E))
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F))
    (ellipticSymbolTriple s.val s.property.1.continuous hi)
    (σE.pullback πM (fun _ _ ↦ rfl)) (σF.pullback πM (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant 𝓘(ℝ, VG) σE σF s.val s.property.1.continuous hi hs)
  let b := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E'))
    (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F'))
    (ellipticSymbolTriple t.val t.property.1.continuous hj)
    (σE'.pullback πM (fun _ _ ↦ rfl)) (σF'.pullback πM (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant 𝓘(ℝ, VG) σE' σF' t.val t.property.1.continuous hj ht)
  have haRank (x : M) : Module.finrank ℂ (a.1.source.Fiber (cotangentZeroSection x)) = r := by
    change Module.finrank ℂ (E x) = r
    rw [VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin r)) E x]
    simp
  have hbRank (x : M) : Module.finrank ℂ (b.1.source.Fiber (cotangentZeroSection x)) = r' := by
    change Module.finrank ℂ (E' x) = r'
    rw [VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin r')) E' x]
    simp
  -- Stabilize the actual original classes with one common complement and summand.
  obtain ⟨C, D, p, q₀, hC, hD, σC, σD, hstable⟩ :=
    exists_fixedRank_equivariant_cotangent_stabilizers 𝓘(ℝ, VG)
      a b r r' haRank hbRank hK
  obtain ⟨C', _, τC, hτC, iC, hiC⟩ :=
    σC.exists_smooth_bundle_iso (VG := VG) (n := n) p hC
  obtain ⟨D', _, τD, hτD, iD, hiD⟩ :=
    σD.exists_smooth_bundle_iso (VG := VG) (n := n) q₀ hD
  let := modelTopology (EuclideanSpace ℂ (Fin C'.rank)) C'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
  -- Keep the same stabilizers and the same source/target sum comparisons.
  obtain ⟨A, B, σA, σB, hσA, hσB, e, f, heg, hfg, S, hSi, hSg, hS, hindexS⟩ :=
    exists_equivariant_homogeneous_stabilization 𝓘(ℝ, VG) σE σF hσE hσF s hi hs C' τC hτC
  obtain ⟨A', B', σA', σB', hσA', hσB', e', f', he'g, hf'g,
      T, hTi, hTg, hT, hindexT⟩ :=
    exists_equivariant_homogeneous_stabilization 𝓘(ℝ, VG)
      σE' σF' hσE' hσF' t hj ht D' τD hτD
  let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin B.rank)) B.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin A'.rank)) A'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin B'.rank)) B'.Fiber
  -- Transport the original stable square through these exact smoothing and sum maps.
  let cE := ((Iso.refl E).sum iC).trans e
  let cF := ((Iso.refl F).sum iC).trans f
  let cE' := ((Iso.refl E').sum iD).trans e'
  let cF' := ((Iso.refl F').sum iD).trans f'
  let qE := (sumPullbackIso πM (FiniteBundle.ofFamily E) C).symm.trans (cE.pullback πM)
  let qF := (sumPullbackIso πM (FiniteBundle.ofFamily F) C).symm.trans (cF.pullback πM)
  let qE' := (sumPullbackIso πM (FiniteBundle.ofFamily E') D).symm.trans (cE'.pullback πM)
  let qF' := (sumPullbackIso πM (FiniteBundle.ofFamily F') D).symm.trans (cF'.pullback πM)
  have hqE : qE.IsEquivariant
      ((σE.pullback πM (fun _ _ ↦ rfl)).sum (σC.pullback πM (fun _ _ ↦ rfl)))
      (σA.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    change e.linearEquiv (g • z.proj)
      (σE.linearMap g z.proj w.1, iC.linearEquiv (g • z.proj) (σC.linearMap g z.proj w.2)) =
        σA.linearMap g z.proj (e.linearEquiv z.proj (w.1, iC.linearEquiv z.proj w.2))
    calc
      _ = e.linearEquiv (g • z.proj)
          (σE.linearMap g z.proj w.1, τC.linearMap g z.proj (iC.linearEquiv z.proj w.2)) :=
        congrArg (fun v ↦ e.linearEquiv (g • z.proj) (σE.linearMap g z.proj w.1, v))
          (hiC g z.proj w.2)
      _ = _ := heg g z.proj (w.1, iC.linearEquiv z.proj w.2)
  have hqF : qF.IsEquivariant
      ((σF.pullback πM (fun _ _ ↦ rfl)).sum (σC.pullback πM (fun _ _ ↦ rfl)))
      (σB.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    change f.linearEquiv (g • z.proj)
      (σF.linearMap g z.proj w.1, iC.linearEquiv (g • z.proj) (σC.linearMap g z.proj w.2)) =
        σB.linearMap g z.proj (f.linearEquiv z.proj (w.1, iC.linearEquiv z.proj w.2))
    calc
      _ = f.linearEquiv (g • z.proj)
          (σF.linearMap g z.proj w.1, τC.linearMap g z.proj (iC.linearEquiv z.proj w.2)) :=
        congrArg (fun v ↦ f.linearEquiv (g • z.proj) (σF.linearMap g z.proj w.1, v))
          (hiC g z.proj w.2)
      _ = _ := hfg g z.proj (w.1, iC.linearEquiv z.proj w.2)
  have hqE' : qE'.IsEquivariant
      ((σE'.pullback πM (fun _ _ ↦ rfl)).sum (σD.pullback πM (fun _ _ ↦ rfl)))
      (σA'.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    change e'.linearEquiv (g • z.proj)
      (σE'.linearMap g z.proj w.1, iD.linearEquiv (g • z.proj) (σD.linearMap g z.proj w.2)) =
        σA'.linearMap g z.proj (e'.linearEquiv z.proj (w.1, iD.linearEquiv z.proj w.2))
    calc
      _ = e'.linearEquiv (g • z.proj)
          (σE'.linearMap g z.proj w.1, τD.linearMap g z.proj (iD.linearEquiv z.proj w.2)) :=
        congrArg (fun v ↦ e'.linearEquiv (g • z.proj) (σE'.linearMap g z.proj w.1, v))
          (hiD g z.proj w.2)
      _ = _ := he'g g z.proj (w.1, iD.linearEquiv z.proj w.2)
  have hqF' : qF'.IsEquivariant
      ((σF'.pullback πM (fun _ _ ↦ rfl)).sum (σD.pullback πM (fun _ _ ↦ rfl)))
      (σB'.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    change f'.linearEquiv (g • z.proj)
      (σF'.linearMap g z.proj w.1, iD.linearEquiv (g • z.proj) (σD.linearMap g z.proj w.2)) =
        σB'.linearMap g z.proj (f'.linearEquiv z.proj (w.1, iD.linearEquiv z.proj w.2))
    calc
      _ = f'.linearEquiv (g • z.proj)
          (σF'.linearMap g z.proj w.1, τD.linearMap g z.proj (iD.linearEquiv z.proj w.2)) :=
        congrArg (fun v ↦ f'.linearEquiv (g • z.proj) (σF'.linearMap g z.proj w.1, v))
          (hiD g z.proj w.2)
      _ = _ := hf'g g z.proj (w.1, iD.linearEquiv z.proj w.2)
  obtain ⟨K, hKcompact, _hKinv, ha, hb, U, V, hU, hV, hUV⟩ := hstable
  let U' := qE.symm.trans (U.trans qE')
  let V' := qF.symm.trans (V.trans qF')
  have hU' : U'.IsEquivariant (σA.pullback πM (fun _ _ ↦ rfl))
      (σA'.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    have hiq : (qE.linearEquiv (g • z)).symm
        ((σA.pullback πM (fun _ _ ↦ rfl)).linearMap g z w) =
      ((σE.pullback πM (fun _ _ ↦ rfl)).sum
        (σC.pullback πM (fun _ _ ↦ rfl))).linearMap g z ((qE.linearEquiv z).symm w) := by
      apply (qE.linearEquiv (g • z)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact ((hqE g z ((qE.linearEquiv z).symm w)).trans
        (congrArg ((σA.pullback πM (fun _ _ ↦ rfl)).linearMap g z)
          ((qE.linearEquiv z).apply_symm_apply w))).symm
    change qE'.linearEquiv (g • z) (U.linearEquiv (g • z)
      ((qE.linearEquiv (g • z)).symm _)) = _
    rw [hiq]
    exact (congrArg (qE'.linearEquiv (g • z))
      (hU g z ((qE.linearEquiv z).symm w))).trans
        (hqE' g z (U.linearEquiv z ((qE.linearEquiv z).symm w)))
  have hV' : V'.IsEquivariant (σB.pullback πM (fun _ _ ↦ rfl))
      (σB'.pullback πM (fun _ _ ↦ rfl)) := by
    intro g z w
    have hiq : (qF.linearEquiv (g • z)).symm
        ((σB.pullback πM (fun _ _ ↦ rfl)).linearMap g z w) =
      ((σF.pullback πM (fun _ _ ↦ rfl)).sum
        (σC.pullback πM (fun _ _ ↦ rfl))).linearMap g z ((qF.linearEquiv z).symm w) := by
      apply (qF.linearEquiv (g • z)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact ((hqF g z ((qF.linearEquiv z).symm w)).trans
        (congrArg ((σB.pullback πM (fun _ _ ↦ rfl)).linearMap g z)
          ((qF.linearEquiv z).apply_symm_apply w))).symm
    change qF'.linearEquiv (g • z) (V.linearEquiv (g • z)
      ((qF.linearEquiv (g • z)).symm _)) = _
    rw [hiq]
    exact (congrArg (qF'.linearEquiv (g • z))
      (hV g z ((qF.linearEquiv z).symm w))).trans
        (hqF' g z (V.linearEquiv z ((qF.linearEquiv z).symm w)))
  -- On the original exterior, the same stabilized boundary is exactly symbol plus identity.
  have hUVsum (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0)
      (hz : (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) ∉ K)
      (w : E x × C.Fiber x) :
      V.linearEquiv ⟨x, ξ⟩ (s.val x ξ w.1, w.2) =
        (t.val x ξ (U.linearEquiv ⟨x, ξ⟩ w).1, (U.linearEquiv ⟨x, ξ⟩ w).2) := by
    have h := hUV ⟨⟨x, ξ⟩, hz⟩ w
    simp only [EquivariantSupportBundleTriple.sum, EquivariantSupportBundleTriple.identity,
      SupportBundleTriple.sum, SupportBundleTriple.identity, SupportBundleTriple.ofBoundary,
      CompactSupportTriple.sum, CompactSupportTriple.enlarge, Iso.restrictTo_apply,
      RelativeTriple.sum_apply, CompactSupportTriple.ofIso] at h
    change V.linearEquiv ⟨x, ξ⟩
      ((ellipticSymbolTriple s.val s.property.1.continuous hi).boundary.linearEquiv
        ⟨⟨x, ξ⟩, hξ⟩ w.1, w.2) =
      ((ellipticSymbolTriple t.val t.property.1.continuous hj).boundary.linearEquiv
        ⟨⟨x, ξ⟩, hξ⟩ (U.linearEquiv ⟨x, ξ⟩ w).1, (U.linearEquiv ⟨x, ξ⟩ w).2) at h
    simpa only [ellipticSymbolTriple_boundary_apply] using h
  have hST : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) ∉ K → ∀ v : A.Fiber x,
      V'.linearEquiv ⟨x, ξ⟩ (S.val x ξ v) =
        T.val x ξ (U'.linearEquiv ⟨x, ξ⟩ v) := by
    intro x ξ hξ hz v
    obtain ⟨w, rfl⟩ := (qE.linearEquiv ⟨x, ξ⟩).surjective v
    have hSsum : S.val x ξ (qE.linearEquiv ⟨x, ξ⟩ w) =
        qF.linearEquiv ⟨x, ξ⟩ (s.val x ξ w.1, w.2) :=
      hS x ξ w.1 (iC.linearEquiv x w.2)
    have hTsum (w' : E' x × D.Fiber x) : T.val x ξ (qE'.linearEquiv ⟨x, ξ⟩ w') =
        qF'.linearEquiv ⟨x, ξ⟩ (t.val x ξ w'.1, w'.2) :=
      hT x ξ w'.1 (iD.linearEquiv x w'.2)
    change qF'.linearEquiv ⟨x, ξ⟩ (V.linearEquiv ⟨x, ξ⟩
      ((qF.linearEquiv ⟨x, ξ⟩).symm (S.val x ξ (qE.linearEquiv ⟨x, ξ⟩ w)))) =
      T.val x ξ (qE'.linearEquiv ⟨x, ξ⟩ (U.linearEquiv ⟨x, ξ⟩
        ((qE.linearEquiv ⟨x, ξ⟩).symm (qE.linearEquiv ⟨x, ξ⟩ w))))
    rw [hSsum, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hTsum]
    exact congrArg (qF'.linearEquiv ⟨x, ξ⟩) (hUVsum x ξ hξ hz w)
  -- The original exterior square gives the full germ-index comparison on these same symbols.
  have hindex := equivariantHomogeneousAnalyticIndex_eq_of_cotangent_germ_iso
    𝓘(ℝ, VG) σA σB σA' σB' hσA hσB hσA' hσB' S T hSi hTi hSg hTg
    K hKcompact U' hU' V' hV' hST
  exact hindexS.symm.trans (hindex.trans hindexT)

end AtiyahSinger
