/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasAnalyticIndex
public import AtiyahSinger.Analysis.DifferentialIndexTheorem
public import AtiyahSinger.Geometry.TangentCharacteristicClasses
public import AtiyahSinger.Geometry.TangentEmbeddingCohomologyIntegral
public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Topology.CompactSupportChernOpenExtension
public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportLocallyFinitePairing
public import AtiyahSinger.Topology.EuclideanTangentChernEvaluation
public import AtiyahSinger.Topology.SupportedNormalThomCharacter
public import AtiyahSinger.Topology.TangentNormalTodd

/-!
# The cohomological Atiyah--Singer formula on the original tangent total space

Public module ID: M0344.

T02. The top-degree class is the finite component of ch(u) cup pi*(A-hat(TM)^2).
Both factors are even, so the existing ordinary-first Hc action has the same
order sign as the source formula. Evaluation uses the actual LF pairing and
the canonically interleaved tangent fundamental class, without orienting M.
The topological and operator indices on the left are the original integers,
cast to the rational coefficients of the characteristic number.

Sources: SG III.13, first Theorem 13.8 and (13.18), p.254; Atiyah--Singer III,
Proposition 2.11 and Index Theorem 2.12, pp.556--557. The latter fixes the
Euclidean Bott normalization: in complex dimension N its character evaluates
to (-1)^N. Combined with the normal defect sign (-1)^(N-n), this gives (-1)^n.
The abbreviated intermediate SG (13.19) must not erase the ambient sign.
Wikipedia's base-manifold formulation uses a Thom inverse whose orientation
convention must be specified before comparing signs; that separate T03 formula
has the base-first factor (-1)^(n*(n+1)/2), not the present TX orientation.

The atlas PDO version retains its supplied homogeneous leading representative;
full-symbol ellipticity alone does not give that representative. It permits
locally varying bundle rank and the original cross-component smoothing terms.
The differential version uses its actual principal polynomial without such an
extra premise. Auxiliary metrics are explicit; the differential symbol retains its supplied
density. No equality of
bundle ranks, connectedness, nonemptiness or positive dimension is assumed.
The proofs retain staged arguments on the original classes, metrics and operators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle Manifold MeasureTheory Topology
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The top-degree supported characteristic class ch(u) cup pi*(A-hat(TM)^2). -/
def tangentIndexCharacteristicClass
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (u : CompactSupportKZero TM) :
    compactSupportCohomology ℚ TM (2 * n) :=
  ∑ k : Fin (n + 1),
    (eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ TM (2 * k.val + 2 * (n - k.val)) ≅
          compactSupportCohomology ℚ TM (2 * n)).hom
      (compactSupportCohomologyAction ℚ TM (2 * k.val) (2 * (n - k.val))
        (singularCohomologyPullback ℚ
          ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ (2 * k.val)
          (tangentAHatSquareComponent (n := n) hV k.val))
        (g.tangentCompactSupportChernCharacterComponent (n - k.val) u))

set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the supported Chern, normal Thom and integral sign comparisons.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- SG (13.18): the original topological index is the canonical TX characteristic number. -/
theorem topologicalIndex_eq_tangent_characteristic_number
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (u : CompactSupportKZero TM) :
    ((topologicalIndex V M u : ℤ) : ℚ) =
      (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ TM (2 * n)
        (tangentIndexCharacteristicClass g hV u)
        (rationalTangentFundamentalClass (n := n) (M := M)) := by
  /- Choose a stabilized proper embedding, then use that same embedding, normal
  quotient, Hermitian metric and tube in every comparison. The Euclidean Bott
  sign and the normal Thom defect are kept until the final parity calculation. -/
  classical
  let : T2Space TM := (tangentBundle_topology V M).1
  let : SecondCountableTopology TM := (tangentBundle_topology V M).2.1
  let : ParacompactSpace TM := (tangentBundle_topology V M).2.2
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (V × V) TM
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace V M
  let : ParacompactSpace M := inferInstance
  -- Adding n zero coordinates also guarantees n ≤ N when the compact base is empty.
  let e := compactEuclideanEmbedding V M
  let N := e.1 + n
  let W := EuclideanSpace ℝ (Fin N)
  let TW := TangentBundle 𝓘(ℝ, W) W
  let : T2Space TW := (tangentBundle_topology W W).1
  let : SecondCountableTopology TW := (tangentBundle_topology W W).2.1
  let : LocallyCompactSpace TW := ChartedSpace.locallyCompactSpace (W × W) TW
  let f := (euclideanZeroAppend e.1 n).comp e.2.1
  have hf : IsSmoothEmbedding 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ f :=
    isSmoothEmbedding_comp e.2.1 (euclideanZeroAppend e.1 n) e.2.2.1
      (euclideanZeroAppend_properties e.1 n).1
  have hp : IsProperMap f := (euclideanZeroAppend_properties e.1 n).2.comp e.2.2.2
  clear_value f
  have hnN : n ≤ N := Nat.le_add_left n e.1
  -- The actual quotient normal and its specified tube give the original K pushforward.
  let S := tangentNormalSplitting f hf
  let tube := (nonempty_tubularNeighborhood (smoothTangentMap f)
    (isImmersion_smoothTangentMap f hf) (isSmoothEmbedding_tangentMap hf).isEmbedding
    (isProperMap_tangentMap hf hp)).some
  let C := ComplexifiedNormalPullback f
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let h := (nonempty_continuousHermitianMetric C).some
  let τ := tangentEmbeddingTubularMap f hf S tube
  let hτ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S tube
  let : T2Space (TotalSpace Unit C) := hτ.isEmbedding.t2Space
  let : LocallyCompactSpace (TotalSpace Unit C) := hτ.locallyCompactSpace
  let r := Module.finrank ℝ W - Module.finrank ℝ V
  have hrn : r = N - n := by simp [r, W]
  have hrN : r + n = N := by omega
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  have hr (z : TM) : Module.finrank ℂ (C z) = r := by
    rw [Module.finrank_baseChange]
    exact ((VectorBundle.continuousLinearEquivAt ℝ (NormalModel V W)
      (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f) z.proj).toLinearEquiv.finrank_eq).trans (by simp [r])
  have hnormal := supportedIntegral_normalChernCharacter_supportedThom f hf.isImmersion
    g h r hr u n
  have htodd (k : ℕ) := inverseTodd_complexifiedNormalPullback_eq f hf.isImmersion hV h k
  let v := h.supportedThomHom u
  have hpush : tangentEmbeddingPushforward f hf hp u =
      compactSupportKZeroOpenPushforward τ hτ v := by rfl
  have htop := DFunLike.congr_fun (topologicalIndex_eq_of_embedding f hf hp) u
  change topologicalIndex V M u =
    euclideanTangentKZeroEquivInt N (tangentEmbeddingPushforward f hf hp u) at htop
  rw [hpush] at htop
  -- Open-extension naturality retains the same supported class in Euclidean Bott evaluation.
  let α := normalCompactSupportChernCharacterComponent f hf.isImmersion N v
  have hα : compactSupportCohomologyToOnePoint ℚ (TotalSpace Unit C) (2 * N) α =
      reducedChernCharacterComponent (OnePoint.infty : OnePoint (TotalSpace Unit C)) N v :=
    normalCompactSupportChernCharacterComponent_toOnePoint f hf.isImmersion N v
  let β := compactSupportCohomologyOpenExtension ℚ τ hτ (2 * N) α
  have hβ := compactSupportChernCharacter_openPushforward τ hτ N v α hα
  have hbott := euclideanTangentKZeroEquivInt_eq_chern_evaluation N
    (compactSupportKZeroOpenPushforward τ hτ v) β hβ
  let := tangentBundleEuclideanChartedSpace (n := n) (M := M)
  let := tangentBundleEuclideanChartedSpace (n := N) (M := W)
  let OM := tangentHomologicalOrientation (n := n) (M := M)
  let OW := tangentHomologicalOrientation (n := N) (M := W)
  have hindex : ((topologicalIndex V M u : ℤ) : ℚ) =
      (-1 : ℚ) ^ N * compactSupportCohomologyIntegral OW β := by
    rw [htop]
    exact hbott
  -- The normalized tube identifies Thom integration with the canonical tangent LF integral.
  have hdim : 2 * N = 2 * n + 2 * r := by omega
  let α' := (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hdim)).hom α
  have hintegral := compactSupportCohomologyIntegral_tangentEmbedding hnN f hf S tube h hr α'
  have hcancel {i j : ℕ} (hij : i = j)
      (a : compactSupportCohomology ℚ (TotalSpace Unit C) i) :
      (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hij.symm)).hom
        ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hij)).hom a) = a := by
    subst j
    rfl
  change compactSupportCohomologyIntegral OM
    (h.supportedComplexCohomologyThomIntegral r hr (2 * n) α') =
      compactSupportCohomologyIntegral OW
        (compactSupportCohomologyOpenExtension ℚ τ hτ (2 * N)
          ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hdim.symm)).hom
            ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hdim)).hom α)))
    at hintegral
  rw [hcancel hdim α] at hintegral
  have hcast (a : ∀ k : ℕ, compactSupportCohomology ℚ (TotalSpace Unit C) (2 * k))
      {i j d : ℕ} (hij : i = j) (hi : 2 * i = d) (hj : 2 * j = d) :
      (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hi)).hom (a i) =
        (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hj)).hom (a j) := by
    subst j
    rfl
  have hαcast := hcast (fun k ↦ normalCompactSupportChernCharacterComponent f hf.isImmersion
    k v) hrN (show 2 * (r + n) = 2 * n + 2 * r by omega) hdim
  rw [hαcast] at hnormal
  -- A-hat has only degrees divisible by four. Its square therefore removes the
  -- component sign of the inverse Todd normal defect without orienting the base.
  have hsign (k : ℕ) : (-1 : ℚ) ^ k • tangentAHatSquareComponent (n := n) hV k =
      tangentAHatSquareComponent (n := n) hV k := by
    by_cases hk : Even k
    · rw [hk.neg_one_pow, one_smul]
    have hzero : tangentAHatSquareComponent (n := n) hV k = 0 := by
      let := RealBundle.isFiniteRank_of_vectorBundle V T
      unfold tangentAHatSquareComponent
      apply Finset.sum_eq_zero
      intro i _
      have hik : i.val + (k - i.val) = k := Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)
      by_cases hi : Even i.val
      · have hki : ¬ Even (k - i.val) := by
          intro heven
          exact hk (hik ▸ hi.add heven)
        simp only [RealBundle.aHatEvenComponent, dite_eq_right hki,
          singularCohomologyEvenCup, map_zero]
      · simp only [RealBundle.aHatEvenComponent, dite_eq_right hi,
          singularCohomologyEvenCup, map_zero, LinearMap.zero_apply]
    rw [hzero, smul_zero]
  -- Keep degree transports explicit while reversing the original finite convolution.
  let term (k l : ℕ) (hkl : 2 * k + 2 * l = 2 * n) :
      compactSupportCohomology ℚ TM (2 * n) :=
    (eqToIso (congrArg (compactSupportCohomology ℚ TM) hkl)).hom
      (compactSupportCohomologyAction ℚ TM (2 * k) (2 * l)
        (singularCohomologyPullback ℚ
          ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ (2 * k)
          (tangentAHatSquareComponent (n := n) hV k))
        (g.tangentCompactSupportChernCharacterComponent l u))
  have hterm {k l k' l' : ℕ} (hk : k = k') (hl : l = l')
      (hkl : 2 * k + 2 * l = 2 * n) (hkl' : 2 * k' + 2 * l' = 2 * n) :
      term k l hkl = term k' l' hkl' := by
    subst k'
    subst l'
    rfl
  have haction (k l : ℕ) : (-1 : ℚ) ^ k •
      compactSupportCohomologyAction ℚ TM (2 * k) (2 * l)
        (singularCohomologyPullback ℚ
          ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ (2 * k)
          (tangentAHatSquareComponent (n := n) hV k))
        (g.tangentCompactSupportChernCharacterComponent l u) =
      compactSupportCohomologyAction ℚ TM (2 * k) (2 * l)
        (singularCohomologyPullback ℚ
          ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ (2 * k)
          (tangentAHatSquareComponent (n := n) hV k))
        (g.tangentCompactSupportChernCharacterComponent l u) := by
    rw [← LinearMap.smul_apply, ← map_smul,
      ← map_smul (ModuleCat.Hom.hom _), hsign]
  let a (k : Fin (n + 1)) := term k.val (n - k.val) (by omega)
  have hsum : h.supportedComplexCohomologyThomIntegral r hr (2 * n) α' =
      (-1 : ℚ) ^ r • tangentIndexCharacteristicClass g hV u := by
    rw [hnormal]
    change _ = (-1 : ℚ) ^ r • ∑ k, a k
    rw [Finset.smul_sum]
    apply Finset.sum_bij (fun i _ ↦ i.rev)
    · intro i _
      exact Finset.mem_univ _
    · intro i _ j _ hij
      exact Fin.rev_injective hij
    · intro i _
      exact ⟨i.rev, Finset.mem_univ _, Fin.rev_rev i⟩
    · intro i _
      rw [htodd (n - i.val), ← tangentAHatSquareComponent_eq_todd hV (n - i.val)]
      rw [pow_add, mul_smul]
      congr 1
      rw [← map_smul (ModuleCat.Hom.hom _), haction]
      change term (n - i.val) i.val (by omega) =
        term i.rev.val (n - i.rev.val) (by omega)
      exact hterm (by simp [Fin.val_rev]) (by simp only [Fin.val_rev]; omega)
        (by omega) (by omega)
  -- The ambient Bott sign (-1)^N and rank sign (-1)^(N-n) leave precisely (-1)^n.
  rw [hintegral.symm, hsum, map_smul] at hindex
  have hsignNr : (-1 : ℚ) ^ N * (-1 : ℚ) ^ r = (-1 : ℚ) ^ n := by
    rw [← pow_add]
    have heq : N + r = n + 2 * r := by omega
    rw [heq, pow_add, pow_mul]
    norm_num
  rw [smul_eq_mul, ← mul_assoc, hsignNr] at hindex
  exact hindex


section AtlasOperator

variable {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- The TX characteristic formula for an original atlas elliptic PDO and its same symbol. -/
theorem AtlasPseudodifferentialOperator.index_eq_tangent_characteristic_number
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (q : SmoothCotangentMetric (n := n) (M := M))
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
    (hp : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
      (atlasRegularizedSymbol A B q m a hs hh)) (hi : IsEllipticAtlasSymbol a) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ TM (2 * n)
        (tangentIndexCharacteristicClass g hV
          ((tangentCotangentKZeroEquiv g).symm (atlasSymbolKClass A B a hs hi)))
        (rationalTangentFundamentalClass (n := n) (M := M)) := by
  /- Stage 1: choose a smooth positive density on the compact smooth base
  with its Borel measurable structure. The analyticIndexOfComponents evaluation
  theorem identifies the index of this exact P with its atlasSymbolKClass A B a hs hi.
  Keep q, the homogeneous representative and its actual principal equality.
  Stage 2: the K-theoretic Atiyah--Singer theorem identifies the original analytic
  and cotangent topological homomorphisms. Use the supplied g in
  cotangentTopologicalIndex_eq on this same actual symbol class.
  Stage 3: apply the tangent characteristic-number theorem to the resulting
  inverse musical image and cast the integer index into Q. The radial metric q
  and tangent metric g have distinct roles. Finite clopen rank decomposition and
  off-diagonal smoothing are handled by the analytic evaluation theorem. -/
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  -- Evaluate this operator on the same homogeneous symbol and use its musical transport.
  have hindex := P.analyticIndexOfComponents_atlasSymbolKClass μ q a hs hh hp hi
  rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ,
    cotangentTopologicalIndex_eq g] at hindex
  change topologicalIndex V M
    ((tangentCotangentKZeroEquiv g).symm (atlasSymbolKClass A B a hs hi)) =
      P.toLinearMap.index at hindex
  rw [← hindex]
  exact topologicalIndex_eq_tangent_characteristic_number g hV _

end AtlasOperator

section DifferentialOperator

variable [MeasurableSpace M] [BorelSpace M]
  {r q : ℕ} {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The TX characteristic formula for a differential operator's original principal polynomial. -/
theorem DifferentialOperator.index_eq_tangent_characteristic_number
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    {m : ℕ}
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (hi : P.IsElliptic) :
    ((P.analyticIndex hi : ℤ) : ℚ) =
      (-1 : ℚ) ^ n * compactSupportLocallyFinitePairing ℚ TM (2 * n)
        (tangentIndexCharacteristicClass g hV
          ((tangentCotangentKZeroEquiv g).symm (P.symbolKClass μ R hi)))
        (rationalTangentFundamentalClass (n := n) (M := M)) := by
  /- Stage 1: DifferentialOperator.index_eq_cotangentTopologicalIndex uses this
  exact operator's own homogeneous principal polynomial, so hi suffices without
  a separate homogeneous-symbol hypothesis. The intrinsic-symbol comparison
  keeps the original bundles and polynomial, including order zero and the
  dimension-zero rank difference.
  Stage 2: use cotangentTopologicalIndex_eq with the same g and apply the tangent
  characteristic formula to the inverse musical image. Cast the original integer
  analytic index to Q. Retain the supplied density and R in the symbol construction;
  neither bundle rank equality nor base orientation is assumed. -/
  rw [P.index_eq_cotangentTopologicalIndex μ R hi, cotangentTopologicalIndex_eq g]
  exact topologicalIndex_eq_tangent_characteristic_number g hV _

end DifferentialOperator

end AtiyahSinger
