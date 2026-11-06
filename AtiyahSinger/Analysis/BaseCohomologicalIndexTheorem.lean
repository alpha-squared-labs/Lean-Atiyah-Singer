/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CohomologicalIndexTheorem
public import AtiyahSinger.Geometry.TangentFiberIntegration

/-!
# The cohomological Atiyah--Singer formula on the oriented base

Public module ID: M0319.

T03. The base orientation is the original integral HomologicalOrientation.
Its induced tangent-fiber cohomological orientation fixes the same Thom
inverse used in fiber integration, including either sign in dimension zero.
The supplied tangent metric equips the original fibers with the native
normed structure required by the Thom API, preserving their topology.
The top-degree class below is the actual finite component of
pi!(ch(u)) cup A-hat(TM)^2. No natural-number subtraction is used to disguise
a character component below the fiber rank as a valid integration input.

Sources: SG III.13, second Theorem 13.8, (13.24), p.255; Atiyah--Singer III,
(2.13) and footnote 4, p.557. The Thom map is pi*(a) cup U, with the base
factor first. Interleaved tangent coordinates differ from base-first/fiber-last
coordinates by (-1)^(n*(n-1)/2). Together with the TX formula's (-1)^n this
gives (-1)^(n*(n+1)/2). Wikipedia's unspecified inverse Thom map does not
independently fix this convention. Ordinary pairing on the compact base
uses the same normalized LF class through the original Hc comparison.

The atlas and differential versions retain precisely their original symbols
and indices. The proofs use the same tangent characteristic formula, Thom inverse
and normalized integral orientation; no characteristic-number equality is added as a premise.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The degree-n component of pi!(ch(u)) cup A-hat(TM)^2, with the prescribed Thom inverse. -/
def baseIndexCharacteristicClass (O : HomologicalOrientation n M)
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (u : CompactSupportKZero TM) : singularCohomology ℚ M n :=
  ∑ k : Fin (n / 2 + 1),
    (eqToIso (by congr 1; omega) :
        singularCohomology ℚ M ((n - 2 * k.val) + 2 * k.val) ≅
          singularCohomology ℚ M n).hom
      (singularCohomologyCup ℚ M (n - 2 * k.val) (2 * k.val)
        (tangentCohomologyFiberIntegral (n := n) g O (n - 2 * k.val)
          ((eqToIso (by congr 1; omega) :
              compactSupportCohomology ℚ TM (2 * (n - k.val)) ≅
                compactSupportCohomology ℚ TM ((n - 2 * k.val) + n)).hom
            (g.tangentCompactSupportChernCharacterComponent (n - k.val) u)))
        (tangentAHatSquareComponent (n := n) hV k.val))

set_option maxHeartbeats 1000000 in
-- The extended limit accommodates the finite characteristic sum, Thom inverse and base orientation
-- transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original topological index equals the oriented base characteristic number. -/
theorem topologicalIndex_eq_base_characteristic_number (O : HomologicalOrientation n M)
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (u : CompactSupportKZero TM) :
    ((topologicalIndex V M u : ℤ) : ℚ) =
      (-1 : ℚ) ^ (n * (n + 1) / 2) *
        compactManifoldCohomologyIntegral O (baseIndexCharacteristicClass O g hV u) := by
  /- Stage 1: apply the existing TX formula to this exact u, g and hV.
  Its tangent orientation is the canonical interleaved orientation, not
  an independently supplied orientation on the total space.
  Stage 2: apply tangent_pairing_eq_base_fiberIntegral to that top-degree
  supported class. The inverse Thom map and base evaluation both arise
  from this same integral O, using the same g for native fiber norms.
  Its factor is (-1)^(n*(n-1)/2); multiplying
  by the TX factor (-1)^n gives the displayed exponent n*(n+1)/2.
  Stage 3: expand the finite top-degree TX component. For 2*k > n its
  ordinary A-hat-square factor vanishes: use the compact Hc-to-ordinary
  equivalence and compactSupportCohomology_subsingleton_above_dim O.
  Every remaining k lies in Fin(n/2+1). Its character degree is exactly
  (n-2*k)+n, so the actual inverse Thom map applies without degree truncation.
  Stage 4: use tangentCohomologyFiberIntegral_projection for each retained
  term. Swap the ordinary A-hat factor past the integrated character by
  graded commutativity; its degree 2*k is even, hence this gives no sign.
  Linearity and canonical degree transports yield precisely the displayed
  finite class. In dimension zero, reversing O reverses both the fiber
  Thom inverse and base evaluation, so signed points are retained. The
  empty and disconnected cases use the same original componentwise maps. -/
  have hintegral : tangentCohomologyFiberIntegral g O n
      ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ TM (2 * n) ≅
          compactSupportCohomology ℚ TM (n + n)).hom
        (tangentIndexCharacteristicClass g hV u)) =
      baseIndexCharacteristicClass O g hV u := by
    classical
    let cT {p q : ℕ} (h : p = q) : compactSupportCohomology ℚ TM p →ₗ[ℚ]
        compactSupportCohomology ℚ TM q :=
      (eqToIso (congrArg (compactSupportCohomology ℚ TM) h)).hom.hom
    let cH {p q : ℕ} (h : p = q) : singularCohomology ℚ M p →ₗ[ℚ]
        singularCohomology ℚ M q :=
      (eqToIso (congrArg (singularCohomology ℚ M) h)).hom.hom
    have hTcomp {p q r : ℕ} (hpq : p = q) (hqr : q = r)
        (a : compactSupportCohomology ℚ TM p) :
        cT hqr (cT hpq a) = cT (hpq.trans hqr) a := by
      subst q
      subst r
      rfl
    have hHcomp {p q r : ℕ} (hpq : p = q) (hqr : q = r)
        (a : singularCohomology ℚ M p) : cH hqr (cH hpq a) = cH (hpq.trans hqr) a := by
      subst q
      subst r
      rfl
    have hIntegralCast {p q : ℕ} (hpq : p = q)
        (a : compactSupportCohomology ℚ TM (p + n)) :
        cH hpq (tangentCohomologyFiberIntegral g O p a) =
          tangentCohomologyFiberIntegral g O q (cT (congrArg (· + n) hpq) a) := by
      subst q
      rfl
    have hActionCast {p q r : ℕ} (hqr : q = r)
        (a : singularCohomology ℚ TM p) (b : compactSupportCohomology ℚ TM q) :
        compactSupportCohomologyAction ℚ TM p r a (cT hqr b) =
          cT (congrArg (p + ·) hqr) (compactSupportCohomologyAction ℚ TM p q a b) := by
      subst r
      rfl
    let J := (tangentCohomologyFiberIntegral g O n).comp (cT (by omega : 2 * n = n + n))
    let a (k : ℕ) := tangentAHatSquareComponent (n := n) hV k
    let b (k : ℕ) := g.tangentCompactSupportChernCharacterComponent (n - k) u
    let p : C(TM, M) := ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩
    let f (k : Fin (n + 1)) : singularCohomology ℚ M n :=
      J (cT (by have := k.isLt; omega)
        (compactSupportCohomologyAction ℚ TM (2 * k.val) (2 * (n - k.val))
          (singularCohomologyPullback ℚ p (2 * k.val) (a k.val)) (b k.val)))
    let t (k : Fin (n / 2 + 1)) : singularCohomology ℚ M n :=
      cH (by have := k.isLt; omega)
        (singularCohomologyCup ℚ M (n - 2 * k.val) (2 * k.val)
          (tangentCohomologyFiberIntegral g O (n - 2 * k.val)
            (cT (by have := k.isLt; omega) (b k.val))) (a k.val))
    -- Above the base dimension the ordinary factor vanishes by compact duality.
    have habove (k : ℕ) (hk : n < 2 * k) : a k = 0 := by
      let := compactSupportCohomology_subsingleton_above_dim O (2 * k) hk
      let e := compactSupportCohomologyIso ℚ M (2 * k)
      have hz : e.inv (a k) = 0 := Subsingleton.elim _ _
      have heq := congrArg e.hom hz
      simpa only [Iso.inv_hom_id_apply, map_zero] using heq
    have hfzero (k : Fin (n + 1)) (hk : n < 2 * k.val) : f k = 0 := by
      dsimp only [f]
      rw [habove k.val hk, map_zero, map_zero, LinearMap.zero_apply, map_zero, map_zero]
    -- Retained terms use the original projection formula and its exact degree transports.
    let e : Fin (n / 2 + 1) → Fin (n + 1) :=
      fun k ↦ ⟨k.val, by have := k.isLt; omega⟩
    have hterm (k : Fin (n / 2 + 1)) : f (e k) = t k := by
      have hk : 2 * k.val ≤ n := by have := k.isLt; omega
      let q := n - 2 * k.val
      let δ := tangentCohomologyFiberIntegral g O q (cT (by dsimp [q]; omega) (b k.val))
      have hproj := tangentCohomologyFiberIntegral_projection g O (2 * k.val) q
        (a k.val) (cT (by dsimp [q]; omega) (b k.val))
      have hpq : 2 * k.val + q = n := by dsimp [q]; omega
      have h := congrArg (cH hpq) hproj
      change cH hpq (tangentCohomologyFiberIntegral g O (2 * k.val + q)
        (cT (by omega)
          (compactSupportCohomologyAction ℚ TM (2 * k.val) (q + n)
            (singularCohomologyPullback ℚ p (2 * k.val) (a k.val))
            (cT (by dsimp [q]; omega) (b k.val))))) =
        cH hpq (singularCohomologyCup ℚ M (2 * k.val) q (a k.val) δ) at h
      rw [hIntegralCast hpq,
        hTcomp (show 2 * k.val + (q + n) = (2 * k.val + q) + n by omega)
          (show (2 * k.val + q) + n = n + n by omega),
        hActionCast (show 2 * (n - k.val) = q + n by dsimp [q]; omega),
        hTcomp (show 2 * k.val + 2 * (n - k.val) = 2 * k.val + (q + n) by
          dsimp [q]; omega)
          (show 2 * k.val + (q + n) = n + n by omega)] at h
      have hcomm := singularCohomologyCup_comm ℚ M (2 * k.val) q (a k.val) δ
      have hsign : (-1 : ℚ) ^ ((2 * k.val) * q) = 1 := by
        rw [Nat.mul_assoc, pow_mul]
        norm_num
      rw [hsign, one_smul] at hcomm
      have hc := congrArg (cH (by omega : q + 2 * k.val = n)) hcomm
      change cH (by omega : q + 2 * k.val = n)
        (cH (Nat.add_comm (2 * k.val) q) _) = _ at hc
      rw [hHcomp (Nat.add_comm (2 * k.val) q)
        (show q + 2 * k.val = n by omega)] at hc
      dsimp only [f, J, e, t, LinearMap.comp_apply]
      rw [hTcomp (show 2 * k.val + 2 * (n - k.val) = 2 * n by omega)
        (show 2 * n = n + n by omega)]
      exact h.trans hc
    -- The smaller Fin range consists exactly of the nonvanishing possible base degrees.
    have hsum : (∑ k, t k) = ∑ k, f k := by
      apply Finset.sum_of_injOn e
      · intro i _ j _ hij
        exact Fin.ext (congrArg (fun z : Fin (n + 1) ↦ z.val) hij)
      · intro i _
        exact Finset.mem_univ _
      · intro k _ hk
        apply hfzero
        by_contra hle
        apply hk
        refine ⟨⟨k.val, by omega⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext rfl
      · intro k _
        exact (hterm k).symm
    change J (tangentIndexCharacteristicClass g hV u) = _
    dsimp only [tangentIndexCharacteristicClass]
    rw [map_sum]
    exact hsum.symm
  -- The two geometric orientation signs combine before the actual base evaluation.
  rw [topologicalIndex_eq_tangent_characteristic_number g hV u,
    tangent_pairing_eq_base_fiberIntegral g O, hintegral, ← mul_assoc, ← pow_add]
  have hdegree : n + n * (n - 1) / 2 = n * (n + 1) / 2 := by
    have hle := Nat.le_mul_self n
    simp only [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_one]
    omega
  rw [hdegree]

section AtlasOperator

variable {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- SG (13.24) for the exact atlas PDO and its supplied homogeneous principal representative. -/
theorem AtlasPseudodifferentialOperator.index_eq_base_characteristic_number
    (O : HomologicalOrientation n M)
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
      (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
        (baseIndexCharacteristicClass O g hV
          ((tangentCotangentKZeroEquiv g).symm (atlasSymbolKClass A B a hs hi))) := by
  /- Stage 1: the original atlas index evaluation and K-theoretic index
  theorem identify this exact P with its original atlasSymbolKClass.
  Choose a smooth positive density internally as in the TX theorem;
  preserve the supplied homogeneous representative and principal equality.
  Stage 2: the same musical metric g gives the displayed inverse transport.
  Apply topologicalIndex_eq_base_characteristic_number with the original O.
  The radial metric q is not identified with g; no equal-rank, connectedness
  or positive-dimension premise is added. Cross-component smoothing and
  finite clopen rank decomposition are handled by the invoked comparisons. -/
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  -- The actual homogeneous representative evaluates the index of this same operator.
  have hindex := P.analyticIndexOfComponents_atlasSymbolKClass μ q a hs hh hp hi
  rw [analyticIndexOfComponents_eq_cotangentTopologicalIndex μ,
    cotangentTopologicalIndex_eq g] at hindex
  change topologicalIndex V M
    ((tangentCotangentKZeroEquiv g).symm (atlasSymbolKClass A B a hs hi)) =
      P.toLinearMap.index at hindex
  rw [← hindex]
  exact topologicalIndex_eq_base_characteristic_number O g hV _

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

/-- The oriented base formula retains the differential operator's original principal polynomial. -/
theorem DifferentialOperator.index_eq_base_characteristic_number
    (O : HomologicalOrientation n M)
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (hi : P.IsElliptic) :
    ((P.analyticIndex hi : ℤ) : ℚ) =
      (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
        (baseIndexCharacteristicClass O g hV
          ((tangentCotangentKZeroEquiv g).symm (P.symbolKClass μ R hi))) := by
  /- Stage 1: apply DifferentialOperator.index_eq_cotangentTopologicalIndex
  to the same original operator, density, quantization presentation and
  ellipticity witness. Its symbol is its own principal polynomial; a second
  homogeneous representative or equality hypothesis is unnecessary.
  Stage 2: transport that exact symbol by the inverse musical map of g
  and apply the preceding base topological formula using this same O and hV.
  The inverse Thom orientation and base fundamental class remain linked
  through O; no unrelated orientation or characteristic-number premise is
  assumed. All dimensions, including zero, retain the original rank behavior. -/
  -- The intrinsic differential symbol retains the supplied density and presentation.
  rw [P.index_eq_cotangentTopologicalIndex μ R hi, cotangentTopologicalIndex_eq g]
  exact topologicalIndex_eq_base_characteristic_number O g hV _

end DifferentialOperator

end AtiyahSinger
