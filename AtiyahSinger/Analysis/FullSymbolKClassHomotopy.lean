/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.FullSymbolKClass
public import AtiyahSinger.Analysis.SymbolKClass
public import AtiyahSinger.Topology.BundleIsoAffineHomotopy
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Choice independence of the general full-symbol K class

Public module ID: M2284.

A one-order-lower difference is a uniformly small relative perturbation beyond one radius
for the entire affine interval. The finite original chart cover gives one compact control
for that interval. The existing affine bundle homotopy then identifies the two actual
symbol classes. Any compact exterior of the same symbol computes that class, and
homogeneous regularization has the accepted original off-zero symbol class. No continuity
assertion about a family of quantized operators is used.

Sources: SG III.3.13 for the principal quotient and SG I.9.26 for compact-support triples.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle IsManifold
open scoped Manifold ContDiff unitInterval

/-- A lower-order difference gives one elliptic exterior for the entire affine interval. -/
theorem IsEllipticFullSymbol.exists_radius_affine_of_lowerOrder {n r q : ℕ} {m : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {a b : SymbolFunction n r q}
    (ha : IsEllipticFullSymbol U m a) (hab : IsSymbol U (m - 1) (b - a))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ (t : unitInterval) x, x ∈ K →
      ∀ ξ : EuclideanSpace ℝ (Fin n), R ≤ ‖ξ‖ →
        ((1 - (t : ℂ)) • a x ξ + (t : ℂ) • b x ξ).IsInvertible := by
  /- The order-minus-m inverse estimate and the order-(m-1) difference give a relative
  bound C D/(1+norm ξ). The interval coefficient has norm at most one, so a single radius
  makes the full affine family a small perturbation of the same original inverse. -/
  classical
  obtain ⟨R₀, C, hR₀, hC, hbound⟩ := ha K hKU hK
  obtain ⟨D, hD, hdiff⟩ := hab.2 K hKU hK 0 0
  have hdiff_zero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K)
      (ξ : EuclideanSpace ℝ (Fin n)) :
      ‖(b - a) x ξ‖ ≤ D * (1 + ‖ξ‖) ^ (m - 1) := by
    simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
      using hdiff x hx ξ
  refine ⟨max R₀ (2 * C * D), lt_of_lt_of_le hR₀ (le_max_left _ _), ?_⟩
  intro t x hx ξ hξ
  obtain ⟨hinv, hinvnorm⟩ := hbound x hx ξ ((le_max_left _ _).trans hξ)
  let e := (t : ℂ) • (b - a) x ξ
  let T := (1 - (t : ℂ)) • a x ξ + (t : ℂ) • b x ξ
  have hTeq : T = a x ξ + e := by
    dsimp only [T, e]
    simp only [Pi.sub_apply]
    module
  -- The same perturbation bound works for every t in the closed unit interval.
  have henorm : ‖e‖ ≤ D * (1 + ‖ξ‖) ^ (m - 1) := by
    calc
      ‖e‖ = (t : ℝ) * ‖(b - a) x ξ‖ := by
        dsimp only [e]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
      _ ≤ 1 * ‖(b - a) x ξ‖ :=
        mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
      _ = ‖(b - a) x ξ‖ := one_mul _
      _ ≤ D * (1 + ‖ξ‖) ^ (m - 1) := hdiff_zero x hx ξ
  have hweight : 0 < 1 + ‖ξ‖ := by positivity
  have hsmall : ‖(a x ξ).inverse‖ * ‖e‖ ≤ 1 / 2 := by
    calc
      ‖(a x ξ).inverse‖ * ‖e‖ ≤
          (C * (1 + ‖ξ‖) ^ (-m)) * (D * (1 + ‖ξ‖) ^ (m - 1)) :=
        mul_le_mul hinvnorm henorm (norm_nonneg _) (by positivity)
      _ = C * D * (1 + ‖ξ‖) ^ (-1 : ℝ) := by
        rw [show (-1 : ℝ) = -m + (m - 1) by ring, Real.rpow_add hweight]
        ring
      _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hweight]
        have hlarge := (le_max_right R₀ (2 * C * D)).trans hξ
        linarith
  -- Apply the standard geometric-series inverse on the original input endomorphism space.
  let L := (a x ξ).inverse.comp e
  have hLsmall : ‖L‖ < 1 :=
    lt_of_le_of_lt (((a x ξ).inverse.opNorm_comp_le e).trans hsmall) (by norm_num)
  have hunit : IsUnit (1 + L) := by
    have h := (Units.oneSub (-L) (by simpa only [norm_neg] using hLsmall)).isUnit
    change IsUnit (1 - -L) at h
    simpa only [sub_neg_eq_add] using h
  have hnormalized : (a x ξ).inverse.comp T = 1 + L := by
    rw [hTeq, ContinuousLinearMap.comp_add, hinv.inverse_comp_self]
    rfl
  have hnormalized_bijective : Function.Bijective ((a x ξ).inverse.comp T) := by
    rw [hnormalized]
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  -- Compose with that same original a; its inverse identities recover the actual affine map.
  have hrecovery : (a x ξ).comp ((a x ξ).inverse.comp T) = T := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, hinv.self_apply_inverse]
  have hTbijective : Function.Bijective T := by
    rw [← hrecovery]
    exact hinv.bijective.comp hnormalized_bijective
  exact ⟨(LinearEquiv.ofBijective T.toLinearMap hTbijective).toContinuousLinearEquiv, rfl⟩

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- One metric disk controls a full-symbol affine family with a lower-order difference. -/
theorem IsEllipticFullGlobalSymbol.exists_metric_radius_affine_of_lowerOrder {m : ℝ}
    {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a)
    (hab : IsGlobalSymbol (r := r) (q := q) E F (m - 1) (b - a))
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 0 < R ∧ ∀ (t : unitInterval) x (ξ : CotangentFiber (n := n) x),
      R < g.length x ξ → ((1 - (t : ℂ)) • a x ξ + (t : ℂ) • b x ξ).IsInvertible := by
  /- On each original compact patch, choose the radius before quantifying over t. The
  existing finite cotangent chart theorem combines these radii, preserving one exterior for
  the whole interval. The same two frames transport its local affine map to the native map. -/
  classical
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q) (E := E) (F := F)
  let K (i : Fin A.size) := tsupport (A.patch i).input.cutoff
  let (i : Fin A.size) : MemTrivializationAtlas (A.patch i).input.frame :=
    (A.patch i).input.frame_mem_atlas
  let (i : Fin A.size) : MemTrivializationAtlas (A.patch i).output.frame :=
    (A.patch i).output.frame_mem_atlas
  have hKU (i : Fin A.size) :
      K i ⊆ symbolChartDomain E F (A.patch i).chart
        (A.patch i).input.frame (A.patch i).output.frame := by
    intro z hz
    exact ⟨(A.patch i).input.support_subset hz,
      (A.patch i).input_support_in_output_frame hz⟩
  -- The actual difference in these frames retains its one-order-lower estimate.
  have hlocal (i : Fin A.size) : ∃ R : ℝ, ∀ (t : unitInterval) z, z ∈ K i →
      ∀ η : EuclideanSpace ℝ (Fin n), R ≤ ‖η‖ →
        ((1 - (t : ℂ)) • globalSymbolInChart E F a (A.patch i).chart
          (A.patch i).input.frame (A.patch i).output.frame z η +
            (t : ℂ) • globalSymbolInChart E F b (A.patch i).chart
              (A.patch i).input.frame (A.patch i).output.frame z η).IsInvertible := by
    have hdiff := hab (A.patch i).chart (A.patch i).chart_mem_atlas
      (A.patch i).input.frame (A.patch i).output.frame
    have hcoord : globalSymbolInChart E F (b - a) (A.patch i).chart
        (A.patch i).input.frame (A.patch i).output.frame =
          globalSymbolInChart E F b (A.patch i).chart
            (A.patch i).input.frame (A.patch i).output.frame -
              globalSymbolInChart E F a (A.patch i).chart
                (A.patch i).input.frame (A.patch i).output.frame := by
      ext z η v
      simp [globalSymbolInChart]
    rw [hcoord] at hdiff
    obtain ⟨R, _, hbound⟩ :=
      (ha (A.patch i).chart (A.patch i).chart_mem_atlas
        (A.patch i).input.frame (A.patch i).output.frame).exists_radius_affine_of_lowerOrder
          hdiff (K i) (hKU i) (A.patch i).input.compact_support
    exact ⟨R, hbound⟩
  choose R hbound using hlocal
  have hcover (x : M) : ∃ i : Fin A.size,
      x ∈ (A.patch i).chart.source ∧ (A.patch i).chart x ∈ K i := by
    have hactive : ∃ i : Fin A.size, (A.patch i).weight x ≠ 0 := by
      by_contra h
      push Not at h
      have hsum := A.sum_weight x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hactive
    have hx : x ∈ (A.patch i).chart.source := by
      by_contra hx
      exact hi (by simp [QuantizationPatch.weight, hx])
    have hcut : (A.patch i).input.cutoff ((A.patch i).chart x) ≠ 0 := by
      simpa only [QuantizationPatch.weight, ite_eq_left hx] using hi
    exact ⟨i, hx, subset_tsupport _ hcut⟩
  obtain ⟨L, hL, hlarge⟩ := exists_metric_radius_of_cotangent_chart_cover g
    (fun i : Fin A.size ↦ (A.patch i).chart)
    (fun i ↦ subset_maximalAtlas («I» := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (n := ∞) (A.patch i).chart_mem_atlas)
    K (fun i ↦ (A.patch i).input.compact_support)
    (fun i z hz ↦ ((A.patch i).input.support_subset hz).1) hcover R
  refine ⟨L, hL, ?_⟩
  intro t x ξ hξ
  obtain ⟨i, hx, hwindow, hfreq⟩ := hlarge x ξ hξ.le
  have he : x ∈ (A.patch i).input.frame.baseSet := by
    have h := (hKU i hwindow).1.2
    simpa only [Set.mem_preimage, (A.patch i).chart.left_inv hx] using h
  have hf : x ∈ (A.patch i).output.frame.baseSet := by
    have h := (hKU i hwindow).2
    simpa only [Set.mem_preimage, (A.patch i).chart.left_inv hx] using h
  let ec := (A.patch i).input.frame.continuousLinearEquivAt ℂ x he
  let fc := (A.patch i).output.frame.continuousLinearEquivAt ℂ x hf
  let η := covectorInChart (A.patch i).chart x ξ
  let H : GlobalSymbolFunction (n := n) E F := (1 - (t : ℂ)) • a + (t : ℂ) • b
  -- This local affine matrix is the same full affine map in the original two frames.
  have hinv : (globalSymbolInChart E F H (A.patch i).chart
      (A.patch i).input.frame (A.patch i).output.frame ((A.patch i).chart x) η).IsInvertible := by
    simpa only [H, globalSymbolInChart_add, globalSymbolInChart_smul, Pi.add_apply, Pi.smul_apply]
      using hbound i t ((A.patch i).chart x) hwindow η hfreq
  have hmatrix : globalSymbolInChart E F H (A.patch i).chart
      (A.patch i).input.frame (A.patch i).output.frame ((A.patch i).chart x) η =
        fc.toContinuousLinearMap.comp ((H x ξ).comp ec.symm.toContinuousLinearMap) := by
    dsimp only [globalSymbolInChart]
    rw [(A.patch i).chart.left_inv hx,
      covectorFromChart_covectorInChart (A.patch i).chart (A.patch i).chart_mem_atlas x hx ξ]
    rw [← (A.patch i).output.frame.coe_continuousLinearEquivAt_eq' (R := ℂ) hf,
      ← (A.patch i).input.frame.symm_continuousLinearEquivAt_eq' (R := ℂ) he]
  rw [hmatrix] at hinv
  simpa only [ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv, H, Pi.add_apply, Pi.smul_apply] using hinv

/-- The standard full-symbol K class depends only on the genuine principal quotient class. -/
theorem fullSymbolKClass_eq_of_principalClass_eq {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (hb : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val)
    (hab : globalPrincipalSymbolClass E F m a = globalPrincipalSymbolClass E F m b) :
    fullSymbolKClass a ha = fullSymbolKClass b hb := by
  /- The quotient equality supplies the actual difference b-a of one lower order. Construct
  one affine exterior, enlarge the two original triples to contain it and both original
  controls, and apply the existing homotopy invariance of their compact-support classes. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  have hdiff : IsGlobalSymbol (r := r) (q := q) E F (m - 1) (b.val - a.val) :=
    (globalPrincipalSymbolClass_eq_iff E F m b a).mp hab.symm
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  obtain ⟨R, _, hfamily⟩ := ha.exists_metric_radius_affine_of_lowerOrder hdiff g
  let D : Set (CotangentTotalSpace (n := n) (M := M)) := {z | g.length z.proj z.snd ≤ R}
  let A := fullSymbolTriple a ha
  let B := fullSymbolTriple b hb
  let K := (A.control ∪ B.control) ∪ D
  have hK : IsCompact K :=
    (A.isCompact_control.union B.isCompact_control).union (g.isCompact_sublevel R)
  have hA : A.control ⊆ K := Set.subset_union_left.trans Set.subset_union_left
  have hB : B.control ⊆ K := Set.subset_union_right.trans Set.subset_union_left
  -- Both endpoint boundary maps are their actual symbols on the same compact exterior.
  have hhom : A.Homotopic B := by
    apply A.homotopic_of_affine B K hK hA hB
    intro t z
    have hzD : z.val ∉ D := fun hz ↦ z.property (Set.subset_union_right hz)
    have hinv := hfamily t z.val.proj z.val.snd (lt_of_not_ge hzD)
    change Function.Bijective (fun v : E z.val.proj ↦
      (1 - (t : ℂ)) • ((A.enlarge K hK hA).boundary.linearEquiv z v : F z.val.proj) +
        (t : ℂ) • ((B.enlarge K hK hB).boundary.linearEquiv z v : F z.val.proj))
    have hfun : (fun v : E z.val.proj ↦
        (1 - (t : ℂ)) • ((A.enlarge K hK hA).boundary.linearEquiv z v : F z.val.proj) +
          (t : ℂ) • ((B.enlarge K hK hB).boundary.linearEquiv z v : F z.val.proj)) =
        ⇑((1 - (t : ℂ)) • a.val z.val.proj z.val.snd +
          (t : ℂ) • b.val z.val.proj z.val.snd) := by
      funext v
      let zA : ↥((fullSymbolTriple a ha).controlᶜ) := ⟨z.val, fun hz ↦ z.property (hA hz)⟩
      let zB : ↥((fullSymbolTriple b hb).controlᶜ) := ⟨z.val, fun hz ↦ z.property (hB hz)⟩
      have hAouter := A.enlarge_apply K hK hA z v
      have hBouter := B.enlarge_apply K hK hB z v
      dsimp only [A] at hAouter
      dsimp only [B] at hBouter
      have hleft : ((A.enlarge K hK hA).boundary.linearEquiv z v : F z.val.proj) =
          a.val z.val.proj z.val.snd v :=
        hAouter.trans (fullSymbolTriple_boundary_apply a ha zA v)
      have hright : ((B.enlarge K hK hB).boundary.linearEquiv z v : F z.val.proj) =
          b.val z.val.proj z.val.snd v :=
        hBouter.trans (fullSymbolTriple_boundary_apply b hb zB v)
      exact congrArg₂ (fun v w ↦ (1 - (t : ℂ)) • v + (t : ℂ) • w) hleft hright
    exact hfun.symm ▸ hinv.bijective
  change A.compactSupportClass = B.compactSupportClass
  exact A.compactSupportClass_eq_of_homotopic B hhom

/-- Any compact exterior of the same actual full symbol computes its constructed K class. -/
theorem fullSymbolKClass_eq_tripleWithControl {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (D : Set (CotangentTotalSpace (n := n) (M := M))) (hD : IsCompact D)
    (hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ D → (a.val z.proj z.snd).IsInvertible) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    fullSymbolKClass a ha = (fullSymbolTripleWithControl a D hD hi).compactSupportClass := by
  /- Enlarge the chosen triple and the supplied triple to their compact union. Their
  forward maps are both the same original a, so their exterior isomorphisms agree exactly. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let A := fullSymbolTriple a ha
  let B := fullSymbolTripleWithControl a D hD hi
  let K := A.control ∪ B.control
  have hK : IsCompact K := A.isCompact_control.union B.isCompact_control
  have heq : A.enlarge K hK Set.subset_union_left =
      B.enlarge K hK Set.subset_union_right := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change E z.val.proj at v
    let zA : ↥((fullSymbolTriple a ha).controlᶜ) :=
      ⟨z.val, fun hz ↦ z.property (Set.subset_union_left hz)⟩
    let zB : ↥(Dᶜ) := ⟨z.val, fun hz ↦ z.property (Set.subset_union_right hz)⟩
    have hAouter := A.enlarge_apply K hK Set.subset_union_left z v
    have hBouter := B.enlarge_apply K hK Set.subset_union_right z v
    dsimp only [A] at hAouter
    dsimp only [B] at hBouter
    have hleft : ((A.enlarge K hK Set.subset_union_left).boundary.linearEquiv z v :
        F z.val.proj) = a.val z.val.proj z.val.snd v :=
      hAouter.trans (fullSymbolTriple_boundary_apply a ha zA v)
    have hright : ((B.enlarge K hK Set.subset_union_right).boundary.linearEquiv z v :
        F z.val.proj) = a.val z.val.proj z.val.snd v :=
      hBouter.trans (fullSymbolTripleWithControl_boundary_apply a D hD hi zB v)
    exact hleft.trans hright.symm
  change A.compactSupportClass = B.compactSupportClass
  calc
    A.compactSupportClass = (A.enlarge K hK Set.subset_union_left).compactSupportClass :=
      (A.compactSupportClass_enlarge K hK Set.subset_union_left).symm
    _ = (B.enlarge K hK Set.subset_union_right).compactSupportClass :=
      congrArg CompactSupportTriple.compactSupportClass heq
    _ = B.compactSupportClass := B.compactSupportClass_enlarge K hK Set.subset_union_right

/-- Homogeneous regularization has the original off-zero symbol's compact-support class. -/
theorem fullSymbolKClass_regularizedSymbol {m : ℝ}
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) :
    fullSymbolKClass (A.regularizedSymbol m a.val a.property.1 a.property.2)
      ((isEllipticFullGlobalSymbol_regularizedSymbol_iff A m a.val
        a.property.1 a.property.2).mpr hi) =
      symbolKClass a.val a.property.1.continuous hi := by
  /- Beyond one metric radius every contributing chart frequency has norm at least one.
  All active cutoffs then equal one and sum_weight recovers the exact original symbol.
  Enlarge the two actual triples to one compact union and compare their boundary actions. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  obtain ⟨C, hC, hnorm⟩ := A.exists_covectorInChart_norm_bounds g
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  -- Recovery at this metric exterior uses the actual finite cutoffs and signed weights.
  have hsame (x : M) (ξ : CotangentFiber (n := n) x) (hξ : C < g.length x ξ) :
      A.regularizedSymbolFunction a.val x ξ = a.val x ξ := by
    have hcut (i : Fin A.size) : (A.patch i).weight x *
        highFrequencyCutoff n (covectorInChart (A.patch i).chart x ξ) = (A.patch i).weight x := by
      by_cases hw : (A.patch i).weight x = 0
      · simp only [hw, zero_mul]
      · have hbound := (hnorm i x hw ξ).1
        have hlarge : 1 ≤ ‖covectorInChart (A.patch i).chart x ξ‖ := by
          by_contra h
          have hlt := lt_of_not_ge h
          have hscaled := mul_lt_mul_of_pos_left hlt hCpos
          rw [mul_one] at hscaled
          linarith
        rw [highFrequencyCutoff_eq_one _ hlarge, mul_one]
    change (∑ i, (((A.patch i).weight x *
      highFrequencyCutoff n (covectorInChart (A.patch i).chart x ξ) : ℝ) : ℂ) • a.val x ξ) = _
    simp only [hcut, ← Finset.sum_smul, ← Complex.ofReal_sum, A.sum_weight,
      Complex.ofReal_one, one_smul]
  let b := A.regularizedSymbol m a.val a.property.1 a.property.2
  have hb : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val :=
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff A m a.val
      a.property.1 a.property.2).mpr hi
  let T := fullSymbolTriple b hb
  let S := ellipticSymbolTriple a.val a.property.1.continuous hi
  let D : Set (CotangentTotalSpace (n := n) (M := M)) := {z | g.length z.proj z.snd ≤ C}
  let K := (T.control ∪ S.control) ∪ D
  have hK : IsCompact K :=
    (T.isCompact_control.union S.isCompact_control).union (g.isCompact_sublevel C)
  have hT : T.control ⊆ K := Set.subset_union_left.trans Set.subset_union_left
  have hS : S.control ⊆ K := Set.subset_union_right.trans Set.subset_union_left
  -- The full representative and original homogeneous data agree as original fiber maps.
  have heq : T.enlarge K hK hT = S.enlarge K hK hS := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change E z.val.proj at v
    have hzD : z.val ∉ D := fun hz ↦ z.property (Set.subset_union_right hz)
    let zT : ↥((fullSymbolTriple b hb).controlᶜ) := ⟨z.val, fun hz ↦ z.property (hT hz)⟩
    let zS : PuncturedCotangentBundle (n := n) (M := M) :=
      ⟨z.val, fun hz ↦ z.property (hS hz)⟩
    have hTouter := T.enlarge_apply K hK hT z v
    have hSouter := S.enlarge_apply K hK hS z v
    dsimp only [T] at hTouter
    dsimp only [S] at hSouter
    have hleft : ((T.enlarge K hK hT).boundary.linearEquiv z v : F z.val.proj) =
        b.val z.val.proj z.val.snd v :=
      hTouter.trans (fullSymbolTriple_boundary_apply b hb zT v)
    have hright : ((S.enlarge K hK hS).boundary.linearEquiv z v : F z.val.proj) =
        a.val z.val.proj z.val.snd v :=
      hSouter.trans (ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous hi zS v)
    have hmiddle : b.val z.val.proj z.val.snd v = a.val z.val.proj z.val.snd v :=
      congrArg (fun f ↦ f v) (hsame z.val.proj z.val.snd (lt_of_not_ge hzD))
    exact hleft.trans (hmiddle.trans hright.symm)
  change T.compactSupportClass = S.compactSupportClass
  calc
    T.compactSupportClass = (T.enlarge K hK hT).compactSupportClass :=
      (T.compactSupportClass_enlarge K hK hT).symm
    _ = (S.enlarge K hK hS).compactSupportClass :=
      congrArg CompactSupportTriple.compactSupportClass heq
    _ = S.compactSupportClass := S.compactSupportClass_enlarge K hK hS

end AtiyahSinger
