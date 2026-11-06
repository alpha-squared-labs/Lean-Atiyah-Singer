/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.InverseSymbolEstimates
import AtiyahSinger.Analysis.SymbolCoordinateEstimates

/-!
# Quantitative ellipticity of full symbols

Public module ID: M0652.

The compact-local inverse bound for general symbols of type (1,0).
Symbol regularity and ellipticity are separate conditions. This is SG III.4.1--4.4
in the compact-local formulation of Taylor III.1.1--1.3; it does not require a
homogeneous leading term. A radius and bound are chosen before the base point and
frequency on each compact set. The results include lower-order perturbation,
quotient invariance, and
comparison with homogeneous symbols. A compact exhaustion gives one smooth
cutoff inverse without imposing a uniform radius on the whole open base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Topology

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {m : ℝ}

/-- High-frequency invertibility with the order-minus-m inverse bound on each compact set. -/
def IsEllipticFullSymbol (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ)
    (a : SymbolFunction n r q) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      (a x ξ).IsInvertible ∧ ‖(a x ξ).inverse‖ ≤ C * (1 + ‖ξ‖) ^ (-m)

/-- A strictly lower-order perturbation preserves quantitative ellipticity. -/
theorem IsEllipticFullSymbol.add_lowerOrder {a b : SymbolFunction n r q}
    (ha : IsEllipticFullSymbol U m a) (ε : ℝ) (hε : 0 < ε)
    (hb : IsSymbol U (m - ε) b) : IsEllipticFullSymbol U m (a + b) := by
  /- Fix a compact K. The inverse estimate for a and the zeroth estimate for b
  give norm(a⁻¹ b) ≤ C_K (1+norm(ξ))^(-ε). Increase the radius until this is
  at most 1/2. The perturbation inequality gives injectivity of a+b and bounds its inverse
  by twice the inverse norm of a. The original a identifies the dimensions, so
  finite-dimensional injectivity gives surjectivity. The radius is uniform on K.
  This is a finite-dimensional perturbation argument; no regularity of a is needed here. -/
  classical
  intro K hKU hK
  obtain ⟨R, C, hR, hC, hbound⟩ := ha K hKU hK
  obtain ⟨D, hD, hperturb⟩ := hb.2 K hKU hK 0 0
  have hbzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K)
      (ξ : EuclideanSpace ℝ (Fin n)) : ‖b x ξ‖ ≤ D * (1 + ‖ξ‖) ^ (m - ε) := by
    simpa only [symbolDerivative, norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
      using hperturb x hx ξ
  -- Choose one radius for the entire compact set, from the strictly negative relative order.
  have hdecay : Filter.Tendsto (fun t : ℝ ↦ C * D * t ^ (-ε)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hε).const_mul (C * D)
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp
    (hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨max R S, 2 * C, lt_of_lt_of_le hR (le_max_left _ _), by positivity, ?_⟩
  intro x hx ξ hξ
  obtain ⟨hinv, hinvnorm⟩ := hbound x hx ξ ((le_max_left _ _).trans hξ)
  have hweight : 0 < 1 + ‖ξ‖ := by positivity
  have hsmall : ‖(a x ξ).inverse‖ * ‖b x ξ‖ ≤ 1 / 2 := by
    calc
      ‖(a x ξ).inverse‖ * ‖b x ξ‖ ≤
          (C * (1 + ‖ξ‖) ^ (-m)) * (D * (1 + ‖ξ‖) ^ (m - ε)) :=
        mul_le_mul hinvnorm (hbzero x hx ξ) (norm_nonneg _) (by positivity)
      _ = C * D * (1 + ‖ξ‖) ^ (-ε) := by
        rw [show -ε = -m + (m - ε) by ring, Real.rpow_add hweight]
        ring
      _ ≤ 1 / 2 := (hS (1 + ‖ξ‖)
        ((le_max_right R S).trans hξ |>.trans (by linarith [norm_nonneg ξ]))).le
  let T := a x ξ + b x ξ
  -- Absorb the perturbation to obtain the same uniform lower bound on the actual map.
  have hlower (v : EuclideanSpace ℂ (Fin r)) :
      ‖v‖ ≤ (2 * ‖(a x ξ).inverse‖) * ‖T v‖ := by
    have heq : (a x ξ).inverse (T v - b x ξ v) = v := by
      simp only [T, add_apply, add_sub_cancel_right,
        hinv.inverse_apply_self]
    have hestimate : ‖v‖ ≤ ‖(a x ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
      calc
        ‖v‖ = ‖(a x ξ).inverse (T v) - (a x ξ).inverse (b x ξ v)‖ := by
          rw [← map_sub, heq]
        _ ≤ ‖(a x ξ).inverse (T v)‖ + ‖(a x ξ).inverse (b x ξ v)‖ := norm_sub_le _ _
        _ ≤ ‖(a x ξ).inverse‖ * ‖T v‖ +
            ‖(a x ξ).inverse‖ * (‖b x ξ‖ * ‖v‖) :=
          add_le_add ((a x ξ).inverse.le_opNorm _) (((a x ξ).inverse.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((b x ξ).le_opNorm v) (norm_nonneg _)))
        _ ≤ ‖(a x ξ).inverse‖ * ‖T v‖ + (1 / 2) * ‖v‖ := by
          rw [← mul_assoc]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsmall (norm_nonneg v))
    nlinarith
  have hinj : Function.Injective T := by
    intro v w hvw
    have h := hlower (v - w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- The original inverse identifies the two dimensions; injectivity then gives surjectivity.
  let L := (a x ξ).inverse.comp T
  have hLinj : Function.Injective L := by
    intro v w hvw
    apply hinj
    have h := congrArg (a x ξ) hvw
    simpa only [L, ContinuousLinearMap.comp_apply, hinv.self_apply_inverse] using h
  have hLsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinj
  have hsurj : Function.Surjective T := by
    intro v
    obtain ⟨w, hw⟩ := hLsurj ((a x ξ).inverse v)
    refine ⟨w, ?_⟩
    have h := congrArg (a x ξ) hw
    simpa only [L, ContinuousLinearMap.comp_apply, hinv.self_apply_inverse] using h
  have hT : T.IsInvertible :=
    ⟨(LinearEquiv.ofBijective T.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩
  refine ⟨hT, ?_⟩
  -- Apply the lower bound to the actual inverse and preserve its order-minus-m decay.
  have hnorm : ‖T.inverse‖ ≤ 2 * ‖(a x ξ).inverse‖ := by
    apply T.inverse.opNorm_le_bound (by positivity)
    intro v
    simpa only [hT.self_apply_inverse] using hlower (T.inverse v)
  exact hnorm.trans (by nlinarith [hinvnorm])

/-- Ellipticity depends only on the full symbol modulo one lower order. -/
theorem isEllipticFullSymbol_iff_of_isSymbol_sub (a b : SymbolFunction n r q)
    (hab : IsSymbol U (m - 1) (a - b)) :
    IsEllipticFullSymbol U m a ↔ IsEllipticFullSymbol U m b := by
  /- In one direction write b=a-(a-b); in the other write a=b+(a-b).
  Negation preserves the displayed symbol order. Apply the perturbation theorem
  with ε=1 in both directions. All inverse bounds remain compact-local. -/
  -- Negation commutes with full iterated derivatives even when U is not open.
  have hneg : IsSymbol U (m - 1) (-(a - b)) := by
    refine ⟨hab.1.neg, ?_⟩
    intro K hKU hK i j
    obtain ⟨C, hC, hbound⟩ := hab.2 K hKU hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    have hderiv : symbolDerivative (-(a - b)) i j x ξ =
        -symbolDerivative (a - b) i j x ξ := by
      unfold symbolDerivative
      simp only [Pi.neg_apply, iteratedFDeriv_neg]
      exact iteratedFDeriv_neg_apply
    rw [hderiv, norm_neg]
    exact hbound x hx ξ
  -- Both implications use the same actual difference and a uniform one-order gap.
  constructor
  · intro ha
    have h := ha.add_lowerOrder 1 (by norm_num) hneg
    have heq : a + -(a - b) = b := by abel
    rwa [heq] at h
  · intro hb
    have h := hb.add_lowerOrder 1 (by norm_num) hab
    have heq : b + (a - b) = a := by abel
    rwa [heq] at h

/-- For smooth homogeneous data, quantitative ellipticity of its cutoff is off-zero ellipticity. -/
theorem isEllipticFullSymbol_frequencyCutoffSymbol_iff (hU : IsOpen U)
    (a : SymbolFunction n r q)
    (hs : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ {ξ | ξ ≠ 0}))
    (hh : IsHomogeneousSymbol U m a) :
    IsEllipticFullSymbol U m (frequencyCutoffSymbol a) ↔ IsEllipticSymbol U a := by
  /- Forward: use the compact singleton at x, dilate any nonzero ξ beyond both
  the ellipticity radius and the unit cutoff radius, and divide by the positive
  scalar t^m. Reverse: inverse matrices vary continuously on K times the unit
  sphere. Compactness bounds their norms, and homogeneity gives degree -m.
  Compare norm(ξ)^(-m) with (1+norm(ξ))^(-m) for norm(ξ)≥1, including negative m.
  When n=0, both high-frequency and off-zero conditions are vacuous. -/
  classical
  -- Nonzero scalar multiplication preserves bijectivity on the original rectangular Hom space.
  have hsmul {T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)}
      {t : ℝ} (ht : t ≠ 0) (hT : Function.Bijective (t • T)) : Function.Bijective T := by
    constructor
    · intro v w hvw
      apply hT.1
      simp only [smul_apply, hvw]
    · intro v
      obtain ⟨w, hw⟩ := hT.2 (t • v)
      exact ⟨w, smul_right_injective _ ht hw⟩
  constructor
  · intro he x hx ξ hξ
    -- The singleton radius can be exceeded along every nonzero positive ray.
    obtain ⟨R, C, hR, hC, hbound⟩ := he {x} (Set.singleton_subset_iff.mpr hx)
      (isCompact_singleton (x := x))
    let t := max R 1 / ‖ξ‖
    have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have ht : 0 < t := div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hnorm
    have hscale : ‖t • ξ‖ = max R 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact div_mul_cancel₀ _ hnorm.ne'
    have hinv := (hbound x (Set.mem_singleton x) (t • ξ)
      (by rw [hscale]; exact le_max_left _ _)).1
    rw [frequencyCutoffSymbol_eq_of_one_le_norm a x (t • ξ)
      (by rw [hscale]; exact le_max_right _ _), hh x hx ξ hξ t ht] at hinv
    exact hsmul (Real.rpow_pos_of_pos ht m).ne' hinv.bijective
  · intro he K hKU hK
    have hinv (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
        (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) : (a x ξ).IsInvertible :=
      ⟨(LinearEquiv.ofBijective (a x ξ).toLinearMap (he x hx ξ hξ)).toContinuousLinearEquiv,
        rfl⟩
    -- The actual inverse is continuous on K times the unit sphere, also when that set is empty.
    let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
    have hne (ξ : EuclideanSpace ℝ (Fin n))
        (hξ : ξ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ξ ≠ 0 := by
      intro hz
      simp [hz] at hξ
    have hcont : ContinuousOn (fun z ↦ ‖(a z.1 z.2).inverse‖) S := by
      intro z hz
      have haCont : ContinuousWithinAt (Function.uncurry a) S z :=
        (hs.contDiffAt ((hU.prod isOpen_ne).mem_nhds
          ⟨hKU hz.1, hne z.2 hz.2⟩)).continuousAt.continuousWithinAt
      have hiCont : ContinuousAt ContinuousLinearMap.inverse (a z.1 z.2) :=
        ((hinv z.1 (hKU hz.1) z.2 (hne z.2 hz.2)).contDiffAt_map_inverse
          (n := (∞ : WithTop ℕ∞))).continuousAt
      exact (hiCont.comp_continuousWithinAt (f := Function.uncurry a) haCont).norm
    obtain ⟨D, hD⟩ := (hS.image_of_continuousOn hcont).bddAbove
    let C := max D 0
    have hC : 0 ≤ C := le_max_right _ _
    have hbound (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K)
        (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.sphere 0 1) :
        ‖(a x v).inverse‖ ≤ C := (hD ⟨(x, v), ⟨hx, hv⟩, rfl⟩).trans (le_max_left _ _)
    -- A sign-uniform weight comparison retains arbitrary real orders.
    have hweight (t : ℝ) (ht : 1 ≤ t) :
        t ^ (-m) ≤ max 1 ((2 : ℝ) ^ m) * (1 + t) ^ (-m) := by
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      by_cases hm : 0 ≤ m
      · calc
          t ^ (-m) = (2 : ℝ) ^ m * (2 * t) ^ (-m) := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htpos.le]
            rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            simp
          _ ≤ (2 : ℝ) ^ m * (1 + t) ^ (-m) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
            exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          _ ≤ max 1 ((2 : ℝ) ^ m) * (1 + t) ^ (-m) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
      · calc
          t ^ (-m) ≤ (1 + t) ^ (-m) :=
            Real.rpow_le_rpow htpos.le (by linarith) (by linarith)
          _ ≤ max 1 ((2 : ℝ) ^ m) * (1 + t) ^ (-m) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (le_max_left 1 ((2 : ℝ) ^ m)) (Real.rpow_nonneg (by positivity : 0 ≤ 1 + t) _)
    refine ⟨1, C * max 1 ((2 : ℝ) ^ m), zero_lt_one,
      mul_nonneg hC (le_trans zero_le_one (le_max_left _ _)), ?_⟩
    intro x hx ξ hξ
    have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hξ
    have hξne : ξ ≠ 0 := norm_pos_iff.mp hξpos
    rw [frequencyCutoffSymbol_eq_of_one_le_norm a x ξ hξ]
    refine ⟨hinv x (hKU hx) ξ hξne, ?_⟩
    let v := ‖ξ‖⁻¹ • ξ
    have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hξne
    have hscale : ‖ξ‖ • v = ξ := by simp [v, smul_smul, hξpos.ne']
    have ha : a x ξ = ‖ξ‖ ^ m • a x v := by
      rw [← hh x (hKU hx) v (hne v hv) ‖ξ‖ hξpos, hscale]
    have hcancel : ‖ξ‖ ^ m * ‖ξ‖ ^ (-m) = 1 := by
      rw [← Real.rpow_add hξpos]
      simp
    have hvinv := hinv x (hKU hx) v (hne v hv)
    -- Rescaling the same inverse gives degree -m; no inverse is replaced by a new witness.
    have hinverse : (a x ξ).inverse = ‖ξ‖ ^ (-m) • (a x v).inverse := by
      apply ContinuousLinearMap.inverse_eq
      · rw [ha]
        ext w : 1
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          ← Complex.coe_smul, map_smul, smul_smul, ← Complex.ofReal_mul,
          mul_comm (‖ξ‖ ^ (-m)), hcancel, Complex.ofReal_one, one_smul, hvinv.self_apply_inverse,
          ContinuousLinearMap.id_apply]
      · rw [ha]
        ext w : 1
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          ← Complex.coe_smul, map_smul, smul_smul, ← Complex.ofReal_mul,
          hcancel, Complex.ofReal_one, one_smul,
          hvinv.inverse_apply_self, ContinuousLinearMap.id_apply]
    rw [hinverse, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hξpos (-m))]
    calc
      ‖ξ‖ ^ (-m) * ‖(a x v).inverse‖ ≤ ‖ξ‖ ^ (-m) * C :=
        mul_le_mul_of_nonneg_left (hbound x hx v hv) (Real.rpow_nonneg hξpos.le _)
      _ ≤ (C * max 1 ((2 : ℝ) ^ m)) * (1 + ‖ξ‖) ^ (-m) := by
        have h := mul_le_mul_of_nonneg_left (hweight ‖ξ‖ hξ) hC
        nlinarith

set_option maxHeartbeats 800000 in
-- Use a compact exhaustion to construct one inverse symbol with compact-local radius bounds.
/-- The cutoff inverse exists without a single radius valid over the entire open base domain. -/
theorem exists_inverse_symbol_of_isEllipticFullSymbol (hU : IsOpen U)
    (a : SymbolFunction n r q) (ha : IsSymbol U m a)
    (he : IsEllipticFullSymbol U m a) :
    ∃ b : SymbolFunction n q r, IsSymbol U (-m) b ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
        ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → b x ξ = (a x ξ).inverse := by
  set_option maxSynthPendingDepth 25 in
  open Filter Set in
  /- A compact exhaustion gives closed high-frequency regions inside the invertible
  locus. One smooth plateau cuts off the actual inverse throughout the open base.
  After spatial localization, the inverse derivative estimate controls high
  frequencies; compactness controls the remaining bounded frequency region. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let W := EuclideanSpace ℂ (Fin q)
  -- Closed high-frequency sets escape to infinity even near the boundary of U.
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let e : CompactExhaustion U := CompactExhaustion.choice U
  let K : ℕ → Set X := fun j ↦ Subtype.val '' e j
  have hK (j : ℕ) : IsCompact (K j) := (e.isCompact j).image continuous_subtype_val
  have hKU (j : ℕ) : K j ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hcover (L : Set X) (hLU : L ⊆ U) (hL : IsCompact L) :
      ∃ j, L ⊆ interior (K j) := by
    apply hL.elim_directed_cover (fun j ↦ interior (K j)) (fun _ ↦ isOpen_interior)
    · intro x hx
      obtain ⟨j, hj⟩ := e.exists_mem_nhds ⟨x, hLU hx⟩
      have h := hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hj
      exact mem_iUnion.mpr ⟨j, mem_interior_iff_mem_nhds.mpr h⟩
    · exact Monotone.directed_le (fun i j hij ↦ interior_mono (image_mono (e.subset hij)))
  choose R C hR hC hInv using fun j ↦ he (K j) (hKU j) (hK j)
  let T : ℕ → ℝ := fun j ↦ max (R j) (j : ℝ)
  let S : ℕ → Set (X × X) := fun j ↦ K j ×ˢ {ξ | T j ≤ ‖ξ‖}
  have hSfinite : LocallyFinite S := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z.2‖
    refine ⟨{w : X × X | ‖w.2‖ < (N : ℝ)},
      (isOpen_lt continuous_snd.norm continuous_const).mem_nhds hN, ?_⟩
    apply (finite_Iio N).subset
    intro j hj
    obtain ⟨w, hw, hwN⟩ := hj
    have hjw : (j : ℝ) ≤ ‖w.2‖ := (le_max_right _ _).trans hw.2
    exact_mod_cast hjw.trans_lt hwN
  have hSclosed : IsClosed (⋃ j, S j) := hSfinite.isClosed_iUnion fun j ↦
    (hK j).isClosed.prod (isClosed_le continuous_const continuous_norm)
  let O : Set (X × X) := {z | z.1 ∈ U ∧ (a z.1 z.2).IsInvertible}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hdom : U ×ˢ (univ : Set X) ∈ 𝓝 z :=
      (hU.prod isOpen_univ).mem_nhds ⟨hz.1, mem_univ _⟩
    have hcont := (ha.1.contDiffAt hdom).continuousAt
    exact Filter.inter_mem (continuous_fst.continuousAt (hU.mem_nhds hz.1))
      (hcont (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hz.2))
  have hSO : (⋃ j, S j) ⊆ O := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact ⟨hKU j hj.1, (hInv j z.1 hj.1 z.2 ((le_max_left _ _).trans hj.2)).1⟩
  obtain ⟨O', hO', hSO', hO'O⟩ := normal_exists_closure_subset hSclosed hO hSO
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO' hSclosed hSO'
  have hχO : tsupport χ ⊆ O := by
    rw [tsupport, hχsupp]
    exact hO'O
  let b : SymbolFunction n q r := fun x ξ ↦ χ (x, ξ) • (a x ξ).inverse
  have hb : ContDiff ℝ ∞ (Function.uncurry b) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport χ
    · have hzO := hχO hz
      have hdom : U ×ˢ (univ : Set X) ∈ 𝓝 z :=
        (hU.prod isOpen_univ).mem_nhds ⟨hzO.1, mem_univ _⟩
      have hia : ContDiffAt ℝ ∞
          (ContinuousLinearMap.inverse : (V →L[ℂ] W) → (W →L[ℂ] V)) (a z.1 z.2) :=
        (hzO.2.contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
      have hiaa := ContDiffAt.comp (f := Function.uncurry a)
        (g := (ContinuousLinearMap.inverse : (V →L[ℂ] W) → (W →L[ℂ] V)))
        z hia (ha.1.contDiffAt hdom)
      exact hχ.contDiffAt.smul hiaa
    · apply (contDiffAt_const (c := (0 : W →L[ℂ] V))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
      change χ w • (a w.1 w.2).inverse = 0
      rw [image_eq_zero_of_notMem_tsupport hw, zero_smul]
  have heq (j : ℕ) (x : X) (hx : x ∈ K j) (ξ : X) (hξ : T j ≤ ‖ξ‖) :
      b x ξ = (a x ξ).inverse := by
    have hχx : χ (x, ξ) = 1 := (hχone _).mp (mem_iUnion.mpr ⟨j, hx, hξ⟩)
    simp only [b, hχx, one_smul]
  refine ⟨b, ?_, ?_⟩
  · refine ⟨hb.contDiffOn, ?_⟩
    intro L hLU hL i j
    -- On a compact spatial neighborhood replace a by one globally smooth symbol.
    obtain ⟨V₀, hV₀, hLV₀, hV₀U, hcV₀⟩ :=
      exists_open_between_and_isCompact_closure hL hU hLU
    obtain ⟨V₁, hV₁, hV₀V₁, hV₁U, hcV₁⟩ :=
      exists_open_between_and_isCompact_closure hcV₀ hU hV₀U
    obtain ⟨ψ, hψ, _, hψsupp, hψone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₁ isClosed_closure hV₀V₁
    have hcψ : HasCompactSupport ψ := by
      simpa only [HasCompactSupport, tsupport, hψsupp] using hcV₁
    have hψU : tsupport ψ ⊆ U := by
      simpa only [tsupport, hψsupp] using hV₁U
    let a' := zeroExtendedSymbol U ψ a
    have ha' : IsSymbol univ m a' :=
      isSymbol_zeroExtendedSymbol U hU m ψ hψ hcψ hψU a ha
    have ha'eq (x : X) (hx : x ∈ V₀) (ξ : X) : a' x ξ = a x ξ := by
      have hψx : ψ x = 1 := (hψone x).mp (subset_closure hx)
      change zeroExtendedSymbol U ψ a x ξ = a x ξ
      rw [zeroExtendedSymbol_apply_of_mem U ψ a x ξ (hV₀U (subset_closure hx)), hψx]
      simp
    obtain ⟨R₀, B, hR₀, hB, hbound⟩ := he L hLU hL
    obtain ⟨D, hD, hD_bound⟩ := exists_symbolDerivative_inverse_bound m a' ha' L hL R₀ B hB
      (fun x hx ξ hξ ↦ by rw [ha'eq x (hLV₀ hx)]; exact (hbound x hx ξ hξ).1)
      (fun x hx ξ hξ ↦ by rw [ha'eq x (hLV₀ hx)]; exact (hbound x hx ξ hξ).2) i j
    obtain ⟨k, hk⟩ := hcover L hLU hL
    let R₁ := max R₀ (T k + 1)
    have hR₁ : 0 < R₁ := hR₀.trans_le (le_max_left _ _)
    -- Above one compact-local radius both totalized maps agree on neighborhoods.
    have hhigh (x : X) (hx : x ∈ L) (ξ : X) (hξ : R₁ ≤ ‖ξ‖) :
        ‖symbolDerivative b i j x ξ‖ ≤ D * (1 + ‖ξ‖) ^ (-m - (j : ℝ)) := by
      have hstrict : T k < ‖ξ‖ := by
        have := (le_max_right R₀ (T k + 1)).trans hξ
        linarith
      have hnear : Function.uncurry b =ᶠ[𝓝 (x, ξ)]
          Function.uncurry (fun y η ↦ (a' y η).inverse) := by
        filter_upwards [continuous_fst.continuousAt (isOpen_interior.mem_nhds (hk hx)),
          continuous_fst.continuousAt (hV₀.mem_nhds (hLV₀ hx)),
          (isOpen_lt continuous_const continuous_snd.norm).mem_nhds hstrict] with z hz₁ hz₂ hz₃
        change b z.1 z.2 = (a' z.1 z.2).inverse
        rw [heq k z.1 (interior_subset hz₁) z.2 hz₃.le, ha'eq z.1 hz₂]
      have hmixed : symbolDerivative b i j x ξ =
          symbolDerivative (fun y η ↦ (a' y η).inverse) i j x ξ := by
        obtain ⟨V₂, hV₂, V₃, hV₃, hprod⟩ := mem_nhds_prod_iff.mp hnear
        have hevent : (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) =ᶠ[𝓝 x]
            (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a' y η).inverse) ξ) := by
          filter_upwards [hV₂] with y hy
          have hevent' : b y =ᶠ[𝓝 ξ] (fun η ↦ (a' y η).inverse) := by
            filter_upwards [hV₃] with η hη
            exact @hprod (y, η) ⟨hy, hη⟩
          exact (hevent'.iteratedFDeriv ℝ j).eq_of_nhds
        exact (hevent.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hmixed]
      exact hD_bound x hx ξ ((le_max_left _ _).trans hξ)
    -- Remaining frequencies form a compact set; divide by the positive target weight.
    let w : X × X → ℝ := fun z ↦ (1 + ‖z.2‖) ^ (-m - (j : ℝ))
    have hwpos (z : X × X) : 0 < w z := by
      dsimp only [w]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hw : Continuous w := by
      have hbase : Continuous (fun z : X × X ↦ (1 : ℝ) + ‖z.2‖) :=
        continuous_const.add continuous_snd.norm
      exact hbase.rpow_const (fun z ↦ Or.inl (ne_of_gt (by positivity)))
    have hratio : Continuous (fun z : X × X ↦
        ‖iteratedFDeriv ℝ (i + j) (Function.uncurry b) z‖ / w z) :=
      (hb.continuous_iteratedFDeriv (by simp)).norm.div hw (fun z ↦ (hwpos z).ne')
    obtain ⟨D₀, hD₀⟩ := ((hL.prod (isCompact_closedBall (0 : X) R₁)).image hratio).bddAbove
    refine ⟨max D (max D₀ 0), hD.trans (le_max_left _ _), ?_⟩
    intro x hx ξ
    by_cases hξ : R₁ ≤ ‖ξ‖
    · exact (hhigh x hx ξ hξ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hwpos (x, ξ)).le)
    · have hlow : (x, ξ) ∈ L ×ˢ Metric.closedBall (0 : X) R₁ :=
        ⟨hx, by
          simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt (lt_of_not_ge hξ)⟩
      have hdiv := hD₀ ⟨(x, ξ), hlow, rfl⟩
      have hnorm : ‖iteratedFDeriv ℝ (i + j) (Function.uncurry b) (x, ξ)‖ ≤
          D₀ * w (x, ξ) := (div_le_iff₀ (hwpos (x, ξ))).mp hdiv
      exact ((norm_mixed_iteratedFDeriv_le b hb i j x ξ).trans hnorm).trans
        (mul_le_mul_of_nonneg_right
          ((le_max_left D₀ 0).trans (le_max_right D (max D₀ 0))) (hwpos (x, ξ)).le)
  · intro L hLU hL
    obtain ⟨j, hj⟩ := hcover L hLU hL
    refine ⟨T j, (hR j).trans_le (le_max_left _ _), ?_⟩
    intro x hx ξ hξ
    exact heq j x (interior_subset (hj hx)) ξ hξ

end AtiyahSinger
