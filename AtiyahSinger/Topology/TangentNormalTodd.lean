/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.ComplexificationBundleMap
public import AtiyahSinger.Topology.ComplexificationInverseTodd
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ComplexifiedNormalPullback
public import AtiyahSinger.Topology.TrivialInverseTodd
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The Todd comparison for the actual tangent and normal bundles

Public module ID: M2241.

A specified trivialization of a direct sum identifies the inverse Todd class
of its second summand with the Todd class of the first. The argument cancels
only the normalized unit characteristic series, so zero divisors in base
cohomology are allowed. The geometric application uses the original normal
quotient and the derivative of its specified Euclidean immersion.

Source: Lawson--Michelsohn, Spin Geometry III.13, the stable tangent-normal
relation in the derivation of (13.18), with the characteristic classes of III.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v w

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hE : ContinuousHermitianMetric E)
  (F : X → Type w) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hF : ContinuousHermitianMetric F)

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A genuine trivialization of the sum identifies its two complementary Todd classes. -/
theorem inverseToddClassComponent_eq_todd_of_sum_trivial (r : ℕ)
    (htrivial : ContinuousHermitianMetric (Bundle.Trivial X (Fin r → ℂ)))
    (e : Iso (E ×ᵇ F) (Bundle.Trivial X (Fin r → ℂ))) (k : ℕ) :
    inverseToddClassComponent F hF k = toddClassComponent E hE k := by
  classical
  let R := SingularEvenCohomology ℚ X
  let series (a : ∀ j, singularCohomology ℚ X (2 * j)) : PowerSeries R :=
    PowerSeries.mk (fun j ↦ singularEvenCohomologyOf ℚ X j (a j))
  have hcoeff (a b : PowerSeries R) (n : ℕ) :
      PowerSeries.coeff n (a * b) =
        ∑ i : Fin (n + 1), PowerSeries.coeff i.val a * PowerSeries.coeff (n - i.val) b := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i a * PowerSeries.coeff j b) n,
      Fin.sum_univ_eq_sum_range
        (fun i ↦ PowerSeries.coeff i a * PowerSeries.coeff (n - i) b) (n + 1)]
  have hconv (a b : ∀ j, singularCohomology ℚ X (2 * j)) (n : ℕ) :
      singularEvenCohomologyOf ℚ X n (∑ i : Fin (n + 1),
        (eqToIso (by congr 1; omega) :
          singularCohomology ℚ X (2 * (i.val + (n - i.val))) ≅
            singularCohomology ℚ X (2 * n)).hom
          (singularCohomologyEvenCup ℚ X i.val (n - i.val) (a i.val) (b (n - i.val)))) =
        PowerSeries.coeff n (series a * series b) := by
    rw [map_sum, hcoeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso ℚ X (by omega), singularEvenCohomologyOf_cup]
    simp only [series, PowerSeries.coeff_mk]
  let A := series (toddClassComponent E hE)
  let B := series (inverseToddClassComponent E hE)
  let C := series (inverseToddClassComponent F hF)
  -- The prescribed inverse class inverts the Todd class of the same first bundle.
  have hAB : A * B = 1 := by
    apply PowerSeries.ext
    intro j
    change PowerSeries.coeff j
      (series (toddClassComponent E hE) * series (inverseToddClassComponent E hE)) = _
    rw [← hconv, toddClassComponent_mul_inverse,
      singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases j <;> simp
  -- The actual sum isomorphism gives the second unit identity on the original base.
  have hBC : B * C = 1 := by
    apply PowerSeries.ext
    intro j
    change PowerSeries.coeff j
      (series (inverseToddClassComponent E hE) * series (inverseToddClassComponent F hF)) = _
    rw [← hconv, ← inverseToddClassComponent_sum,
      inverseToddClassComponent_eq_of_iso (E ×ᵇ F) (hE.sum hF)
        (Bundle.Trivial X (Fin r → ℂ)) htrivial e,
      inverseToddClassComponent_trivial, singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases j <;> simp
  have hCA : C = A := by
    calc
      C = (A * B) * C := by rw [hAB, one_mul]
      _ = A * (B * C) := mul_assoc _ _ _
      _ = A := by rw [hBC, mul_one]
  apply singularEvenCohomologyOf_injective ℚ X k
  simpa only [A, C, series, PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) hCA

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped ContDiff Manifold TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  sumTopology isFiniteRank_sum
  trivialTopology isFiniteRank_trivial tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

variable {n N : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ (Fin N)
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

set_option maxHeartbeats 800000 in
-- Normalize the original tangent/quotient-normal complexifications and sum atlas.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual tangent and quotient normal complexifications have their stable trivialization. -/
theorem nonempty_tangentNormal_complexification_iso
    (f : ContMDiffMap 𝓘(ℝ, V) 𝓘(ℝ, W) M W ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ f) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := complexificationTopology V T
    letI := complexificationTopology (NormalModel V W)
      (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f)
    Nonempty (Iso ((fun x : M ↦ ℂ ⊗[ℝ] T x) ×ᵇ
      (fun x : M ↦ ℂ ⊗[ℝ] NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f x))
      (Bundle.Trivial M (Fin N → ℂ))) := by
  classical
  let ν := NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f
  let Q := NormalModel V W
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let := complexificationTopology V T
  let := complexificationTopology Q ν
  let := RealBundle.isFiniteRank_of_vectorBundle V T
  let := RealBundle.isFiniteRank_of_vectorBundle Q ν
  let := RealBundle.isFiniteRank_complexification V T
  let := RealBundle.isFiniteRank_complexification Q ν
  obtain ⟨s, hs, hQs⟩ := exists_smooth_normal_rightInverse f hf
  let D (x : M) : T x →L[ℝ] W := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, W) f x
  let s₀ (x : M) : ν x →L[ℝ] W := s x
  let L (x : M) : (T x × ν x) →ₗ[ℝ] W :=
    (D x).toLinearMap.coprod (s₀ x).toLinearMap
  -- The derivative and a lift of its actual quotient give complementary summands.
  have hL (x : M) : Function.Bijective (L x) := by
    let q : W →ₗ[ℝ] ν x := (LinearMap.range (D x).toLinearMap).mkQ
    have hqD (v : T x) : q (D x v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    have hqs (w : ν x) : q (s₀ x w) = w := hQs x w
    constructor
    · apply (injective_iff_map_eq_zero (L x)).mpr
      rintro ⟨v, w⟩ hzero
      change D x v + s₀ x w = 0 at hzero
      have hw := congrArg q hzero
      rw [map_add, hqD, hqs w, map_zero, zero_add] at hw
      subst w
      have hv : D x v = 0 := by simpa using hzero
      have hvzero : v = 0 := hf.mfderiv_injective (by simp) x
        (hv.trans (D x).map_zero.symm)
      exact Prod.ext hvzero rfl
    · intro y
      have hquot : q (y - s₀ x (q y)) = 0 := by
        rw [map_sub, hqs (q y), sub_self]
      obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp hquot
      change D x v = y - s₀ x (q y) at hv
      refine ⟨(v, q y), ?_⟩
      change D x v + s₀ x (q y) = y
      rw [hv, sub_add_cancel]
  let A := T ×ᵇ ν
  let U := Bundle.Trivial M W
  have hLcont : Continuous (fun z : TotalSpace (V × Q) A ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace W U)) := by
    have hp := (FiberBundle.Prod.isInducing_diag V T Q ν).continuous
    have hD : Continuous (fun z : TotalSpace V T ↦ D z.proj z.snd) :=
      continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, W)).continuous.comp
        (smoothTangentMap f).contMDiff.continuous)
    have hS : Continuous (fun z : TotalSpace Q ν ↦ s z.proj z.snd) :=
      continuous_snd.comp ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, W)).continuous.comp
        ((Pullback.continuous_lift W (TangentSpace 𝓘(ℝ, W)) f).comp hs.continuous))
    exact (Bundle.Trivial.homeomorphProd M W).symm.continuous.comp
      (((FiberBundle.continuous_proj V T).comp hp.fst).prodMk
        ((hD.comp hp.fst).add (hS.comp hp.snd)))
  let := complexificationTopology (V × Q) A
  let := complexificationTopology W U
  let := RealBundle.isFiniteRank_of_vectorBundle (V × Q) A
  let := RealBundle.isFiniteRank_of_vectorBundle W U
  let := RealBundle.isFiniteRank_complexification (V × Q) A
  let := RealBundle.isFiniteRank_complexification W U
  let H : Hom (fun x ↦ ℂ ⊗[ℝ] A x) (fun x ↦ ℂ ⊗[ℝ] U x) :=
    { linearMap x := (L x).baseChange ℂ
      continuous_total := continuous_complexification_map L hLcont }
  have hH (x : M) : Function.Bijective (H.linearMap x) :=
    ((LinearEquiv.ofBijective (L x) (hL x)).baseChange ℝ ℂ _ _).bijective
  -- Scalar extension of real Euclidean coordinates is the original complex coordinate space.
  let eW : (ℂ ⊗[ℝ] W) ≃ₗ[ℂ] (Fin N → ℂ) :=
    ((EuclideanSpace.equiv (Fin N) ℝ).toLinearEquiv.baseChange ℝ ℂ _ _).trans
      (TensorProduct.piScalarRight ℝ ℂ ℂ (Fin N))
  have heW (v : ℂ ⊗[ℝ] W) (i : Fin N) :
      eW v i = ((complexificationReIm W v).1 i : ℂ) +
        Complex.I * ((complexificationReIm W v).2 i : ℂ) := by
    induction v using TensorProduct.inductionOn with
    | tmul z v =>
      simp only [eW, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Complex.real_smul, (complexificationReIm_properties W).1, PiLp.smul_apply]
      change (v i : ℂ) * z = ((z.re * v i : ℝ) : ℂ) +
        Complex.I * ((z.im * v i : ℝ) : ℂ)
      rw [Complex.ofReal_mul, Complex.ofReal_mul]
      calc
        (v i : ℂ) * z = (v i : ℂ) * (z.re + z.im * Complex.I) := by
          rw [Complex.re_add_im]
        _ = _ := by ring
    | add v w hv hw =>
      simp only [map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add, PiLp.add_apply,
        Complex.ofReal_add, mul_add, hv, hw]
      ring
  let C : Hom (fun x : M ↦ ℂ ⊗[ℝ] U x) (Bundle.Trivial M (Fin N → ℂ)) :=
    { linearMap _ := eW.toLinearMap
      continuous_total := by
        have hd := (complexificationDoubleTotalHomeomorph W U).continuous
        have hp := (FiberBundle.Prod.isInducing_diag W U W U).continuous.comp hd
        have h₁ := (Bundle.Trivial.homeomorphProd M W).continuous.comp hp.fst
        have h₂ := (Bundle.Trivial.homeomorphProd M W).continuous.comp hp.snd
        apply continuous_induced_rng.mpr
        apply h₁.fst.prodMk
        apply continuous_pi
        intro i
        exact ((Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i).continuous.comp h₁.snd)).add
            (continuous_const.mul (Complex.continuous_ofReal.comp
              ((EuclideanSpace.proj i).continuous.comp h₂.snd)))).congr
          (fun z ↦ (heW z.snd i).symm) }
  exact ⟨(RealBundle.complexificationSumIso V T Q ν).symm.trans
    ((H.toIso hH).trans (C.toIso (fun _ ↦ eW.bijective)))⟩

/-- The original quotient normal complement has the Todd class of the original tangent bundle. -/
theorem inverseTodd_normalComplexification_eq_todd
    (f : ContMDiffMap 𝓘(ℝ, V) 𝓘(ℝ, W) M W ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ f)
    (hT : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] T x))
    (hν :
      letI := complexificationTopology (NormalModel V W)
        (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f)
      ContinuousHermitianMetric
        (fun x : M ↦ ℂ ⊗[ℝ] NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f x)) (k : ℕ) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := RealBundle.isFiniteRank_of_vectorBundle V T
    letI := RealBundle.isFiniteRank_of_vectorBundle (NormalModel V W)
      (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f)
    letI := complexificationTopology V T
    letI := complexificationTopology (NormalModel V W)
      (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f)
    letI := RealBundle.isFiniteRank_complexification V T
    letI := RealBundle.isFiniteRank_complexification (NormalModel V W)
      (NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f)
    inverseToddClassComponent (fun x : M ↦ ℂ ⊗[ℝ] NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f x)
      hν k = toddClassComponent (fun x : M ↦ ℂ ⊗[ℝ] T x) hT k := by
  classical
  let ν := NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f
  let Q := NormalModel V W
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := RealBundle.isFiniteRank_of_vectorBundle V T
  let := RealBundle.isFiniteRank_of_vectorBundle Q ν
  let := complexificationTopology V T
  let := complexificationTopology Q ν
  let := RealBundle.isFiniteRank_complexification V T
  let := RealBundle.isFiniteRank_complexification Q ν
  obtain ⟨e⟩ := nonempty_tangentNormal_complexification_iso f hf
  let h₀ := (nonempty_continuousHermitianMetric (Bundle.Trivial M (Fin N → ℂ))).some
  exact inverseToddClassComponent_eq_todd_of_sum_trivial (fun x ↦ ℂ ⊗[ℝ] T x) hT
    (fun x ↦ ℂ ⊗[ℝ] ν x) hν N h₀ e k

set_option maxHeartbeats 600000 in
-- Compare the two actual pullback topologies before applying metric independence.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original normal bundle over TM has the pulled-back tangent Todd component. -/
theorem inverseTodd_complexifiedNormalPullback_eq
    (f : ContMDiffMap 𝓘(ℝ, V) 𝓘(ℝ, W) M W ∞)
    (hf : Manifold.IsImmersion 𝓘(ℝ, V) 𝓘(ℝ, W) ∞ f)
    (hT : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] T x))
    (h : ContinuousHermitianMetric (ComplexifiedNormalPullback f)) (k : ℕ) :
    letI := isFiniteRank_complexifiedNormalPullback f hf
    letI := RealBundle.isFiniteRank_of_vectorBundle V T
    letI := complexificationTopology V T
    letI := RealBundle.isFiniteRank_complexification V T
    inverseToddClassComponent (ComplexifiedNormalPullback f) h k =
      singularCohomologyPullback ℚ
        ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ (2 * k)
        (toddClassComponent (fun x : M ↦ ℂ ⊗[ℝ] T x) hT k) := by
  classical
  let ν := NormalBundle 𝓘(ℝ, V) 𝓘(ℝ, W) f
  let Q := NormalModel V W
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := RealBundle.isFiniteRank_of_vectorBundle V T
  let := RealBundle.isFiniteRank_of_vectorBundle Q ν
  let := complexificationTopology V T
  let := complexificationTopology Q ν
  let := RealBundle.isFiniteRank_complexification V T
  let := RealBundle.isFiniteRank_complexification Q ν
  let E := fun x : M ↦ ℂ ⊗[ℝ] ν x
  let hν := (nonempty_continuousHermitianMetric E).some
  let p : C(TangentBundle 𝓘(ℝ, V) M, M) :=
    ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩
  let originalTopology := complexifiedNormalPullbackTopology f
  let pulledTopology : TopologicalSpace (TotalSpace Unit (ComplexifiedNormalPullback f)) :=
    inferInstanceAs (TopologicalSpace (TotalSpace Unit ((Bundle.TotalSpace.proj :
      TangentBundle 𝓘(ℝ, V) M → M) *ᵖ (fun x : M ↦ ℂ ⊗[ℝ] ν x))))
  have htop : originalTopology = pulledTopology := complexificationTopology_pullback Q ν p
  -- State the class comparison for either of the equal total-space topologies.
  let Statement (t : TopologicalSpace (TotalSpace Unit (ComplexifiedNormalPullback f))) : Prop :=
    letI := t
    ∀ (hFin : IsFiniteRank (ComplexifiedNormalPullback f)),
      letI := hFin
      ∀ hF : ContinuousHermitianMetric (ComplexifiedNormalPullback f),
        inverseToddClassComponent (ComplexifiedNormalPullback f) hF k =
          singularCohomologyPullback ℚ p (2 * k)
            (toddClassComponent (fun x : M ↦ ℂ ⊗[ℝ] T x) hT k)
  have hpull : Statement pulledTopology := by
    let := pulledTopology
    intro hFin hF
    let := hFin
    let : IsFiniteRank ((p : _ → M) *ᵖ E) := hFin
    have hmetric := inverseToddClassComponent_metric_independent
      ((p : _ → M) *ᵖ E) hF (hν.pullback p) k
    have hnature := inverseToddClassComponent_pullback E hν p k
    have hbase := inverseTodd_normalComplexification_eq_todd f hf hT hν k
    exact hmetric.trans (hnature.symm.trans
      (congrArg (singularCohomologyPullback ℚ p (2 * k)) hbase))
  rw [← htop] at hpull
  exact hpull (isFiniteRank_complexifiedNormalPullback f hf) h

end AtiyahSinger
