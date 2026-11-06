/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Fredholm
public import AtiyahSinger.Analysis.Parametrix

/-!
# Parametrices on actual Sobolev completions

Public module ID: M1003.

A04/A05/A06/SL02: extend both smooth-kernel remainder identities to the same
Sobolev spaces as the original operator. Compactness gives Atkinson Fredholmness;
the left identity also gives finite Sobolev gains and a single smooth lift for a
smooth right-hand side. These statements use actual PDO section maps and arbitrary
real orders. They do not identify formal transposes with Hilbert adjoints or assert
local distributional regularity. Fredholmness uses both smooth-kernel errors;
the lift and estimate arguments need only the left error.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

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
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The actual left residual extends the same smooth kernel to H^s(E). -/
theorem sobolevRealization_comp_sub_id_eq
    (K : SmoothKernel (n := n) (r := r) (q := r) E E)
    (hK : K.toLinearMap μ = Q.toLinearMap.comp P.toLinearMap - LinearMap.id) (s : ℝ) :
    (Q.sobolevRealization B A (s - m) s (by linarith)).comp (P.sobolevExtension A B s) -
        ContinuousLinearMap.id ℂ (A.SobolevSpace s) =
      K.sobolevExtension μ A A s s := by
  /- Stage 1: evaluate both continuous maps on A.smoothToSobolev s u. The
  realization formulas identify the composite with the embedding of Q(Pu).
  Subtract u and apply hK to identify this with the embedding of K u.
  Stage 2: that is the kernel extension's value on the same dense smooth image.
  Equality extends by continuity. The return map has target exactly s because
  (s-m)-(-m)=s; no identification of different completion carriers is implicit. -/
  -- Identify both maps on the same dense image of the original smooth sections.
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    (((Q.sobolevRealization B A (s - m) s (by linarith)).comp
      (P.sobolevExtension A B s)) - ContinuousLinearMap.id ℂ (A.SobolevSpace s)).continuous
    (K.sobolevExtension μ A A s s).continuous
  funext u
  simp only [Function.comp_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    P.sobolevExtension_smoothToSobolev, Q.sobolevRealization_smoothToSobolev,
    K.sobolevExtension_smoothToSobolev]
  rw [hK, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]

/-- The actual right residual extends the same smooth kernel to H^(s-m)(F). -/
theorem comp_sobolevRealization_sub_id_eq
    (K : SmoothKernel (n := n) (r := q) (q := q) F F)
    (hK : K.toLinearMap μ = P.toLinearMap.comp Q.toLinearMap - LinearMap.id) (s : ℝ) :
    (P.sobolevExtension A B s).comp (Q.sobolevRealization B A (s - m) s (by linarith)) -
        ContinuousLinearMap.id ℂ (B.SobolevSpace (s - m)) =
      K.sobolevExtension μ B B (s - m) (s - m) := by
  /- Evaluate on the dense smooth image in the F completion. Q then P realizes
  exactly their original smooth composite. Subtract the F identity and use hK.
  Density identifies the bounded maps. This residual acts on F, whereas the
  preceding residual acts on E; the bundles need not be identified. -/
  -- This time the dense input and the residual both belong to the target bundle.
  apply DFunLike.coe_injective
  apply (B.denseRange_smoothToSobolev (s - m)).equalizer
    (((P.sobolevExtension A B s).comp
      (Q.sobolevRealization B A (s - m) s (by linarith))) -
      ContinuousLinearMap.id ℂ (B.SobolevSpace (s - m))).continuous
    (K.sobolevExtension μ B B (s - m) (s - m)).continuous
  funext u
  simp only [Function.comp_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Q.sobolevRealization_smoothToSobolev, P.sobolevExtension_smoothToSobolev,
    K.sobolevExtension_smoothToSobolev]
  rw [hK, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]

/-- A smooth-kernel left parametrix error is compact on the actual source completion. -/
theorem isCompactOperator_sobolevRealization_comp_sub_id
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    IsCompactOperator
      ((Q.sobolevRealization B A (s - m) s (by linarith)).comp
          (P.sobolevExtension A B s) - ContinuousLinearMap.id ℂ (A.SobolevSpace s)) := by
  /- Extract the E-to-E kernel from hQ.1, identify the actual residual by
  sobolevRealization_comp_sub_id_eq, and apply smooth-kernel compactness.
  This uses a strict intermediate Sobolev gain followed by compact inclusion. -/
  obtain ⟨K, hK⟩ := hQ.1
  rw [P.sobolevRealization_comp_sub_id_eq Q A B K hK s]
  exact K.isCompactOperator_sobolevExtension μ A A s s

/-- A smooth-kernel right parametrix error is compact on the actual target completion. -/
theorem isCompactOperator_comp_sobolevRealization_sub_id
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    IsCompactOperator
      ((P.sobolevExtension A B s).comp
          (Q.sobolevRealization B A (s - m) s (by linarith)) -
        ContinuousLinearMap.id ℂ (B.SobolevSpace (s - m))) := by
  /- Extract the F-to-F kernel from hQ.2. The right residual equality and
  smooth-kernel compactness apply on H^(s-m)(F). Compactness of just the left
  residual would not by itself give a finite-dimensional cokernel. -/
  obtain ⟨K, hK⟩ := hQ.2
  rw [P.comp_sobolevRealization_sub_id_eq Q A B K hK s]
  exact K.isCompactOperator_sobolevExtension μ B B (s - m) (s - m)

/-- SG III.5.1 applied to actual Sobolev extensions of a two-sided parametrix pair. -/
theorem isFredholm_sobolevExtension_of_isParametrix
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) (s : ℝ) :
    (P.sobolevExtension A B s).IsFredholm := by
  /- The concrete Sobolev carriers are closed subspaces of finite Hilbert sums,
  hence complete complex inner-product spaces, without fiberwise Hermitian data.
  Use the displayed return realization as the bounded inverse modulo compacts.
  The two compact residual theorems supply precisely the two hypotheses of
  Atkinson. This establishes closed range as well as finite kernel and cokernel. -/
  -- Atkinson uses exactly the return realization appearing in both residual identities.
  exact (atkinson (P.sobolevExtension A B s)).mpr
    ⟨Q.sobolevRealization B A (s - m) s (by linarith),
      P.isCompactOperator_sobolevRealization_comp_sub_id Q A B hQ s,
      P.isCompactOperator_comp_sobolevRealization_sub_id Q A B hQ s⟩

/-- A left smooth-kernel inverse lifts solutions to every higher admissible Sobolev order. -/
theorem existsUnique_sobolev_lift_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s t : ℝ) (hst : s ≤ t) (u : A.SobolevSpace s) (v : B.SobolevSpace (t - m))
    (hu : P.sobolevExtension A B s u =
      B.sobolevInclusion (t - m) (s - m) (by linarith) v) :
    ∃! w : A.SobolevSpace t,
      A.sobolevInclusion t s hst w = u ∧ P.sobolevExtension A B t w = v := by
  /- Stage 1: extract the left error K=QP-I. Define w=Q(v)-K(u) at target order t,
  using Q's return realization and the kernel's all-order extension H^s -> H^t.
  Stage 2: inclusions commute with these bounded maps, since the identities hold
  on dense smooth sections. The left residual identity at order s and hu then
  give inclusion(w)=u. Apply P and use the same density compatibility. Injectivity
  of the target inclusion shows P_t(w)=v. Injectivity of the source inclusion
  gives uniqueness. This concerns global Sobolev solutions, not arbitrary D' inputs. -/
  obtain ⟨K, hK⟩ := hQ
  let Rs := Q.sobolevRealization B A (s - m) s (by linarith)
  let Rt := Q.sobolevRealization B A (t - m) t (by linarith)
  let iA := A.sobolevInclusion t s hst
  let iB := B.sobolevInclusion (t - m) (s - m) (by linarith)
  -- The return map and original operator commute with the specified inclusions.
  have hR : iA.comp Rt = Rs.comp iB := by
    apply DFunLike.coe_injective
    apply (B.denseRange_smoothToSobolev (t - m)).equalizer
      (iA.comp Rt).continuous (Rs.comp iB).continuous
    funext z
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, Rs, Rt, iA, iB,
      Q.sobolevRealization_smoothToSobolev, A.sobolevInclusion_smoothToSobolev,
      B.sobolevInclusion_smoothToSobolev]
  have hP : iB.comp (P.sobolevExtension A B t) =
      (P.sobolevExtension A B s).comp iA := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev t).equalizer
      (iB.comp (P.sobolevExtension A B t)).continuous
      ((P.sobolevExtension A B s).comp iA).continuous
    funext z
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, iA, iB,
      P.sobolevExtension_smoothToSobolev, A.sobolevInclusion_smoothToSobolev,
      B.sobolevInclusion_smoothToSobolev]
  -- The same kernel corrects the return value at the higher order.
  let w : A.SobolevSpace t := Rt v - K.sobolevExtension μ A A s t u
  have hres := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
    (P.sobolevRealization_comp_sub_id_eq Q A B K hK s)
  change Rs (P.sobolevExtension A B s u) - u = K.sobolevExtension μ A A s s u at hres
  have hw : iA w = u := by
    have hRv := congrArg (fun T : B.SobolevSpace (t - m) →L[ℂ] A.SobolevSpace s ↦ T v) hR
    have hKv := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
      (K.sobolevInclusion_comp_sobolevExtension μ A A s t s hst)
    change iA (Rt v) = Rs (iB v) at hRv
    change iA (K.sobolevExtension μ A A s t u) = K.sobolevExtension μ A A s s u at hKv
    change iA (Rt v - K.sobolevExtension μ A A s t u) = u
    rw [map_sub, hRv, hKv, ← hu]
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hres).trans (add_comm _ _))
  have hPw : P.sobolevExtension A B t w = v := by
    apply B.sobolevInclusion_injective (t - m) (s - m) (by linarith)
    have hPw := congrArg (fun T : A.SobolevSpace t →L[ℂ] B.SobolevSpace (s - m) ↦ T w) hP
    change iB (P.sobolevExtension A B t w) = P.sobolevExtension A B s (iA w) at hPw
    exact hPw.trans ((congrArg (P.sobolevExtension A B s) hw).trans hu)
  refine ⟨w, ⟨hw, hPw⟩, ?_⟩
  -- Injectivity of the original inclusion fixes the lift uniquely.
  intro z hz
  exact A.sobolevInclusion_injective t s hst (hz.1.trans hw.symm)

/-- A smooth right-hand side gives one actual smooth solution representing the input. -/
theorem existsUnique_smooth_lift_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s : ℝ) (u : A.SobolevSpace s) (v : smoothSections (n := n) (r := q) F)
    (hu : P.sobolevExtension A B s u = B.smoothToSobolev (s - m) v) :
    ∃! w : smoothSections (n := n) (r := r) E,
      A.smoothToSobolev s w = u ∧ P.toLinearMap w = v := by
  /- Stage 1: choose the left error kernel K=QP-I. Its sobolevToSmooth sends u
  to a single smooth section. Set w=Q(v)-K(u) as an actual smooth section.
  Stage 2: the left residual identity and hu show that w embeds as u in H^s.
  Apply the extension of P and its smooth-action formula. Injectivity of the
  smooth embedding in the target yields P(w)=v. Injectivity in the source gives
  uniqueness. Only the left smoothing error is needed for this regularity claim. -/
  obtain ⟨K, hK⟩ := hQ
  -- The smoothing output is a single section, common to every target regularity.
  let w : smoothSections (n := n) (r := r) E :=
    Q.toLinearMap v - K.sobolevToSmooth μ A A s u
  have hres := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
    (P.sobolevRealization_comp_sub_id_eq Q A B K hK s)
  change Q.sobolevRealization B A (s - m) s (by linarith)
    (P.sobolevExtension A B s u) - u = K.sobolevExtension μ A A s s u at hres
  rw [hu, Q.sobolevRealization_smoothToSobolev] at hres
  have hw : A.smoothToSobolev s w = u := by
    change A.smoothToSobolev s (Q.toLinearMap v - K.sobolevToSmooth μ A A s u) = u
    rw [map_sub, K.smoothToSobolev_sobolevToSmooth]
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hres).trans (add_comm _ _))
  -- The same input equality and injective target embedding recover the original equation.
  have hPw : P.toLinearMap w = v := by
    apply B.smoothToSobolev_injective (s - m)
    rw [← P.sobolevExtension_smoothToSobolev, hw]
    exact hu
  refine ⟨w, ⟨hw, hPw⟩, ?_⟩
  intro z hz
  exact A.smoothToSobolev_injective s (hz.1.trans hw.symm)

/-- The parametrix identity controls the solution by its image and any lower Sobolev norm. -/
theorem exists_estimate_of_isSmoothingOperator
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s l : ℝ) (hls : l ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.SobolevSpace s,
      ‖u‖ ≤ C * (‖P.sobolevExtension A B s u‖ + ‖A.sobolevInclusion s l hls u‖) := by
  /- Stage 1: write u=Q(Pu)-K(u) using the left residual identity at order s.
  Density identifies K's H^s-to-H^s extension with its H^l-to-H^s extension
  composed with the inclusion. This uses one fixed kernel K from hQ.
  Stage 2: apply the operator norms of Q:H^(s-m)->H^s and K:H^l->H^s, then
  the triangle inequality. Their sum is a nonnegative constant uniform in u.
  No right parametrix error or injectivity of P is needed for this estimate. -/
  obtain ⟨K, hK⟩ := hQ
  let R := Q.sobolevRealization B A (s - m) s (by linarith)
  let S := K.sobolevExtension μ A A l s
  refine ⟨‖R‖ + ‖S‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  intro u
  -- Evaluate the left identity and lower only the input order of the same kernel.
  have hres := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
    (P.sobolevRealization_comp_sub_id_eq Q A B K hK s)
  change R (P.sobolevExtension A B s u) - u = K.sobolevExtension μ A A s s u at hres
  have hKlower := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
    (K.sobolevExtension_comp_sobolevInclusion μ A A s l s hls)
  change S (A.sobolevInclusion s l hls u) = K.sobolevExtension μ A A s s u at hKlower
  have hformula : u = R (P.sobolevExtension A B s u) -
      S (A.sobolevInclusion s l hls u) := by
    rw [hKlower]
    exact (sub_eq_iff_eq_add.mpr
      ((sub_eq_iff_eq_add.mp hres).trans (add_comm _ _))).symm
  -- Operator norms now give one uniform nonnegative constant.
  calc
    ‖u‖ = ‖R (P.sobolevExtension A B s u) - S (A.sobolevInclusion s l hls u)‖ :=
      congrArg norm hformula
    _ ≤ ‖R (P.sobolevExtension A B s u)‖ + ‖S (A.sobolevInclusion s l hls u)‖ :=
      norm_sub_le _ _
    _ ≤ ‖R‖ * ‖P.sobolevExtension A B s u‖ + ‖S‖ * ‖A.sobolevInclusion s l hls u‖ :=
      add_le_add (R.le_opNorm _) (S.le_opNorm _)
    _ ≤ _ := by
      nlinarith [mul_nonneg (norm_nonneg R) (norm_nonneg (A.sobolevInclusion s l hls u)),
        mul_nonneg (norm_nonneg S) (norm_nonneg (P.sobolevExtension A B s u))]

end PseudodifferentialOperator

end AtiyahSinger
