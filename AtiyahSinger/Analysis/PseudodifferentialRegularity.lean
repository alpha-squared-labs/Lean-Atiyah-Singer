/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialSpace

/-!
# Sobolev realizations, compactness and the smoothing intersection

Public module ID: M0899.

D05/A02/A03/A05/A08: realize the PDO order filtration on actual Sobolev completions.
A strict gain in output regularity gives compactness by Rellich. Membership in every
PDO order is equivalent to a smooth kernel. Equal principal classes give a compact
difference at the critical Sobolev orders, without giving a smooth difference.
Fixed-presentation quantization is linear on these completions and continuous along
finite scalar combinations. No topology on the full symbol space or ellipticity of
an interpolated family is asserted. These are consequences of SG III.2 and III.3.17,
not additional numbered lemmas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

variable {E F μ}

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The order-m extension followed by the specified lower-order Sobolev inclusion. -/
def sobolevRealization (s t : ℝ) (ht : t ≤ s - m) :
    A.SobolevSpace s →L[ℂ] B.SobolevSpace t :=
  (B.sobolevInclusion (s - m) t ht).comp (P.sobolevExtension A B s)

/-- A lower target order still realizes precisely the original smooth-section action. -/
theorem sobolevRealization_smoothToSobolev (s t : ℝ) (ht : t ≤ s - m)
    (u : smoothSections (n := n) (r := r) E) :
    P.sobolevRealization A B s t ht (A.smoothToSobolev s u) =
      B.smoothToSobolev t (P.toLinearMap u) := by
  /- First use sobolevExtension_smoothToSobolev for the critical target order.
  Then use the smooth-section action of sobolevInclusion. Both steps retain
  the same original output section and only change its completion coordinate. -/
  change B.sobolevInclusion (s - m) t ht
    (P.sobolevExtension A B s (A.smoothToSobolev s u)) = _
  rw [P.sobolevExtension_smoothToSobolev, B.sobolevInclusion_smoothToSobolev]

/-- The Sobolev realization depends on the section action, not its declared order bound. -/
theorem sobolevRealization_eq_of_toLinearMap_eq {l : ℝ}
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ l)
    (hPQ : P.toLinearMap = Q.toLinearMap) (s t : ℝ)
    (htm : t ≤ s - m) (htl : t ≤ s - l) :
    P.sobolevRealization A B s t htm = Q.sobolevRealization A B s t htl := by
  /- The preceding action formula and hPQ give equality on every smooth section.
  The smooth image is dense in A.SobolevSpace s, and both maps are continuous
  into the same Hausdorff completion. Extend this equality by density. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    (P.sobolevRealization A B s t htm).continuous
    (Q.sobolevRealization A B s t htl).continuous
  funext u
  have hPu : P.toLinearMap u = Q.toLinearMap u := LinearMap.congr_fun hPQ u
  have hP := P.sobolevRealization_smoothToSobolev A B s t htm u
  have hQ := Q.sobolevRealization_smoothToSobolev A B s t htl u
  exact hP.trans ((congrArg (B.smoothToSobolev t) hPu).trans hQ.symm)

/-- A strict improvement over the critical target order makes the realization compact. -/
theorem isCompactOperator_sobolevRealization (s t : ℝ) (ht : t < s - m) :
    IsCompactOperator (P.sobolevRealization A B s t ht.le) := by
  /- The bounded order-m extension lands in H^(s-m). Since t<s-m, global Rellich
  makes the subsequent inclusion into H^t compact. Compose that compact inclusion
  with the continuous extension. Equality at the critical exponent is insufficient. -/
  exact (B.isCompactOperator_sobolevInclusion (s - m) t ht).comp_clm
    (P.sobolevExtension A B s)

/-- Every specified same-order Sobolev realization of a negative-order PDO is compact. -/
theorem isCompactOperator_of_order_neg (hm : m < 0) (s : ℝ)
    (T : A.SobolevSpace s →L[ℂ] B.SobolevSpace s)
    (hT : ∀ u : smoothSections (n := n) (r := r) E,
      T (A.smoothToSobolev s u) = B.smoothToSobolev s (P.toLinearMap u)) :
    IsCompactOperator T := by
  /- Negative order implies s<s-m. The previous compact realization at target s
  agrees with T on the dense smooth image by hT. Equality of continuous maps
  transfers compactness to the actual supplied operator T. -/
  have hdrop : s < s - m := by linarith
  have heq : T = P.sobolevRealization A B s s hdrop.le := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer T.continuous
      (P.sobolevRealization A B s s hdrop.le).continuous
    funext u
    exact (hT u).trans (P.sobolevRealization_smoothToSobolev A B s s hdrop.le u).symm
  rw [heq]
  exact P.isCompactOperator_sobolevRealization A B s s hdrop

set_option synthInstance.maxHeartbeats 200000 in
-- Resolve the coercions of both completed Sobolev spaces in this operator difference.
/-- Equal principal classes give a compact difference of critical Sobolev extensions. -/
theorem isCompactOperator_sub_sobolevExtension
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hPQ : P.principalSymbol = Q.principalSymbol) (s : ℝ) :
    IsCompactOperator (P.sobolevExtension A B s - Q.sobolevExtension A B s) := by
  /- Stage 1: principalSymbol_eq_iff realizes the actual difference P-Q at order m-1.
  Its bounded extension lands in H^(s-(m-1)), strictly above H^(s-m).
  Stage 2: include into the critical target by Rellich. The resulting compact map
  agrees with the displayed difference on all smooth sections. Density gives
  equality on the completion. No ellipticity or infinite smoothing is inferred. -/
  let R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (m - 1) :=
    { toLinearMap := P.toLinearMap - Q.toLinearMap
      isPseudodifferentialOperator := (P.principalSymbol_eq_iff Q).mp hPQ }
  have hdrop : s - m < s - (m - 1) := by linarith
  have heq : P.sobolevExtension A B s - Q.sobolevExtension A B s =
      R.sobolevRealization A B s (s - m) hdrop.le := by
    apply DFunLike.coe_injective
    apply (A.denseRange_smoothToSobolev s).equalizer
      (P.sobolevExtension A B s - Q.sobolevExtension A B s).continuous
      (R.sobolevRealization A B s (s - m) hdrop.le).continuous
    funext u
    simp only [Function.comp_apply, sub_apply, sobolevExtension_smoothToSobolev,
      sobolevRealization_smoothToSobolev]
    change _ = B.smoothToSobolev (s - m) ((P.toLinearMap - Q.toLinearMap) u)
    rw [LinearMap.sub_apply, map_sub]
  rw [heq]
  exact R.isCompactOperator_sobolevRealization A B s (s - m) hdrop

end PseudodifferentialOperator

variable (μ)

/-- On a closed base, the intersection of all real PDO orders is the smooth-kernel class. -/
theorem isSmoothingOperator_iff_forall_isPseudodifferentialOperator
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    IsSmoothingOperator μ P ↔ ∀ m : ℝ, IsPseudodifferentialOperator E F μ m P := by
  /- Forward: use the smooth kernel as the entire remainder with an empty local
  family, at every order. Reverse: given s,t, apply the order s-t assumption and
  its unique Sobolev extension to obtain the exact action H^s -> H^t; transport
  the identity s-(s-t)=t. The existing all-order Sobolev/kernel characterization
  yields one smooth kernel for the original map P. No common local representation
  for all orders is assumed, and no kernel conclusion follows from one fixed order. -/
  constructor
  · intro hP m
    exact hP.isPseudodifferentialOperator m P
  · intro hP
    apply (isSmoothingOperator_iff_sobolevExtensions μ P A B).mpr
    intro s t
    -- Use the order s-t certificate for the same section map at this requested pair.
    let Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (s - t) :=
      { toLinearMap := P
        isPseudodifferentialOperator := hP (s - t) }
    have horder : t ≤ s - (s - t) := by linarith
    exact ⟨Q.sobolevRealization A B s t horder,
      Q.sobolevRealization_smoothToSobolev A B s t horder⟩

/-- Negative integer orders are cofinal for recognizing a smoothing section operator. -/
theorem isSmoothingOperator_iff_forall_neg_nat_order
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) :
    IsSmoothingOperator μ P ↔ ∀ k : ℕ, IsPseudodifferentialOperator E F μ (-(k : ℝ)) P := by
  /- Forward: specialize the all-real-order characterization. Reverse: for each
  real m choose k with -k≤m by the Archimedean property, then use PDO order
  monotonicity. Apply the same characterization with the supplied presentations. -/
  rw [isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ P A B]
  constructor
  · intro hP k
    exact hP (-(k : ℝ))
  · intro hP m
    obtain ⟨k, hk⟩ := exists_nat_ge (-m)
    exact IsPseudodifferentialOperator.mono (by linarith) P (hP k)

namespace QuantizationPresentation

variable (C C' : QuantizationPresentation (n := n) (r := r) (q := q) E F)
  {m : ℝ} (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Changing the quantization presentation changes the operator by at most one lower order. -/
theorem isPseudodifferentialOperator_sub_quantize
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    IsPseudodifferentialOperator E F μ (m - 1)
      ((C.quantize μ p).toLinearMap - (C'.quantize μ p).toLinearMap) := by
  /- Both constructed operators have principal class equal to the quotient of p.
  Apply principalSymbol_eq_iff to that equality. Different charts and cutoffs may
  change lower-order terms, so the conclusion is one-order improvement only. -/
  apply ((C.quantize μ p).principalSymbol_eq_iff (C'.quantize μ p)).mp
  rw [C.principalSymbol_quantize, C'.principalSymbol_quantize]

/-- Fixed quantization preserves symbol sums on the actual Sobolev completions. -/
theorem sobolevExtension_quantize_add (s : ℝ)
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (C.quantize μ (p + p')).sobolevExtension A B s =
      (C.quantize μ p).sobolevExtension A B s +
        (C.quantize μ p').sobolevExtension A B s := by
  /- On smooth sections, toLinearMap_add gives exact equality of the two actions.
  The smoothToSobolev map preserves addition. Both sides are continuous into
  the same critical target, so density proves equality of the bounded maps. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((C.quantize μ (p + p')).sobolevExtension A B s).continuous
    ((C.quantize μ p).sobolevExtension A B s +
      (C.quantize μ p').sobolevExtension A B s).continuous
  funext u
  simp only [Function.comp_apply, add_apply,
    PseudodifferentialOperator.sobolevExtension_smoothToSobolev]
  change B.smoothToSobolev (s - m) (C.toLinearMap (p + p') u) = _
  rw [C.toLinearMap_add]
  simp only [LinearMap.add_apply, map_add]
  rfl

/-- Fixed quantization preserves complex scalars on the actual Sobolev completions. -/
theorem sobolevExtension_quantize_smul (s : ℝ) (a : ℂ)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    (C.quantize μ (a • p)).sobolevExtension A B s =
      a • (C.quantize μ p).sobolevExtension A B s := by
  /- On the dense smooth image, use toLinearMap_smul and complex linearity of
  smoothToSobolev. Equality extends to the completion by continuity. The same
  quantization presentation is kept fixed for p and a*p. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((C.quantize μ (a • p)).sobolevExtension A B s).continuous
    (a • (C.quantize μ p).sobolevExtension A B s).continuous
  funext u
  simp only [Function.comp_apply, smul_apply,
    PseudodifferentialOperator.sobolevExtension_smoothToSobolev]
  change B.smoothToSobolev (s - m) (C.toLinearMap (a • p) u) = _
  rw [C.toLinearMap_smul]
  simp only [LinearMap.smul_apply, map_smul]
  rfl

/-- Fixed quantization followed by the unique critical Sobolev realization is complex-linear. -/
def sobolevQuantizationLinearMap (s m : ℝ) :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m →ₗ[ℂ]
      (A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m)) where
  toFun := fun p ↦ (C.quantize μ p).sobolevExtension A B s
  map_add' := C.sobolevExtension_quantize_add μ A B s
  map_smul' := C.sobolevExtension_quantize_smul μ A B s

/-- Finite continuous scalar combinations give operator-norm continuous quantized families. -/
theorem continuous_sobolevQuantization_finite_sum
    {ι Z : Type*} [Fintype ι] [TopologicalSpace Z]
    (p : ι → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (a : ι → Z → ℂ) (ha : ∀ j, Continuous (a j)) (s : ℝ) :
    Continuous (fun z ↦ (C.quantize μ (∑ j, a j z • p j)).sobolevExtension A B s) := by
  /- Linearity of sobolevQuantizationLinearMap identifies the family with the
  finite sum of a_j(z) times fixed bounded maps. Scalar multiplication and finite
  addition are continuous in the operator norm. This proves continuity only for
  the stated finite span, without inventing a topology on the entire symbol space. -/
  have hfamily : (fun z ↦ (C.quantize μ (∑ j, a j z • p j)).sobolevExtension A B s) =
      fun z ↦ ∑ j, a j z • (C.quantize μ (p j)).sobolevExtension A B s := by
    funext z
    change C.sobolevQuantizationLinearMap μ A B s m (∑ j, a j z • p j) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hfamily]
  exact continuous_finsetSum _ (fun j _ ↦ (ha j).smul continuous_const)

end QuantizationPresentation

end AtiyahSinger
