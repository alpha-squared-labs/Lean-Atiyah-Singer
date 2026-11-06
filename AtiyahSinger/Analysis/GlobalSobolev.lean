/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Geometry.SmoothBundlePresentation
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Global Sobolev spaces from actual localized Bessel coordinates

Public module ID: M0676.

For a finite presentation A and real s, map a smooth section to the tuple
(J^s localize_j(u))_j in the finite Hilbert sum of Euclidean L² spaces. The Sobolev
space is the closure of the range of this actual linear map. Thus it is a concrete
completion, with an inherited Hilbert norm, not an unspecified Hilbert-space family.
We use the square-sum norm; SG (2.17) uses the equivalent finite sum of local norms.

Local distribution realizations retain the relationship between different orders.
At order s the j-th coordinate is J^s(χ_j u), so J^(-s) recovers the localized
distribution. Norm comparison and maps between completions are stated separately.
Sources: Spin Geometry III.2.2, (2.17), and the existing Bessel realization module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap

variable {n r : ℕ}

/-- Bessel coordinates of Schwartz functions preserve addition. -/
theorem schwartzSobolevCoordinate_add (s : ℝ)
    (u v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    schwartzSobolevCoordinate s (u + v) =
      schwartzSobolevCoordinate s u + schwartzSobolevCoordinate s v := by
  /- The Fourier multiplier is additive, and the map from Schwartz functions to
  their L² classes is additive. Compose these two equalities for the explicit map. -/
  unfold schwartzSobolevCoordinate
  rw [map_add]
  exact (SchwartzMap.toLpCLM ℂ _ 2 volume).map_add _ _

/-- The real Bessel weight also commutes with complex scalar multiplication. -/
theorem schwartzSobolevCoordinate_smul (s : ℝ) (c : ℂ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    schwartzSobolevCoordinate s (c • u) = c • schwartzSobolevCoordinate s u := by
  /- Fourier transform and its inverse are complex-linear. Multiplication by the
  positive real Bessel weight commutes with complex scalars. Passing to L² classes
  preserves this identity, even though the existing multiplier was packaged over ℝ. -/
  -- Express the unchanged real multiplier using its equal complex-linear version.
  have hweight := Function.hasTemperateGrowth_one_add_norm_sq_rpow
    (EuclideanSpace ℝ (Fin n)) (s / 2)
  unfold schwartzSobolevCoordinate
  rw [← SchwartzMap.fourierMultiplierCLM_ofReal ℂ hweight,
    ← SchwartzMap.fourierMultiplierCLM_ofReal ℂ hweight, map_smul]
  exact (SchwartzMap.toLpCLM ℂ _ 2 volume).map_smul c _

/-- The existing Bessel-coordinate formula, packaged as a complex-linear map. -/
def schwartzSobolevCoordinateLinearMap (n r : ℕ) (s : ℝ) :
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →ₗ[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := schwartzSobolevCoordinate s
  map_add' := schwartzSobolevCoordinate_add s
  map_smul' := schwartzSobolevCoordinate_smul s

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

/-- The finite Hilbert sum containing the localized Bessel coordinates. -/
abbrev SobolevCoordinates : Type :=
  PiLp 2 (fun _ : Fin A.size ↦
    Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))

/-- The actual map u ↦ (J^s(χ_j u))_j, with the finite square-sum Hilbert norm. -/
def sobolevCoordinates (s : ℝ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] A.SobolevCoordinates :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap.comp
    (LinearMap.pi fun j ↦
      (schwartzSobolevCoordinateLinearMap n r s).comp (A.localizeLinearMap j))

/-- Localization by a partition of unity and invertible Bessel weights is injective. -/
theorem sobolevCoordinates_injective (s : ℝ) :
    Function.Injective (A.sobolevCoordinates s) := by
  /- If the coordinate tuples agree, apply J^(-s) in each chart. The Bessel
  realization identity gives equal localized smooth distributions, hence equal
  localized functions. Pull back through each frame and sum χ_j u using Σχ_j=1.
  Equality of every fiber value gives equality of the original smooth sections. -/
  classical
  intro u v huv
  -- The inverse Bessel realization recovers the same actual Schwartz localization.
  have hlocal (j : Fin A.size) : A.localize j u = A.localize j v := by
    have hcoord := congrArg (fun f : A.SobolevCoordinates ↦ f j) huv
    change schwartzSobolevCoordinate s (A.localize j u) =
      schwartzSobolevCoordinate s (A.localize j v) at hcoord
    have hdist := congrArg (besselRealization n r s) hcoord
    rw [besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate] at hdist
    apply (SchwartzMap.injective_toLp 2 volume)
    apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
    change ((A.localize j u).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) =
      ((A.localize j v).toLp 2 volume :
        𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hdist
  apply Subtype.ext
  funext x
  -- Pull each cutoff equality back through the original frame at the same point.
  have hcut (j : Fin A.size) :
      (A.cutoff j x : ℂ) • u.val x = (A.cutoff j x : ℂ) • v.val x := by
    by_cases hx : x ∈ tsupport (A.cutoff j)
    · let := A.frame_mem_atlas j
      have hsource := (A.support_subset j hx).1
      have hframe := (A.support_subset j hx).2
      have hpointu : (⟨(A.chart j).symm ((A.chart j) x),
          u.val ((A.chart j).symm ((A.chart j) x))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, u.val x⟩ :=
        congrArg (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((A.chart j).left_inv hsource)
      have hpointv : (⟨(A.chart j).symm ((A.chart j) x),
          v.val ((A.chart j).symm ((A.chart j) x))⟩ :
            TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, v.val x⟩ :=
        congrArg (fun y ↦ (⟨y, v.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          ((A.chart j).left_inv hsource)
      have hcoords := congrArg (fun f ↦ f ((A.chart j) x)) (hlocal j)
      change A.localizedFunction j u ((A.chart j) x) =
        A.localizedFunction j v ((A.chart j) x) at hcoords
      simp only [localizedFunction, ite_eq_left ((A.chart j).map_source hsource),
        sectionInChart, hpointu, hpointv, (A.chart j).left_inv hsource] at hcoords
      apply ((A.frame j).linearEquivAt ℂ x hframe).injective
      rw [map_smul, map_smul]
      exact hcoords
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- Sum with the supplied partition of unity to recover both original sections.
  have hsum : ∑ j, (A.cutoff j x : ℂ) = 1 := by exact_mod_cast A.sum_cutoff x
  calc
    u.val x = (∑ j, (A.cutoff j x : ℂ)) • u.val x := by rw [hsum, one_smul]
    _ = ∑ j, (A.cutoff j x : ℂ) • u.val x := Finset.sum_smul
    _ = ∑ j, (A.cutoff j x : ℂ) • v.val x := Finset.sum_congr rfl (fun j _ ↦ hcut j)
    _ = (∑ j, (A.cutoff j x : ℂ)) • v.val x := Finset.sum_smul.symm
    _ = v.val x := by rw [hsum, one_smul]

/-- The completion of smooth sections in the specified real-order Sobolev norm.
It is realized as a closed subspace of the finite Hilbert sum of local L² spaces. -/
abbrev SobolevSpace (s : ℝ) : Type :=
  (A.sobolevCoordinates s).range.topologicalClosure

/-- The dense linear embedding of actual smooth sections into their Sobolev completion. -/
def smoothToSobolev (s : ℝ) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ] A.SobolevSpace s :=
  (Submodule.inclusion (A.sobolevCoordinates s).range.le_topologicalClosure).comp
    (A.sobolevCoordinates s).rangeRestrict

/-- The embedding retains the original section, rather than quotienting distinct smooth inputs. -/
theorem smoothToSobolev_injective (s : ℝ) : Function.Injective (A.smoothToSobolev s) := by
  /- The underlying Hilbert tuple of smoothToSobolev u is exactly sobolevCoordinates u.
  Equality in the closure therefore gives equality of those tuples; apply their
  injectivity to recover equality of the original smooth sections. -/
  intro u v h
  exact A.sobolevCoordinates_injective s (congrArg Subtype.val h)

/-- Smooth sections are dense in this concrete Sobolev completion. -/
theorem denseRange_smoothToSobolev (s : ℝ) : DenseRange (A.smoothToSobolev s) := by
  /- The space was defined as the topological closure of the range of the coordinate
  map. Restricting the ambient range to its closure is dense there, and the displayed
  smooth-section map has exactly that range. No additional density axiom is assumed. -/
  have hdense : DenseRange
      (Set.inclusion (A.sobolevCoordinates s).range.le_topologicalClosure) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hdense.comp (A.sobolevCoordinates s).surjective_rangeRestrict.denseRange
    (continuous_inclusion _)

/-- The norm is the square sum of the actual localized Bessel L² norms. -/
theorem norm_smoothToSobolev_sq (s : ℝ)
    (u : smoothSections (n := n) (r := r) E) :
    ‖A.smoothToSobolev s u‖ ^ 2 =
      ∑ j, ‖schwartzSobolevCoordinate s (A.localize j u)‖ ^ 2 := by
  /- The subspace norm is inherited from PiLp 2. Its squared norm is the finite sum
  of the squared coordinate norms. The coordinate map uses exactly the Bessel L²
  representatives appearing on the right, by its explicit definition. -/
  exact PiLp.norm_sq_eq_of_L2 _ (A.sobolevCoordinates s u)

/-- The localized distribution χ_j u represented by a Sobolev vector. -/
def localDistribution (s : ℝ) (j : Fin A.size) (u : A.SobolevSpace s) :
    𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
  besselRealization n r s (u.val j)

/-- On smooth inputs the local distribution is precisely the cutoff section in that chart. -/
theorem localDistribution_smoothToSobolev (s : ℝ) (j : Fin A.size)
    (u : smoothSections (n := n) (r := r) E) :
    A.localDistribution s j (A.smoothToSobolev s u) =
      (A.localize j u : 𝓢'(_, _)) := by
  /- The j-th Hilbert coordinate is J^s applied to the localized Schwartz function.
  The previously stated Bessel realization identity cancels this weight with J^(-s),
  recovering exactly the distribution induced by that localized function. -/
  exact besselRealization_schwartzSobolevCoordinate s (A.localize j u)

/-- The localized distribution has the same fixed compact support bound after completion. -/
theorem isSupportedIn_localDistribution (s : ℝ) (j : Fin A.size)
    (u : A.SobolevSpace s) :
    IsSupportedIn (A.localDistribution s j u) ((A.chart j) '' tsupport (A.cutoff j)) := by
  /- Approximate u by smooth sections in the defining Hilbert closure. Their localized
  functions have support in the displayed fixed compact set. Evaluation of the Bessel
  realization on each Schwartz test function is continuous. For a compactly supported
  test function disjoint from this set, pass the zero evaluation to the limit. -/
  have hK : IsCompact ((A.chart j) '' tsupport (A.cutoff j)) :=
    (A.compact_support j).image_of_continuousOn
      ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
  -- Compact tests characterize this same closed support bound.
  apply (isSupportedIn_iff_compact_tests _ _ hK.isClosed).mpr
  intro φ _ hdisjoint
  -- Fixed-test evaluation is continuous for the original distribution topology.
  let T : A.SobolevCoordinates →L[ℂ] EuclideanSpace ℂ (Fin r) :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp
      ((besselRealization n r s).comp (PiLp.proj 2 _ j))
  have heval : Continuous (fun w : A.SobolevSpace s ↦ A.localDistribution s j w φ) :=
    T.continuous.comp continuous_subtype_val
  refine (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_eq heval continuous_const)
    ?_
  intro v
  rw [A.localDistribution_smoothToSobolev]
  -- Each smooth localization vanishes wherever the disjoint test function can be nonzero.
  change (∫ x, φ x • A.localizedFunction j v x) = 0
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro x
  change φ x • A.localizedFunction j v x = 0
  by_cases hx : x ∈ tsupport φ
  · have hnot : x ∉ tsupport (A.localizedFunction j v) := fun hlocal ↦
      Set.disjoint_left.mp hdisjoint hx (A.tsupport_localizedFunction_subset j v hlocal)
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end SmoothBundlePresentation

end AtiyahSinger
