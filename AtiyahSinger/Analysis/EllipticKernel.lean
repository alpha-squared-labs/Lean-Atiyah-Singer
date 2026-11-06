/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DualTranspose
public import AtiyahSinger.Analysis.EllipticRegularity

/-!
# Smooth and Sobolev kernels of an elliptic differential operator

Public module ID: M0450.

A06/A07: SG III.5.2(ii). Restrict the actual smooth-to-Sobolev embedding to
kernels, prove its bijectivity by global regularity, then form the canonical linear
equivalence. The independent dual-bundle transpose kernel is also represented by
smooth covectors, using SG (5.1) and the already specified common dual-bundle
realization. No Hilbert adjoint is identified with a formal transpose.
The natural kernel map and injectivity use no ellipticity. Global regularity
proves surjectivity and both the original and transpose dimension comparisons.
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
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace DifferentialOperator

variable {m : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- A smooth kernel element embeds in the kernel of the original bounded realization. -/
theorem smoothToSobolev_mem_ker (s : ℝ) (u : P.toLinearMap.ker) :
    A.smoothToSobolev s u.val ∈ (P.sobolevExtension A B s).ker := by
  /- Apply the smooth-input specification of P's extension. Since P u=0, the
  output is the target embedding of zero. This uses no ellipticity and supplies
  the membership certificate for the actual restricted embedding below. -/
  change P.sobolevExtension A B s (A.smoothToSobolev s u.val) = 0
  rw [← P.sobolevExtension_toPseudodifferentialOperator μ A B s,
    PseudodifferentialOperator.sobolevExtension_smoothToSobolev]
  change B.smoothToSobolev (s - m) (P.toLinearMap u.val) = 0
  rw [u.property, map_zero]

/-- The smooth-section embedding restricted to the actual differential kernels. -/
def sobolevKerMap (s : ℝ) :
    P.toLinearMap.ker →ₗ[ℂ] (P.sobolevExtension A B s).ker :=
  ((A.smoothToSobolev s).comp P.toLinearMap.ker.subtype).codRestrict
    (P.sobolevExtension A B s).ker (P.smoothToSobolev_mem_ker μ A B s)

/-- The kernel map retains the given smooth section under the original embedding. -/
theorem sobolevKerMap_apply (s : ℝ) (u : P.toLinearMap.ker) :
    (P.sobolevKerMap μ A B s u).val = A.smoothToSobolev s u.val := by
  /- Project the codomain restriction of the explicit composite. The membership
  proof changes no vector, so the result is exactly the same smooth embedding. -/
  rfl

/-- Injectivity of the smooth embedding already gives injectivity on kernels. -/
theorem sobolevKerMap_injective (s : ℝ) :
    Function.Injective (P.sobolevKerMap μ A B s) := by
  /- Equality in the Sobolev kernel gives equality in the ambient completion.
  Use smoothToSobolev_injective and then subtype extensionality on the smooth
  kernel. No Fredholmness or finite-dimensionality is needed for this direction. -/
  intro u v huv
  apply Subtype.ext
  exact A.smoothToSobolev_injective s (congrArg Subtype.val huv)

/-- Elliptic regularity makes every Sobolev kernel vector the image of a smooth one. -/
theorem sobolevKerMap_surjective (hP : P.IsElliptic) (s : ℝ) :
    Function.Surjective (P.sobolevKerMap μ A B s) := by
  /- Given a Sobolev kernel vector, apply existsUnique_smooth_lift with smooth
  right-hand side zero. The resulting section lies in the smooth kernel and its
  embedding is the original vector. Package it as a subtype and use the map formula. -/
  intro u
  have hu : P.sobolevExtension A B s u.val = B.smoothToSobolev (s - m) 0 := by
    rw [map_zero]
    exact u.property
  obtain ⟨w, ⟨hw, hPw⟩, _⟩ := P.existsUnique_smooth_lift μ A B hP s u.val 0 hu
  refine ⟨⟨w, hPw⟩, ?_⟩
  exact Subtype.ext hw

/-- The canonical kernel identification induced by the original smooth embedding. -/
def sobolevKerEquiv (hP : P.IsElliptic) (s : ℝ) :
    P.toLinearMap.ker ≃ₗ[ℂ] (P.sobolevExtension A B s).ker :=
  LinearEquiv.ofBijective (P.sobolevKerMap μ A B s)
    ⟨P.sobolevKerMap_injective μ A B s, P.sobolevKerMap_surjective μ A B hP s⟩

/-- The kernel dimension is the same in every Sobolev realization and on smooth sections. -/
theorem finrank_ker_sobolevExtension (hP : P.IsElliptic) (s : ℝ) :
    Module.finrank ℂ (P.sobolevExtension A B s).ker = Module.finrank ℂ P.toLinearMap.ker := by
  /- Apply invariance of dimension to sobolevKerEquiv. Fredholmness supplies finite
  dimension of the Sobolev kernel, and the equivalence transfers it to the smooth
  kernel. This comparison does not rely on the earlier smooth finiteness theorem. -/
  exact (P.sobolevKerEquiv μ A B hP s).finrank_eq.symm

/-- The opposite-order weak transpose kernel has one smooth covector representative. -/
theorem existsUnique_smooth_of_sobolevTranspose_eq_zero (hP : P.IsElliptic)
    (s : ℝ) (α : B.DualSobolevSpace (-(s - m)))
    (hα : P.sobolevTranspose μ A B s α = 0) :
    ∃! β : smoothDualSections (n := n) (r := q) F,
      B.dualSmoothToSobolev (-(s - m)) β = α ∧ P.formalTranspose μ β = 0 := by
  /- Stage 1: use dualSobolevEquiv to move α to the common F* Sobolev model.
  The transpose diagram puts it in the kernel of formalTransposeSobolevExtension.
  This is the elliptic differential transpose at input order -(s-m); normalize
  its output order using -(s-m)-m=-s.
  Stage 2: apply global smooth lifting to formalTransposeOperator, which is
  elliptic by isElliptic_formalTranspose_iff. Move the smooth section back through
  dualSectionsEquiv. The smooth compatibility diagrams give the two equalities.
  Injectivity of the dual smooth embedding gives uniqueness of the representative. -/
  -- Transport only the target order of the common transpose realization.
  have hcast (t v : ℝ) (htv : t = v)
      (T : B.dualPresentation.SobolevSpace (-(s - m)) →L[ℂ]
        A.dualPresentation.SobolevSpace t)
      (z : B.dualPresentation.SobolevSpace (-(s - m))) :
      (htv ▸ T) z = 0 → T z = 0 := by
    subst v
    exact id
  have hzero : (P.formalTransposeOperator μ).sobolevExtension B.dualPresentation
      A.dualPresentation (-(s - m)) (B.dualSobolevEquiv (-(s - m)) α) = 0 := by
    have h := P.dualSobolevEquiv_transpose μ A B s α
    rw [hα, map_zero] at h
    exact hcast _ _ (by ring) _ _ h.symm
  -- Ellipticity of the actual dual-bundle operator gives its smooth representative.
  have hPt := (P.isElliptic_formalTranspose_iff μ).mpr hP
  obtain ⟨β, ⟨hβ, hPβ⟩, _⟩ := (P.formalTransposeOperator μ).existsUnique_smooth_lift
    μ B.dualPresentation A.dualPresentation hPt (-(s - m))
      (B.dualSobolevEquiv (-(s - m)) α) 0 (by simpa only [map_zero] using hzero)
  let γ := (dualSectionsEquiv F).symm β
  have hrep : B.dualSmoothToSobolev (-(s - m)) γ = α := by
    apply (B.dualSobolevEquiv (-(s - m))).injective
    rw [B.dualSobolevEquiv_smooth, LinearEquiv.apply_symm_apply]
    exact hβ
  have hPγ : P.formalTranspose μ γ = 0 := by
    apply (dualSectionsEquiv E).injective
    rw [map_zero, ← P.formalTransposeOperator_apply μ γ]
    simpa only [γ, LinearEquiv.apply_symm_apply] using hPβ
  refine ⟨γ, ⟨hrep, hPγ⟩, ?_⟩
  intro δ hδ
  exact B.dualSmoothToSobolev_injective (-(s - m)) (hδ.1.trans hrep.symm)

/-- The weak transpose kernel has the dimension of the original smooth transpose kernel. -/
theorem finrank_ker_sobolevTranspose (hP : P.IsElliptic) (s : ℝ) :
    Module.finrank ℂ (P.sobolevTranspose μ A B s).ker =
      Module.finrank ℂ (P.formalTranspose μ).ker := by
  /- Restrict B.dualSmoothToSobolev to the smooth transpose kernel. Its action
  formula gives a map to the weak kernel, injectivity follows from the embedding,
  and the preceding smooth lifting gives surjectivity. Its linear equivalence
  preserves dimension. Finiteness also follows from the common elliptic transpose
  realization; no identification with a Hilbert adjoint has been made. -/
  let f := (B.dualSmoothToSobolev (-(s - m))).comp (P.formalTranspose μ).ker.subtype
  have hf (β : (P.formalTranspose μ).ker) :
      f β ∈ (P.sobolevTranspose μ A B s).ker := by
    change P.sobolevTranspose μ A B s
      (B.dualSmoothToSobolev (-(s - m)) β.val) = 0
    rw [P.sobolevTranspose_smooth, β.property, map_zero]
  let g := f.codRestrict (P.sobolevTranspose μ A B s).ker hf
  have hinj : Function.Injective g := by
    intro β γ h
    apply Subtype.ext
    exact B.dualSmoothToSobolev_injective (-(s - m)) (congrArg Subtype.val h)
  -- Every weak zero has the same smooth representative supplied by regularity.
  have hsurj : Function.Surjective g := by
    intro α
    obtain ⟨β, ⟨hβ, hPβ⟩, _⟩ :=
      P.existsUnique_smooth_of_sobolevTranspose_eq_zero μ A B hP s α.val α.property
    exact ⟨⟨β, hPβ⟩, Subtype.ext hβ⟩
  exact (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq.symm

end DifferentialOperator

end AtiyahSinger
