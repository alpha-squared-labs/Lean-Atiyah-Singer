/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual cotangent lift of a diffeomorphism

Public module ID: M1147.

D03/P02: a covector is transported by the dual of the inverse differential.
This is not an unchanged model covector for a general coordinate change.
The forward formula is fixed before packaging its homeomorphism certificate.
Sources: SG III.1 (1.6), III.3 coordinate covariance, and III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n m k : ℕ} {M N W : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace W] [ChartedSpace (EuclideanSpace ℝ (Fin k)) W]

/-- The cotangent lift sends (x,ξ) to (e x, ξ composed with the inverse differential). -/
def cotangentDiffeomorphMap
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    CotangentTotalSpace (n := n) (M := M) → CotangentTotalSpace (n := m) (M := N) :=
  fun z ↦ ⟨e z.proj,
    z.snd.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e.symm (e z.proj))⟩

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hW : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ W]

include hM hN in
/-- The inverse-dual differential gives a homeomorphism of the original cotangent bundles. -/
theorem isHomeomorph_cotangentDiffeomorphMap
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    IsHomeomorph (cotangentDiffeomorphMap e) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  -- Compose the original covector coordinates with the actual inverse differential.
  have hforward : Continuous (cotangentDiffeomorphMap e) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let tM := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) z₀.proj
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦ z) (x₀ := z₀)).mp continuousAt_id
    have hξ : ContinuousAt (fun z : CotangentTotalSpace (n := n) (M := M) ↦
        z.snd.comp (tM.symmL ℝ z.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : CotangentTotalSpace (n := n) (M := M) ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj).comp
          (z.snd.comp (tM.symmL ℝ z.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    have hbase := e.continuous.continuousAt.comp hsource.1
    have hd := ((e.symm.contMDiffAt (x := e z₀.proj)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : CotangentTotalSpace (n := n) (M := M) ↦ e z.proj) hbase
    have hprod := hξ.clm_comp hd
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨hbase, ?_⟩
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hsource.1.preimage_mem_nhds
      (tM.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))]
      with z hz
    apply ContinuousLinearMap.ext
    intro v
    have hscalar :
        (trivializationAt ℝ (fun _ : N ↦ ℝ) (e z₀.proj)).continuousLinearMapAt ℝ
          (e z.proj) = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ (e z.proj) = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [cotangentDiffeomorphMap, Function.comp_apply, inTangentCoordinates,
      ContinuousLinearMap.inCoordinates, Function.id_def, e.symm_apply_apply,
      ContinuousLinearMap.comp_apply, hscalar, ContinuousLinearMap.id_apply]
    erw [e.symm_apply_apply, ContinuousLinearMap.comp_apply]
    change z.snd ((mfderiv J I e.symm (e z.proj))
        ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace J)
          (e z₀.proj)).symmL ℝ (e z.proj) v)) =
      z.snd (tM.symmL ℝ z.proj (tM.continuousLinearMapAt ℝ z.proj
        ((mfderiv J I e.symm (e z.proj))
          ((trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace J)
            (e z₀.proj)).symmL ℝ (e z.proj) v))))
    erw [tM.symmL_continuousLinearMapAt (R := ℝ) hz]
  -- The same coordinate argument applies to the inverse diffeomorphism.
  let g := e.symm
  have hbackward : Continuous (cotangentDiffeomorphMap g) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let tN := trivializationAt (EuclideanSpace ℝ (Fin m)) (TangentSpace J) z₀.proj
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : CotangentTotalSpace (n := m) (M := N) ↦ z) (x₀ := z₀)).mp continuousAt_id
    have hξ : ContinuousAt (fun z : CotangentTotalSpace (n := m) (M := N) ↦
        z.snd.comp (tN.symmL ℝ z.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : CotangentTotalSpace (n := m) (M := N) ↦
        ((Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ z.proj).comp
          (z.snd.comp (tN.symmL ℝ z.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    have hbase := g.continuous.continuousAt.comp hsource.1
    have hd := ((g.symm.contMDiffAt (x := g z₀.proj)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt.comp
      (f := fun z : CotangentTotalSpace (n := m) (M := N) ↦ g z.proj) hbase
    have hprod := hξ.clm_comp hd
    apply (continuousAt_hom_bundle (RingHom.id ℝ) _).mpr
    refine ⟨hbase, ?_⟩
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hsource.1.preimage_mem_nhds
      (tN.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ z₀.proj))]
      with z hz
    apply ContinuousLinearMap.ext
    intro v
    have hscalar :
        (trivializationAt ℝ (fun _ : M ↦ ℝ) (g z₀.proj)).continuousLinearMapAt ℝ
          (g z.proj) = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (g z.proj) = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    simp only [cotangentDiffeomorphMap, Function.comp_apply, inTangentCoordinates,
      ContinuousLinearMap.inCoordinates, Function.id_def, g.symm_apply_apply,
      ContinuousLinearMap.comp_apply, hscalar, ContinuousLinearMap.id_apply]
    erw [g.symm_apply_apply, ContinuousLinearMap.comp_apply]
    change z.snd ((mfderiv I J g.symm (g z.proj))
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I)
          (g z₀.proj)).symmL ℝ (g z.proj) v)) =
      z.snd (tN.symmL ℝ z.proj (tN.continuousLinearMapAt ℝ z.proj
        ((mfderiv I J g.symm (g z.proj))
          ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I)
            (g z₀.proj)).symmL ℝ (g z.proj) v))))
    erw [tN.symmL_continuousLinearMapAt (R := ℝ) hz]
  -- The chain rule identifies the two fiber composites with the identity.
  have hleft : Function.LeftInverse (cotangentDiffeomorphMap e.symm)
      (cotangentDiffeomorphMap e) := by
    rintro ⟨x, ξ⟩
    have hd := mfderiv_comp x (e.symm.mdifferentiable (by simp) (e x))
      (e.mdifferentiable (by simp) x)
    have he : (e.symm : N → M) ∘ e = id := funext e.symm_apply_apply
    rw [he, mfderiv_id] at hd
    dsimp only [cotangentDiffeomorphMap]
    erw [e.symm_apply_apply]
    congr 1
    erw [ContinuousLinearMap.comp_assoc, ← hd, ContinuousLinearMap.comp_id]
  have hright : Function.RightInverse (cotangentDiffeomorphMap e.symm)
      (cotangentDiffeomorphMap e) := by
    rintro ⟨y, η⟩
    have hd := mfderiv_comp y (e.mdifferentiable (by simp) (e.symm y))
      (e.symm.mdifferentiable (by simp) y)
    have he : (e : M → N) ∘ e.symm = id := funext e.apply_symm_apply
    rw [he, mfderiv_id] at hd
    dsimp only [cotangentDiffeomorphMap]
    erw [e.apply_symm_apply]
    congr 1
    erw [ContinuousLinearMap.comp_assoc, ← hd, ContinuousLinearMap.comp_id]
  -- Package the original maps, with the native bundle topologies unchanged.
  exact (show CotangentTotalSpace (n := n) (M := M) ≃ₜ
      CotangentTotalSpace (n := m) (M := N) from
    { toFun := cotangentDiffeomorphMap e
      invFun := cotangentDiffeomorphMap e.symm
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hforward
      continuous_invFun := hbackward }).isHomeomorph

/-- The cotangent homeomorphism with exactly the specified forward differential formula. -/
def cotangentDiffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N) :
    CotangentTotalSpace (n := n) (M := M) ≃ₜ CotangentTotalSpace (n := m) (M := N) :=
  (isHomeomorph_cotangentDiffeomorphMap e).homeomorph (cotangentDiffeomorphMap e)

/-- Cotangent lifts respect composition, including their actual inverse-dual fiber maps. -/
theorem cotangentDiffeomorph_trans
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
    (f : N ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin m)), 𝓘(ℝ, EuclideanSpace ℝ (Fin k))⟯ W) :
    cotangentDiffeomorph (e.trans f) = (cotangentDiffeomorph e).trans (cotangentDiffeomorph f) := by
  -- The inverse of the composite is e.symm after f.symm, on the actual base points.
  apply Homeomorph.ext
  intro z
  change cotangentDiffeomorphMap (e.trans f) z =
    cotangentDiffeomorphMap f (cotangentDiffeomorphMap e z)
  have hd := mfderiv_comp (f (e z.proj))
    (e.symm.mdifferentiable (by simp) (f.symm (f (e z.proj))))
    (f.symm.mdifferentiable (by simp) (f (e z.proj)))
  -- Covector precomposition has precisely the contravariant chain-rule order.
  dsimp only [cotangentDiffeomorphMap]
  congr 1
  change z.snd.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((e.symm : N → M) ∘ f.symm) (f (e z.proj))) = _
  erw [hd, ContinuousLinearMap.comp_assoc, f.symm_apply_apply]
  rfl

end AtiyahSinger
