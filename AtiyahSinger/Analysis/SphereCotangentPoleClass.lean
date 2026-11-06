/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SphereTangentIndex
public import AtiyahSinger.Geometry.SphereCotangentPoleCoordinates
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph
public import AtiyahSinger.Topology.EquivariantProperHomotopy

/-!
# The original pole class in inverse-dual cotangent coordinates

Public module ID: M1006.

A proper equivariant positive-fiber homotopy removes the round metric's
conformal factor from the actual musical image of the pole class. The
remaining class is the original exterior Bott class extended through the
specified inverse-dual pole chart. This precedes the common-open comparison
and does not use any point-index normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff unitInterval Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 35

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent tangentBundleFullChartedSpace
  compactSpace_orthogonalGroup

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Retain the original support quotient through the full positive imaginary-fiber cylinder.
/-- The actual musical pole class is the original Bott class in the inverse-dual pole chart. -/
theorem orthogonalSphereMusicalKMap_polePushforward (r : ℕ) (atInfinity : Bool) :
    orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r atInfinity 1) =
      equivariantSupportTripleKZeroOpenPushforward
        (orthogonalSphereCotangentChart r atInfinity)
        (orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity)
        (orthogonalSphereCotangentChart_equivariant r atInfinity)
        (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) := by
  classical
  let := compactSpace_orthogonalGroup r
  let V := EuclideanSpace ℂ (Fin r)
  let E := EuclideanSpace ℝ (Fin r)
  let S := orthogonalSpherePoleImaginaryScale r
  let R := euclideanComplexRealProductHomeomorph r
  let s := orthogonalSpherePoleConformalFactor r
  have hs := orthogonalSpherePoleConformalFactor_pos r
  have hSe := orthogonalSpherePoleImaginaryScale_equivariant r
  have hSi (g : Matrix.orthogonalGroup (Fin r) ℝ) (z : V) :
      S.symm (orthogonalComplexificationRepresentation r g z) =
        orthogonalComplexificationRepresentation r g (S.symm z) := by
    apply S.injective
    rw [S.apply_symm_apply, hSe, S.apply_symm_apply]
  -- The cylinder fixes the real base and interpolates only its positive imaginary factor.
  let c (t : I) (u : E) : ℝ := (1 - (t : ℝ)) + (t : ℝ) * s u
  have hc (t : I) (u : E) : 0 < c t u := by
    dsimp only [c]
    by_cases ht : (t : ℝ) = 0
    · simp only [ht, sub_zero, zero_mul, add_zero, zero_lt_one]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) (hs u))
  have hcontinuous : Continuous (fun z : I × (E × E) ↦ c z.1 z.2.1) := by
    dsimp only [c]
    fun_prop
  let A₀ : I × (E × E) ≃ₜ I × (E × E) := {
    toFun z := (z.1, z.2.1, c z.1 z.2.1 • z.2.2)
    invFun z := (z.1, z.2.1, (c z.1 z.2.1)⁻¹ • z.2.2)
    left_inv z := by
      change (z.1, z.2.1, (c z.1 z.2.1)⁻¹ • (c z.1 z.2.1 • z.2.2)) = z
      rw [smul_smul, inv_mul_cancel₀ (hc z.1 z.2.1).ne', one_smul]
    right_inv z := by
      change (z.1, z.2.1, c z.1 z.2.1 • ((c z.1 z.2.1)⁻¹ • z.2.2)) = z
      rw [smul_smul, mul_inv_cancel₀ (hc z.1 z.2.1).ne', one_smul]
    continuous_toFun := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (hcontinuous.smul (continuous_snd.comp continuous_snd)))
    continuous_invFun := continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        ((hcontinuous.inv₀ (fun z ↦ (hc z.1 z.2.1).ne')).smul
          (continuous_snd.comp continuous_snd))) }
  let B := (Homeomorph.refl I).prodCongr R
  let A := (B.trans A₀).trans B.symm
  let H : ContinuousMap.Homotopy (ContinuousMap.id V) (⟨S, S.continuous⟩ : C(V, V)) := {
    toFun z := (A z).2
    continuous_toFun := continuous_snd.comp A.continuous
    map_zero_left z := by
      change R.symm ((R z).1, c 0 (R z).1 • (R z).2) = z
      simp only [c, (show ((0 : I) : ℝ) = 0 from rfl), sub_zero, zero_mul, add_zero, one_smul]
      exact R.symm_apply_apply z
    map_one_left z := by
      change R.symm ((R z).1, c 1 (R z).1 • (R z).2) = S z
      simp only [c, (show ((1 : I) : ℝ) = 1 from rfl), sub_self, one_mul, zero_add]
      rfl }
  have hHp : IsProperMap H :=
    isProperMap_snd_of_compactSpace.comp A.isProperMap
  -- Real linearity of the original complexified action preserves the entire interpolation.
  have hlinear (t : I) (z : V) : H (t, z) = (1 - (t : ℝ)) • z + (t : ℝ) • S z := by
    have hHcoords : R (H (t, z)) = ((R z).1, c t (R z).1 • (R z).2) :=
      R.apply_symm_apply _
    apply R.injective
    rw [hHcoords]
    apply Prod.ext
    · ext i
      change (z i).re = (((1 - (t : ℝ)) • z + (t : ℝ) • S z) i).re
      simp only [V, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        Complex.add_re, Complex.smul_re]
      change (z i).re = (1 - (t : ℝ)) * (z i).re + (t : ℝ) * (z i).re
      ring
    · ext i
      change c t (R z).1 * (z i).im =
        (((1 - (t : ℝ)) • z + (t : ℝ) • S z) i).im
      simp only [V, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        Complex.add_im, Complex.smul_im]
      change ((1 - (t : ℝ)) + (t : ℝ) * s (R z).1) * (z i).im =
        (1 - (t : ℝ)) * (z i).im + (t : ℝ) * (s (R z).1 * (z i).im)
      ring
  have hHe (t : I) (g : Matrix.orthogonalGroup (Fin r) ℝ) (z : V) :
      H (t, orthogonalComplexificationRepresentation r g z) =
        orthogonalComplexificationRepresentation r g (H (t, z)) := by
    have hcomm (a : ℝ) (w : V) :
        orthogonalComplexificationRepresentation r g (a • w) =
          a • orthogonalComplexificationRepresentation r g w :=
      ((orthogonalComplexificationRepresentation r g).restrictScalars ℝ).map_smul a w
    rw [hlinear, hlinear, hSe, map_add, hcomm, hcomm]
  have hS := equivariantSupportTripleKZeroPullback_eq_of_proper_homotopy
    (ContinuousMap.id V) ⟨S, S.continuous⟩ (fun _ _ ↦ rfl) hSe
      isProperMap_id S.isProperMap H hHe hHp
  rw [equivariantSupportTripleKZeroPullback_id] at hS
  have hinverse := equivariantSupportTripleKZeroPullback_comp
    (⟨S, S.continuous⟩ : C(V, V)) ⟨S.symm, S.symm.continuous⟩ hSe hSi
    S.isProperMap S.symm.isProperMap
  have hid : (⟨S, S.continuous⟩ : C(V, V)).comp ⟨S.symm, S.symm.continuous⟩ =
      ContinuousMap.id V := by
    apply ContinuousMap.ext
    intro z
    exact S.apply_symm_apply z
  have hinverse' : AddMonoidHom.id (EquivariantSupportTripleKZero
      (Matrix.orthogonalGroup (Fin r) ℝ) V) =
      equivariantSupportTripleKZeroPullback ⟨S.symm, S.symm.continuous⟩
        hSi S.symm.isProperMap := by
    simpa only [hid, equivariantSupportTripleKZeroPullback_id, ← hS,
      AddMonoidHom.comp_id] using hinverse
  have hopenS : equivariantSupportTripleKZeroOpenPushforward
      (⟨S, S.continuous⟩ : C(V, V)) S.isOpenEmbedding hSe =
      AddMonoidHom.id (EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ) V) := by
    have hh := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm S.symm hSi hSe
    simpa only [Homeomorph.symm_symm] using hh.symm.trans hinverse'.symm
  -- Compose the exact geometric chart factorization with the same original Bott generator.
  let g := (orthogonalSphereRoundMetric r).flatHomeomorph
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let : T2Space T := (tangentBundle_topology E (OrthogonalSphere r)).1
  let : LocallyCompactSpace T := ChartedSpace.locallyCompactSpace (E × E) T
  have hg (a : Matrix.orthogonalGroup (Fin r) ℝ) (v : T) : g (a • v) = a • g v := by
    apply g.symm.injective
    rw [g.symm_apply_apply, orthogonalSphereRoundMetric_flat_symm_equivariant,
      g.symm_apply_apply]
  let f := orthogonalSphereTangentChart r atInfinity
  let j := orthogonalSphereCotangentChart r atInfinity
  have hf := orthogonalSphereTangentChart_isOpenEmbedding r atInfinity
  have hfe := orthogonalSphereTangentChart_equivariant r atInfinity
  have hj := orthogonalSphereCotangentChart_isOpenEmbedding r atInfinity
  have hje := orthogonalSphereCotangentChart_equivariant r atInfinity
  have hmaps : (⟨g, g.continuous⟩ : C(T, _)).comp f = j.comp ⟨S, S.continuous⟩ := by
    apply ContinuousMap.ext
    intro z
    exact orthogonalSphereRoundMetric_flat_tangentChart r atInfinity z
  have hleft := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    f hf hfe ⟨g, g.continuous⟩ g.isOpenEmbedding hg
  have hright := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    ⟨S, S.continuous⟩ S.isOpenEmbedding hSe j hj hje
  have hmapEq : (equivariantSupportTripleKZeroOpenPushforward ⟨g, g.continuous⟩
      g.isOpenEmbedding hg).comp (equivariantSupportTripleKZeroOpenPushforward f hf hfe) =
      equivariantSupportTripleKZeroOpenPushforward j hj hje := by
    have hh : equivariantSupportTripleKZeroOpenPushforward
        ((⟨g, g.continuous⟩ : C(T, _)).comp f) (g.isOpenEmbedding.comp hf)
        (fun a z ↦ (congrArg g (hfe a z)).trans (hg a (f z))) =
        equivariantSupportTripleKZeroOpenPushforward j hj hje := by
      simpa only [hmaps, hopenS, V, AddMonoidHom.comp_id] using hright
    exact hleft.symm.trans hh
  change equivariantSupportTripleKZeroPullback ⟨g.symm, g.symm.continuous⟩
      (orthogonalSphereRoundMetric_flat_symm_equivariant r) g.symm.isProperMap
      (equivariantSupportTripleKZeroOpenPushforward f hf hfe
        ((1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) •
          equivariantExteriorBottClass (orthogonalComplexification_unitary r))) = _
  rw [one_smul,
    equivariantSupportTripleKZeroPullback_eq_openPushforward_symm g.symm
      (orthogonalSphereRoundMetric_flat_symm_equivariant r) hg]
  exact DFunLike.congr_fun hmapEq _

end AtiyahSinger
