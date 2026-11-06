/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedSphereIndexInputs
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDiffeomorph
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexModule
public import AtiyahSinger.Analysis.EquivariantSmoothIndexOrder
public import AtiyahSinger.Analysis.PositiveHodgeNativeRealization
public import AtiyahSinger.Analysis.SphereHodgeIndex
public import AtiyahSinger.Analysis.SphereHodgeNativeAction
public import AtiyahSinger.Analysis.SphereHodgeSymbolClass
public import AtiyahSinger.Geometry.ComplexifiedTangentFormBundle
public import AtiyahSinger.Geometry.SphereExteriorFormNaturality
public import AtiyahSinger.Geometry.SphereHodgeParitySymbol
public import AtiyahSinger.Geometry.SphereMusical
public import AtiyahSinger.Geometry.SphereReflectionMusical
public import AtiyahSinger.Topology.LowSphereTangentClasses
public import AtiyahSinger.Topology.SphereDeRhamClass

/-!
# The original sphere index on its native tangent K group

Public module ID: M1012.

AL03 transports the existing cotangent analytic index by proper pullback
along the inverse of the specified round musical homeomorphism. Both group
actions are the original derivative and inverse-differential actions. The
result is linear over the full representation ring and is invariant under
the actual tangent lift of vertical reflection.

The value on `orthogonalSphereDeRhamClass` is compared with the actual smooth
Hodge operator's kernel-minus-cokernel representation. The source Koszul map
is wedge plus contraction. With the project's D_j = -i partial_j convention,
the Hodge principal map is i times wedge minus contraction. Multiplication by
i^p in exterior degree p gives the exact parity-preserving conjugacy; these
maps must not be called literally equal. The real round metric is extended
complex-linearly to identify tangent exterior powers with covariant forms.

Sources: SG II.5, pp.123--126; III.9, pp.211--212; III.13, pp.247 and 253;
ASI I section 8, pp.523--524. The explicit bundle-model, phase, and equivariant
order-reduction comparison is a project supplement, using the actual
equivariant invertible radial PDO. Dimension zero is retained.
No equality of analytic and topological indices is assumed.
Reflection naturality and representation linearity hold on the original full K group.
The comparison retains the original smooth kernel and the actual range quotient.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent tangentBundleFullChartedSpace

/-- Proper pullback by the inverse round musical map sends actual tangent classes to cotangent. -/
def orthogonalSphereMusicalKMap (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
  equivariantSupportTripleKZeroPullback
    ⟨(orthogonalSphereRoundMetric r).flatHomeomorph.symm,
      (orthogonalSphereRoundMetric r).flatHomeomorph.symm.continuous⟩
    (orthogonalSphereRoundMetric_flat_symm_equivariant r)
    (orthogonalSphereRoundMetric r).flatHomeomorph.symm.isProperMap

/-- The existing full sphere analytic index applied after that same round musical transport. -/
def orthogonalSphereTangentAnalyticIndex (r : ℕ) :
    EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) →+
      RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ) :=
  (orthogonalSphereAnalyticIndex r).comp (orthogonalSphereMusicalKMap r)

open scoped Matrix.Norms.L2Operator in
/-- The transported original analytic index is linear over the same full representation ring. -/
theorem orthogonalSphereTangentAnalyticIndex_smul (r : ℕ)
    (a : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ))
    (z : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r))) :
    orthogonalSphereTangentAnalyticIndex r (a • z) =
      a • orthogonalSphereTangentAnalyticIndex r z := by
  -- Use the original compact orthogonal Lie group, sphere action and native cotangent lift.
  let := orthogonalGroupChartedSpace r
  let := lieGroup_orthogonalGroup r
  let := compactSpace_orthogonalGroup r
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  -- The same proper inverse round-musical pullback respects every virtual representation.
  change orthogonalSphereAnalyticIndex r (orthogonalSphereMusicalKMap r (a • z)) = _
  rw [show orthogonalSphereMusicalKMap r (a • z) =
    a • orthogonalSphereMusicalKMap r z from
      equivariantSupportTripleKZeroPullback_smul _ _ _ a z]
  -- Compose with full representation-linearity of the original analytic index.
  exact equivariantAnalyticIndexMap_smul
    (VG := OrthogonalGroupModel r) (G := Matrix.orthogonalGroup (Fin r) ℝ)
    (n := r) (M := OrthogonalSphere r) a (orthogonalSphereMusicalKMap r z)

attribute [local instance] sphereComplexifiedTangentTopology exteriorTopology
  exteriorParityTopology isFiniteRank_sphereComplexifiedTangent isFiniteRank_exteriorParity

set_option maxHeartbeats 2200000 in
-- Retain one native realization through both actions, the symbol square and the full index.
open scoped Matrix.Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual tangent exterior class has the original round Hodge operator's full index. -/
theorem orthogonalSphereTangentAnalyticIndex_deRhamClass (r : ℕ) :
    orthogonalSphereTangentAnalyticIndex r (orthogonalSphereDeRhamClass r) =
      orthogonalSphereDeRhamIndex r := by
  classical
  let g := orthogonalSphereRoundMetric r
  let IG := 𝓘(ℝ, OrthogonalGroupModel r)
  let := lieGroup_orthogonalGroup r
  let := compactSpace_orthogonalGroup r
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  let := g.isSmoothPositiveMeasure_riemannianVolume
  -- One realization fixes the original operator, both native bundles and all section coordinates.
  obtain ⟨E, F, e, f, Φ, hΦ, Ψ, hΨ, _, _, _, _, P, hP, b, hb, hprincipal⟩ :=
    exists_positiveHodgeDirac_nativeRealization g
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  obtain ⟨σ, hσ, τ, hτ, hσfiber, hτfiber, hΦaction, hΨaction, hPequiv⟩ :=
    exists_sphereHodgeNativeAction r E F e f Φ hΦ Ψ hΨ
  have hPg := hPequiv P hP
  obtain ⟨e₀, f₀, he₀, hf₀⟩ :=
    exists_sphereComplexifiedTangentFormIso r E F e f Φ hΦ Ψ hΨ
  -- The metric exterior maps intertwine the same derivative and inverse-pullback actions.
  have hequiv : e₀.IsEquivariant (sphereExteriorParityEquivariantStructure r 0) σ := by
    intro A x u
    change e₀.linearEquiv (A • x)
      ((sphereExteriorParityEquivariantStructure r 0).linearMap A x u) =
        σ.linearMap A x (e₀.linearEquiv x u)
    rw [he₀, he₀, hσfiber]
    exact congrArg (e (A • x)) (complexifiedTangentEvenFormEquiv_sphere_naturality r A x u)
  have hfequiv : f₀.IsEquivariant (sphereExteriorParityEquivariantStructure r 1) τ := by
    intro A x u
    change f₀.linearEquiv (A • x)
      ((sphereExteriorParityEquivariantStructure r 1).linearMap A x u) =
        τ.linearMap A x (f₀.linearEquiv x u)
    rw [hf₀, hf₀, hτfiber]
    exact congrArg (f (A • x)) (complexifiedTangentOddFormEquiv_sphere_naturality r A x u)
  let U₀ := exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
    (sphereComplexifiedRoundMetric r) 0
  let U₁ := exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
    (sphereComplexifiedRoundMetric r) 1
  let d₀ := U₀.trans e₀
  let d₁ := U₁.trans f₀
  have hd₀ : d₀.IsEquivariant (sphereExteriorParityEquivariantStructure r 0) σ := by
    intro A x u
    exact (congrArg (e₀.linearEquiv (A • x))
      (exteriorHodgePhaseBundleIso_sphere_isEquivariant r 0 A x u)).trans
        (hequiv A x (U₀.linearEquiv x u))
  have hd₁ : d₁.IsEquivariant (sphereExteriorParityEquivariantStructure r 1) τ := by
    intro A x u
    exact (congrArg (f₀.linearEquiv (A • x))
      (exteriorHodgePhaseBundleIso_sphere_isEquivariant r 1 A x u)).trans
        (hfequiv A x (U₁.linearEquiv x u))
  -- The actual degree phase gives the exact symbol square, including at the zero section.
  have hsquare (x : OrthogonalSphere r) (v : TangentSpace (𝓡 r) x)
      (u : CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) 0) :
      d₁.linearEquiv x (sphereDeRhamSymbol r 0 ⟨x, v⟩ u) =
        b.val x (g.inner x v) (d₀.linearEquiv x u) := by
    let core := (sphereComplexifiedRoundMetric r).toCore x
    let : NormedAddCommGroup (SphereComplexifiedTangent r x) := core.toNormedAddCommGroup
    let : InnerProductSpace ℂ (SphereComplexifiedTangent r x) :=
      InnerProductSpace.ofCore core.toCore
    change f₀.linearEquiv x (U₁.linearEquiv x (sphereDeRhamSymbol r 0 ⟨x, v⟩ u)) =
      b.val x (g.inner x v) (e₀.linearEquiv x (U₀.linearEquiv x u))
    rw [hf₀, he₀]
    change f x (complexifiedTangentOddFormEquiv g x
        ((exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
          (sphereComplexifiedRoundMetric r) 1).linearEquiv x
            (sphereDeRhamSymbol r 0 ⟨x, v⟩ u))) =
      b.val x (g.inner x v) (e x (complexifiedTangentEvenFormEquiv g x
        ((exteriorHodgePhaseBundleIso (SphereComplexifiedTangent r)
          (sphereComplexifiedRoundMetric r) 0).linearEquiv x u)))
    rw [exteriorHodgePhaseBundleIso_eq, exteriorHodgePhaseBundleIso_eq, hb]
    exact congrArg (f x) (sphereDeRhamSymbol_hodge_components r ⟨x, v⟩ u)
  -- Off zero, this same square identifies the symbol with the actual Koszul equivalence.
  have hi : IsEllipticGlobalSymbol E.Fiber F.Fiber b.val := by
    intro x ξ hξ
    let v := g.sharp x ξ
    have hv : v ≠ 0 := by
      intro hv
      apply hξ
      rw [← (g.sharp_flat_inverse x 0 ξ).2, show g.sharp x ξ = 0 from hv, map_zero]
    have hvector : sphereDeRhamVector r 0 ⟨x, v⟩ ≠ 0 := by
      intro h
      exact hv (((sphereDeRhamVector_properties r).1 0 ⟨x, v⟩).mp h |>.1)
    let L := ((d₀.linearEquiv x).symm.trans
      (sphereDeRhamSymbolEquiv r 0 ⟨x, v⟩ hvector)).trans (d₁.linearEquiv x)
    have hL : (b.val x ξ : E.Fiber x → F.Fiber x) = L := by
      funext w
      have hs := hsquare x v ((d₀.linearEquiv x).symm w)
      rw [LinearEquiv.apply_symm_apply, (g.sharp_flat_inverse x 0 ξ).2] at hs
      exact hs.symm
    rw [hL]
    exact L.bijective
  obtain ⟨R⟩ := nonempty_quantizationPresentation (n := r)
    (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  have hp := hprincipal R
  have hbg : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
      (ξ : CotangentFiber (n := r) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σ τ A b.val x ξ = b.val x ξ := by
    intro A
    apply (QuantizationPresentation.equivariant_regularizedSymbol_class_eq_iff
      IG σ τ hσ hτ R R 1 b b A).mp
    rw [← hp]
    exact P.equivariant_principalSymbol IG σ τ hσ hτ hPg A
  -- The original inverse-musical class is this exact native homogeneous symbol class.
  have hclass := equivariantHomogeneousSymbolKClass_eq_sphereDeRham
    r E F σ τ d₀ d₁ hd₀ hd₁ b hi hbg (fun x v _ u ↦ hsquare x v u)
  change orthogonalSphereAnalyticIndex r (orthogonalSphereMusicalKMap r
    (orthogonalSphereDeRhamClass r)) = orthogonalSphereDeRhamIndex r
  rw [show orthogonalSphereMusicalKMap r (orthogonalSphereDeRhamClass r) =
    equivariantHomogeneousSymbolKClass IG σ τ 1 b hi hbg from hclass]
  -- Real-order evaluation uses an actual equivariant invertible radial PDO and preserves
  -- the original smooth kernel and range quotient; no specified spectral power is needed here.
  have hindex := (equivariantAnalyticIndexMap_eq_smooth_of_homogeneous σ τ hσ hτ
    g.riemannianVolume P hPg R b hp hi hbg).trans
      (P.smoothEquivariantAnalyticIndex_eq_orthogonalSphereDeRhamIndex
        r E F σ τ hσ hτ Φ Ψ hΦaction hΨaction hPg
        ((P.isElliptic_iff_homogeneous R b hp).mpr hi) hP)
  -- The original index uses the Borel presentation of this same measurable structure.
  have hmap : orthogonalSphereAnalyticIndex r = equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel r) (G := Matrix.orthogonalGroup (Fin r) ℝ)
      (n := r) (M := OrthogonalSphere r) := by
    simp only [orthogonalSphereAnalyticIndex, id_eq]
    congr 1
    · exact (BorelSpace.measurable_eq (α := OrthogonalSphere r)).symm
    · exact proof_irrel_heq _ _
  rw [hmap]
  exact hindex

open scoped Matrix.Norms.L2Operator in
/-- The same analytic index is invariant under the genuine base-reflection tangent pullback. -/
theorem orthogonalSphereTangentAnalyticIndex_reflectionPullback (r : ℕ)
    (z : EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
      (TangentBundle (𝓡 r) (OrthogonalSphere r))) :
    orthogonalSphereTangentAnalyticIndex r (orthogonalSphereReflectionPullback r z) =
      orthogonalSphereTangentAnalyticIndex r z := by
  /- Stage 1: the original ambient vertical reflection is an isometry for
  the specified round metric. The chain rule and the ambient metric formula
  show that its derivative lift is carried by flat to the inverse-dual
  cotangent lift of this same sphere diffeomorphism. Consequently the two
  proper pullbacks commute with the inverse-flat transport defining the
  displayed tangent index, in the original equivariant support groups.
  Stage 2: represent a cotangent class by actual equivariant elliptic
  symbols on its finite invariant clopen rank partition. Pulling a symbol
  along that cotangent lift is realized by conjugating its actual operator
  with pullback of smooth sections by the same base diffeomorphism. Native
  coordinate covariance preserves the original principal-symbol class.
  Vertical reflection commutes with O(r), so these section comparisons
  intertwine the same group actions on the actual kernels and smooth range
  quotients. Their full representation-valued indices therefore agree.
  Stage 3: apply the existing K-index evaluation and its finite-piece
  assembly. Reflection may permute pieces; the sum is unchanged. In dimension
  zero it simply permutes the two actual points. This invariance concerns
  the derivative of a base diffeomorphism; fiber reversal theta has a
  different action and is not asserted to preserve the index. -/
  let := orthogonalGroupChartedSpace r
  let := lieGroup_orthogonalGroup r
  let := compactSpace_orthogonalGroup r
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin r) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin r) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin r) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere r) := borel (OrthogonalSphere r)
  let : BorelSpace (OrthogonalSphere r) := ⟨rfl⟩
  let D := orthogonalSphereVerticalDiffeomorph r
  let C : C(CotangentTotalSpace (n := r) (M := OrthogonalSphere r),
      CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
    ⟨cotangentDiffeomorph D, (cotangentDiffeomorph D).continuous⟩
  let pull := equivariantSupportTripleKZeroPullback C
    (orthogonalSphereVerticalCotangent_equivariant r) (cotangentDiffeomorph D).isProperMap
  -- The chosen round musical map commutes with these same two reflection lifts.
  have hmusical : orthogonalSphereMusicalKMap r (orthogonalSphereReflectionPullback r z) =
      pull (orthogonalSphereMusicalKMap r z) := by
    unfold orthogonalSphereMusicalKMap orthogonalSphereReflectionPullback
    change (equivariantSupportTripleKZeroPullback _ _ _)
      ((equivariantSupportTripleKZeroPullback _ _ _) z) =
        (equivariantSupportTripleKZeroPullback _ _ _)
          ((equivariantSupportTripleKZeroPullback _ _ _) z)
    rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply,
      ← equivariantSupportTripleKZeroPullback_comp,
      ← equivariantSupportTripleKZeroPullback_comp]
    congr 1
    congr 1
    apply ContinuousMap.ext
    intro w
    exact (orthogonalSphereRoundMetric_flat_symm_reflection r w).symm
  have hbase (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r) :
      D.symm (A • x) = A • D.symm x := by
    apply Subtype.ext
    rfl
  -- Whole-family naturality permits varying ranks and compares the full defect representations.
  change orthogonalSphereAnalyticIndex r
    (orthogonalSphereMusicalKMap r (orthogonalSphereReflectionPullback r z)) = _
  rw [hmusical]
  exact equivariantAnalyticIndexMap_diffeomorphPullback
    (VG := OrthogonalGroupModel r) (G := Matrix.orthogonalGroup (Fin r) ℝ)
    D.symm hbase (orthogonalSphereVerticalCotangent_equivariant r)
    (orthogonalSphereMusicalKMap r z)

end AtiyahSinger
