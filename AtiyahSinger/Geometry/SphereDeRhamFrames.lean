/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereDeRhamCoordinates
public import AtiyahSinger.Topology.EquivariantPullbackTransport
public import AtiyahSinger.Topology.ExteriorFamilyContinuity

/-!
# Unitary exterior frames in the actual sphere pole coordinates

Public module ID: M1427.

The derivative of the prescribed stereographic chart is conformal. Its positive
normalization gives a genuine unitary frame for the prescribed round metric.
Taking exterior powers gives actual parity bundle frames. In these frames,
the compressed de Rham symbol is the Euclidean Koszul symbol multiplied by
the displayed positive scalar on the odd target. That factor remains explicit
for boundary-map comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] sphereComplexifiedTangentTopology
  continuousSMul_orthogonalSphere
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_model isFiniteRank_pullback

/-- The unitary normalization of the actual complexified inverse-chart derivative. -/
def sphereTangentChartUnitaryFrame (r : ℕ) (atInfinity : Bool)
    (u : EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℂ (Fin r) →ₗ[ℂ]
      SphereComplexifiedTangent r ((orthogonalSphereNormalizedChart r atInfinity).symm u) :=
  (((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ) • sphereTangentChartComplexification r atInfinity u

/-- The prescribed normalized chart frame preserves the round Hermitian form. -/
theorem sphereTangentChartUnitaryFrame_inner (r : ℕ) (atInfinity : Bool)
    (u : EuclideanSpace ℝ (Fin r)) (z w : EuclideanSpace ℂ (Fin r)) :
    ((sphereComplexifiedRoundMetric r).toCore
      ((orthogonalSphereNormalizedChart r atInfinity).symm u)).inner
        (sphereTangentChartUnitaryFrame r atInfinity u z)
        (sphereTangentChartUnitaryFrame r atInfinity u w) = inner ℂ z w := by
  let core := (sphereComplexifiedRoundMetric r).toCore
    ((orthogonalSphereNormalizedChart r atInfinity).symm u)
  let : NormedAddCommGroup (SphereComplexifiedTangent r
      ((orthogonalSphereNormalizedChart r atInfinity).symm u)) := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ (SphereComplexifiedTangent r
      ((orthogonalSphereNormalizedChart r atInfinity).symm u)) :=
    InnerProductSpace.ofCore core.toCore
  change inner ℂ ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ) •
    sphereTangentChartComplexification r atInfinity u z)
    ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ) •
      sphereTangentChartComplexification r atInfinity u w) = _
  rw [inner_smul_left, inner_smul_right]
  change starRingEnd ℂ ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) *
    (((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) *
      ((sphereComplexifiedRoundMetric r).toCore
        ((orthogonalSphereNormalizedChart r atInfinity).symm u)).inner
        (sphereTangentChartComplexification r atInfinity u z)
        (sphereTangentChartComplexification r atInfinity u w)) = _
  rw [(sphereTangentChartComplexification_properties r atInfinity).2.2.1]
  rw [show starRingEnd ℂ ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) =
    ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) from Complex.conj_ofReal _]
  have h : (1 + ‖u‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hc : (((1 + ‖u‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h
  push_cast
  push_cast at hc
  field_simp [hc]
  ring

set_option maxHeartbeats 700000 in
-- The parity frame carries both the varying pullback topology and the fixed exterior topology.
/-- Exterior powers of the normalized derivative give actual continuous parity frames. -/
theorem exists_sphereTangentChartExteriorFrame (r : ℕ) (atInfinity : Bool) (i : ZMod 2) :
    let V := EuclideanSpace ℂ (Fin r)
    let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
    let f : C(V, OrthogonalSphere r) :=
      ⟨fun z ↦ (orthogonalSphereTangentChart r atInfinity z).proj,
        (orthogonalSphereTangentProjection r).continuous.comp
          (orthogonalSphereTangentChart r atInfinity).continuous⟩
    letI := modelTopology P (Bundle.Trivial V P)
    ∃ d : Iso (Bundle.Trivial V P)
      ((f : V → OrthogonalSphere r) *ᵖ
        (fun x ↦ CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i)),
      ∀ (z : V) (w : P), (d.linearEquiv z w).val =
        ExteriorAlgebra.map (sphereTangentChartUnitaryFrame r atInfinity
          (WithLp.toLp 2 (fun j ↦ (z j).re))) w.val := by
  classical
  dsimp only
  let V := EuclideanSpace ℂ (Fin r)
  let R := EuclideanSpace ℝ (Fin r)
  let : IsFiniteRank (SphereComplexifiedTangent r) := isFiniteRank_sphereComplexifiedTangent r
  let re (z : V) : R := WithLp.toLp 2 (fun j ↦ (z j).re)
  let f : C(V, OrthogonalSphere r) :=
    ⟨fun z ↦ (orthogonalSphereTangentChart r atInfinity z).proj,
      (orthogonalSphereTangentProjection r).continuous.comp
        (orthogonalSphereTangentChart r atInfinity).continuous⟩
  let e (z : V) := sphereTangentChartUnitaryFrame r atInfinity (re z)
  have he (z : V) : Function.Bijective (e z) := by
    have hc : ((((1 + ‖re z‖ ^ 2) / 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show (0 : ℝ) < (1 + ‖re z‖ ^ 2) / 2 by positivity))
    exact (show Function.Bijective (fun w ↦
      ((((1 + ‖re z‖ ^ 2) / 2 : ℝ) : ℂ)) • w) from
      (LinearEquiv.smulOfNeZero ℂ _ _ hc).bijective).comp
        ((sphereTangentChartComplexification_properties r atInfinity).1 (re z))
  have hre : Continuous re := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun j ↦ Complex.continuous_re.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j))
  have hc : Continuous (fun z : V ↦ ((((1 + ‖re z‖ ^ 2) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (hre.norm.pow 2)).div_const 2)
  have htotal : Continuous (fun p : V × V ↦
      (⟨f p.1, e p.1 p.2⟩ : TotalSpace Unit (SphereComplexifiedTangent r))) := by
    have h := (sphereTangentChartComplexification_properties r atInfinity).2.2.2.comp
      ((hre.comp continuous_fst).prodMk ((hc.comp continuous_fst).smul continuous_snd))
    apply h.congr
    intro p
    apply congrArg (TotalSpace.mk (f p.1))
    change sphereTangentChartComplexification r atInfinity (re p.1)
      (((((1 + ‖re p.1‖ ^ 2) / 2 : ℝ) : ℂ)) • p.2) =
      (((((1 + ‖re p.1‖ ^ 2) / 2 : ℝ) : ℂ)) •
        sphereTangentChartComplexification r atInfinity (re p.1) p.2)
    exact map_smul _ _ _
  exact exists_exteriorParity_family_iso f e he htotal i

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Contraction naturality is checked on exterior generators for the actual varying round metric.
/-- The positive round-metric symbol is the Euclidean Koszul symbol in the normalized frame.
The positive scalar on the odd target is explicit; the different raw metrics are not equated. -/
theorem sphereDeRhamSymbol_chart_frame (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r))
    (w : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin r))) 0)
    (a : (sphereDeRhamParityBundle r 0).Fiber (orthogonalSphereTangentChart r atInfinity z))
    (ha : a.val = ExteriorAlgebra.map (sphereTangentChartUnitaryFrame r atInfinity
      (WithLp.toLp 2 (fun j ↦ (z j).re))) w.val) :
    (sphereDeRhamSymbol r 1 (orthogonalSphereTangentChart r atInfinity z) a).val =
      ((2 / (1 + ‖(WithLp.toLp 2 (fun j ↦ (z j).re) :
        EuclideanSpace ℝ (Fin r))‖ ^ 2) : ℝ) : ℂ) •
        ExteriorAlgebra.map (sphereTangentChartUnitaryFrame r atInfinity
          (WithLp.toLp 2 (fun j ↦ (z j).re)))
          (koszulSymbolParity (sphereHemisphereKoszulVector r atInfinity 1
            (WithLp.toLp 2 (fun j ↦ (z j).re))
            (WithLp.toLp 2 (fun j ↦ (z j).im))) 0 w).val := by
  let V := EuclideanSpace ℂ (Fin r)
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).im)
  let x := (orthogonalSphereTangentChart r atInfinity z).proj
  let W := SphereComplexifiedTangent r x
  let core := (sphereComplexifiedRoundMetric r).toCore x
  let : NormedAddCommGroup W := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ W := InnerProductSpace.ofCore core.toCore
  let L : V →ₗ[ℂ] W := sphereTangentChartUnitaryFrame r atInfinity u
  let E : V →ₗ[ℂ] W := sphereTangentChartComplexification r atInfinity u
  let F := ExteriorAlgebra.map L
  let d : ℝ := 2 / (1 + ‖u‖ ^ 2)
  let b : V := sphereHemisphereKoszulVector r atInfinity 1 u v
  let av : ExteriorAlgebra ℂ W := a.val
  let y : W := sphereDeRhamVector r 1 (orthogonalSphereTangentChart r atInfinity z)
  have hav : av = F w.val := ha
  have hden : (1 + ‖u‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hscale (q : V) : E q = (d : ℂ) • L q := by
    change E q = (d : ℂ) • (((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) • E q)
    rw [smul_smul]
    have hc : (d : ℂ) * ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ)) = 1 := by
      dsimp only [d]
      rw [← Complex.ofReal_mul]
      norm_cast
      field_simp
    rw [hc, one_smul]
  have hvector : sphereDeRhamVector r 1 (orthogonalSphereTangentChart r atInfinity z) =
      (d : ℂ) • L b :=
    (sphereDeRhamDifferential_chart r atInfinity 1 z).1.symm.trans (hscale b)
  have hinner (p q : V) : inner ℂ (L p) (L q) = inner ℂ p q :=
    sphereTangentChartUnitaryFrame_inner r atInfinity u p q
  -- The pulled metric dual is d times the original Euclidean dual, on this same frame.
  let f : V →ₗ[ℂ] ℂ := innerₛₗ ℂ b
  let g : W →ₗ[ℂ] ℂ := innerₛₗ ℂ ((d : ℂ) • L b)
  have hg (q : V) : g (L q) = ((d : ℂ) • f) q := by
    change inner ℂ ((d : ℂ) • L b) (L q) = (d : ℂ) * inner ℂ b q
    rw [inner_smul_left, hinner]
    rw [Complex.conj_ofReal]
  have hnatural (c : ExteriorAlgebra ℂ V) :
      CliffordAlgebra.contractLeft g (F c) =
        F (CliffordAlgebra.contractLeft ((d : ℂ) • f) c) := by
    generalize (d : ℂ) • f = f' at hg ⊢
    have hF (q : V) : F (ExteriorAlgebra.ι ℂ q) = ExteriorAlgebra.ι ℂ (L q) :=
      ExteriorAlgebra.map_apply_ι L q
    induction c using CliffordAlgebra.left_induction with
    | algebraMap c => simp
    | add c e hc he => simp only [map_add, hc, he]
    | ι_mul c q hc =>
      simp only [map_mul, hF,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, hg, hc]
  -- Combine exterior multiplication and contraction, retaining the real positive factor.
  change (koszulSymbolParity
    (sphereDeRhamVector r 1 (orthogonalSphereTangentChart r atInfinity z)) 0 a).val = _
  rw [(koszulSymbolParity_formula (V := W)).1,
    (koszulSymbolParity_formula (V := V)).1]
  change ExteriorAlgebra.ι ℂ y * av +
    CliffordAlgebra.contractLeft (innerₛₗ ℂ y) av =
        (d : ℂ) • F (ExteriorAlgebra.ι ℂ b * w.val +
          CliffordAlgebra.contractLeft f w.val)
  change y = (d : ℂ) • L b at hvector
  rw [hvector, hav, hnatural]
  simp only [F, map_smul, LinearMap.smul_apply, smul_mul_assoc, map_add, map_mul,
    ExteriorAlgebra.map_apply_ι, smul_add]

set_option maxHeartbeats 900000 in
-- The equality keeps both moving tangent fibers through their actual Re/Im total spaces.
/-- The normalized frames intertwine the prescribed orthogonal actions on both fibers. -/
theorem sphereTangentChartUnitaryFrame_equivariant (r : ℕ) (atInfinity : Bool)
    (A : Matrix.orthogonalGroup (Fin r) ℝ)
    (u : EuclideanSpace ℝ (Fin r)) (z : EuclideanSpace ℂ (Fin r)) :
    (⟨(orthogonalSphereNormalizedChart r atInfinity).symm
        (orthogonalEuclideanIsometry r A u),
      sphereTangentChartUnitaryFrame r atInfinity (orthogonalEuclideanIsometry r A u)
        (orthogonalComplexificationRepresentation r A z)⟩ :
          TotalSpace Unit (SphereComplexifiedTangent r)) =
      ⟨A • (orthogonalSphereNormalizedChart r atInfinity).symm u,
        sphereComplexifiedTangentAction r A
          ((orthogonalSphereNormalizedChart r atInfinity).symm u)
          (sphereTangentChartUnitaryFrame r atInfinity u z)⟩ := by
  let R := EuclideanSpace ℝ (Fin r)
  let V := EuclideanSpace ℂ (Fin r)
  let E := fun x : OrthogonalSphere r ↦ TangentSpace (𝓡 r) x
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let U := orthogonalEuclideanIsometry r A
  let e := orthogonalSphereNormalizedChart r atInfinity
  let D (v : R) := mfderiv (𝓡 r) (𝓡 r) e.symm v
  let DA (x : OrthogonalSphere r) :=
    mfderiv (𝓡 r) (𝓡 r) (orthogonalSphereDiffeomorph r A) x
  let re (w : V) : R := WithLp.toLp 2 (fun j ↦ (w j).re)
  let im (w : V) : R := WithLp.toLp 2 (fun j ↦ (w j).im)
  have hre (w : V) : re (orthogonalComplexificationRepresentation r A w) = U (re w) := by
    ext i
    change (∑ j, (A.val i j : ℂ) * w j).re = ∑ j, A.val i j * (w j).re
    simp
  have him (w : V) : im (orthogonalComplexificationRepresentation r A w) = U (im w) := by
    ext i
    change (∑ j, (A.val i j : ℂ) * w j).im = ∑ j, A.val i j * (w j).im
    simp
  -- The established native tangent chart square supplies both real derivative squares.
  have hT (v : R) : (⟨e.symm (U u), D (U u) (U v)⟩ : T) =
      ⟨A • e.symm u, DA (e.symm u) (D u v)⟩ := by
    let w : V := WithLp.toLp 2 (fun j ↦ Complex.mk (u j) (v j))
    have h := orthogonalSphereTangentChart_equivariant r atInfinity A w
    change (⟨e.symm (re (orthogonalComplexificationRepresentation r A w)),
      D (re (orthogonalComplexificationRepresentation r A w))
        (im (orthogonalComplexificationRepresentation r A w))⟩ : T) =
      ⟨A • e.symm u, DA (e.symm u) (D u v)⟩ at h
    rw [hre, him] at h
    exact h
  have hpair {x y : OrthogonalSphere r} {u₁ u₂ : E x} {v₁ v₂ : E y}
      (h₁ : (⟨x, u₁⟩ : T) = ⟨y, v₁⟩) (h₂ : (⟨x, u₂⟩ : T) = ⟨y, v₂⟩) :
      (⟨x, (u₁, u₂)⟩ : TotalSpace (R × R) (E ×ᵇ E)) = ⟨y, (v₁, v₂)⟩ := by
    have hxy := congrArg (fun t : T ↦ t.proj) h₁
    dsimp only at hxy
    subst y
    have hu := TotalSpace.mk_injective x h₁
    have hv := TotalSpace.mk_injective x h₂
    cases hu
    cases hv
    rfl
  have hcoords (v : R) (w : V) :
      complexificationReIm (E (e.symm v))
        (sphereTangentChartComplexification r atInfinity v w) =
      (D v (re w), D v (im w)) := by
    rw [(sphereTangentChartComplexification_properties r atInfinity).2.1]
    rw [map_add, (complexificationReIm_properties _).1,
      (complexificationReIm_properties _).1]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      one_smul, zero_smul, Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have haction (x : OrthogonalSphere r) (w : SphereComplexifiedTangent r x) :
      complexificationReIm (E (A • x)) (sphereComplexifiedTangentAction r A x w) =
        (DA x (complexificationReIm (E x) w).1,
          DA x (complexificationReIm (E x) w).2) := by
    induction w using TensorProduct.inductionOn with
    | tmul a v =>
      erw [sphereComplexifiedTangentAction, LinearMap.baseChange_tmul,
        (complexificationReIm_properties (E (A • x))).1,
        (complexificationReIm_properties (E x)).1]
      simp only [ContinuousLinearMap.coe_coe, map_smul]
      rfl
    | add v w hv hw =>
      simp only [map_add, hv, hw, Prod.fst_add, Prod.snd_add]
      rfl
  have hraw : (⟨e.symm (U u), sphereTangentChartComplexification r atInfinity (U u)
        (orthogonalComplexificationRepresentation r A z)⟩ :
          TotalSpace Unit (SphereComplexifiedTangent r)) =
      ⟨A • e.symm u, sphereComplexifiedTangentAction r A (e.symm u)
        (sphereTangentChartComplexification r atInfinity u z)⟩ := by
    apply (complexificationDoubleTotalHomeomorph R E).injective
    change (⟨e.symm (U u), complexificationReIm (E (e.symm (U u)))
      (sphereTangentChartComplexification r atInfinity (U u)
        (orthogonalComplexificationRepresentation r A z))⟩ :
        TotalSpace (R × R) (E ×ᵇ E)) =
      ⟨A • e.symm u, complexificationReIm (E (A • e.symm u))
        (sphereComplexifiedTangentAction r A (e.symm u)
          (sphereTangentChartComplexification r atInfinity u z))⟩
    rw [hcoords, haction, hcoords, hre, him]
    exact hpair (hT (re z)) (hT (im z))
  -- The normalizing factor is the same invariant positive scalar in both native fibers.
  have hs := congrArg (fun p : TotalSpace Unit (SphereComplexifiedTangent r) ↦
    (⟨p.proj, (((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ) • p.snd⟩ :
      TotalSpace Unit (SphereComplexifiedTangent r))) hraw
  dsimp only at hs
  change (⟨e.symm (U u), (((1 + ‖U u‖ ^ 2) / 2 : ℝ) : ℂ) •
    sphereTangentChartComplexification r atInfinity (U u)
      (orthogonalComplexificationRepresentation r A z)⟩ :
      TotalSpace Unit (SphereComplexifiedTangent r)) =
    ⟨A • e.symm u, sphereComplexifiedTangentAction r A (e.symm u)
      ((((1 + ‖u‖ ^ 2) / 2 : ℝ) : ℂ) •
        sphereTangentChartComplexification r atInfinity u z)⟩
  rw [U.norm_map, map_smul]
  exact hs

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- The proof compares exterior maps across one prescribed moving-base equality.
/-- Each exterior frame with the specified formula intertwines the original pulled action. -/
theorem sphereTangentChartExteriorFrame_isEquivariant
    (r : ℕ) (atInfinity : Bool) (i : ZMod 2) :
    let V := EuclideanSpace ℂ (Fin r)
    let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
    let f : C(V, OrthogonalSphere r) :=
      ⟨fun z ↦ (orthogonalSphereTangentChart r atInfinity z).proj,
        (orthogonalSphereTangentProjection r).continuous.comp
          (orthogonalSphereTangentChart r atInfinity).continuous⟩
    let hf := fun A z ↦ congrArg TotalSpace.proj
      (orthogonalSphereTangentChart_equivariant r atInfinity A z)
    letI := modelTopology P (Bundle.Trivial V P)
    ∀ d : Iso (Bundle.Trivial V P)
      ((f : V → OrthogonalSphere r) *ᵖ
        (fun x ↦ CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i)),
      (∀ (z : V) (w : P), (d.linearEquiv z w).val =
        ExteriorAlgebra.map (sphereTangentChartUnitaryFrame r atInfinity
          (WithLp.toLp 2 (fun j ↦ (z j).re))) w.val) →
      d.IsEquivariant
        (exteriorParityEquivariantStructure
          (G := Matrix.orthogonalGroup (Fin r) ℝ) (V := V) i)
        ((sphereExteriorParityEquivariantStructure r i).pullback f hf) := by
  dsimp only
  intro d hd A z w
  let V := EuclideanSpace ℂ (Fin r)
  let R := EuclideanSpace ℝ (Fin r)
  let C := SphereComplexifiedTangent r
  let P : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let := modelTopology P (Bundle.Trivial V P)
  let Q (x : OrthogonalSphere r) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C x)) i
  let f : C(V, OrthogonalSphere r) :=
    ⟨fun z ↦ (orthogonalSphereTangentChart r atInfinity z).proj,
      (orthogonalSphereTangentProjection r).continuous.comp
        (orthogonalSphereTangentChart r atInfinity).continuous⟩
  let hf := fun A z ↦ congrArg TotalSpace.proj
    (orthogonalSphereTangentChart_equivariant r atInfinity A z)
  let re (z : V) : R := WithLp.toLp 2 (fun j ↦ (z j).re)
  let Az : V := orthogonalComplexificationRepresentation r A z
  let L (z : V) := sphereTangentChartUnitaryFrame r atInfinity (re z)
  let aA : V →ₗ[ℂ] V := (orthogonalComplexificationRepresentation r A).toLinearMap
  let S := sphereComplexifiedTangentAction r A (f z)
  have hre : re Az = orthogonalEuclideanIsometry r A (re z) := by
    ext j
    change (∑ k, (A.val j k : ℂ) * z k).re = ∑ k, A.val j k * (z k).re
    simp
  -- The frame square induces the same square on the whole exterior algebra.
  have hExt {x y : OrthogonalSphere r} (hxy : x = y)
      (p : V →ₗ[ℂ] C x) (q : V →ₗ[ℂ] C y)
      (hpq : ∀ v, (⟨x, p v⟩ : TotalSpace Unit C) = ⟨y, q v⟩)
      (v : ExteriorAlgebra ℂ V) :
      (⟨x, ExteriorAlgebra.map p v⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x))) =
        ⟨y, ExteriorAlgebra.map q v⟩ := by
    subst y
    have hp : p = q := by
      ext a
      exact TotalSpace.mk_injective x (hpq a)
    rw [hp]
  have hvectors (v : V) :
      (⟨f Az, (L Az).comp aA v⟩ : TotalSpace Unit C) =
        ⟨A • f z, S.comp (L z) v⟩ := by
    have h := sphereTangentChartUnitaryFrame_equivariant r atInfinity A (re z) v
    change (⟨(orthogonalSphereNormalizedChart r atInfinity).symm (re Az),
      sphereTangentChartUnitaryFrame r atInfinity (re Az)
        (orthogonalComplexificationRepresentation r A v)⟩ : TotalSpace Unit C) = _
    rw [hre]
    exact h
  have hexteriorRaw := hExt (hf A z) ((L Az).comp aA) (S.comp (L z)) hvectors w.val
  have hL := congrArg (fun v : ExteriorAlgebra ℂ (C (f Az)) ↦
    (⟨f Az, v⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x))))
    (AlgHom.congr_fun (ExteriorAlgebra.map_comp_map aA (L Az)) w.val)
  have hR := congrArg (fun v : ExteriorAlgebra ℂ (C (A • f z)) ↦
    (⟨A • f z, v⟩ : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x))))
    (AlgHom.congr_fun (ExteriorAlgebra.map_comp_map (L z) S).symm w.val)
  have hexterior := hL.trans (hexteriorRaw.trans hR)
  -- Lift the pulled action into the original parity total space before comparing vectors.
  let ρ := sphereExteriorParityEquivariantStructure r i
  let lift (p : TotalSpace Unit Q) : TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x)) :=
    ⟨p.proj, p.snd.val⟩
  have hpull := congrArg lift (ρ.pullback_lift_action f hf A z (d.linearEquiv z w))
  change (⟨f Az, ((ρ.pullback f hf).linearMap A z (d.linearEquiv z w)).val⟩ :
    TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x))) =
      ⟨A • f z, (ρ.linearMap A (f z) (d.linearEquiv z w)).val⟩ at hpull
  have hright : (ρ.linearMap A (f z) (d.linearEquiv z w)).val =
      ExteriorAlgebra.map S (ExteriorAlgebra.map (L z) w.val) := by
    rw [sphereExteriorParityEquivariantStructure_apply, hd]
  rw [hright] at hpull
  apply Subtype.ext
  apply TotalSpace.mk_injective (F := Unit) (E := fun x ↦ ExteriorAlgebra ℂ (C x)) (f Az)
  have hleft : (d.linearEquiv Az (exteriorParityAction A i w)).val =
      ExteriorAlgebra.map (L Az) (ExteriorAlgebra.map aA w.val) := hd _ _
  change (⟨f Az, (d.linearEquiv Az (exteriorParityAction A i w)).val⟩ :
    TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (C x))) = _
  rw [hleft]
  exact hexterior.trans hpull.symm

end AtiyahSinger
