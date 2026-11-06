/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereDeRhamFrames
public import AtiyahSinger.Topology.EquivariantBottConjugation

/-!
# The original de Rham endpoint in a specified full pole chart

Public module ID: M2162.

The inverse image of the two-pole control under either actual full chart is
exactly the origin. This compact inverse image permits pulling back this
particular representative, although the chart is not proper and its image
does not contain the other pole. No pullback homomorphism for arbitrary
compact-support classes along this chart is asserted.

The chart model retains the original bundles, positive symbol, round metric,
and transported derivative actions. The normalized exterior frames supply
the comparison with the original SG Bott boundary on these same carriers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent sphereComplexifiedTangentTopology
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_model isFiniteRank_pullback

/-- Either full pole chart has precisely one zero of the prescribed endpoint vector. -/
theorem sphereDeRhamVector_tangentChart_eq_zero_iff (r : ℕ) (atInfinity : Bool)
    (z : EuclideanSpace ℂ (Fin r)) :
    sphereDeRhamVector r 1 (orthogonalSphereTangentChart r atInfinity z) = 0 ↔ z = 0 := by
  let u : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).re)
  let v : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun j ↦ (z j).im)
  let w := sphereHemisphereKoszulVector r atInfinity 1 u v
  let e := sphereTangentChartComplexification r atInfinity u
  have he : e w = sphereDeRhamVector r 1 (orthogonalSphereTangentChart r atInfinity z) :=
    (sphereDeRhamDifferential_chart r atInfinity 1 z).1
  have hezero : e w = 0 ↔ w = 0 := by
    constructor
    · intro h
      exact ((sphereTangentChartComplexification_properties r atInfinity).1 u).1
        (h.trans (map_zero e).symm)
    · intro h
      rw [h, map_zero]
  rw [← he]
  change e w = 0 ↔ z = 0
  rw [hezero]
  constructor
  · intro h
    ext j
    have hj := congrArg (fun w : EuclideanSpace ℂ (Fin r) ↦ w j) h
    have hj' : (z j).im = 0 ∧ (z j).re = 0 := by
      cases atInfinity <;> simpa [w, sphereHemisphereKoszulVector, u, v,
        Complex.ext_iff] using hj
    exact Complex.ext hj'.2 hj'.1
  · intro h
    subst z
    ext j
    cases atInfinity <;> simp [w, sphereHemisphereKoszulVector, u, v]

/-- Equivariance survives pullback whenever this representative has compact control preimage.
This does not define pullback on arbitrary compact-support classes along the given map. -/
theorem ComplexBundle.CompactSupportTriple.IsEquivariant.pullback_of_isCompact_preimage
    {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
    {E F : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
    (a : CompactSupportTriple E F) (ρE : EquivariantStructure G E)
    (ρF : EquivariantStructure G F) (ha : a.IsEquivariant ρE ρF)
    (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hcompact : IsCompact (f ⁻¹' a.control)) :
    ({ control := f ⁻¹' a.control
       isCompact_control := hcompact
       boundary := a.boundary.pullback f } :
      CompactSupportTriple ((f : X → Y) *ᵖ E) ((f : X → Y) *ᵖ F)).IsEquivariant
      (ρE.pullback f hf) (ρF.pullback f hf) := by
  have hInv (g : G) (x : X) :
      g • x ∈ f ⁻¹' a.control ↔ x ∈ f ⁻¹' a.control := by
    change f (g • x) ∈ a.control ↔ f x ∈ a.control
    rw [hf]
    exact ha.invariant_control g (f x)
  refine ⟨hInv, ?_⟩
  intro g x v
  -- This compact inverse image uses the original relative pullback square on every boundary fiber.
  have htransport (y z : Y) (hyz : y = z) (hy : y ∈ a.controlᶜ)
      (hz : z ∈ a.controlᶜ) (LE : E (f x) →ₗ[ℂ] E z) (LF : F (f x) →ₗ[ℂ] F z)
      (hsquare : ∀ w, a.boundary.linearEquiv ⟨z, hz⟩ (LE w) =
        LF (a.boundary.linearEquiv ⟨f x, x.property⟩ w)) :
      a.boundary.linearEquiv ⟨y, hy⟩
        ((Eq.mpr (congrArg (fun b ↦ E (f x) →ₗ[ℂ] E b) hyz) LE) v) =
        (Eq.mpr (congrArg (fun b ↦ F (f x) →ₗ[ℂ] F b) hyz) LF)
          (a.boundary.linearEquiv ⟨f x, x.property⟩ v) := by
    subst z
    exact hsquare v
  have hsquare := htransport (f (g • x)) (g • f x) (hf g x)
    (fun h ↦ x.property ((hInv g x).mp h))
    (fun h ↦ x.property ((ha.invariant_control g (f x)).mp h))
    (ρE.linearMap g (f x)) (ρF.linearMap g (f x))
    (ha.boundary_intertwines g ⟨f x, x.property⟩)
  have hl := RelativeTriple.pullback_apply a.boundary f
    ⟨g • x.val, fun h ↦ x.property ((hInv g x).mp h)⟩
    ((ρE.pullback f hf).linearMap g x v)
  have hr := RelativeTriple.pullback_apply a.boundary f x v
  exact hl.trans (hsquare.trans
    (congrArg ((ρF.pullback f hf).linearMap g x) hr).symm)
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 900000 in
-- The pulled boundary keeps its two dependent fiber transports along the exact chart square.
/-- The original endpoint pulled into a full pole chart, using its compact inverse-image control. -/
def equivariantSphereDeRhamChartTriple (r : ℕ) (atInfinity : Bool) :
    EquivariantSupportBundleTriple (Matrix.orthogonalGroup (Fin r) ℝ)
      (EuclideanSpace ℂ (Fin r)) := by
  let f := orthogonalSphereTangentChart r atInfinity
  let hf := orthogonalSphereTangentChart_equivariant r atInfinity
  let a := sphereDeRhamTriple r 1
  let E := (sphereDeRhamParityBundle r 0).Fiber
  let F := (sphereDeRhamParityBundle r 1).Fiber
  let ρE := sphereDeRhamParityAction r 0
  let ρF := sphereDeRhamParityAction r 1
  have ha := sphereDeRhamTriple_isEquivariant r 1
  have hcompact : IsCompact (f ⁻¹' a.control) := by
    have heq : f ⁻¹' a.control = ({0} : Set (EuclideanSpace ℂ (Fin r))) := by
      ext z
      exact sphereDeRhamVector_tangentChart_eq_zero_iff r atInfinity z
    rw [heq]
    exact isCompact_singleton
  let b : CompactSupportTriple ((f : _ → _) *ᵖ E) ((f : _ → _) *ᵖ F) :=
    { control := f ⁻¹' a.control
      isCompact_control := hcompact
      boundary := a.boundary.pullback f }
  have hb : b.IsEquivariant (ρE.pullback f hf) (ρF.pullback f hf) :=
    CompactSupportTriple.IsEquivariant.pullback_of_isCompact_preimage a ρE ρF ha f hf hcompact
  exact EquivariantSupportBundleTriple.ofBoundary
    ((sphereDeRhamParityBundle r 0).pullback f) ((sphereDeRhamParityBundle r 1).pullback f)
    b (ρE.pullback f hf) (ρF.pullback f hf) hb

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2200000 in
-- Retain both pullback topologies in the exact original boundary square.
/-- The two original chart models are the SG Bott class and its actual conjugation pullback. -/
theorem equivariantSphereDeRhamChartTriple_class (r : ℕ) (atInfinity : Bool) :
    (equivariantSphereDeRhamChartTriple r atInfinity).kZeroClass =
      if atInfinity then orthogonalComplexificationConjugationPullback r
        (equivariantExteriorBottClass (orthogonalComplexification_unitary r))
      else equivariantExteriorBottClass (orthogonalComplexification_unitary r) := by
  let V := EuclideanSpace ℂ (Fin r)
  let R := EuclideanSpace ℝ (Fin r)
  let G : Type := Matrix.orthogonalGroup (Fin r) ℝ
  let : DistribMulAction G V := orthogonalComplexificationDistribMulAction r
  let P (i : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let Q (i : ZMod 2) (x : OrthogonalSphere r) : Type :=
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i
  let : IsFiniteRank (SphereComplexifiedTangent r) := isFiniteRank_sphereComplexifiedTangent r
  let := modelTopology (P 0) (Bundle.Trivial V (P 0))
  let := modelTopology (P 1) (Bundle.Trivial V (P 1))
  let f := orthogonalSphereTangentChart r atInfinity
  let hf := orthogonalSphereTangentChart_equivariant r atInfinity
  let p := orthogonalSphereTangentProjection r
  let b := p.comp f
  let hb := fun A z ↦ congrArg TotalSpace.proj (hf A z)
  let re (z : V) : R := WithLp.toLp 2 (fun j ↦ (z j).re)
  let L (z : V) := sphereTangentChartUnitaryFrame r atInfinity (re z)
  obtain ⟨d₀, hd₀⟩ := exists_sphereTangentChartExteriorFrame r atInfinity 0
  obtain ⟨d₁, hd₁⟩ := exists_sphereTangentChartExteriorFrame r atInfinity 1
  have hde₀ := sphereTangentChartExteriorFrame_isEquivariant r atInfinity 0 d₀ hd₀
  have hde₁ := sphereTangentChartExteriorFrame_isEquivariant r atInfinity 1 d₁ hd₁
  let c₀ := pullbackCompIso (E := Q 0) p f
  let c₁ := pullbackCompIso (E := Q 1) p f
  let e₀ := d₀.trans c₀.symm
  let e₁ := d₁.trans c₁.symm
  have hc (i : ZMod 2) (z : V) (w : Q i (p (f z))) :
      ((pullbackCompIso (E := Q i) p f).linearEquiv z).symm w = w := by
    apply (pullbackCompIso (E := Q i) p f).linearEquiv z |>.injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
  have he₀ (z : V) (w : P 0) : (e₀.linearEquiv z w).val =
      ExteriorAlgebra.map (L z) w.val := by
    change ((c₀.linearEquiv z).symm (d₀.linearEquiv z w)).val = _
    rw [hc]
    exact hd₀ z w
  have he₁ (z : V) (w : P 1) : (e₁.linearEquiv z w).val =
      ExteriorAlgebra.map (L z) w.val := by
    change ((c₁.linearEquiv z).symm (d₁.linearEquiv z w)).val = _
    rw [hc]
    exact hd₁ z w
  have hactions (i : ZMod 2) (A : G) (z : V) (w : Q i (p (f z))) :
      ((sphereExteriorParityEquivariantStructure r i).pullback b hb).linearMap A z w =
        ((sphereDeRhamParityAction r i).pullback f hf).linearMap A z w := by
    have h := (sphereExteriorParityEquivariantStructure r i).pullbackCompIso_isEquivariant
      p (fun _ _ ↦ rfl) f hf A z w
    change (pullbackCompIso (E := Q i) p f).linearEquiv
      (orthogonalComplexificationRepresentation r A z)
      (((sphereDeRhamParityAction r i).pullback f hf).linearMap A z w) =
        ((sphereExteriorParityEquivariantStructure r i).pullback b hb).linearMap A z
          ((pullbackCompIso (E := Q i) p f).linearEquiv z w) at h
    rw [pullbackCompIso_apply, pullbackCompIso_apply] at h
    exact h.symm
  have heq₀ : e₀.IsEquivariant (exteriorParityEquivariantStructure (G := G) (V := V) 0)
      ((sphereDeRhamParityAction r 0).pullback f hf) := by
    intro A z w
    change (c₀.linearEquiv (orthogonalComplexificationRepresentation r A z)).symm
      (d₀.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (exteriorParityAction A 0 w)) =
        ((sphereDeRhamParityAction r 0).pullback f hf).linearMap A z
          ((c₀.linearEquiv z).symm (d₀.linearEquiv z w))
    rw [hc, hc, ← hactions]
    exact hde₀ A z w
  have heq₁ : e₁.IsEquivariant (exteriorParityEquivariantStructure (G := G) (V := V) 1)
      ((sphereDeRhamParityAction r 1).pullback f hf) := by
    intro A z w
    change (c₁.linearEquiv (orthogonalComplexificationRepresentation r A z)).symm
      (d₁.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (exteriorParityAction A 1 w)) =
        ((sphereDeRhamParityAction r 1).pullback f hf).linearMap A z
          ((c₁.linearEquiv z).symm (d₁.linearEquiv z w))
    rw [hc, hc, ← hactions]
    exact hde₁ A z w
  -- Scale the odd frame by the positive conformal factor and its fixed pole phase.
  let k (z : V) : ℂ :=
    ((2 / (1 + ‖re z‖ ^ 2) : ℝ) : ℂ) * (if atInfinity then Complex.I else -Complex.I)
  have hre : Continuous re := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℝ)).comp
    (continuous_pi fun j ↦ Complex.continuous_re.comp
      (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j))
  have hden (z : V) : (1 + ‖re z‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hscale : Continuous (fun z : V ↦ (2 / (1 + ‖re z‖ ^ 2) : ℝ)) :=
    continuous_const.div (continuous_const.add (hre.norm.pow 2)) hden
  have hk : Continuous k := (Complex.continuous_ofReal.comp hscale).mul continuous_const
  have hkne (z : V) : k z ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt (show (0 : ℝ) < 2 / (1 + ‖re z‖ ^ 2) by positivity))
    · cases atInfinity <;> simp
  have hkinv (A : G) (z : V) : k (orthogonalComplexificationRepresentation r A z) = k z := by
    have hreal : re (orthogonalComplexificationRepresentation r A z) =
        orthogonalEuclideanIsometry r A (re z) := by
      ext j
      change (∑ l, (A.val j l : ℂ) * z l).re = ∑ l, A.val j l * (z l).re
      simp
    dsimp only [k]
    rw [hreal, (orthogonalEuclideanIsometry r A).norm_map]
  let t : TotalSpace Unit (Bundle.Trivial V (P 1)) ≃ₜ V × P 1 :=
    (unitTotalHomeomorph (P 1) (Bundle.Trivial V (P 1))).trans
      (Bundle.Trivial.homeomorphProd V (P 1))
  let s : Hom (Bundle.Trivial V (P 1)) (Bundle.Trivial V (P 1)) :=
    { linearMap z := k z • LinearMap.id
      continuous_total := by
        apply (t.symm.continuous.comp
          (t.continuous.fst.prodMk ((hk.comp t.continuous.fst).smul t.continuous.snd))).congr
        intro z
        rfl }
  let q := s.toIso (fun z ↦ (LinearEquiv.smulOfNeZero ℂ (P 1) (k z) (hkne z)).bijective)
  let odd := q.trans e₁
  have hodd (z : V) (w : P 1) : (odd.linearEquiv z w).val =
      k z • ExteriorAlgebra.map (L z) w.val := by
    change (e₁.linearEquiv z (k z • w)).val = _
    rw [he₁]
    exact map_smul _ _ _
  have hoddeq : odd.IsEquivariant (exteriorParityEquivariantStructure (G := G) (V := V) 1)
      ((sphereDeRhamParityAction r 1).pullback f hf) := by
    intro A z w
    change e₁.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (k (orthogonalComplexificationRepresentation r A z) • exteriorParityAction A 1 w) =
      ((sphereDeRhamParityAction r 1).pullback f hf).linearMap A z
        (e₁.linearEquiv z (k z • w))
    rw [hkinv, map_smul, map_smul]
    have hm := ((sphereDeRhamParityAction r 1).pullback f hf).linearMap A z
      |>.map_smul (k z) (e₁.linearEquiv z w)
    exact (congrArg (fun w ↦ k z • w) (heq₁ A z w)).trans hm.symm
  let H : C(V, V) := if atInfinity then orthogonalComplexificationConjugation r
    else ContinuousMap.id V
  have hHeq : ∀ (A : G) (z : V), H (orthogonalComplexificationRepresentation r A z) = A • H z := by
    cases atInfinity
    · exact fun _ _ ↦ rfl
    · exact orthogonalComplexificationConjugation_equivariant r
  have hHp : IsProperMap H := by
    cases atInfinity
    · exact isProperMap_id
    · exact orthogonalComplexificationConjugation_isProperMap r
  have hH0 : H 0 = 0 := by
    cases atInfinity
    · rfl
    · ext j
      exact star_zero _
  have hHinv : Function.Involutive H := by
    cases atInfinity
    · exact fun _ ↦ rfl
    · intro z
      ext j
      exact star_star (z j)
  -- Pullback of the original constant model has the same vector-preserving trivialization.
  have trivialize (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] :
      letI := modelTopology W (Bundle.Trivial V W)
      ∃ e : Iso ((H : V → V) *ᵖ (Bundle.Trivial V W)) (Bundle.Trivial V W),
        ∀ (z : V) (w : W), e.linearEquiv z w = w := by
    let := modelTopology W (Bundle.Trivial V W)
    let t : TotalSpace Unit (Bundle.Trivial V W) ≃ₜ V × W :=
      (unitTotalHomeomorph W (Bundle.Trivial V W)).trans (Bundle.Trivial.homeomorphProd V W)
    let e : Iso ((H : V → V) *ᵖ (Bundle.Trivial V W)) (Bundle.Trivial V W) :=
      { linearEquiv z := LinearEquiv.refl ℂ W
        continuous_total := by
          have hp := Pullback.continuous_proj Unit (Bundle.Trivial V W) H
          have hv := (t.continuous.comp
            (Pullback.continuous_lift Unit (Bundle.Trivial V W) H)).snd
          exact (t.symm.continuous.comp (hp.prodMk hv)).congr (fun _ ↦ rfl)
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V W) H).continuous_iff]
          exact (t.continuous.fst.prodMk (t.symm.continuous.comp
            ((H.continuous.comp t.continuous.fst).prodMk t.continuous.snd))).congr
              (fun _ ↦ rfl) }
    exact ⟨e, fun _ _ ↦ rfl⟩
  obtain ⟨j₀, hj₀⟩ := trivialize (P 0)
  obtain ⟨j₁, hj₁⟩ := trivialize (P 1)
  let evenH := j₀.trans e₀
  let oddH := j₁.trans odd
  have hja₀ (A : G) (z : V) (w : P 0) :
      ((exteriorParityEquivariantStructure (G := G) (V := V) 0).pullback H hHeq).linearMap
        A z w = exteriorParityAction A 0 w := by
    have h := (exteriorParityEquivariantStructure (G := G) (V := V) 0).pullback_lift_action
      H hHeq A z w
    exact congrArg (fun p : TotalSpace Unit (Bundle.Trivial V (P 0)) ↦ p.snd) h
  have hja₁ (A : G) (z : V) (w : P 1) :
      ((exteriorParityEquivariantStructure (G := G) (V := V) 1).pullback H hHeq).linearMap
        A z w = exteriorParityAction A 1 w := by
    have h := (exteriorParityEquivariantStructure (G := G) (V := V) 1).pullback_lift_action
      H hHeq A z w
    exact congrArg (fun p : TotalSpace Unit (Bundle.Trivial V (P 1)) ↦ p.snd) h
  have hevenH : evenH.IsEquivariant
      ((exteriorParityEquivariantStructure (G := G) (V := V) 0).pullback H hHeq)
      ((sphereDeRhamParityAction r 0).pullback f hf) := by
    intro A z w
    change e₀.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (j₀.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (((exteriorParityEquivariantStructure (G := G) (V := V) 0).pullback H hHeq).linearMap
        A z w)) = _
    have hleft := (hj₀ (orthogonalComplexificationRepresentation r A z)
      (((exteriorParityEquivariantStructure (G := G) (V := V) 0).pullback H hHeq).linearMap
        A z w)).trans (hja₀ A z w)
    have hright := congrArg (e₀.linearEquiv z) (hj₀ z w)
    exact (congrArg (e₀.linearEquiv (orthogonalComplexificationRepresentation r A z)) hleft).trans
      ((heq₀ A z w).trans (congrArg
        (((sphereDeRhamParityAction r 0).pullback f hf).linearMap A z) hright).symm)
  have hoddH : oddH.IsEquivariant
      ((exteriorParityEquivariantStructure (G := G) (V := V) 1).pullback H hHeq)
      ((sphereDeRhamParityAction r 1).pullback f hf) := by
    intro A z w
    change odd.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (j₁.linearEquiv (orthogonalComplexificationRepresentation r A z)
      (((exteriorParityEquivariantStructure (G := G) (V := V) 1).pullback H hHeq).linearMap
        A z w)) = _
    have hleft := (hj₁ (orthogonalComplexificationRepresentation r A z)
      (((exteriorParityEquivariantStructure (G := G) (V := V) 1).pullback H hHeq).linearMap
        A z w)).trans (hja₁ A z w)
    have hright := congrArg (odd.linearEquiv z) (hj₁ z w)
    exact (congrArg (odd.linearEquiv (orthogonalComplexificationRepresentation r A z)) hleft).trans
      ((hoddeq A z w).trans (congrArg
        (((sphereDeRhamParityAction r 1).pullback f hf).linearMap A z) hright).symm)
  -- Both phases are exact scalar identities for the already prescribed positive and SG symbols.
  have hphase (z : V) (w : P 0) :
      (koszulSymbolParity (sphereHemisphereKoszulVector r atInfinity 1 (re z)
        (WithLp.toLp 2 (fun j ↦ (z j).im))) 0 w).val =
        (if atInfinity then Complex.I else -Complex.I) •
          (cliffordSymbolParity (H z) 0 w).val := by
    have hneg (v : V) : cliffordSymbolParity (-v) 0 w = -cliffordSymbolParity v 0 w := by
      apply Subtype.ext
      change cliffordSymbol (-v) w.val = -(cliffordSymbol v w.val)
      simp [cliffordSymbol, exteriorMultiplication, contraction, sub_eq_add_neg, add_comm]
    cases atInfinity
    · have hv : sphereHemisphereKoszulVector r false 1 (re z)
          (WithLp.toLp 2 (fun j ↦ (z j).im)) = -Complex.I • z := by
        ext j
        change (z j).im + (-Complex.I) * (1 : ℂ) * (re z j : ℂ) =
          (-Complex.I) * z j
        apply Complex.ext <;> simp [re, Complex.mul_re, Complex.mul_im]
      rw [hv]
      simp [koszulSymbolParity, H, smul_smul]
    · have hv : sphereHemisphereKoszulVector r true 1 (re z)
          (WithLp.toLp 2 (fun j ↦ (z j).im)) =
          Complex.I • orthogonalComplexificationConjugation r z := by
        ext j
        apply Complex.ext <;> simp [sphereHemisphereKoszulVector, re,
          orthogonalComplexificationConjugation, Complex.mul_re, Complex.mul_im]
      rw [hv]
      simp [koszulSymbolParity, H, smul_smul, hneg]
  let a := equivariantExteriorBottTriple (orthogonalComplexification_unitary r)
  let aH := a.pullback H hHeq hHp
  let c := equivariantSphereDeRhamChartTriple r atInfinity
  have hiso : aH.IsIsomorphic c := by
    refine ⟨{0}, isCompact_singleton, ?_, ?_, ?_, evenH, oddH, hevenH, hoddH, ?_⟩
    · intro A z
      simp only [Set.mem_singleton_iff]
      exact (DistribMulAction.toLinearEquiv ℂ V A).map_eq_zero_iff
    · intro z hz
      exact hHinv.injective ((show H z = 0 from hz).trans hH0.symm)
    · intro z hz
      exact (sphereDeRhamVector_tangentChart_eq_zero_iff r atInfinity z).mp hz
    · intro z w
      rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply]
      apply Subtype.ext
      let zz : (f ⁻¹' (sphereDeRhamTriple r 1).controlᶜ : Set V) :=
        ⟨z.val, fun h ↦ z.property ((sphereDeRhamVector_tangentChart_eq_zero_iff
          r atInfinity z.val).mp h)⟩
      let za : (H ⁻¹' ({0} : Set V)ᶜ : Set V) :=
        ⟨z.val, fun h ↦ z.property (hHinv.injective
          ((show H z.val = 0 from h).trans hH0.symm))⟩
      change (oddH.linearEquiv z ((exteriorBottTriple V).boundary.pullback H |>.linearEquiv
        za w)).val = ((sphereDeRhamTriple r 1).boundary.pullback f |>.linearEquiv zz
          (evenH.linearEquiv z w)).val
      have hleft := RelativeTriple.pullback_apply (exteriorBottTriple V).boundary H za w
      have hright := RelativeTriple.pullback_apply (sphereDeRhamTriple r 1).boundary f zz
        (evenH.linearEquiv z w)
      apply Eq.trans (congrArg (fun v : P 1 ↦ (oddH.linearEquiv z v).val) hleft)
      apply Eq.trans ?_ (congrArg Subtype.val hright).symm
      change (odd.linearEquiv z (j₁.linearEquiv z (cliffordSymbolParity (H z.val) 0 w))).val =
        (sphereDeRhamSymbol r 1 (f z) (e₀.linearEquiv z (j₀.linearEquiv z w))).val
      rw [hj₁, hj₀]
      apply (hodd z.val (cliffordSymbolParity (H z.val) 0 w)).trans
      apply Eq.trans ?_
        (sphereDeRhamSymbol_chart_frame r atInfinity z.val w _ (he₀ z w)).symm
      rw [hphase, map_smul, smul_smul]
  have hclass := (equivariantSupportTripleKZero_generator_relations.1 aH c hiso).symm
  have hpull := equivariantSupportTripleKZeroPullback_apply H hHeq hHp a
  have h := hclass.trans hpull.symm
  cases atInfinity
  · change c.kZeroClass = a.kZeroClass
    change c.kZeroClass = equivariantSupportTripleKZeroPullback (ContinuousMap.id V)
      (fun _ _ ↦ rfl) isProperMap_id a.kZeroClass at h
    rw [equivariantSupportTripleKZeroPullback_id] at h
    exact h
  · exact h

end AtiyahSinger
