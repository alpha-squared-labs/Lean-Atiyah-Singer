/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Geometry.TangentChartOrientation
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.ChartHomologicalOrientation
public import AtiyahSinger.Topology.LocalHomologyChartDifferentiation
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.LocallyFiniteFundamentalClass
public import Mathlib.Tactic.FinCases

/-!
# The canonical integral orientation and fundamental class of the original tangent total space

Public module ID: M1482.

The native tangent charts have coordinates (x,v). The fixed coordinate
equivalence below lists these as (x1,v1,...,xn,vn), the real coordinate order
of x+i v in complex n-space. Recharting uses the existing original tangent
atlas and linearModelChartedSpace, with unchanged points and topology.

The integral homological orientation is uniquely determined by sending its
local generator to the translated positive Euclidean simplex class in every
one of these charts. On overlaps the derivative of the native tangent chart
transition is block triangular with diagonal A,A, hence has positive real
determinant det(A)^2. This constructs the canonical orientation even when the
base is nonorientable. It does not construct or assume a global complex
structure or a connection-dependent horizontal/vertical splitting.

The locally finite fundamental class is the existing actual class of that
same orientation. Its rational version is the original coefficient image.
The integral generator, the ordering, the total topology, and the rational
normalization are therefore specified together.

Sources: Lawson--Michelsohn, Spin Geometry, first Theorem III.13.8, (13.18),
pp.254--255; Atiyah--Singer III, Index Theorem 2.12, p.556; Hatcher, section 3.3, for
homological orientations. Local chart transport and the determinant-square
argument are explicit project supplements to that geometric convention.
The Euclidean target and original homology maps share universe zero; this
technical scope places M in Type, without a mathematical dimension bound.
Second countability reuses the existing tangentBundle_topology certificate.
The proofs use the same derivative square and actual local-chart excision maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Manifold
open scoped ContDiff

/-- The original product coordinates, interleaved in the order of x+i v. -/
def tangentModelCoordinateEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := by
  -- First label each coordinate by its original index and its real/imaginary position.
  let e : (Fin n ⊕ Fin n) ≃ (Fin n × Fin 2) :=
    { toFun := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1))
      invFun := fun p ↦ if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
      left_inv := by
        intro i
        cases i <;> simp
      right_inv := by
        rintro ⟨i, j⟩
        fin_cases j <;> simp }
  -- The row-major finite-product index sends (i,0),(i,1) to 2*i,2*i+1.
  exact (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin n) (κ := Fin n)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (e.trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))))).toContinuousLinearEquiv

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "E₂" => EuclideanSpace ℝ (Fin (2 * n))
local notation "TM" => TangentBundle 𝓘(ℝ, E) M

/-- The exact native tangent charts followed by the fixed interleaved linear coordinates. -/
@[reducible]
def tangentBundleEuclideanChartedSpace : ChartedSpace E₂ TM := by
  letI := tangentBundleFullChartedSpace E M
  exact linearModelChartedSpace (tangentModelCoordinateEquiv n) TM

attribute [local instance] tangentBundleEuclideanChartedSpace

variable [T2Space M] [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The interleaved original tangent charts determine one canonical integral orientation. -/
theorem existsUnique_tangentHomologicalOrientation :
    letI : T2Space TM := (tangentBundle_topology E M).1
    ∃! O : HomologicalOrientation (2 * n) TM,
      ∀ (q z : TM) (hz : z ∈ (chartAt E₂ q).source),
        localHomologyChartEquiv (chartAt E₂ q) z hz (2 * n)
          (O.localGenerator z 1) =
            euclideanLocalOrientationCycle (2 * n) (chartAt E₂ q z) := by
  /- Stage 1: use the native tangent charts followed by
  tangentModelCoordinateEquiv, with coordinates (x1,v1,...,xn,vn).
  Transport the positive translated simplex through localHomologyChartEquiv
  to define the local class z. Its primitivity gives a generator of the
  original integral local homology group at each tangent point.
  Stage 2: exists_pos_tangentChartTransition gives the derivative of each
  native transition with positive determinant. Its two diagonal blocks are
  the same base derivative and its upper-right block is zero; the lower-left
  block does not affect the determinant square. Conjugating both ends by
  the interleaving map retains positivity. The local-homology derivative
  comparison therefore identifies the transported classes in every chart,
  including orientation-reversing base transitions.
  Stage 3: in one fixed chart, all classes are translations of the same
  Euclidean class. This is the chart-transport hypothesis for
  existsUnique_homologicalOrientation_of_chart_transport. Apply that theorem
  with the primitive local classes to obtain the compatible orientation;
  a global fundamental class is not an input.
  Stage 4: normalization identifies any other candidate's local class at
  every point, so the same theorem's uniqueness clause applies. The argument
  includes zero dimension and empty bases and retains the native topology.
  No metric, connection, compactness, or global frame is needed. -/
  classical
  let : T2Space TM := (tangentBundle_topology E M).1
  let := tangentBundleFullChartedSpace E M
  let e := tangentModelCoordinateEquiv n
  let b := (EuclideanSpace.basisFun (Fin (2 * n)) ℝ).toBasis
  let γ := realOrientationCycle b b.orientation
  have hsource (q z : TM) (hz : z ∈ (chartAt E₂ q).source) :
      z ∈ (chartAt (E × E) q).source := by
    exact hz.1
  -- Conjugating both ends by the same interleaving map preserves the positive determinant.
  have hder (p q z : TM) (hp : z ∈ (chartAt E₂ p).source)
      (hq : z ∈ (chartAt E₂ q).source) :
      ∃ L : E₂ ≃L[ℝ] E₂,
        HasFDerivAt (fun v ↦ chartAt E₂ q ((chartAt E₂ p).symm v))
          L.toContinuousLinearMap (chartAt E₂ p z) ∧ 0 < LinearMap.det L.toLinearMap := by
    obtain ⟨L, hL, hpos⟩ := exists_pos_tangentChartTransition p q z
      (hsource p z hp) (hsource q z hq)
    let D : E₂ ≃L[ℝ] E₂ := e.symm.trans (L.trans e)
    have hd : HasFDerivAt (fun v ↦ chartAt E₂ q ((chartAt E₂ p).symm v))
        D.toContinuousLinearMap (chartAt E₂ p z) := by
      have hL' : HasFDerivAt
          (fun v ↦ chartAt (E × E) q ((chartAt (E × E) p).symm v))
          L.toContinuousLinearMap (e.symm (chartAt E₂ p z)) := by
        change HasFDerivAt _ _ (e.symm (e (chartAt (E × E) p z)))
        rw [e.symm_apply_apply]
        exact hL
      let f : E × E → E × E :=
        fun v ↦ chartAt (E × E) q ((chartAt (E × E) p).symm v)
      have hinner : HasFDerivAt (fun v : E₂ ↦ f (e.symm v))
          (L.toContinuousLinearMap.comp e.symm.toContinuousLinearMap) (chartAt E₂ p z) :=
        hL'.comp _ e.symm.toContinuousLinearMap.hasFDerivAt
      have houter : HasFDerivAt (fun v : E₂ ↦ e (f (e.symm v)))
          (e.toContinuousLinearMap.comp
            (L.toContinuousLinearMap.comp e.symm.toContinuousLinearMap))
          (chartAt E₂ p z) := e.toContinuousLinearMap.hasFDerivAt.comp _ hinner
      exact houter
    refine ⟨D, hd, ?_⟩
    have hdet : LinearMap.det D.toLinearMap = LinearMap.det L.toLinearMap :=
      LinearMap.det_conj L.toLinearMap e.toLinearEquiv
    rw [hdet]
    exact hpos
  let z (x : TM) := (localHomologyChartEquiv (chartAt E₂ x) x
    (mem_chart_source E₂ x) (2 * n)).symm
      (euclideanLocalOrientationCycle (2 * n) (chartAt E₂ x x))
  -- The actual positive derivative map fixes the original signed simplex at zero.
  have hnorm (q x : TM) (hx : x ∈ (chartAt E₂ q).source) :
      localHomologyChartEquiv (chartAt E₂ q) x hx (2 * n) (z x) =
        euclideanLocalOrientationCycle (2 * n) (chartAt E₂ q x) := by
    obtain ⟨L, hL, hpos⟩ := hder x q x (mem_chart_source E₂ x) hx
    have h := localHomologyChartEquiv_transition_derivative (chartAt E₂ x)
      (chartAt E₂ q) x (mem_chart_source E₂ x) hx L hL (2 * n)
    rw [relativeSingularHomologyMap_eq_id_of_det_pos ℤ b L hpos (2 * n),
      Category.id_comp] at h
    exact congrArg (fun F ↦ F γ) h
  -- Each transported simplex remains primitive in the original integral local homology group.
  have hgen (x : TM) : Function.Bijective (LinearMap.toSpanSingleton ℤ _ (z x)) := by
    let a := chartAt E₂ x x
    let t : C(E₂, E₂) := ⟨fun v ↦ a + v, continuous_const.add continuous_id⟩
    let s : C(E₂, E₂) := ⟨fun v ↦ v - a, continuous_id.sub continuous_const⟩
    have ht : Set.MapsTo t {v : E₂ | v ≠ 0} ({a}ᶜ : Set E₂) :=
      fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero a).symm))
    have hs : Set.MapsTo s ({a}ᶜ : Set E₂) {v : E₂ | v ≠ 0} :=
      fun _ hv h ↦ hv (sub_eq_zero.mp h)
    let T := relativeSingularHomologyMap ℤ t ht (2 * n)
    let : IsIso T := isIso_relativeSingularHomologyMap_of_inverse ℤ t s ht hs
      (by apply ContinuousMap.ext; intro v; dsimp [t, s]; abel)
      (by apply ContinuousMap.ext; intro v; dsimp [t, s]; abel) (2 * n)
    let C := localHomologyChartEquiv (chartAt E₂ x) x (mem_chart_source E₂ x) (2 * n)
    have h := C.symm.bijective.comp
      (((ConcreteCategory.isIso_iff_bijective T).mp inferInstance).comp
        (realOrientationCycle_is_generator b b.orientation))
    convert h using 1
    funext k
    change (relativeSingularHomology ℤ ({x}ᶜ : Set TM) (2 * n)).isModule.smul
      k (C.symm (T γ)) = C.symm (T (k • γ))
    rw [int_smul_eq_zsmul, map_zsmul, map_zsmul]
  have hlocal (x : TM) : ∃ U : Set TM, IsOpen U ∧ x ∈ U ∧
      ∃ hUe : U ⊆ (chartAt E₂ x).source,
      ∃ c : relativeSingularHomology ℤ {v : E₂ | v ≠ 0} (2 * n),
        ∀ y (hy : y ∈ U),
          relativeSingularHomologyMap ℤ
            (⟨fun v : E₂ ↦ chartAt E₂ x y + v,
              continuous_const.add continuous_id⟩ : C(E₂, E₂))
            (A := {v : E₂ | v ≠ 0}) (B := ({chartAt E₂ x y}ᶜ : Set E₂))
            (fun _ hv h ↦ hv (add_left_cancel
              (h.trans (add_zero (chartAt E₂ x y)).symm))) (2 * n) c =
            localHomologyChartEquiv (chartAt E₂ x) y (hUe hy) (2 * n) (z y) := by
    exact ⟨(chartAt E₂ x).source, (chartAt E₂ x).open_source, mem_chart_source E₂ x,
      Set.Subset.rfl, γ, fun y hy ↦ (hnorm x y hy).symm⟩
  -- The common chart classes construct local compatibility; normalization then gives uniqueness.
  obtain ⟨O, hO, hUnique⟩ := existsUnique_homologicalOrientation_of_chart_transport z hgen hlocal
  refine ⟨O, ?_, ?_⟩
  · intro q x hx
    rw [hO]
    exact hnorm q x hx
  · intro O' hO'
    apply hUnique
    intro x
    apply (localHomologyChartEquiv (chartAt E₂ x) x (mem_chart_source E₂ x) (2 * n)).injective
    exact (hO' x x (mem_chart_source E₂ x)).trans
      (hnorm x x (mem_chart_source E₂ x)).symm

/-- The canonical integral orientation fixed by every interleaved native tangent chart. -/
def tangentHomologicalOrientation : HomologicalOrientation (2 * n) TM :=
  (existsUnique_tangentHomologicalOrientation (n := n) (M := M)).exists.choose

/-- The selected orientation has the exact positive affine-simplex normalization in each chart. -/
theorem tangentHomologicalOrientation_chart (q z : TM)
    (hz : z ∈ (chartAt E₂ q).source) :
    letI : T2Space TM := (tangentBundle_topology E M).1
    localHomologyChartEquiv (chartAt E₂ q) z hz (2 * n)
      ((tangentHomologicalOrientation (n := n) (M := M)).localGenerator z 1) =
        euclideanLocalOrientationCycle (2 * n) (chartAt E₂ q z) := by
  /- Take the chart normalization from the same unique-existence witness
  used to define tangentHomologicalOrientation. The chart, source point,
  relative inclusion maps, and positive translated simplex are unchanged. -/
  exact (existsUnique_tangentHomologicalOrientation (n := n) (M := M)).exists.choose_spec q z hz

/-- The original integral locally finite fundamental class for the canonical tangent orientation. -/
def tangentFundamentalClass : locallyFiniteSingularHomology ℤ TM (2 * n) := by
  letI : T2Space TM := (tangentBundle_topology E M).1
  letI : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  exact locallyFiniteFundamentalClass (tangentHomologicalOrientation (n := n) (M := M))

/-- The canonical rational tangent fundamental class is the actual image of the integral class. -/
def rationalTangentFundamentalClass : locallyFiniteSingularHomology ℚ TM (2 * n) :=
  locallyFiniteSingularHomologyRationalization TM (2 * n)
    (tangentFundamentalClass (n := n) (M := M))

end AtiyahSinger
