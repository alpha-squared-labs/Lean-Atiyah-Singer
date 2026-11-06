/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentCohomologyOrientation
public import AtiyahSinger.Geometry.TangentFundamentalClassSign
public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Topology.CompactManifoldPairing
public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.ThomGysinComparison

/-!
# Fiber integration on the original oriented tangent bundle

Public module ID: M1479.

T03. The original base homological orientation determines the normalized
integral tangent-fiber cohomology orientation. Its actual rationalization
is the orientation in the existing compact-support Thom equivalence.
The ordinary/compact-support comparison on the compact base supplies its
ordinary-domain version. The displayed fiber integral is the inverse of
this particular equivalence, not a freely chosen integration map.

The forward map is pi*(a) cup U, with U on the right, by the existing
compactSupportCohomologyThomMap_compact comparison. The projection formula
keeps this order. The supplied smooth metric installs the native normed
fiber instances required by the existing Thom API. These retain the original
tangent topology and operations; the fiber orientation still comes only
from O. The characteristic-number formula uses this same metric for its
original supported Chern character. No connection or new topology is chosen.

Sources: SG III.13, the second Theorem 13.8 and (13.24), p.255;
Atiyah--Singer III, (2.13) and footnote 4, p.557, explicitly specifying
the right-hand Thom factor. Hatcher section 3.3 and Corollary 4D.9 supply
the underlying cap normalization and Thom isomorphism. The comparison
between the ordered tangent orientation and the original singular models
is a project supplement to that source convention, not an input premise.

The signed top-degree identity compares the interleaved TX orientation
(x1,v1,...,xn,vn) with base-first coordinates (x1,...,xn,v1,...,vn).
Its factor is (-1)^(n*(n-1)/2). Combining this with T02's (-1)^n gives
T03's (-1)^(n*(n+1)/2). A change of the base orientation changes both the
fiber integral and the base fundamental class, leaving the product fixed.
This includes either orientation on a zero-dimensional component. Both the
projection formula and the signed top-degree pairing are proved below using
the same specified orientations and fiber integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory
open scoped Bundle Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The actual ordered tangent Thom equivalence with its ordinary base cohomology domain. -/
def tangentCohomologyThomEquiv (g : SmoothTangentMetric (n := n) (M := M))
    (O : HomologicalOrientation n M) (p : ℕ) :
    singularCohomology ℚ M p ≃ₗ[ℚ] compactSupportCohomology ℚ TM (p + n) := by
  -- The native normed fiber instances retain the original tangent topology and operations.
  letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  exact (compactSupportCohomologyIso ℚ M p).symm.toLinearEquiv.trans
    (compactSupportCohomologyThomEquiv ℚ n T
      (tangentCohomologyOrientation (n := n) g O).rationalization p)

/-- Integration along the original tangent fibers is the inverse of pi*(a) cup U. -/
def tangentCohomologyFiberIntegral (g : SmoothTangentMetric (n := n) (M := M))
    (O : HomologicalOrientation n M) (p : ℕ) :
    compactSupportCohomology ℚ TM (p + n) →ₗ[ℚ] singularCohomology ℚ M p :=
  (tangentCohomologyThomEquiv g O p).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The tangent fiber projection formula preserves the left base factor and the same orientation. -/
theorem tangentCohomologyFiberIntegral_projection
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M)
    (p q : ℕ) (a : singularCohomology ℚ M p)
    (b : compactSupportCohomology ℚ TM (q + n)) :
    tangentCohomologyFiberIntegral g O (p + q)
        ((eqToIso (by rw [Nat.add_assoc]) :
            compactSupportCohomology ℚ TM (p + (q + n)) ≅
              compactSupportCohomology ℚ TM ((p + q) + n)).hom
          (compactSupportCohomologyAction ℚ TM p (q + n)
            (singularCohomologyPullback ℚ
              ⟨Bundle.TotalSpace.proj, FiberBundle.continuous_proj V T⟩ p a) b)) =
      singularCohomologyCup ℚ M p q a (tangentCohomologyFiberIntegral g O q b) := by
  /- Stage 1: use this exact tangent Thom equivalence to express b as
  the Thom image of its displayed inverse image. On the compact base,
  compactSupportCohomologyThomMap_compact identifies that forward map
  with the original zero-section pushforward, pi*(c) cup U, where U is
  the rationalization of the orientation supplied by this same O.
  Stage 2: on the zero-section support representative, reassociate the
  ordinary-relative action and use ordinary pullback multiplicativity.
  The result is pi*(a cup c) cup U. The actual support injection and
  compactSupportCohomologyAction_representative retain that equality
  in total compact-support cohomology. No properness of pi is used.
  Stage 3: cancel the same tangent Thom equivalence against its inverse.
  The only degree transport is p+(q+n)=(p+q)+n. No factors are swapped,
  hence no graded sign is introduced; all rational inputs are allowed,
  without an integral-lift, rank-parity or connectedness assumption. -/
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  let o := (tangentCohomologyOrientation (n := n) g O).rationalization
  let U := compactSupportCohomologyThomClass ℚ n T o
  -- The actual compact-base comparison identifies the forward map on every base class.
  have hforward (k : ℕ) (c : singularCohomology ℚ M k) :
      tangentCohomologyThomEquiv g O k c =
        compactSupportCohomologyAction ℚ TM k n
          (singularCohomologyPullback ℚ (bundleProjection n T) k c) U := by
    change compactSupportCohomologyThomMap ℚ n T o k
      ((compactSupportCohomologyIso ℚ M k).inv c) = _
    rw [compactSupportCohomologyThomMap_compact]
    have hc : compactSupportCohomologyToOrdinary ℚ M k
        ((compactSupportCohomologyIso ℚ M k).inv c) = c :=
      congrArg (fun f ↦ f c) (compactSupportCohomologyIso ℚ M k).inv_hom_id
    rw [hc]
    exact (compactSupportCohomologyAction_representative ℚ TM
      (cohomologyZeroSectionSupport n T) k n
      (singularCohomologyPullback ℚ (bundleProjection n T) k c)
      (cohomologyThomClass ℚ n T o)).symm
  let c := tangentCohomologyFiberIntegral g O q b
  have hb : tangentCohomologyThomEquiv g O q c = b :=
    (tangentCohomologyThomEquiv g O q).apply_symm_apply b
  let i : compactSupportCohomology ℚ TM ((p + q) + n) ≅
      compactSupportCohomology ℚ TM (p + (q + n)) :=
    eqToIso (by rw [Nat.add_assoc])
  -- Reassociate the original action at its unchanged support; no cup factors are permuted.
  have hproduct : i.hom (tangentCohomologyThomEquiv g O (p + q)
      (singularCohomologyCup ℚ M p q a c)) =
        compactSupportCohomologyAction ℚ TM p (q + n)
          (singularCohomologyPullback ℚ (bundleProjection n T) p a) b := by
    rw [← hb, hforward, hforward, singularCohomologyPullback_cup]
    exact compactSupportCohomologyAction_assoc ℚ TM p q n
      (singularCohomologyPullback ℚ (bundleProjection n T) p a)
      (singularCohomologyPullback ℚ (bundleProjection n T) q c) U
  -- Cancel the same forward equivalence against its specified inverse.
  let e := tangentCohomologyThomEquiv g O (p + q)
  apply e.injective
  change e (e.symm (i.inv (compactSupportCohomologyAction ℚ TM p (q + n)
    (singularCohomologyPullback ℚ (bundleProjection n T) p a) b))) =
      e (singularCohomologyCup ℚ M p q a c)
  rw [e.apply_symm_apply, ← hproduct]
  exact congrArg (fun f ↦ f (e (singularCohomologyCup ℚ M p q a c))) i.hom_inv_id

variable [SecondCountableTopology M]

/-- Interleaved tangent evaluation is the signed integral of the same ordered fiber integral. -/
theorem tangent_pairing_eq_base_fiberIntegral
    (g : SmoothTangentMetric (n := n) (M := M)) (O : HomologicalOrientation n M)
    (a : compactSupportCohomology ℚ TM (2 * n)) :
    compactSupportLocallyFinitePairing ℚ TM (2 * n) a
        (rationalTangentFundamentalClass (n := n) (M := M)) =
      (-1 : ℚ) ^ (n * (n - 1) / 2) * compactManifoldCohomologyIntegral O
        (tangentCohomologyFiberIntegral g O n
          ((eqToIso (by congr 1; omega) :
              compactSupportCohomology ℚ TM (2 * n) ≅
                compactSupportCohomology ℚ TM (n + n)).hom a)) := by
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  -- The same compact restrictions carry the grouped/interleaved permutation sign.
  rw [tangent_pairing_eq_grouped_integral g O a]
  congr 1
  let b := (eqToIso (congrArg (compactSupportCohomology ℚ TM)
    (by omega : 2 * n = n + n))).hom a
  -- The ordered Thom inverse preserves the actual grouped top-degree integral.
  rw [← compactSupportCohomologyIntegral_thomIntegral n T O
    (tangentCohomologyOrientation g O) b]
  -- The original tangent inverse uses the same compact-to-ordinary comparison on the base.
  let i := compactSupportCohomologyIso ℚ M n
  let c := compactSupportCohomologyThomIntegral ℚ n T
    (tangentCohomologyOrientation g O).rationalization n b
  change compactSupportCohomologyIntegral O c =
    compactSupportCohomologyIntegral O (i.inv (i.hom c))
  rw [Iso.hom_inv_id_apply]


end AtiyahSinger
