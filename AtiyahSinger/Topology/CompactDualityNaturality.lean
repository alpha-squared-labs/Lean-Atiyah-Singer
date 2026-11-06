/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityBasic
public import AtiyahSinger.Topology.OpenFundamentalClass
public import AtiyahSinger.Topology.RelativeCapNaturality

/-!
# Open-extension naturality of the original compact-support duality map

Public module ID: M1637.

The cap-duality map commutes with an orientation-preserving open embedding:
cohomology extends by excision and ordinary homology pushes forward. Both sides
use the same compact image, prescribed local orientation, and front-face cap.
The comparison needs the constructed map, not its bijectivity.

Source: the cap naturality and fundamental-class arguments in Hatcher,
Algebraic Topology, section 3.3. This identity supplies integration naturality
and the open-embedding case of the PD-defined Gysin comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
  [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]

/-- Cap with the specified fundamental class commutes with orientation-preserving open extension. -/
theorem compactPoincareDuality_openExtension
    (OX : HomologicalOrientation n X) (OY : HomologicalOrientation n Y)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (ho : IsOrientationPreservingOpenEmbedding OX OY f hf)
    (p q : ℕ) (h : p + q = n) (a : compactSupportCohomology ℚ X p) :
    compactPoincareDuality OY p q h (compactSupportCohomologyOpenExtension ℚ f hf p a) =
      singularHomologyMap ℚ f q (compactPoincareDuality OX p q h a) := by
  subst n
  obtain ⟨K, a, rfl⟩ := compactSupportCohomology_exists_representative ℚ X p a
  let L := openEmbeddingCompactImage f K
  let P := openEmbeddingCohomologySupportPullback ℚ f hf K p
  let : IsIso P := isIso_openEmbeddingCohomologySupportPullback ℚ f hf K p
  let b := (asIso P).inv a
  have hb : P b = a := congrArg (fun h ↦ h a) (asIso P).inv_hom_id
  -- The excision inverse retains the same compact-image support.
  rw [compactSupportCohomologyOpenExtension_representative]
  change compactPoincareDuality OY p q rfl (compactSupportCohomologyClass ℚ Y L p b) = _
  rw [compactPoincareDuality_representative, compactPoincareDuality_representative]
  change relativeSingularCapProduct ℚ (L : Set Y)ᶜ p q b
      (rationalCompactRelativeFundamentalClass OY L) =
    singularHomologyMap ℚ f q (relativeSingularCapProduct ℚ (K : Set X)ᶜ p q a
      (rationalCompactRelativeFundamentalClass OX K))
  have hpair : Set.MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ :=
    fun x hx h ↦ hx (hf.injective.mem_set_image.mp h)
  -- Actual cap naturality compares precisely the same rationalized fundamental classes.
  have hcap := relativeSingularCapProduct_naturality ℚ f hpair p q b
    (rationalCompactRelativeFundamentalClass OX K)
  have hfund := rationalCompactRelativeFundamentalClass_openEmbedding OX OY f hf ho K
  change P b = a at hb
  change singularHomologyMap ℚ f q
    (relativeSingularCapProduct ℚ (K : Set X)ᶜ p q (P b)
      (rationalCompactRelativeFundamentalClass OX K)) = _ at hcap
  rw [hb, hfund] at hcap
  exact hcap.symm

end AtiyahSinger
