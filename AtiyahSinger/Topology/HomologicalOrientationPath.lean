/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HomologicalOrientationChartSign
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Agreement of integral homological orientations along paths

Public module ID: M1909.

Two prescribed orientations have a locally constant integral comparison in every
Euclidean chart. Agreement of their original local generators therefore propagates
along any path. This permits orientation comparisons on vector-bundle total spaces
to be checked on the zero section, using the actual fiber contraction afterwards.

The proof uses the original integral chart signs and does not choose a new
orientation or assume orientability of an unrelated base. Signed zero-dimensional
orientations and disconnected manifolds are included. This is the standard local
system argument in Hatcher, Algebraic Topology, section 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Agreement of two specified integral local generators propagates along any path. -/
theorem HomologicalOrientation.localGenerator_eq_of_joined
    (O P : HomologicalOrientation n M) {x y : M} (hxy : Joined x y)
    (hx : O.localGenerator x 1 = P.localGenerator x 1) :
    O.localGenerator y 1 = P.localGenerator y 1 := by
  let c (z : M) : ℤ := (O.localGenerator z).symm (P.localGenerator z 1)
  -- In one fixed chart, the comparison is the product of the two original integral signs.
  have hchart (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z : M) (hz : z ∈ e.source) :
      c z = homologicalOrientationChartSign P e z hz *
        homologicalOrientationChartSign O e z hz := by
    let C := localHomologyChartEquiv e z hz n
    calc
      c z = (O.localGenerator z).symm (C.symm (C (P.localGenerator z 1))) := by
        rw [C.symm_apply_apply]
      _ = _ := by
        rw [show C (P.localGenerator z 1) =
          homologicalOrientationChartSign P e z hz •
            euclideanLocalOrientationCycle n (e z) from
          localHomologyChartEquiv_localGenerator P e z hz]
        rw [map_zsmul, map_zsmul]
        rfl
  have hc : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_exists_open c).mpr
    intro z
    let e := chartAt (EuclideanSpace ℝ (Fin n)) z
    have hz : z ∈ e.source := mem_chart_source _ z
    obtain ⟨U, hU, hzU, hUe, hO⟩ :=
      exists_locally_constant_homologicalOrientationChartSign O e z hz
    obtain ⟨V, hV, hzV, hVe, hP⟩ :=
      exists_locally_constant_homologicalOrientationChartSign P e z hz
    refine ⟨U ∩ V, hU.inter hV, ⟨hzU, hzV⟩, ?_⟩
    intro w hw
    rw [hchart e w (hUe hw.1), hchart e z hz, hO w hw.1, hP w hw.2]
  -- The continuous path has connected parameter interval, so the comparison is constant.
  obtain ⟨γ⟩ := hxy
  have hpath := (hc.comp_continuous γ.continuous).apply_eq_of_preconnectedSpace
    (0 : unitInterval) 1
  have hcx : c x = 1 := by
    change (O.localGenerator x).symm (P.localGenerator x 1) = 1
    rw [← hx, LinearEquiv.symm_apply_apply]
  have hcy : c y = 1 := by
    simpa only [Function.comp_apply, γ.source, γ.target, hcx] using hpath.symm
  apply (O.localGenerator y).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact hcy.symm

end AtiyahSinger
