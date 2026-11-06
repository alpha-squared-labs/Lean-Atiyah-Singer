/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalQuantization

/-!
# Quantization frames with fixed scalar weights

Public module ID: M0909.

A quantization presentation for two bundles supplies matching presentations in
the reverse direction and on either factor. The chart and both scalar cutoffs
are retained exactly. Only the bundle frames change, using the original
cross-frame support conditions. These implementation constructions synchronize
the frequency weights of the four blocks of a graded tensor operator.

The reverse presentation is not asserted to quantize formal adjoints exactly;
the lower-order difference is handled by the principal-symbol calculus.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]

/-- Reverse the bundle frames while preserving the original input and output cutoffs. -/
def QuantizationPatch.reverseFrames
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F) :
    QuantizationPatch (n := n) (r := q) (q := r) F E where
  chart := A.chart
  chart_mem_atlas := A.chart_mem_atlas
  input := {
    frame := A.output.frame
    frame_mem_atlas := A.output.frame_mem_atlas
    cutoff := A.input.cutoff
    smooth_cutoff := A.input.smooth_cutoff
    compact_support := A.input.compact_support
    support_subset := fun _ hz ↦
      ⟨(A.input.support_subset hz).1, A.input_support_in_output_frame hz⟩ }
  output := {
    frame := A.input.frame
    frame_mem_atlas := A.input.frame_mem_atlas
    cutoff := A.output.cutoff
    smooth_cutoff := A.output.smooth_cutoff
    compact_support := A.output.compact_support
    support_subset := fun _ hz ↦
      ⟨(A.output.support_subset hz).1, A.output_support_in_input_frame hz⟩ }
  input_support_in_output_frame := fun _ hz ↦ (A.input.support_subset hz).2
  output_support_in_input_frame := fun _ hz ↦ (A.output.support_subset hz).2
  output_eq_one := A.output_eq_one

/-- Use the input bundle frame on both sides with the same two scalar cutoffs. -/
def QuantizationPatch.inputEndomorphism
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F) :
    QuantizationPatch (n := n) (r := r) (q := r) E E where
  chart := A.chart
  chart_mem_atlas := A.chart_mem_atlas
  input := A.input
  output := {
    frame := A.input.frame
    frame_mem_atlas := A.input.frame_mem_atlas
    cutoff := A.output.cutoff
    smooth_cutoff := A.output.smooth_cutoff
    compact_support := A.output.compact_support
    support_subset := fun _ hz ↦
      ⟨(A.output.support_subset hz).1, A.output_support_in_input_frame hz⟩ }
  input_support_in_output_frame := fun _ hz ↦ (A.input.support_subset hz).2
  output_support_in_input_frame := A.output_support_in_input_frame
  output_eq_one := A.output_eq_one

/-- Reversing frames preserves the exact manifold partition weight. -/
@[simp]
theorem QuantizationPatch.weight_reverseFrames
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F) (x : M) :
    A.reverseFrames.weight x = A.weight x := rfl

/-- Passing to the input endomorphism preserves the exact manifold partition weight. -/
@[simp]
theorem QuantizationPatch.weight_inputEndomorphism
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F) (x : M) :
    A.inputEndomorphism.weight x = A.weight x := rfl

/-- The reverse bundle direction with the original charts and scalar partition. -/
def QuantizationPresentation.reverseFrames
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    QuantizationPresentation (n := n) (r := q) (q := r) F E where
  size := A.size
  patch i := (A.patch i).reverseFrames
  sum_weight := A.sum_weight

/-- An endomorphism presentation of the input bundle with the original scalar partition.
Apply this construction to `reverseFrames` for the output bundle. -/
def QuantizationPresentation.inputEndomorphism
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) :
    QuantizationPresentation (n := n) (r := r) (q := r) E E where
  size := A.size
  patch i := (A.patch i).inputEndomorphism
  sum_weight := A.sum_weight

end AtiyahSinger
