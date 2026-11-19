import Hironaka.Analytic.PshCodimTwoExtension
import Hironaka.Analytic.HolomorphicPullback
import Hironaka.Analytic.PotentialTheory.PlurisubharmonicAE
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

/-!
# Upper semicontinuous regularizations across codimension-two sets are plurisubharmonic

Let `H : O → B` be a biholomorphism of open subsets of `ℂⁿ` carrying `S ∩ O` into a coordinate
plane `{w_i = w_j = 0}`.  If `u` is plurisubharmonic on `O \ S`, then its upper semicontinuous
regularization across `S` is plurisubharmonic on `O`.

Transport `u` to `B`, extend across the plane (`PshCodimTwoExtension`) and pull back to get a
plurisubharmonic `E ∘ H` equal to `u` off `S`.  A function `F` which agrees with `u` off `S`, is
upper semicontinuous, and is bounded by every `c` bounding `u` near a point off `S` equals
`E ∘ H`: `E ∘ H ≤ F` almost everywhere (`S ∩ O` is Lebesgue-null), hence everywhere
(`PlurisubharmonicOn.le_of_ae_le`); and `F ≤ E ∘ H` by upper semicontinuity of `E ∘ H`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.PshCodimTwoLocal

open Hironaka PshCodimTwoExtension

noncomputable section

variable {n : ℕ}

/-- A coordinate plane of codimension two is Lebesgue-null. -/
theorem volume_coordPlane {i j : Fin n} : volume (coordPlane i j) = 0 := by
  set L : ComplexModel n →ₗ[ℝ] ℂ :=
    ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).toLinearMap
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : unitVec i ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, unitVec] at this
  refine measure_mono_null (fun w hw => ?_) (Measure.addHaar_submodule volume _ hne)
  show L w = 0
  exact hw.1

theorem plurisubharmonicOn_of_regularization {O B : Set (ComplexModel n)} (hO : IsOpen O)
    (hB : IsOpen B) {H G : ComplexModel n → ComplexModel n} (hH : DifferentiableOn ℂ H O)
    (hG : DifferentiableOn ℂ G B) (hHO : MapsTo H O B) (hGB : MapsTo G B O)
    (hGH : ∀ w ∈ O, G (H w) = w) (hHG : ∀ b ∈ B, H (G b) = b) {i j : Fin n} (hij : i ≠ j)
    {S : Set (ComplexModel n)} (hSO : IsOpen (O \ S)) (hS : ∀ w ∈ O, w ∈ S → H w ∈ coordPlane i j)
    {u F : ComplexModel n → EReal} (hu : PlurisubharmonicOn u (O \ S))
    (hFeq : EqOn F u (O \ S)) (hFusc : UpperSemicontinuousOn F O)
    (hFle : ∀ w ∈ O, ∀ c : EReal, (∀ᶠ w' in 𝓝 w, w' ∉ S → u w' < c) → F w ≤ c) :
    PlurisubharmonicOn F O := by
  set A := H '' (O ∩ S)
  have hAplane : A ⊆ coordPlane i j := by
    rintro _ ⟨w, ⟨hwO, hwS⟩, rfl⟩; exact hS w hwO hwS
  have hBA_eq : B \ A = B ∩ G ⁻¹' (O \ S) := by
    ext b
    constructor
    · rintro ⟨hb, hbA⟩
      refine ⟨hb, hGB hb, fun hGS => hbA ⟨G b, ⟨hGB hb, hGS⟩, hHG b hb⟩⟩
    · rintro ⟨hb, -, hGS⟩
      refine ⟨hb, ?_⟩
      rintro ⟨w, ⟨hwO, hwS⟩, rfl⟩
      exact hGS (by rw [hGH w hwO]; exact hwS)
  have hBA : IsOpen (B \ A) := by
    rw [hBA_eq]; exact hG.continuousOn.isOpen_inter_preimage hB hSO
  have hg : PlurisubharmonicOn (fun b => u (G b)) (B \ A) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hBA (hG.mono sdiff_subset)
      (fun b hb => by rw [hBA_eq] at hb; exact hb.2) hu
  obtain ⟨hE, hEeq⟩ := plurisubharmonicOn_extension hij hAplane hB hg hBA
  set E := extension A fun b => u (G b)
  have hEH : PlurisubharmonicOn (fun w => E (H w)) O :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hO hH hHO hE
  have hoff : ∀ w ∈ O, w ∉ S → E (H w) = u w := fun w hwO hwS => by
    have hHw : H w ∈ B \ A := by
      rw [hBA_eq]; exact ⟨hHO hwO, by rw [mem_preimage, hGH w hwO]; exact ⟨hwO, hwS⟩⟩
    rw [hEeq hHw]
    show u (G (H w)) = u w
    rw [hGH w hwO]
  -- `S ∩ O` is null
  have hnull : volume (O ∩ S) = 0 := by
    refine measure_mono_null (t := G '' (B ∩ coordPlane i j)) ?_
      (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        ((hG.restrictScalars ℝ).mono inter_subset_left)
        (measure_mono_null inter_subset_right volume_coordPlane))
    rintro w ⟨hwO, hwS⟩
    exact ⟨H w, ⟨hHO hwO, hS w hwO hwS⟩, hGH w hwO⟩
  have hle1 : ∀ w ∈ O, E (H w) ≤ F w := by
    refine hEH.le_of_ae_le hO hFusc volume ?_
    have h0 : ∀ᵐ w ∂volume, w ∉ O ∩ S := measure_eq_zero_iff_ae_notMem.mp hnull
    refine (ae_restrict_iff' hO.measurableSet).mpr ?_
    filter_upwards [h0] with w hw hwO
    have hwS : w ∉ S := fun h => hw ⟨hwO, h⟩
    rw [hoff w hwO hwS, hFeq ⟨hwO, hwS⟩]
  have hle2 : ∀ w ∈ O, F w ≤ E (H w) := by
    intro w hwO
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => hFle w hwO c ?_
    have husc := hEH.discPshOn.upperSemicontinuousOn w hwO c hc
    rw [nhdsWithin_eq_nhds.mpr (hO.mem_nhds hwO)] at husc
    filter_upwards [husc, hO.mem_nhds hwO] with w' hw' hw'O hw'S
    rwa [← hoff w' hw'O hw'S]
  intro w hwO
  refine (hEH w hwO).congr ?_
  filter_upwards [hO.mem_nhds hwO] with w' hw'
  exact le_antisymm (hle1 w' hw') (hle2 w' hw')

end

end Hironaka.PshCodimTwoLocal
