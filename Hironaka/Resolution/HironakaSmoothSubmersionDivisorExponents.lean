/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.Invariant.MonomialCase
import Hironaka.Invariant.AmbientDivisorExponent
import Hironaka.Invariant.MonomialAmbientDataExact
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionDivisorExponents
open Hironaka.HolomorphicIdealSheaves
open GermIdealOrder DivisorExponent MonomialCase MonomialInvariant
open HironakaSmoothSubmersionOrder HironakaSmoothSubmersionCoefficientIdeals
open MarkedIdeals
open Hironaka
noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- Genuine submersion charts internally give equality of the WHOLE neighbourhood image filter. -/
theorem map_nhds_submersion_eq {f : Y → X} {y : Y}
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y) :
 Filter.map f (𝓝 y) = 𝓝 (f y) := by
 obtain ⟨s, hsbase, hsh, hsection⟩ := exists_holomorphic_localSection hf
 have hsat : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) s (f y) :=
   mem_of_mem_nhds hsh
 have hs : Tendsto s (𝓝 (f y)) (𝓝 y) := by
   simpa only [hsbase] using hsat.continuousAt.tendsto
 apply le_antisymm hf.contMDiffAt.continuousAt.tendsto
 calc
  𝓝 (f y) = Filter.map (f ∘ s) (𝓝 (f y)) := by
    simpa only [Filter.map_id, Function.comp_def] using (Filter.map_congr hsection).symm
  _ = Filter.map f (Filter.map s (𝓝 (f y))) := (Filter.map_map).symm
  _ ≤ Filter.map f (𝓝 y) := Filter.map_mono hs

variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I : GermIdeal n X} (hI : I.IsCoherent)
include hf hI

/-- Every ACTUAL original divisibility predicate along an actual preimage, in every degree. -/
theorem isDivNear_pullback_iff (H : Set X) (e : ℕ) (y : Y) :
 IsDivNear m (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) e y ↔
 IsDivNear n I H e (f y) := by
 show (∀ᶠ z in 𝓝 y, z ∈ f ⁻¹' H →
   z ∈ cosupport m univ (GermIdeal.pullback (m := m) f I) e) ↔
   ∀ᶠ z in 𝓝 (f y), z ∈ H → z ∈ cosupport n univ I e
 rw [cosupport_pullback_eq hf hI e, ← map_nhds_submersion_eq (hf.isSubmersionAt y),
   Filter.eventually_map]
 rfl

/-- The literal original divisibility exponent, including the actual no-first-failure fallback. -/
theorem divExp_pullback_eq (H : Set X) (y : Y) :
 divExp m (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) y = divExp n I H (f y) := by
 classical
 have hP : (fun e => IsDivNear m (GermIdeal.pullback (m := m) f I) (f ⁻¹' H) e y) =
   fun e => IsDivNear n I H e (f y) :=
   funext fun e => propext (isDivNear_pullback_iff hf hI H e y)
 unfold divExp
 show (if h : ∃ e, ¬ (fun e => IsDivNear m (GermIdeal.pullback (m := m) f I)
     (f ⁻¹' H) e y) (e+1) then Nat.find h else 0) =
   (if h : ∃ e, ¬ (fun e => IsDivNear n I H e (f y)) (e+1) then Nat.find h else 0)
 rw [hP]

/-- The ENTIRE original indexed exponent function, including every index beyond the literal length. -/
theorem expData_pullback_eq (E : List (Set X)) (y : Y) :
 expData m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) y =
 expData n I E (f y) := by
 funext i
 unfold expData
 by_cases hi : i < E.length
 · have hi' : i < (E.map (f ⁻¹' ·)).length := by simpa using hi
   rw [dif_pos hi', dif_pos hi]
   have hget : (E.map (f ⁻¹' ·)).get ⟨i, hi'⟩ = f ⁻¹' E.get ⟨i, hi⟩ := by simp
   rw [hget]
   exact divExp_pullback_eq hf hI _ y
 · have hi' : ¬ i < (E.map (f ⁻¹' ·)).length := by simpa using hi
   rw [dif_neg hi', dif_neg hi]

omit hf hI in
private theorem memberIdx_preimage_eq (E : List (Set X)) (g : Y → X) (y : Y) :
 memberIdx (E.map (g ⁻¹' ·)) y = memberIdx E (g y) := by
 ext i
 rw [mem_memberIdx, mem_memberIdx]
 constructor
 · rintro ⟨hi, hx⟩
   refine ⟨by simpa using hi, ?_⟩
   simpa using hx
 · rintro ⟨hi, hx⟩
   refine ⟨by simpa using hi, ?_⟩
   simpa using hx

/-- The ACTUAL source-dimension gamma expressed in ENTIRE original index and exponent data. -/
theorem gamma_pullback_original_dictionary (E : List (Set X)) (d : ℕ) (y : Y) :
 gamma m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
 inv m (memberIdx E (f y)) (expData n I E (f y)) d := by
 unfold gamma
 rw [memberIdx_preimage_eq, expData_pullback_eq hf hI E y]

omit hf in
/-- Equal-dimensional genuine submersions preserve the literal ENTIRE original gamma. -/
theorem gamma_same_dimension_pullback_eq {Z : Type*} [TopologicalSpace Z]
 [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] {g : Z → X}
 (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 (E : List (Set X)) (d : ℕ) (z : Z) :
 gamma n (GermIdeal.pullback (m := n) g I) (E.map (g ⁻¹' ·)) d z = gamma n I E d (g z) := by
 exact gamma_pullback_original_dictionary hg hI E d z

omit hI in
/-- The literal original markedPullback has the ACTUAL complete monomial dictionary in its genuine ambient dimension. -/
theorem gamma_markedPullback_original_dictionary (M : MarkedIdeal n X) (hM : M.ideal.IsCoherent)
 (y : Y) :
 gamma m (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).E
   (markedPullback (m := m) f M).d y =
 inv m (memberIdx M.E (f y)) (expData n M.ideal M.E (f y)) M.d := by
 exact gamma_pullback_original_dictionary hf hM M.E M.d y
end
end Hironaka.HironakaSmoothSubmersionDivisorExponents
