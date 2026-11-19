import Hironaka.Analytic.ShiftedBergmanBranch

set_option autoImplicit false

/-!
# Shifted Bergman branches at arbitrary exponents

The local branch construction is theta-plurisubharmonic for every natural
exponent already admitted by `LocalBergmanPatch`.  At positive exponent this is
the usual scaled logarithmic branch.  At exponent zero the logarithmic
coefficient vanishes, so the branch is the negative local potential; after
adding that potential, it is a finite constant.  Thus finite atlas data needs
no separate branch-PSH witness.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.ShiftedBergmanBranchAnyExponent


open Hironaka.AnalyticGluingData
open Hironaka.HolomorphicMaps
open Hironaka.LocalPotentialPullback
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite real shift of a local Bergman branch is theta-plurisubharmonic on
its source for every exponent represented by `LocalBergmanPatch`.  The zero
case follows directly from the retained smooth local potential. -/
theorem shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) :
    ThetaPlurisubharmonicOn θ (shiftedBergmanBranch D a) D.source := by
  by_cases hm : 0 < m
  · exact shiftedBergmanBranch_thetaPlurisubharmonicOn D hm a
  · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    intro e z hz hzsource
    let hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (id : M → M) := contMDiff_id
    let F : ComplexModel n → ComplexModel n := coordinateMap (id : M → M) e D.chart
    let W : Set (ComplexModel n) := potentialDomain (id : M → M) e D.chart D.domain
    let ρe : ComplexModel n → ℝ := D.potential ∘ F
    have hW : IsOpen W := potentialDomain_isOpen hid e D.chart D.domain.isOpen
    have hzW : z ∈ W := by
      constructor
      · change z ∈ e.val.target ∧ e.val.symm z ∈ D.chart.val.source
        exact ⟨hz, hzsource.1⟩
      · change D.chart.val (e.val.symm z) ∈ D.domain
        exact hzsource.2
    have hρpull : IsSmoothLocalPotential (SmoothRealForm.pullback hid θ) e W ρe :=
      isSmoothLocalPotential_pullback hid e D.localPotential
    have hρe : IsSmoothLocalPotential θ e W ρe :=
      (SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e W ρe |>.mp hρpull
    refine ⟨W, ρe, hzW, hρe, ?_⟩
    intro y hy
    have hconst : PlurisubharmonicAt (fun _ : ComplexModel n => (a : EReal)) y :=
      plurisubharmonicAt_const _ (EReal.coe_ne_top _) y
    refine hconst.congr ?_
    filter_upwards [hW.mem_nhds hy] with w hw
    have hwsource : e.val.symm w ∈ D.source := by
      constructor
      · exact hw.1.2
      · exact hw.2
    change (a : EReal) = shiftedBergmanBranch D a (e.val.symm w) + (ρe w : EReal)
    have hcoefficient : (((m : ℝ)⁻¹ : ℝ) : EReal) = 0 := by
      have hmreal : (m : ℝ) = 0 := by exact_mod_cast hmzero
      rw [hmreal]
      norm_num
    rw [shiftedBergmanBranch, bergmanBranch, dif_pos hwsource, hcoefficient]
    simp only [zero_mul, zero_sub]
    change (a : EReal) =
      -(D.potential (F w) : EReal) + (a : EReal) + (D.potential (F w) : EReal)
    rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

end
end Hironaka.ShiftedBergmanBranchAnyExponent
