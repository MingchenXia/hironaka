import Hironaka.Analytic.AdmissiblePresentationPullback
import Hironaka.Analytic.NonNefLocusKahlerIndependence
import Hironaka.Analytic.LelongNumberPole

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Pulling a Kähler current up a blowup against a Kähler perturbation

Source: CT22, proof of Lemma 4.2 (`transcendental-nakamaye-copy4-20260911`, `sec:prelim`).

Let `π : Z → Y` be the blowup of a complex manifold along a smooth centre and let
`T = θ + ddᶜ u ≥ ω'` be a Kähler current on `Y`.  The pullback `π^* T` is only semipositive,
which is why `Hironaka.BlowupBigPullback.pullbackCurrent` has to add `ε log (U ∘ π)` — a term
whose pole along the exceptional locus is precisely what puts `Exc π` into `E_nK(π^* α)`.

When the target class is allowed one *Kähler* perturbation `K` upstairs, no such correction is
needed: `π^* T + K ≥ K` is already a Kähler current in `π^* α + {K}`, with the **unchanged**
potential `u ∘ π`.  This is `pullbackAddKahler`.  Its point is that the Lelong numbers of the
resulting current are those of `u ∘ π`.  In particular, if `u` is finite at `π z` — which
Demailly regularization arranges at every point where the original current has zero Lelong
number — then the pulled-back current has zero Lelong number at `z`, *including* when `z` is an
exceptional point, because a `θ`-PSH function with a positive Lelong number at a point has a
pole there (`Hironaka.eq_bot_of_lelongNumber_pos`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupKahlerCurrentPullback

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  AdmissiblePresentationPullback

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- The representative of a Kähler current is theta-PSH for its own background, because the
Kähler lower bound is semipositive. -/
theorem thetaPlurisubharmonic_representative {alpha : RealBottChern n Y}
    (T : KahlerCurrent alpha) :
    ThetaPlurisubharmonic T.representative.val T.potential := by
  have h := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive T.strictlyPsh.1
    T.lowerBound.isSemipositive
  rwa [sub_add_cancel] at h

/-- **The pullback of a Kähler current, corrected by a Kähler form upstairs.**  The potential
is literally `u ∘ π`; in particular its Lelong numbers are those of `u ∘ π`. -/
def pullbackAddKahler {θ : ClosedRealOneOneForm n Y}
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) (K : KahlerBackground n Z) :
    KahlerCurrent (RealBottChern.ofRepresentative
        (ClosedRealOneOneForm.pullback hg.contMDiff θ) +
      RealBottChern.ofRepresentative K.form) where
  representative := ClosedRealOneOneForm.pullback hg.contMDiff T.representative + K.form
  represents := by
    rw [RealBottChern.ofRepresentative_add,
      ofRepresentative_pullback_congr hg.contMDiff T.represents]
  potential := fun z => T.potential (g z)
  lowerBound := K
  strictlyPsh := by
    refine ⟨?_, ?_⟩
    · have hpull : ThetaPlurisubharmonic
          (ClosedRealOneOneForm.pullback hg.contMDiff T.representative).val
          (fun z => T.potential (g z)) :=
        GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff
          (thetaPlurisubharmonic_representative T)
      have hform : ClosedRealOneOneForm.pullback hg.contMDiff T.representative + K.form
          - K.form = ClosedRealOneOneForm.pullback hg.contMDiff T.representative := by
        abel
      rw [hform]
      exact hpull
    · intro x U hU hxU
      have hnot : ¬ U ⊆ g ⁻¹' C := fun hsub => by
        have hx := interior_maximal hsub hU hxU
        rw [ExceptionalFibres.interior_preimage_eq_empty hg] at hx
        exact hx
      obtain ⟨z₀, hz₀U, hz₀C⟩ := not_subset.mp hnot
      have hz₀E : z₀ ∉ exceptionalLocus n g := fun hE =>
        hz₀C (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg hE)
      have himg : g '' U ∈ 𝓝 (g z₀) := by
        rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus
          hg.contMDiff hz₀E]
        exact image_mem_map (hU.mem_nhds hz₀U)
      obtain ⟨y, hyi, hy⟩ := T.strictlyPsh.2 (g z₀) _ isOpen_interior
        (mem_interior_iff_mem_nhds.mpr himg)
      obtain ⟨z, hzU, rfl⟩ := interior_subset hyi
      exact ⟨z, hzU, hy⟩

@[simp] theorem pullbackAddKahler_potential {θ : ClosedRealOneOneForm n Y}
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) (K : KahlerBackground n Z) (z : Z) :
    (pullbackAddKahler T hg K).potential z = T.potential (g z) := rfl

/-- **The pulled-back current has zero Lelong number over every point where the original
potential is finite**, exceptional points included.  No comparison of Lelong numbers under
pullback is needed: the potential upstairs is `u ∘ π`, whose value at `z` is `u (π z) ≠ ⊥`, and
a `θ`-PSH function with a positive Lelong number at a point is `-∞` there. -/
theorem lelongNumber_pullbackAddKahler_eq_zero (hn : 0 < n) {θ : ClosedRealOneOneForm n Y}
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    {C : Set Y} {g : Z → Y} (hg : IsBlowupAlong n C g) (K : KahlerBackground n Z) {z : Z}
    (hz : T.potential (g z) ≠ ⊥) :
    lelongNumber (n := n) (pullbackAddKahler T hg K).potential z = 0 := by
  by_contra hne
  exact hz (eq_bot_of_lelongNumber_pos hn (pullbackAddKahler T hg K).strictlyPsh.1
    (pos_iff_ne_zero.mpr hne))

end

end Hironaka.BlowupKahlerCurrentPullback
