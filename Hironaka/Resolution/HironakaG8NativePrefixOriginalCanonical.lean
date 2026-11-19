import Hironaka.Resolution.HironakaG8NativeSimultaneousCentre
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8NativePrefixOriginalCanonical
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantSeq ResolutionDriver CanonicalCentres
  HironakaStageCenters HironakaG8NativeSimultaneousCentre HironakaActualPowerBoundaryExponents
  HironakaG1OriginalUnequalMarkCanonical HironakaG11PresLineState HironakaG11PresLineStable
  HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong

private theorem eq_local_maximum_of_nonempty_trace {A : Type*} {Λ : Type*} [LinearOrder Λ]
    (f : A → Λ) (P C : Set A) (m : Λ)
    (hUpper : ∀ z ∈ P, f z ≤ m)
    (hTrace : C = {z | z ∈ P ∧ f z = m}) (hC : C.Nonempty) :
    C = maxLocus f P := by
  obtain ⟨x, hx⟩ := hC
  have hx' : x ∈ P ∧ f x = m := (Set.ext_iff.mp hTrace x).mp hx
  rw [hTrace]
  ext z
  exact ⟨fun hz => ⟨hz.1, fun w hw => (hUpper w hw).trans_eq hz.2.symm⟩,
    fun hz => ⟨hz.1, le_antisymm (hUpper z hz.1) (hx'.2.symm.trans_le (hz.2 x hx'.1))⟩⟩

set_option maxHeartbeats 1000000 in
/-- A labelled physical prefix with simultaneous maxima is canonical on
each literal marked window restriction, including windows whose local
center is empty even when the ambient center is nonempty. -/
theorem simultaneous_stages_original_canonical {n k : ℕ} {X Y : CMfd.{0} n}
    {I Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (T : BlowupTower X Y) (hT : NativeSimultaneousStages R U P T) (i : I) :
    IsCanonical (P i) (R.inv (P i)) (restrict (U i) T) := by
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    obtain ⟨hS, hCentre⟩ := hT
    let V := openPreimage S (U i)
    let F := (Subtype.val : V → _) ⁻¹' C
    refine ⟨ih hS, ?_⟩
    change F = ∅ ∨ F = maxLocus (R.inv (P i) (restrict (U i) S))
      (geoTransformAlong (P i) (restrict (U i) S)).cosupp
    rcases hCentre with hEmpty | ⟨m, hm⟩
    · exact Or.inl (by simp [F, hEmpty])
    · by_cases hF : F.Nonempty
      · exact Or.inr (eq_local_maximum_of_nonempty_trace _ _ _ m (hm.upper i) (hm.trace i) hF)
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hF)

set_option maxHeartbeats 1000000 in
/-- The same physical prefix is original-canonical for the actual raw
native records underlying positive whole-power synchronization. The
power changes the mark without changing a single stage or boundary slot. -/
theorem simultaneous_powered_prefix_raw_canonical {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {I : Type}
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain n (P i)) (e : I → ℕ) (he : ∀ i, 1 ≤ e i)
    (T : BlowupTower X Y)
    (hT : NativeSimultaneousStages (canonicalInvariant n) U (fun i => powerMarked (P i) (e i)) T)
    (i : I) :
    IsCanonical (P i) ((invFamily hn n).inv (P i)) (restrict (U i) T) := by
  have hPower := simultaneous_stages_original_canonical (canonicalInvariant n) U
    (fun i => powerMarked (P i) (e i)) T hT i
  have hRaw := (canonicalInvariant_isCanonical_power_iff (P i) (hP i) (e i) (he i)
    (restrict (U i) T)).mpr hPower
  rwa [HironakaSmoothSubmersionOriginalAmbientCanonical.canonicalInvariant_eq_invFamily hn] at hRaw

set_option maxHeartbeats 1200000 in
/-- An independently selected native presentation on a literal window
inherits original canonicality for the same physical prefix. Its full
ordered boundary and initial scaled exponent data determine the
comparison even when the native marks differ. -/
theorem simultaneous_prefix_independent_native_canonical {n : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} {I : Type}
    (U : I → Opens X) (P Q : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain n (P i)) (hQ : ∀ i, IsInvDomain n (Q i))
    (W : Set X) (H : ℕ → ℕ)
    (hNP : ∀ i, NativeHSState (P i) ((Subtype.val : U i → X) ⁻¹' W) H)
    (hNQ : ∀ i, NativeHSState (Q i) ((Subtype.val : U i → X) ⁻¹' W) H)
    (hE : ∀ i, (Q i).E = (P i).E)
    (hExp : ∀ i, ∀ F ∈ (P i).E, ∀ z ∈ (P i).cosupp, z ∈ F →
      (Q i).d * divExpAlong n (P i).N (P i).ideal F z =
      (P i).d * divExpAlong n (Q i).N (Q i).ideal F z)
    (e : I → ℕ) (he : ∀ i, 1 ≤ e i) (T : BlowupTower X Y)
    (hT : NativeSimultaneousStages (canonicalInvariant n) U (fun i => powerMarked (P i) (e i)) T)
    (i : I) :
    IsCanonical (Q i) ((invFamily hn n).inv (Q i)) (restrict (U i) T) := by
  let A := CMfd.of (n := n) (U i)
  have hEqN : (P i).N = (Q i).N := (hNP i).2.2.1.trans (hNQ i).2.2.1.symm
  have hDim := SameCarrierDim.of_N_eq (X := A) (A := P i) (B := Q i) hEqN
  have hL := locWPEquiv_native (hNP i) (hNQ i) (hE i)
  exact (invFamily_isCanonical_iff_of_local hn (P i) (Q i) (hP i) (hQ i) hL hDim
    (hExp i) (restrict (U i) T)).mp
    (simultaneous_powered_prefix_raw_canonical hn U P hP e he T hT i)

end
end Hironaka.HironakaG8NativePrefixOriginalCanonical
