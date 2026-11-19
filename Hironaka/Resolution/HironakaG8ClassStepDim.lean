import Hironaka.Resolution.HironakaG8ClassStepMain
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.Resolution.HironakaG11InvBMLowerDomain
import Hironaka.Invariant.IdealOrderArithmetic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The lower ideals of class-equivalent marked ideals have carriers of the same dimension (G8C lane, run 0080, round 2;
(B') plan module 10)

Blueprint: `hironaka-g8-class-step-dim.tex`.  The `SameCarrierDim` part of the class data of the lower ideals
(`HironakaG8ClassStep.LowerPairs`): at a point `x` of the cosupport of the restricted lower ideal of `A`, the strict
transforms of the two hypersurfaces of maximal contact have dimension one less than the carriers of `A_{T₀}`, `B_{T₀}`
(`ContactStageInvDomain.exists_regularAtDim_strictAlong_stage`), and those have the same dimension at `x` (lane G8's
`HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong`, `x` lying in the cosupport of `A_{T₀}`).

* **`lowerPairs_sameCarrierDim`**; **`lowerClassBM_of_exp`** (`R`-free: `LowerClassBM` from its `ExpAgree` part);
* **`classFunctorialMaxOrder_stepOneInvBM_of_exp`**: (B') plan module 10 in lane G11B's shape (I-1361) given only the
  boundary-exponent part of the class data of the lower ideals.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8ClassStepDim

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG8LocalHistory
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The `SameCarrierDim` part of the class data of the lower ideals**: for class-equivalent marked ideals `A ≈ B` of the
domain of maximal order (`LocWPEquiv`, the same divisor, carriers of the same dimension on the cosupport), on every common open
of the masks the two restricted lower ideals have carriers of the same dimension on the cosupport. -/
theorem lowerPairs_sameCarrierDim (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hE : A.E = B.E) (hdim : SameCarrierDim A B) :
    LowerPairs A B fun {_} P Q => SameCarrierDim P Q := by
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB
  have hloc := HironakaG8ClassStepCut.lowerPairs_locWPEquiv hn hA hB hmA hmB h hE T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r'
    hdA hdB
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hyA : y₀ ∈ (geoTransformAlong A T₀).cosupp := (hWA.2 T₀).2 hT₀ ▸ hy₀
  have hyB : y₀ ∈ (geoTransformAlong (barMarked B) T₀).cosupp := by
    rw [(hWB.2 T₀).2 hTJB, ← (hW.2 T₀).2 hTA]
    exact hyA
  obtain ⟨-, hwA⟩ := StepOneLowerDomain.tangentChoice_spec A
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T₀ hT₀ hy₀)
  obtain ⟨-, hwB⟩ := StepOneLowerDomain.tangentChoice_spec B
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T₀ hTJB hyB)
  let UA : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1, hwA.isOpen⟩
  let UB : Opens X := ⟨(tangentChoice B (T₀.proj y₀)).1, hwB.isOpen⟩
  have hOU : ∀ (C : MarkedIdeal n X) (s' : ℕ), O ≤ maskBM C s' T₀ y₀ →
      ∀ z ∈ O, T₀.proj z ∈ (tangentChoice C (T₀.proj y₀)).1 := by
    intro C s' hO z hz
    cases s' with
    | zero => exact (interior_subset (hO hz)).1
    | succ s' =>
      exact (interior_subset (show z ∈ interior (T₀.proj ⁻¹' (tangentChoice C (T₀.proj y₀)).1) from (hO hz).2) :
        z ∈ T₀.proj ⁻¹' (tangentChoice C (T₀.proj y₀)).1)
  intro x hx j
  have hcohA := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ s
  have hcohB := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ s
  have hxB : x ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀)).cosupp :=
    hloc.cosupp_eq_base ▸ hx
  have hxA' : (x : Y₀) ∈ (lowerIdealBM A s T₀ y₀).cosupp := by
    have h1 := MarkedIdealRestrictOpen.cosupp_pullback_val (lowerIdealBM A s T₀ y₀)
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcohA) O
    have h2 : x ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀)).cosupp := hx
    rw [h1] at h2
    exact h2
  have hxNA : (x : Y₀) ∈ strictAlong T₀ (A.N ∩ {z | (tangentChoice A (T₀.proj y₀)).2 z = 0}) := by
    rw [← lowerIdealBM_N A T₀ y₀ s]
    exact (lowerIdealBM A s T₀ y₀).cosupp_subset_N hxA'
  have hxNB : (x : Y₀) ∈ strictAlong T₀ (B.N ∩ {z | (tangentChoice B (T₀.proj y₀)).2 z = 0}) := by
    have h1 := MarkedIdealRestrictOpen.cosupp_pullback_val (lowerIdealBM B s T₀ y₀)
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcohB) O
    have h2 := hxB
    rw [h1] at h2
    rw [← lowerIdealBM_N B T₀ y₀ s]
    exact (lowerIdealBM B s T₀ y₀).cosupp_subset_N h2
  -- `x` lies in the cosupport of the coefficient ideal on maximal contact, hence in that of `A_{T₀}`
  have hcC : (geoTransformAlong (coeffEmptyBM A) T₀).ideal.IsCoherent :=
    HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hxC : (x : Y₀) ∈ (contactCoeffBM A (tangentChoice A (T₀.proj y₀)).2 T₀).cosupp := by
    cases s with
    | zero => exact hxA'
    | succ s =>
      obtain ⟨hxN, hxo⟩ := hxA'
      exact ⟨hxN, fun g hg => hxo g (IdealOrderArithmetic.le_sumIdeal_left'
        (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcC) (x : Y₀) g hg)⟩
  have hxT : (x : Y₀) ∈ (geoTransformAlong A T₀).cosupp :=
    (HironakaG11InvBMLowerDomain.cosupp_contactCoeffBM_iff hA.isWellFormed hA.one_le_d UA hwA T₀ hTA
      (hOU A s hOA x x.2)).mp hxC
  -- the dimensions
  obtain ⟨j₁, hNA, hPA⟩ := ContactStageInvDomain.exists_regularAtDim_strictAlong_stage A hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent hA.one_le_d UA hwA T₀ hTA (hOU A s hOA x x.2) hxNA
  obtain ⟨j₂, hNB, hPB⟩ := ContactStageInvDomain.exists_regularAtDim_strictAlong_stage B hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isCoherent hB.one_le_d UB hwB T₀ hTB (hOU B s hOB x x.2) hxNB
  have hsd := HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hA.isWellFormed hB.isWellFormed hW hdim T₀ hTA
    (x : Y₀) hxT (j₁ + 1)
  have hj : j₂ = j₁ := Nat.succ_injective (RegularPointDimension.eq_of_regularAtDim hNB (hsd.mp hNA))
  rw [hj] at hPB
  show RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM A s T₀ y₀).N) x j ↔
    RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM B s T₀ y₀).N) x j
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff,
    lowerIdealBM_N, lowerIdealBM_N]
  exact HironakaG8SpecialLoci.regularAtDim_iff_of_regularAtDim hPA hPB j

/-- **The class data of the lower ideals, given their boundary exponents** (`R`-free; the form lane G8B's
`HironakaG8BFamilyClassStep.LowerClassStepBM` consumes): for every pair of class-equivalent marked ideals of the domain of
maximal order, `LowerClassBM A B` follows from the `ExpAgree` part alone (the `LocWPEquiv` and `SameCarrierDim` parts are
proved). -/
theorem lowerClassBM_of_exp (hn : 0 < n) {k : ℕ}
    (hExp : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerPairs A B fun {_} P Q => ExpAgree P Q) :
    ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → HironakaG8ClassStep.LowerClassBM A B :=
  fun A B hA hB hmA hmB h hd hE hdim h0 => HironakaG8ClassStep.lowerClassBM_of_parts
    (HironakaG8ClassStepCut.lowerPairs_locWPEquiv hn hA hB hmA hmB h hE)
    (lowerPairs_sameCarrierDim hn hA hB hmA hmB h hE hdim) (hExp A B hA hB hmA hmB h hd hE hdim h0)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **(B') plan module 10, given the boundary exponents of the lower ideals**: lane G11B's statement (I-1361) with the
remaining `R`-free part of the class data of the lower ideals (`hExp`, the boundary exponents) as the only extra hypothesis. -/
theorem classFunctorialMaxOrder_stepOneInvBM_of_exp (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    (hTI : ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R)
    (hExp : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerPairs A B fun {_} P Q => ExpAgree P Q) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) :=
  HironakaG8ClassStepMain.classFunctorialMaxOrder_stepOneInvBM_of_dimExp hn R hR hTI
    (fun _ _ hA hB hmA hmB h _ hE hdim _ => lowerPairs_sameCarrierDim hn hA hB hmA hmB h hE hdim) hExp

end

end Hironaka.HironakaG8ClassStepDim
