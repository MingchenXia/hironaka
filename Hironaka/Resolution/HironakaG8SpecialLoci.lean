import Hironaka.Resolution.HironakaG11InvBMClass
import Hironaka.Resolution.HironakaG8LocalCompanion
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Analytic.AnalyticSubsetOpens

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Carrier dimensions and the codimension-one part for equivalent marked ideals (G8 lane, run 0080, round 3; (B') port P2)

Blueprint: `hironaka-g8-resume-special-loci.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2, P2 ("the
special loci for equal-dimension carriers", L-spec), design decision D4 (levels, special points, regimes are
cosupport-determined, hence class-determined).

Two marked ideals compared by the (B') induction may have DIFFERENT carriers of the same local dimension
(`HironakaG11InvBMClass.SameCarrierDim`, plan D2).  This module proves that the data of the Step 1 skeleton read from the
cosupport and the carrier dimension agree:

* **`codimOnePartAlong_eq_of_cosupp_eq`**: equal cosupports and carriers of the same local dimension on the cosupport give
  the same codimension-one part (`CodimOneSupportAlong.codimOnePartAlong`, regular points of the cosupport of dimension
  one less than the carrier);
* `SameCarrierDim.symm_of_cosupp_eq`;
* **`sameCarrierDim_geoTransform`** (one admissible blowup; the carriers are transformed by strict transform, which keeps
  the dimension at every point, `BlowupStrictSubmanifold.regularAtDim_geoStrictTransform_of_mem/_of_notMem`) and
  **`sameCarrierDim_geoTransformAlong`** (along every common test tower of Włodarczyk-equivalent well-formed marked ideals);
* `codimOnePartAlong_geoTransformAlong_eq`: the codimension-one parts agree at every stage of a common test tower;
* `sameCarrierDim_pullback_val`: carrier dimensions restrict to open subsets.

Not here: the member loci (`MemberInterLocusAlong.memberInterLocus`) for different carriers, which need the dimension
count `dim (N ∩ H_x) = dim N − codim H_x` for members transverse to the carrier (see the report).  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8SpecialLoci

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism GermIdealOrder
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)
open Hironaka.CodimOneSupportAlong (codimOnePartAlong)
open Hironaka.BlowupStrictSubmanifold (geoStrictTransform regularAtDim_geoStrictTransform_of_mem
  regularAtDim_geoStrictTransform_of_notMem le_of_regularAtDim_subset)
open Hironaka.RegularPointDimension (eq_of_regularAtDim)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)

noncomputable section

variable {n : ℕ}

section Basic

variable {X : CMfd.{u} n} {P Q : MarkedIdeal n X}

/-- **The same codimension-one part**: equal cosupports and carriers of the same local dimension on the cosupport. -/
theorem codimOnePartAlong_eq_of_cosupp_eq (hc : P.cosupp = Q.cosupp) (hdim : SameCarrierDim P Q) :
    codimOnePartAlong P.N P.ideal P.d = codimOnePartAlong Q.N Q.ideal Q.d := by
  have hc' : cosupport n P.N P.ideal P.d = cosupport n Q.N Q.ideal Q.d := hc
  ext x
  constructor
  · rintro ⟨k, hN, hS⟩
    have hx : x ∈ P.cosupp := hS.2.1
    refine ⟨k, (hdim x hx (k + 1)).mp hN, ?_⟩
    rw [← hc']
    exact hS
  · rintro ⟨k, hN, hS⟩
    have hx : x ∈ P.cosupp := by
      have h := hS.2.1
      rw [← hc'] at h
      exact h
    refine ⟨k, (hdim x hx (k + 1)).mpr hN, ?_⟩
    rw [hc']
    exact hS

/-- `SameCarrierDim` is symmetric for marked ideals with the same cosupport. -/
theorem SameCarrierDim.symm_of_cosupp_eq (hc : P.cosupp = Q.cosupp) (hdim : SameCarrierDim P Q) :
    SameCarrierDim Q P := fun x hx j => (hdim x (hc ▸ hx) j).symm

end Basic

/-! ### Carrier dimensions along admissible blowups -/

section Blowup

variable {X Y : CMfd.{u} n}

/-- The dimension of the carrier is unique at a point, so two carriers regular of the same dimension at `z` have the same
regular dimensions there. -/
theorem regularAtDim_iff_of_regularAtDim {N N' : Set Y} {z : Y} {k : ℕ} (hN : RegularAtDim (n := n) N z k)
    (hN' : RegularAtDim (n := n) N' z k) (j : ℕ) :
    RegularAtDim (n := n) N z j ↔ RegularAtDim (n := n) N' z j := by
  constructor
  · intro h
    rw [← eq_of_regularAtDim hN h]
    exact hN'
  · intro h
    rw [← eq_of_regularAtDim hN' h]
    exact hN

/-- **The strict transform of a carrier keeps its dimension at every point over the cosupport** (centre inside the
carrier). -/
theorem regularAtDim_geoStrictTransform_carrier {C N : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (hNc : IsClosed N)
    (hCN : C ⊆ N) {z : Y} (hz : z ∈ geoStrictTransform π C N) {k : ℕ} (hNz : RegularAtDim (n := n) N (π z) k) :
    RegularAtDim (n := n) (geoStrictTransform π C N) z k := by
  by_cases hzC : π z ∈ C
  · obtain ⟨kC, hkC⟩ := hπ.1.2 (π z) hzC
    exact regularAtDim_geoStrictTransform_of_mem hπ (le_of_regularAtDim_subset hkC hNz hCN) hkC hNz hCN hz
  · exact regularAtDim_geoStrictTransform_of_notMem hπ hNc hzC hNz

/-- **Carrier dimensions after one admissible blowup.**  Let `A`, `B` have closed submanifold carriers of the same local
dimension on the cosupport, `C` an admissible centre of `A` inside the carrier of `B`, and the transforms with equal
cosupports.  Then the transforms have carriers of the same local dimension on the cosupport. -/
theorem sameCarrierDim_geoTransform {A B : MarkedIdeal n X} (hNA : IsClosedSubmanifold n A.N)
    (hNB : IsClosedSubmanifold n B.N) (hA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x) (hdim : SameCarrierDim A B)
    {C : Set X} (hCA : A.IsAdmissibleCentre C) (hCB : C ⊆ B.N) {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hc : (A.geoTransform C π).cosupp = (B.geoTransform C π).cosupp) :
    SameCarrierDim (A.geoTransform C π) (B.geoTransform C π) := by
  intro z hz j
  have hzA : π z ∈ A.cosupp :=
    CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hNA.1 hA hCA hπ hz
  obtain ⟨k, hk⟩ := hNA.2 (π z) (A.cosupp_subset_N hzA)
  have hkB : RegularAtDim (n := n) B.N (π z) k := (hdim (π z) hzA k).mp hk
  have hCN : C ⊆ A.N := fun c hc => A.cosupp_subset_N (hCA.2.1 hc)
  have hzN : z ∈ geoStrictTransform π C A.N := (A.geoTransform C π).cosupp_subset_N hz
  have hzN' : z ∈ geoStrictTransform π C B.N := (B.geoTransform C π).cosupp_subset_N (hc ▸ hz)
  exact regularAtDim_iff_of_regularAtDim (regularAtDim_geoStrictTransform_carrier hπ hNA.1 hCN hzN hk)
    (regularAtDim_geoStrictTransform_carrier hπ hNB.1 hCB hzN' hkB) j

/-- **Carrier dimensions along a common test tower** of Włodarczyk-equivalent well-formed marked ideals. -/
theorem sameCarrierDim_geoTransformAlong {A B : MarkedIdeal n X} (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hW : WEquiv A B) (hdim : SameCarrierDim A B) :
    ∀ {Z : CMfd.{u} n} (T : BlowupTower X Z), IsGeoTestTower A T →
      SameCarrierDim (geoTransformAlong A T) (geoTransformAlong B T)
  | _, .refl, _ => hdim
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hTT
    have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA T hTT
    have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hB T hTB
    have hcos : (geoTransformAlong A T).cosupp = (geoTransformAlong B T).cosupp := (hW.2 T).2 hTT
    have hCB : C ⊆ (geoTransformAlong B T).N := fun c hc =>
      (geoTransformAlong B T).cosupp_subset_N (hcos ▸ hC.2.1 hc)
    have hc1 : (geoTransformAlong A (.step T C π hπ)).cosupp = (geoTransformAlong B (.step T C π hπ)).cosupp :=
      (hW.2 (.step T C π hπ)).2 hT
    exact sameCarrierDim_geoTransform hwA.isClosedSubmanifold_N hwB.isClosedSubmanifold_N
      (fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwA.isCoherent hg)
      (sameCarrierDim_geoTransformAlong hA hB hW hdim T hTT) hC hCB hπ hc1

/-- **The codimension-one parts agree at every stage of a common test tower** (P2 at level `0` of the Step 1 skeleton). -/
theorem codimOnePartAlong_geoTransformAlong_eq {A B : MarkedIdeal n X} (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hW : WEquiv A B) (hdim : SameCarrierDim A B) {Z : CMfd.{u} n} (T : BlowupTower X Z) (hT : IsGeoTestTower A T) :
    codimOnePartAlong (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).d =
      codimOnePartAlong (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).d :=
  codimOnePartAlong_eq_of_cosupp_eq ((hW.2 T).2 hT) (sameCarrierDim_geoTransformAlong hA hB hW hdim T hT)

end Blowup

/-! ### Restriction to open subsets -/

section Restrict

variable {X : CMfd.{u} n}

/-- **Carrier dimensions restrict to open subsets.** -/
theorem sameCarrierDim_pullback_val {A B : MarkedIdeal n X} (hA : ∀ x g, A.ideal.mem x g → HolomorphicAt n g x)
    (hdim : SameCarrierDim A B) (U : Opens X) :
    SameCarrierDim (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) A)
      (MarkedIdeal.pullback (Subtype.val : U → X) B) := by
  intro z hz j
  have hz' : (z : X) ∈ A.cosupp := by
    have h := MarkedIdealRestrictOpen.cosupp_pullback_val A hA U
    have h2 : z ∈ (MarkedIdeal.pullback (Subtype.val : U → X) A).cosupp := hz
    rw [h] at h2
    exact h2
  show RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' A.N) z j ↔ RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' B.N) z j
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff]
  exact hdim z hz' j

end Restrict

end

end Hironaka.HironakaG8SpecialLoci
