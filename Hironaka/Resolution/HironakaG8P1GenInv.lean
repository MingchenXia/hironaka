import Hironaka.Resolution.HironakaG8P1Entries
import Hironaka.Resolution.HironakaG8E4cCarrier
import Hironaka.Invariant.GeneralStepValue

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Class functoriality of the general value (G8B lane, run 0080; (B') plan module 11)

Blueprint: `hironaka-g8-p1-geninv.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §1 module 11 and §6c ("Modules 10--13 against
lane G11C's target"); the shape was fixed by lane G11B (inbox I-1350, confirmed in I-1355).  Source: Bierstone--Milman 2008,
Theorem 7.1(4) and §5 Step II (the invariant of the general step is read off the class: the first entry is the order of the
nonmonomial part, then either the monomial invariant or the lower invariant of the companion ideal).

The general value `GeneralValue.genInv M` (TN3's value of the general step, generic in the maximal-order value `M`) is
**class functorial** for the local `s(i,ii)`-equivalence `LocWPEquiv` as soon as `M` is class functorial on the marked ideals
of maximal order: two marked ideals `A ≈ B` of the domain with the same mark, the same divisor, carriers of the same dimension
on the cosupport and agreeing boundary exponents have the same canonical segments and, along them, the same values on the
cosupport.

* `ClassFunctorialMaxOrderFor Eqv k M`: the fields of `HironakaG11InvBMClass.ClassFunctorialFor` for marked ideals of maximal
  order (the hypothesis lane G11B's module 10 proves for `stepOneInvBM`); `ClassFunctorialFor.toMaxOrder`,
  `ClassFunctorialMaxOrderFor.mono`, `ClassFunctorialMaxOrderFor.maxOrderClassValue` (lane G8C's `MaxOrderClassValue`);
* `locWPEquiv_genInv_eq_of_nmOrd_eq_zero` (E3 for values in any universe): at the points of order `0` the general values agree;
* `CompanionValueAgree k M`: the conclusion of E4 (the companion values at a common split agree, given lower data for both);
* **`genInv_eq_of_isCanonical`**: along a tower canonical for both, the values agree on the cosupport (E1 the first entry,
  E3 at order `0`, E2 the common split and E4 at positive order);
* **`isCanonical_genInv_iff`**: the canonical segments correspond (induction along the tower: the maximum loci agree);
* **`classFunctorialFor_genInv_of_companion`**: class functoriality given E4;
* `companionValueAgree_of_maxOrderClassValue` (E4 from lane G8C's `HironakaG8E4cCarrier.genLowerValue_eq_of_carrierData`),
  `classFunctorial_genInv_of_maxOrderClassValue`, **`classFunctorial_genInv`** (the theorem of plan module 11).

Sorry-free.  Universe `0` for the manifolds (the exponent calculus of lane G8 is `CMfd.{0}`); values in any universe.
Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG8P1GenInv

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.MaxOrderValue (IsMaxOrderValue)
open Hironaka.GeneralValue (genInv genLowerValue GenLowerData)
open Hironaka.NonmonomialOrderLocal (nmOrd)
open Hironaka.StepOneRegime (regimeRun)
open Hironaka.NonmonomialOrderRegime (OrdRegime)
open Hironaka.BlowupTowerSplit (head tail)
open Hironaka.MonomialCaseAlong (gammaAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)

noncomputable section

variable {n : ℕ}

/-! ### Class functoriality on the marked ideals of maximal order -/

section MaxOrder

variable {Λ : Type v} [LinearOrder Λ]

/-- **Class functoriality on the marked ideals of maximal order**: the fields of `HironakaG11InvBMClass.ClassFunctorialFor`
with both marked ideals of maximal order (the hypothesis on the maximal-order value `M` of the general step). -/
structure ClassFunctorialMaxOrderFor (Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop) (k : ℕ)
    (inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop where
  /-- The same canonical segments. -/
  canonical_iff : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → Eqv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A (inv A) T ↔ IsCanonical B (inv B) T
  /-- The same values along them, on the cosupport. -/
  inv_eq : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
    IsMaximalOrderAlong A.N A.ideal A.d → IsMaximalOrderAlong B.N B.ideal B.d → Eqv A B →
    A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical A (inv A) T →
      ∀ y ∈ (geoTransformAlong A T).cosupp, inv A T y = inv B T y

/-- **A class-functorial value function is class functorial on the marked ideals of maximal order.** -/
theorem ClassFunctorialFor.toMaxOrder {Eqv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop} {k : ℕ}
    {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (h : ClassFunctorialFor Eqv k inv) : ClassFunctorialMaxOrderFor Eqv k inv where
  canonical_iff A B hA hB _ _ hAB := h.canonical_iff A B hA hB hAB
  inv_eq A B hA hB _ _ hAB := h.inv_eq A B hA hB hAB

/-- **A finer equivalence keeps class functoriality on the marked ideals of maximal order.** -/
theorem ClassFunctorialMaxOrderFor.mono {Eqv Eqv' : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → MarkedIdeal n X → Prop}
    {k : ℕ} {inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    (h : ClassFunctorialMaxOrderFor Eqv k inv)
    (hle : ∀ {X : CMfd.{u} n} (A B : MarkedIdeal n X), Eqv' A B → Eqv A B) : ClassFunctorialMaxOrderFor Eqv' k inv where
  canonical_iff A B hA hB hmA hmB hAB := h.canonical_iff A B hA hB hmA hmB (hle A B hAB)
  inv_eq A B hA hB hmA hmB hAB := h.inv_eq A B hA hB hmA hmB (hle A B hAB)

/-- **The value part, in lane G8C's form** (`HironakaG8E4cValue.MaxOrderClassValue`, the hypothesis of E4). -/
theorem ClassFunctorialMaxOrderFor.maxOrderClassValue {k : ℕ}
    {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
    (h : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k M) :
    HironakaG8E4cValue.MaxOrderClassValue k M :=
  fun P Q hP hQ hmP hmQ hPQ hd hE hS hX _ T hT y hy => h.inv_eq P Q hP hQ hmP hmQ hPQ hd hE hS hX T hT y hy

end MaxOrder

/-! ### E3 for values in any universe -/

section Entries

variable {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}

/-- **E3** (carriers of the same dimension; the value type in any universe): at the points of order `0` of a common test
tower the general values of `A ≈ B` agree (both are `(0, γ)`, and the monomial invariants `γ` agree). -/
theorem locWPEquiv_genInv_eq_of_nmOrd_eq_zero {Λ : Type v} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ)
    (h : LocWPEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hdim : SameCarrierDim A B)
    (hd : B.d = A.d) (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp) (hzero : nmOrd (geoTransformAlong A T) y = 0) :
    genInv M A T y = genInv M B T y := by
  have hP := LocEquiv.projEquiv h
  have hW := hP.wEquiv
  have hOrd : HironakaG8ProjEquiv.TowerOrdAgree A B :=
    HironakaG8P1NormalizedOrder.towerOrdAgree_of_projEquiv hP hA hB hdim hd
  have hnm := HironakaG8P1Entries.locWPEquiv_nmOrd_geoTransformAlong_eq h hA hB hdim hd h0 T hT hy
  rw [GeneralValue.genInv_of_nmOrd_eq_zero M A T hzero,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T (hnm.symm.trans hzero)]
  have hTB : IsGeoTestTower B T := (hW.2 T).1.mp hT
  have hET : (geoTransformAlong B T).E = (geoTransformAlong A T).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hW.1.symm T
  have hexp := HironakaG8P1Entries.expDataAlong_eq_of_expAgree'
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hT).isWellFormed
    (InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB).isWellFormed hET
    (HironakaG8P1Entries.expAgree_geoTransformAlong_of_ordAgree' hW hOrd hA hB hd h0 T hT) hy
  have hγ : gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
      (geoTransformAlong A T).d y =
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d y := by
    unfold gammaAlong
    rw [hexp, hET, d_geoTransformAlong, d_geoTransformAlong, hd]
  rw [hγ]

end Entries

/-! ### The induction along the tower -/

section Induction

variable {Λ : Type v} [LinearOrder Λ]

/-- **E4, the conclusion consumed by the induction**: for `A ≈ B` (`LocWPEquiv`, domain, carriers of the same dimension, the
same mark, agreeing exponents), a common test stage `T₀` and lower data of both at the split `T₀ T₁` at `y`, the companion
values agree.  Discharged by lane G8C's `HironakaG8E4cCarrier.genLowerValue_eq_of_carrierData`. -/
def CompanionValueAgree (k : ℕ)
    (M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ) : Prop :=
  ∀ {X : CMfd.{0} n} {kA kB : ℕ} {A B : MarkedIdeal n X}, LocWPEquiv A B → IsInvDomain kA A → IsInvDomain kB B →
    SameCarrierDim A B → B.d = A.d → ExpAgree A B → ∀ {o : ℕ}, 1 ≤ o →
    ∀ {Y₀ Y : CMfd.{0} n} (T₀ : BlowupTower X Y₀), IsGeoTestTower A T₀ → ∀ (T₁ : BlowupTower Y₀ Y) (y : Y),
      GenLowerData M k A o T₀ T₁ y → GenLowerData M k B o T₀ T₁ y →
      genLowerValue M A o T₀ T₁ y = genLowerValue M B o T₀ T₁ y

variable {k : ℕ} {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}
  {X : CMfd.{0} n} {A B : MarkedIdeal n X}

/-- **The values agree along a tower canonical for both** (on the cosupport): E1 for the first entry, E3 at order `0`, and
at positive order the common split (E2), lower data for both (`GeneralCanonicalTail.hasGenLowerData_of_isCanonical`) and E4. -/
theorem genInv_eq_of_isCanonical (hM : IsMaxOrderValue n k M) (hn : 0 < n) (hE4 : CompanionValueAgree k M)
    (hA : IsInvDomain k A) (hB : IsInvDomain k B) (h : LocWPEquiv A B) (hd : B.d = A.d) (hdim : SameCarrierDim A B)
    (h0 : ExpAgree A B) {Y : CMfd.{0} n} (T : BlowupTower X Y) (hcanA : IsCanonical A (genInv M A) T)
    (hcanB : IsCanonical B (genInv M B) T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp) :
    genInv M A T y = genInv M B T y := by
  have hTA := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hA T hcanA
  have hTB := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hB T hcanB
  have hyB : y ∈ (geoTransformAlong B T).cosupp := ((LocEquiv.wEquiv h).2 T).2 hTA ▸ hy
  have hν := HironakaG8P1Entries.locWPEquiv_nmOrd_geoTransformAlong_eq h hA hB hdim hd h0 T hTA hy
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong A T) y) with hz | hpos
  · exact locWPEquiv_genInv_eq_of_nmOrd_eq_zero M h hA hB hdim hd h0 T hTA hy hz
  · generalize ho : nmOrd (geoTransformAlong A T) y = o at hν hpos
    have hoB : nmOrd (geoTransformAlong B T) y = o := hν.symm
    have hrun := HironakaG8P1Entries.locWPEquiv_regimeRun_eq h hA hB hdim hd h0 o T hTA y
    have hLA := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hA T hTA hcanA y hy o ho hpos
    have hLB := GeneralCanonicalTail.hasGenLowerData_of_isCanonical M hM hn hB T hTB hcanB y hyB o hoB hpos
    rw [← hrun] at hLB
    have hT₀ := ((BlowupTowerSplit.isGeoTestTower_iff_head_tail A T (regimeRun (OrdRegime A o) T y)).mp hTA).1
    rw [GeneralValue.genInv_of_nmOrd_ne_zero M A T ho hpos.ne',
      GeneralValue.genInv_of_nmOrd_ne_zero M B T hoB hpos.ne', ← hrun,
      hE4 h hA hB hdim hd h0 hpos _ hT₀ _ y hLA hLB]

/-- **The canonical segments of the general value correspond** for `A ≈ B`: by induction along the tower, the prefixes
correspond, the cosupports agree and the values agree on them (`genInv_eq_of_isCanonical`), so the maximum loci agree. -/
theorem isCanonical_genInv_iff (hM : IsMaxOrderValue n k M) (hn : 0 < n) (hE4 : CompanionValueAgree k M)
    (hA : IsInvDomain k A) (hB : IsInvDomain k B) (h : LocWPEquiv A B) (hd : B.d = A.d) (hdim : SameCarrierDim A B)
    (h0 : ExpAgree A B) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsCanonical A (genInv M A) T ↔ IsCanonical B (genInv M B) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      have ih := isCanonical_genInv_iff hM hn hE4 hA hB h hd hdim h0 T
      show (IsCanonical A (genInv M A) T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (genInv M A T) (geoTransformAlong A T).cosupp)) ↔
        (IsCanonical B (genInv M B) T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (genInv M B T) (geoTransformAlong B T).cosupp))
      have key : IsCanonical A (genInv M A) T →
          ResolutionDriver.maxLocus (genInv M A T) (geoTransformAlong A T).cosupp =
            ResolutionDriver.maxLocus (genInv M B T) (geoTransformAlong B T).cosupp := by
        intro hcA
        have hTA := GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn hA T hcA
        rw [← ((LocEquiv.wEquiv h).2 T).2 hTA]
        exact ResolutionInvariantExt.maxLocus_congr fun y hy =>
          genInv_eq_of_isCanonical hM hn hE4 hA hB h hd hdim h0 T hcA (ih.mp hcA) hy
      constructor
      · rintro ⟨hcA, hC⟩
        exact ⟨ih.mp hcA, hC.imp id fun hC' => hC'.trans (key hcA)⟩
      · rintro ⟨hcB, hC⟩
        have hcA := ih.mpr hcB
        exact ⟨hcA, hC.imp id fun hC' => hC'.trans (key hcA).symm⟩

/-- **Class functoriality of the general value, given E4**: if `M` is a maximal-order value (`IsMaxOrderValue n k M`) whose
companion values are class determined (`CompanionValueAgree k M`), then `genInv M` is class functorial for `LocWPEquiv`. -/
theorem classFunctorialFor_genInv_of_companion (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hE4 : CompanionValueAgree k M) :
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k (genInv M) where
  canonical_iff := by
    intro _ A B hA hB h hd _ hdim h0 _ T
    exact isCanonical_genInv_iff hM hn hE4 hA hB h hd.symm hdim h0 T
  inv_eq := by
    intro _ A B hA hB h hd _ hdim h0 _ T hcan y hy
    exact genInv_eq_of_isCanonical hM hn hE4 hA hB h hd.symm hdim h0 T hcan
      ((isCanonical_genInv_iff hM hn hE4 hA hB h hd.symm hdim h0 T).mp hcan) hy

end Induction

/-! ### The theorem of module 11 -/

section Main

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {M : ∀ {X : CMfd.{0} n}, MarkedIdeal n X → ∀ {Y : CMfd.{0} n}, BlowupTower X Y → Y → Λ}

/-- **E4 for carriers of the same dimension** (lane G8C's `HironakaG8E4cCarrier.genLowerValue_eq_of_carrierData`): a
maximal-order value whose values are class determined on the marked ideals of maximal order has class-determined companion
values. -/
theorem companionValueAgree_of_maxOrderClassValue (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hcl : HironakaG8E4cValue.MaxOrderClassValue k M) : CompanionValueAgree k M := by
  intro _ _ _ _ _ h hA hB hdim hd h0 _ ho _ _ T₀ hT₀ T₁ y hLA hLB
  exact HironakaG8E4cCarrier.genLowerValue_eq_of_carrierData hM hcl h hA hB hdim hd h0 hn ho T₀ hT₀ T₁ y hLA hLB

/-- **Class functoriality of the general value from the value part of `M`'s class functoriality** (lane G8C's
`MaxOrderClassValue`: equal values of class-equivalent marked ideals of maximal order along canonical segments; the
correspondence of `M`'s canonical segments is not needed). -/
theorem classFunctorial_genInv_of_maxOrderClassValue (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hcl : HironakaG8E4cValue.MaxOrderClassValue k M) :
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k (genInv M) :=
  classFunctorialFor_genInv_of_companion hM hn (companionValueAgree_of_maxOrderClassValue hM hn hcl)

/-- **Class functoriality of the general value** ((B') plan module 11; Bierstone--Milman 2008, Theorem 7.1(4), §5 Step II):
if `M` is a value function for the marked ideals of maximal order in dimension `≤ k` (`IsMaxOrderValue n k M`) which is class
functorial on them for `LocWPEquiv`, then the general value `genInv M` is class functorial for `LocWPEquiv` (marked ideals of
the domain with the same mark and divisor, carriers of the same dimension and agreeing boundary exponents have the same
canonical segments and, along them, the same values on the cosupport). -/
theorem classFunctorial_genInv (hM : IsMaxOrderValue n k M) (hn : 0 < n)
    (hMcf : ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k M) :
    ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k (genInv M) :=
  classFunctorial_genInv_of_maxOrderClassValue hM hn hMcf.maxOrderClassValue

end Main

end

end Hironaka.HironakaG8P1GenInv
