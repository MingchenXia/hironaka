import Hironaka.Resolution.HironakaActualMixedPullbackNormalization
import Hironaka.Resolution.HironakaActualOriginalPowerTransform

/-! Actual varying-dimension mixed tests and ORIGINAL whole-power normalization.
Controlled actions use the native proper-carrier colon; exceptional actions
use ORDINARY pullback. Every old/born/horizontal/empty slot is retained.
Blueprint FIRST: hironaka-actual-mixed-test-power-normalization.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualMixedTestPowerNormalization
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec RelativePrincipalizationSpan InvertibleIdealQuotient
  IdealWeightPowers GermIdealPullbackCalculus RestrictedIdealExtension
  RestrictedIdealWeight RestrictedIdealQuotient RestrictLeCalculus
  MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal BlowupStrictSubmanifold
  HironakaActualProjectionTestRecord HironakaActualExceptionalTestRecord
  HironakaActualPowerBoundaryExponents HironakaActualOriginalPowerTransform
  HironakaActualMixedPullbackNormalization
open scoped ProductComplexManifold

/-- Geometry only: source admissibility is imposed separately by IsTest. -/
inductive History {n : ℕ} (X : CMfd.{u} n) (E : List (Set X)) :
    {m : ℕ} → (Y : CMfd.{u} m) → List (Set Y) → Type (u+1)
  | refl : History X E X E
  | controlled {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : History X E Y F) (C : Set Y) {Z : CMfd.{u} m} (π : Z → Y)
      (hπ : IsBlowupAlong m C π) :
      History X E Z (F.map (geoStrictTransform π C) ++ [π ⁻¹' C])
  | projection {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : History X E Y F) : History X E (projectionAmbient Y)
        (F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y])
  | exceptional {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
      (H : History X E Y F) (i j : Fin F.length) (hij : i ≠ j)
      {Z : CMfd.{u} m} (π : Z → Y)
      (hπ : IsBlowupAlong m (F.get i ∩ F.get j) π) :
      History X E Z (F.map (geoStrictTransform π (F.get i ∩ F.get j)) ++
        [π ⁻¹' (F.get i ∩ F.get j)])

variable {n : ℕ} {X : CMfd.{u} n} {E : List (Set X)}

def boundary {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (_H : History X E Y F) : List (Set Y) := F

def length : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → ℕ
  | _,_,_,.refl => 0
  | _,_,_,.controlled H _ _ _ => length H+1
  | _,_,_,.projection H => length H+1
  | _,_,_,.exceptional H _ _ _ _ _ => length H+1

def projections : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → ℕ
  | _,_,_,.refl => 0
  | _,_,_,.controlled H _ _ _ => projections H
  | _,_,_,.projection H => projections H+1
  | _,_,_,.exceptional H _ _ _ _ _ => projections H

/-- The actual original composite map, including dimension changes. -/
def baseMap : {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → Y → X
  | _,_,_,.refl => id
  | _,_,_,.controlled H _ π _ => baseMap H ∘ π
  | _,_,_,.projection H => baseMap H ∘ Prod.fst
  | _,_,_,.exceptional H _ _ _ π _ => baseMap H ∘ π

theorem baseMap_holomorphic {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X E Y F) : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (baseMap H) := by
  induction H with
  | refl => exact contMDiff_id
  | controlled H C π hπ ih => exact ih.comp hπ.contMDiff
  | @projection m Y F H ih =>
    exact ih.comp (ProductComplexManifold.contMDiff_fst
      (n := m) (m := 1) (X := Y) (Y := ComplexModel 1))
  | exceptional H i j hij π hπ ih => exact ih.comp hπ.contMDiff

/-- Proper carrier geometry depends only on the original carrier. -/
def carrier (N : Set X) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → Set Y
  | _,_,_,.refl => N
  | _,_,_,.controlled H C π _ => geoStrictTransform π C (carrier N H)
  | _,_,_,.projection H => Prod.fst ⁻¹' carrier N H
  | _,_,_,.exceptional H i j _ π _ =>
    geoStrictTransform π ((boundary H).get i ∩ (boundary H).get j) (carrier N H)

/-- Entire original recursive ideal; only controlled actions have a denominator. -/
def wholeIdeal (N : Set X) (I : GermIdeal n X) (d : ℕ) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → GermIdeal m Y
  | _,_,_,.refl => I
  | m,_,_,.controlled H C π _ =>
    colonAlong m (geoStrictTransform π C (carrier N H))
      (GermIdeal.pullback (m := m) π (wholeIdeal N I d H))
      (idealPow (GermIdeal.pullback (m := m) π (vanishingIdeal (n := m) C)) d)
  | _,_,_,.projection H => GermIdeal.pullback Prod.fst (wholeIdeal N I d H)
  | _,_,_,.exceptional H _ _ _ π _ => GermIdeal.pullback π (wholeIdeal N I d H)

/-- Same native fields, actual final ambient and full boundary, original mark. -/
def record (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) : MarkedIdeal m Y :=
  ⟨carrier M.N H,F,wholeIdeal M.N M.ideal M.d H,M.d⟩

theorem record_controlled (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m}
    {F : List (Set Y)} (H : History X M.E Y F) (C : Set Y) {Z : CMfd.{u} m}
    (π : Z → Y) (hπ : IsBlowupAlong m C π) :
    record M (.controlled H C π hπ)=(record M H).geoTransform C π := rfl

theorem record_projection (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m}
    {F : List (Set Y)} (H : History X M.E Y F) :
    record M (.projection H)=projectionTest (record M H) := rfl

theorem record_exceptional (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m}
    {F : List (Set Y)} (H : History X M.E Y F) (i j : Fin F.length) (hij : i ≠ j)
    {Z : CMfd.{u} m} (π : Z → Y) (hπ : IsBlowupAlong m (F.get i ∩ F.get j) π) :
    record M (.exceptional H i j hij π hπ)=exceptionalTest (record M H) i j π := rfl

/-- No centre/cosupport test is imposed at either ORDINARY action. -/
def IsTest (M : MarkedIdeal n X) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X M.E Y F → Prop
  | _,_,_,.refl => True
  | _,_,_,.controlled H C _ _ => IsTest M H ∧ (record M H).IsAdmissibleCentre C
  | _,_,_,.projection H => IsTest M H
  | _,_,_,.exceptional H _ _ _ _ _ => IsTest M H

/-- Every action counts, and only a genuine projection raises dimension. -/
theorem history_clocks (M : MarkedIdeal n X) {m : ℕ} {Y : CMfd.{u} m}
    {F : List (Set Y)} (H : History X M.E Y F) :
    m=n+projections H ∧ (record M H).E.length=M.E.length+length H := by
  induction H with
  | refl => exact ⟨(Nat.add_zero _).symm,(Nat.add_zero _).symm⟩
  | @controlled m Y F H C Z π hπ ih =>
    constructor
    · exact ih.1
    · change (F.map (geoStrictTransform π C) ++ [_]).length=M.E.length+(length H+1)
      simp only [List.length_append,List.length_map,List.length_singleton]
      have hlen:=ih.2
      change F.length=M.E.length+length H at hlen
      omega
  | @projection m Y F H ih =>
    constructor
    · change m+1=n+(projections H+1)
      omega
    · change (F.map _ ++ [_]).length=M.E.length+(length H+1)
      simp only [List.length_append,List.length_map,List.length_singleton]
      have hlen:=ih.2
      change F.length=M.E.length+length H at hlen
      omega
  | @exceptional m Y F H i j hij Z π hπ ih =>
    constructor
    · exact ih.1
    · change (F.map _ ++ [_]).length=M.E.length+(length H+1)
      simp only [List.length_append,List.length_map,List.length_singleton]
      have hlen:=ih.2
      change F.length=M.E.length+length H at hlen
      omega

/-- All native domain fields are derived at every actual prefix. -/
theorem record_isInvDomain (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F),
      IsTest M H → IsInvDomain (k+projections H) (record M H)
  | _,_,_,.refl,_ => by
    rcases M with ⟨N,E,I,d⟩
    exact hM
  | _,_,_,.controlled H C π hπ,hH => by
    have hd:=record_isInvDomain M hM H hH.1
    exact InvDomainTowerAlong.isInvDomain_geoTransformAlong hd
      (.step .refl C π hπ) ⟨trivial,hH.2⟩
  | _,_,_,.projection H,hH => by
    have hd:=projection_test_isInvDomain (record M H) (record_isInvDomain M hM H hH)
    simpa only [record_projection,projections,Nat.add_assoc] using hd
  | _,_,_,.exceptional H i j hij π hπ,hH =>
    exceptional_test_isInvDomain (record M H) (record_isInvDomain M hM H hH) i j hij hπ

/-- Original whole power, not a reset power history or target certificate. -/
theorem original_power_normalization (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (e : ℕ) (he : 1≤e) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F),IsTest M H →
      IsTest (powerMarked M e) H ∧
        RestrictEquiv (record (powerMarked M e) H) (powerMarked (record M H) e)
  | _,_,_,.refl,_ =>
    ⟨trivial,RestrictEquiv.refl (isCoherent_idealPow hM.isWellFormed.isCoherent e)⟩
  | _,_,_,.controlled H C π hπ,hH => by
    obtain ⟨ht,hr⟩:=original_power_normalization M hM e he H hH.1
    have hd:=record_isInvDomain M hM H hH.1
    have hp:=record_isInvDomain (powerMarked M e) (powerMarked_isInvDomain M hM he) H ht
    have hc : (powerMarked (record M H) e).IsAdmissibleCentre C := by
      unfold IsAdmissibleCentre
      rw [powerMarked_cosupp (record M H) hd he]
      exact hH.2
    have hcP:=hr.isAdmissibleCentre_iff.mpr hc
    have hwhole:=hr.geoTransform_eq (C := C) (π := π) hp.isWellFormed.isClosedSubmanifold_N.1
      hp.isWellFormed.isCoherent (isCoherent_idealPow hd.isWellFormed.isCoherent e) hπ.contMDiff
    have hone:=(HironakaActualOriginalPowerTransform.original_power_transform
      (record M H) hd e he (.step .refl C π hπ) ⟨trivial,hH.2⟩).2
    refine ⟨⟨ht,hcP⟩,?_⟩
    change RestrictEquiv ((record (powerMarked M e) H).geoTransform C π)
      (powerMarked ((record M H).geoTransform C π) e)
    rw [hwhole]
    exact hone
  | _,_,_,.projection H,hH => by
    obtain ⟨ht,hr⟩:=original_power_normalization M hM e he H hH
    have hd:=record_isInvDomain M hM H hH
    have hp:=record_isInvDomain (powerMarked M e) (powerMarked_isInvDomain M hM he) H ht
    exact ⟨ht,projection_power_normalization (record M H) hd
      (record (powerMarked M e) H).ideal hp.isWellFormed.isCoherent e hr.le hr.ge⟩
  | _,_,_,.exceptional H i j hij π hπ,hH => by
    obtain ⟨ht,hr⟩:=original_power_normalization M hM e he H hH
    have hd:=record_isInvDomain M hM H hH
    have hp:=record_isInvDomain (powerMarked M e) (powerMarked_isInvDomain M hM he) H ht
    exact ⟨ht,exceptional_power_normalization (record M H) hd
      (record (powerMarked M e) H).ideal hp.isWellFormed.isCoherent e hr.le hr.ge i j hπ⟩

/-- Same genuine geometry tests the two ORIGINAL records iff. -/
theorem original_power_test_iff (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) : IsTest (powerMarked M e) H ↔ IsTest M H := by
  refine ⟨?_,fun ht=>(original_power_normalization M hM e he H ht).1⟩
  induction H with
  | refl => intro _;trivial
  | controlled H C π hπ ih =>
    intro hp
    have ht:=ih hp.1
    have hd:=record_isInvDomain M hM H ht
    have hr:=(original_power_normalization M hM e he H ht).2
    have hc:=hr.isAdmissibleCentre_iff.mp hp.2
    refine ⟨ht,?_⟩
    unfold IsAdmissibleCentre at hc ⊢
    rwa [powerMarked_cosupp (record M H) hd he] at hc
  | projection H ih => exact ih
  | exceptional H i j hij π hπ ih => exact ih

/-- Literal current prefix plus every constructor predecessor, including refl. -/
def AllPrefixes (P : ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)},History X E Y F → Prop) :
    {m : ℕ} → {Y : CMfd.{u} m} → {F : List (Set Y)} → History X E Y F → Prop
  | _,_,_,.refl => P .refl
  | _,_,_,.controlled H C π hπ => P (.controlled H C π hπ) ∧ AllPrefixes P H
  | _,_,_,.projection H => P (.projection H) ∧ AllPrefixes P H
  | _,_,_,.exceptional H i j hij π hπ => P (.exceptional H i j hij π hπ) ∧ AllPrefixes P H

private theorem prefix_dictionary (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (e : ℕ) (he : 1≤e) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X M.E Y F) (hH : IsTest M H) :
    let A:=record M H
    let B:=record (powerMarked M e) H
    IsTest M H ∧ IsTest (powerMarked M e) H ∧ RestrictEquiv B (powerMarked A e) ∧
      B.N=A.N ∧ B.E=A.E ∧ B.d=M.d*e ∧
      restrictOn m A.N B.ideal=restrictOn m A.N (idealPow A.ideal e) ∧
      B.cosupp=A.cosupp ∧ B.E.length=M.E.length+length H ∧ m=n+projections H := by
  obtain ⟨ht,hr⟩:=original_power_normalization M hM e he H hH
  have hd:=record_isInvDomain M hM H hH
  refine ⟨hH,ht,hr,rfl,rfl,rfl,?_,?_,(history_clocks M H).2,(history_clocks M H).1⟩
  · exact restrictOn_eq_of_restrictLe hd.isWellFormed.isClosedSubmanifold_N.1 hr.le hr.ge
  · exact hr.cosupp_eq.trans (powerMarked_cosupp (record M H) hd he)

/-- EVERY literal prefix carries the proved original-power comparison and clocks. -/
theorem original_power_all_prefixes (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (e : ℕ) (he : 1≤e) :
    ∀ {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)} (H : History X M.E Y F),IsTest M H →
      AllPrefixes (fun {r} {_Z} {_G} P=>
        let A:=record M P
        let B:=record (powerMarked M e) P
        IsTest M P ∧ IsTest (powerMarked M e) P ∧ RestrictEquiv B (powerMarked A e) ∧
          B.N=A.N ∧ B.E=A.E ∧ B.d=M.d*e ∧
          restrictOn r A.N B.ideal=restrictOn r A.N (idealPow A.ideal e) ∧
          B.cosupp=A.cosupp ∧ B.E.length=M.E.length+length P ∧ r=n+projections P) H
  | _,_,_,.refl,hH => prefix_dictionary M hM e he .refl hH
  | _,_,_,.controlled H C π hπ,hH =>
    ⟨prefix_dictionary M hM e he (.controlled H C π hπ) hH,
      original_power_all_prefixes M hM e he H hH.1⟩
  | _,_,_,.projection H,hH =>
    ⟨prefix_dictionary M hM e he (.projection H) hH,original_power_all_prefixes M hM e he H hH⟩
  | _,_,_,.exceptional H i j hij π hπ,hH =>
    ⟨prefix_dictionary M hM e he (.exceptional H i j hij π hπ) hH,
      original_power_all_prefixes M hM e he H hH⟩

end
end Hironaka.HironakaActualMixedTestPowerNormalization
