import Hironaka.Resolution.HironakaActualCurveCoreContactComparison
import Hironaka.Resolution.HironakaActualPositiveCoreOrderPresentation

/-! The ACTUAL original general core through its SAME source-clock
companion. Original core cuts derive whole companion Step One core cuts;
lower CAN, lower-data and a value comparison are not caller inputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaActualInitialGeneralCoreComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupTowerSplit
  CompanionRebase CompanionReductionAlong NonmonomialOrderLocal NonmonomialOrderTail
  NonmonomialOrderRegime StepOneRegime GeneralValue HironakaStageCenters
  HironakaActualRecursiveCoreValues HironakaActualInitialCountCoreComparison
  HironakaActualPositiveCoreOrderPresentation CanonicalCentres HomogenizedIdealAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- The literal finite positive outer branch in the unchanged native
value type, interpreted by the actual fixed-companion theorem below. -/
def positiveCoreValue (k q : ℕ) (value : ℕ ×ₗ WithTop (ValTy (k+1))) : ValTy (k+2) :=
  toLex (q,toLex (Sum.inr (value : WithTop (ℕ ×ₗ WithTop (ValTy (k+1))))))

private theorem positiveCoreValue_le_iff (k q : ℕ) (a b : ℕ ×ₗ WithTop (ValTy (k+1))) :
    positiveCoreValue k q a≤positiveCoreValue k q b ↔ a≤b := by
  constructor
  · intro h
    rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨_,h⟩
    · exact (lt_irrefl q h).elim
    · exact WithTop.coe_le_coe.mp (Sum.Lex.inr_le_inr_iff.mp h)
  · intro h
    exact Prod.Lex.toLex_le_toLex.mpr
      (Or.inr ⟨rfl,Sum.Lex.inr_le_inr_iff.mpr (WithTop.coe_le_coe.mpr h)⟩)

private theorem split_at_length : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    split T T.length=⟨X,.refl,T⟩
  | _, .refl => rfl
  | _, .step T C π hπ => by
      change (⟨(split T T.length).1,(split T T.length).2.1,
        .step (split T T.length).2.2 C π hπ⟩ :
          Σ A : CMfd.{u} n, BlowupTower X A × BlowupTower A _) = _
      rw [split_at_length T]

private theorem general_native_full_run {Λ : Type v} [LinearOrder Λ]
    (F : ∀ {A : CMfd.{u} n}, MarkedIdeal n A → ∀ {B : CMfd.{u} n}, BlowupTower A B → B → Λ)
    (M : MarkedIdeal n X) (q : ℕ) (hq : q≠0) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (y : Y) (hOrder : nmOrd (geoTransformAlong M T) y=q)
    (hRun : regimeRun (OrdRegime M q) T y=T.length)
    (hMask : y∈openPreimage T (ordMask M q)) :
    genInv F M T y=toLex (q,toLex (Sum.inr
      ((F (compAt M q (.refl : BlowupTower X X)) (restrict (ordMask M q) T)
        ⟨y,hMask⟩ : Λ) : WithTop Λ))) := by
  rw [genInv_of_nmOrd_ne_zero F M T hOrder hq,hRun]
  unfold head tail
  rw [split_at_length T]
  have hMask' : T.proj y∈ordMask (geoTransformAlong M (.refl : BlowupTower X X)) q := hMask
  rw [genLowerValue_eq_of_mem F M hMask']
  rfl

private theorem erase_positive_general (k q : ℕ) (value : ℕ ×ₗ WithTop (ValTy (k+1))) :
    eraseGamma (k+2) (positiveCoreValue k q value) =
      positiveCoreValue k q (toLex ((ofLex value).1,WithTop.map (eraseGamma (k+1)) (ofLex value).2)) := rfl

private theorem native_order (hn : 0<n) (k : ℕ) (M : MarkedIdeal n X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex ((invFamily hn (k+2)).inv M T y)).1=nmOrd (geoTransformAlong M T) y := rfl

/-- Actual order-cut centres DERIVE the genuine companion TEST before the
native full-run formula identifies its actual projected Step One value. -/
theorem actual_initial_general_core_companion
    (hn : 0<n) (k : ℕ) {b : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (q : ℕ) (hq : 1≤q) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T)
    (hCuts : StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T) :
    let W := ordMask M q
    let A := MarkedIdeal.pullback (Subtype.val : W → X) M
    let J := companionOf n (M := CMfd.of (n := n) W) A q
    IsInvDomain b J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsGeoTestTower J (restrict W T) ∧
      (geoTransformAlong J (restrict W T)).E=(geoTransformAlong M T).E.map
        (fun H=>(Subtype.val : openPreimage T W → Y) ⁻¹' H) ∧
      (geoTransformAlong J (restrict W T)).cosupp=
        (Subtype.val : openPreimage T W → Y) ⁻¹'
          (ordGe (geoTransformAlong M T) q∩(geoTransformAlong M T).cosupp) ∧
      ∀ p∈(geoTransformAlong J (restrict W T)).cosupp,
        coreInv hn (k+2) M T p=positiveCoreValue k q (stepOneCoreInv hn k J (restrict W T) p) := by
  dsimp only
  let W := ordMask M q
  let A := MarkedIdeal.pullback (Subtype.val : W → X) M
  let J := companionOf n (M := CMfd.of (n := n) W) A q
  obtain ⟨hJ,hMax,hTJ,hCos,hE,_hUpper⟩ :=
    actual_positive_order_masked_whole_presentation hn M hM q hq T hT hCuts
  refine ⟨hJ,hMax,hTJ,hE,hCos,?_⟩
  intro p hp
  have hpSplit : (p : Y)∈ordGe (geoTransformAlong M T) q∩(geoTransformAlong M T).cosupp := by
    rw [hCos] at hp
    exact hp
  have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hOrderGe := (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
    ((geoTransformAlong M T).cosupp_subset_N hpSplit.2) q).mp hpSplit.1
  have hT' : IsGeoTestTower M ((.refl : BlowupTower X X).append T) := by
    simpa only [BlowupTower.refl_append] using hT
  have hpParent : (p : Y)∈(geoTransformAlong M ((.refl : BlowupTower X X).append T)).cosupp := by
    simpa only [BlowupTower.refl_append] using hpSplit.2
  have hpOrder : q≤nmOrd (geoTransformAlong M ((.refl : BlowupTower X X).append T)) p := by
    simpa only [BlowupTower.refl_append] using hOrderGe
  have hReg := ordRegime_and_le_regimeRun hn hM hq (.refl : BlowupTower X X) W
    (fun _ _ hx=>notMem_ordGe_of_mem_ordMask hx) T hT' hTJ p hpParent p.2 hpOrder
  simp only [BlowupTower.refl_append] at hReg
  have hRun : regimeRun (OrdRegime M q) T p=T.length :=
    (regimeRun_le_length _ T p).antisymm hReg.2
  have hNative := general_native_full_run
    (fun {A} L {B} S y=>Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1)) L S y)
    M q (by omega) T p hReg.1.2 hRun p.2
  have hNative' : (invFamily hn (k+2)).inv M T p=
      toLex (q,toLex (Sum.inr ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn (k+1))
        J (restrict W T) p : ℕ ×ₗ WithTop (ValTy (k+1))) :
          WithTop (ℕ ×ₗ WithTop (ValTy (k+1)))))) := hNative
  rw [coreInv,hNative']
  exact erase_positive_general k q _

private theorem original_core_cuts_order
    (hn : 0<n) (k : ℕ) {b : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (q : ℕ) (value : ℕ ×ₗ WithTop (ValTy (k+1))) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      StageCentres (fun S C=>∀c∈C,positiveCoreValue k q value≤coreInv hn (k+2) M S c) T →
        StageCentres (fun S C=>C⊆ordGe (geoTransformAlong M S) q) T
  | _, .refl, _, _ => trivial
  | _, .step S C π hπ, hT, hCuts => by
      refine ⟨original_core_cuts_order hn k M hM q value S hT.1 hCuts.1,?_⟩
      intro c hc
      have h := hCuts.2 c hc
      have hFirst : q≤nmOrd (geoTransformAlong M S) c := by
        change toLex (q,_)≤toLex (_,_) at h
        rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h,_⟩
        · exact h.le.trans_eq (native_order hn k M S c)
        · exact h.le.trans_eq (native_order hn k M S c)
      have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM S hT.1
      exact (mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong M S).cosupp_subset_N (hT.2.2.1 hc)) q).mpr hFirst

/-- Actual ORIGINAL general-core cuts DERIVE every actual companion core
cut and the ENTIRE fixed-source native cut identity, without future data. -/
theorem actual_initial_general_core_cut_presentation
    (hn : 0<n) (k : ℕ) {b : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain b M)
    (q : ℕ) (hq : 1≤q) (value : ℕ ×ₗ WithTop (ValTy (k+1)))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (hCuts : StageCentres
      (fun S C=>∀c∈C,positiveCoreValue k q value≤coreInv hn (k+2) M S c) T) :
    let W := ordMask M q
    let A := MarkedIdeal.pullback (Subtype.val : W → X) M
    let J := companionOf n (M := CMfd.of (n := n) W) A q
    IsInvDomain b J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsGeoTestTower J (restrict W T) ∧
      (geoTransformAlong J (restrict W T)).E=(geoTransformAlong M T).E.map
        (fun H=>(Subtype.val : openPreimage T W → Y) ⁻¹' H) ∧
      StageCentres (fun S C=>∀c∈C,value≤stepOneCoreInv hn k J S c) (restrict W T) ∧
      {p | p∈(geoTransformAlong J (restrict W T)).cosupp ∧ value≤stepOneCoreInv hn k J (restrict W T) p}=
        (Subtype.val : openPreimage T W → Y) ⁻¹'
          {y | y∈(geoTransformAlong M T).cosupp ∧ positiveCoreValue k q value≤coreInv hn (k+2) M T y} := by
  dsimp only
  let W := ordMask M q
  let A := MarkedIdeal.pullback (Subtype.val : W → X) M
  let J := companionOf n (M := CMfd.of (n := n) W) A q
  have hOrderCuts := original_core_cuts_order hn k M hM q value T hT hCuts
  obtain ⟨hJ,hMax,hTJ,hE,hCos,hValues⟩ :=
    actual_initial_general_core_companion hn k M hM q hq T hT hOrderCuts
  have hCompanionCuts : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower M T →
      StageCentres (fun S C=>∀c∈C,positiveCoreValue k q value≤coreInv hn (k+2) M S c) T →
        StageCentres (fun S C=>∀c∈C,value≤stepOneCoreInv hn k J S c) (restrict W T) := by
    intro Y T
    induction T with
    | refl => intro _ _; trivial
    | @step Y Z S C π hπ ih =>
      intro hT hCuts
      have hOrd := original_core_cuts_order hn k M hM q value (.step S C π hπ) hT hCuts
      obtain ⟨_hJ,_hMax,hNext,_hE,_hCos,_hValues⟩ :=
        actual_initial_general_core_companion hn k M hM q hq (.step S C π hπ) hT hOrd
      obtain ⟨_hJ,_hMax,_hTest,_hE,_hCos,hValueS⟩ :=
        actual_initial_general_core_companion hn k M hM q hq S hT.1 hOrd.1
      refine ⟨ih hT.1 hCuts.1,?_⟩
      intro p hp
      have hpCos : p∈(geoTransformAlong J (restrict W S)).cosupp := hNext.2.2.1 hp
      have hCut := hCuts.2 p hp
      rw [hValueS p hpCos] at hCut
      exact (positiveCoreValue_le_iff k q _ _).mp hCut
  refine ⟨hJ,hMax,hTJ,hE,hCompanionCuts T hT hCuts,?_⟩
  ext p
  constructor
  · rintro ⟨hp,hValue⟩
    have hpParent : (p : Y)∈(geoTransformAlong M T).cosupp := by
      rw [hCos] at hp
      exact hp.2
    refine ⟨hpParent,?_⟩
    rw [hValues p hp]
    exact (positiveCoreValue_le_iff k q _ _).mpr hValue
  · rintro ⟨hpParent,hCut⟩
    have hOrder : q≤nmOrd (geoTransformAlong M T) p := by
      change toLex (q,_)≤toLex (_,_) at hCut
      rcases Prod.Lex.toLex_le_toLex.mp hCut with h | ⟨h,_⟩
      · exact h.le.trans_eq (native_order hn k M T p)
      · exact h.le.trans_eq (native_order hn k M T p)
    have hCurrent := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
    have hpCompanion : p∈(geoTransformAlong J (restrict W T)).cosupp := by
      rw [hCos]
      exact ⟨(mem_ordGe_iff hCurrent.isWellFormed hCurrent.isNonzeroAlongAt
        ((geoTransformAlong M T).cosupp_subset_N hpParent) q).mpr hOrder,hpParent⟩
    refine ⟨hpCompanion,?_⟩
    rw [hValues p hpCompanion] at hCut
    exact (positiveCoreValue_le_iff k q _ _).mp hCut

end
end Hironaka.HironakaActualInitialGeneralCoreComparison
