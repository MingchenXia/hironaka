import Hironaka.Resolution.HironakaActualPowerBoundaryExponents
import Hironaka.Blowup.BlowupTowerSplit

/-! ORIGINAL whole-power recoding through the SAME actual geometric history.
Proper carriers retain restricted whole-ideal equality, not a false ambient
power identity. Weighted overlap/value/CAN comparison and H12 remain open. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalPowerTransform
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  RelativePrincipalizationSpan IdealWeightPowers GermIdealPullbackCalculus
  RestrictedIdealExtension RestrictedIdealWeight RestrictLeCalculus MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantSpec
  HironakaActualPowerBoundaryExponents

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem equivalence_trans {A B C : MarkedIdeal n X}
    (hAB : RestrictEquiv A B) (hBC : RestrictEquiv B C) : RestrictEquiv A C := by
  have hl : RestrictLe A.N B.ideal C.ideal := by rw [hAB.N_eq]; exact hBC.le
  have hg : RestrictLe A.N C.ideal B.ideal := by rw [hAB.N_eq]; exact hBC.ge
  exact ⟨hAB.N_eq.trans hBC.N_eq,hAB.E_eq.trans hBC.E_eq,hAB.d_eq.trans hBC.d_eq,
    RestrictLeCalculus.RestrictLe.trans hAB.le hl,
    RestrictLeCalculus.RestrictLe.trans hg hAB.ge⟩

private theorem power_one (M : MarkedIdeal n X) (hc : M.ideal.IsCoherent) :
    powerMarked M 1=M := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    (𝔪 := powerMarked M 1) (𝔫 := M) rfl rfl ?_ (Nat.mul_one _)
  exact BlowupControlledTransform.unitIdeal_mul hc

private theorem power_succ (M : MarkedIdeal n X) (e : ℕ) :
    powerMarked M (e+1)=
      MarkedIdealOperationsTransform.MarkedIdeal.mul (powerMarked M e) M :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl rfl (Nat.mul_succ _ _)

private theorem power_centre_iff {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) (C : Set X) :
    (powerMarked M e).IsAdmissibleCentre C ↔ M.IsAdmissibleCentre C := by
  unfold IsAdmissibleCentre
  rw [powerMarked_cosupp M hM he]
  rfl

/-- The ORIGINAL source power traverses every actual original test.
The whole transformed ideals are compared on their actual proper carrier. -/
theorem original_power_transform {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) :
    ∀e : ℕ,1≤e → ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),IsGeoTestTower M T →
      IsGeoTestTower (powerMarked M e) T ∧
        RestrictEquiv (geoTransformAlong (powerMarked M e) T)
          (powerMarked (geoTransformAlong M T) e) := by
  intro e
  induction e with
  | zero => intro he; omega
  | succ e ih =>
    intro _he Y T hT
    have hCurrent:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
    by_cases he0 : e=0
    · subst e
      rw [power_one M hM.isWellFormed.isCoherent,
        power_one (geoTransformAlong M T) hCurrent.isWellFormed.isCoherent]
      exact ⟨hT,RestrictEquiv.refl hCurrent.isWellFormed.isCoherent⟩
    · have he : 1≤e:=by omega
      obtain ⟨hPowerTest,hComparison⟩:=ih he T hT
      have hPair : IsSubmanifoldPair (powerMarked M e) M :=
        ⟨rfl,rfl,hM.isWellFormed.isClosedSubmanifold_N,
          isCoherent_idealPow hM.isWellFormed.isCoherent e,hM.isWellFormed.isCoherent⟩
      obtain ⟨hProductTest,hProduct,hPairCurrent,_hProductCoherent⟩:=
        geoTransformAlong_mul_along (powerMarked M e) M hPair T hPowerTest hT
      have hPowerCurrent:=InvDomainTowerAlong.isInvDomain_geoTransformAlong
        (powerMarked_isInvDomain M hM he) T hPowerTest
      have hMultiply : RestrictEquiv
          (MarkedIdealOperationsTransform.MarkedIdeal.mul
            (geoTransformAlong (powerMarked M e) T) (geoTransformAlong M T))
          (powerMarked (geoTransformAlong M T) (e+1)) := by
        refine ⟨hComparison.N_eq,hComparison.E_eq,?_,?_,?_⟩
        · change (geoTransformAlong (powerMarked M e) T).d+
            (geoTransformAlong M T).d=(geoTransformAlong M T).d*(e+1)
          rw [hComparison.d_eq]
          exact (Nat.mul_succ _ _).symm
        · exact restrictLe_mul
            (hol_of_isCoherent (isCoherent_idealPow hCurrent.isWellFormed.isCoherent e))
            (hol_of_isCoherent hCurrent.isWellFormed.isCoherent)
            hComparison.le (restrictLe_refl hCurrent.isWellFormed.isCoherent)
        · exact restrictLe_mul (hol_of_isCoherent hPowerCurrent.isWellFormed.isCoherent)
            (hol_of_isCoherent hCurrent.isWellFormed.isCoherent)
            hComparison.ge (restrictLe_refl hCurrent.isWellFormed.isCoherent)
      rw [power_succ M e]
      exact ⟨hProductTest,equivalence_trans hProduct hMultiply⟩

/-- ANY actual geometric history tests the original power iff it tests M.
No powered-current-history or future comparison packet is assumed. -/
theorem original_power_test_iff {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    {e : ℕ} (he : 1≤e) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    IsGeoTestTower (powerMarked M e) T ↔ IsGeoTestTower M T := by
  refine ⟨?_,fun hT=>(original_power_transform M hM e he T hT).1⟩
  induction T with
  | refl => intro _; trivial
  | @step Y Z T C pi hpi ih =>
    intro hPowered
    obtain ⟨hPrefix,hCentre⟩:=
      (isGeoTestTower_step_iff (powerMarked M e) T C pi hpi).mp hPowered
    have hOriginal:=ih hPrefix
    have hCurrent:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hOriginal
    have hComparison:=(original_power_transform M hM e he T hOriginal).2
    exact (isGeoTestTower_step_iff M T C pi hpi).mpr
      ⟨hOriginal,(power_centre_iff (geoTransformAlong M T) hCurrent he C).mp
        (hComparison.isAdmissibleCentre_iff.mp hCentre)⟩

/-- EVERY literal native head retains normalized WHOLE ideals, actual
marks/full ordered old+born+empty boundary and the original physical clock. -/
theorem original_power_head_dictionary {k : ℕ} (M : MarkedIdeal n X)
    (hM : IsInvDomain k M) {e : ℕ} (he : 1≤e) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) :
    ∀j : ℕ,
      let P:=BlowupTowerSplit.head T j
      let A:=geoTransformAlong M P
      let B:=geoTransformAlong (powerMarked M e) P
      IsGeoTestTower M P ∧ IsGeoTestTower (powerMarked M e) P ∧
        RestrictEquiv B (powerMarked A e) ∧ B.N=A.N ∧ B.E=A.E ∧ B.d=M.d*e ∧
        restrictOn n A.N B.ideal=restrictOn n A.N (idealPow A.ideal e) ∧
        B.cosupp=A.cosupp ∧ B.E.length=M.E.length+P.length := by
  intro j
  let P:=BlowupTowerSplit.head T j
  have hP:=((BlowupTowerSplit.isGeoTestTower_iff_head_tail M T j).mp hT).1
  have hCurrent:=InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hP
  obtain ⟨hPower,hEq⟩:=original_power_transform M hM e he P hP
  have hN : (geoTransformAlong (powerMarked M e) P).N=(geoTransformAlong M P).N:=hEq.N_eq
  refine ⟨hP,hPower,hEq,hEq.N_eq,hEq.E_eq,?_,?_,?_,?_⟩
  · exact d_geoTransformAlong (powerMarked M e) P
  · apply restrictOn_eq_of_restrictLe hCurrent.isWellFormed.isClosedSubmanifold_N.1
    · rw [←hN]
      exact hEq.le
    · rw [←hN]
      exact hEq.ge
  · exact hEq.cosupp_eq.trans
      (powerMarked_cosupp (geoTransformAlong M P) hCurrent he)
  · rw [hEq.E_eq]
    exact length_E_geoTransformAlong M P

end
end Hironaka.HironakaActualOriginalPowerTransform
