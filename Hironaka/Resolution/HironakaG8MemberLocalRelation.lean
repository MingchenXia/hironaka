import Hironaka.Resolution.HironakaG8LocalContact
import Hironaka.Resolution.HironakaG8ClassStepCut
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8MemberLocalRelation
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealAlongRestrictionTower DerivativeIdealAlong DerivativeIdealAlongCoherent RestrictedIdealWeight
  RestrictLeCalculus BlowupStrictSubmanifold BlowupFunctionTransform MarkedIdealBiholomorphism
  HironakaG8ContactGood HironakaG8ContactMax HironakaG8LocalHistory HironakaG8LocalStable HironakaG8LocalContact
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open scoped ProductComplexManifold
noncomputable section
section Rel
variable {m : ℕ} {Y : CMfd.{u} m}
structure MemberRel (P Q : MarkedIdeal m Y) (F : ℕ → MarkedIdeal m Y) (S : Set Y) : Prop where
  closed : IsClosedSubmanifold m P.N
  coh : P.ideal.IsCoherent
  d_pos : 1 ≤ P.d
  fN : ∀ i < P.d, (F i).N = P.N
  fE : ∀ i < P.d, (F i).E = P.E
  fd : ∀ i < P.d, (F i).d = P.d - i
  fcoh : ∀ i < P.d, (F i).ideal.IsCoherent
  fle : ∀ i < P.d, RestrictLe P.N (F i).ideal (iterDerivIdealAlong P.N P.ideal i)
  sub : IsClosedSubmanifold m S
  SN : S ⊆ P.N
  good : ∀ p ∈ S, GoodAt P F S p
  qcoh : Q.ideal.IsCoherent
  equiv : RestrictEquiv Q (withN (msum F P.d) S)

namespace MemberRel

variable {P Q : MarkedIdeal m Y} {F : ℕ → MarkedIdeal m Y} {S : Set Y}

/-- The family `F` is a family on the closed submanifold `P.N`. -/
theorem fam (h : MemberRel P Q F S) : IsSubmanifoldFamily F P.d where
  N i hi := by rw [h.fN i hi, h.fN 0 h.d_pos]
  E i hi := by rw [h.fE i hi, h.fE 0 h.d_pos]
  closed := by rw [h.fN 0 h.d_pos]; exact h.closed
  coh := h.fcoh
  d i hi := by rw [h.fd i hi]; omega

/-- The same boundary. -/
theorem E_eq (h : MemberRel P Q F S) : Q.E = P.E := by
  rw [h.equiv.E_eq]
  exact h.fE 0 h.d_pos

/-- The cosupport of `P` lies in that of each `F i` (Giraud along `N`). -/
theorem cosupp_subset_F (h : MemberRel P Q F S) {i : ℕ} (hi : i < P.d) : P.cosupp ⊆ (F i).cosupp := by
  intro x hx
  have h1 : x ∈ cosupport m P.N P.ideal ((P.d - i) + i) := by rw [Nat.sub_add_cancel hi.le]; exact hx
  have h2 := TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent h.coh)
    (P.d - i) i h1
  have h3 := cosupport_subset_of_restrictLe (h.fle i hi) _ h2
  show x ∈ cosupport m (F i).N (F i).ideal (F i).d
  rw [h.fN i hi, h.fd i hi]
  exact h3

/-- **The same cosupport** (`le:Giraud` and `le:S` (2) at a stage): `cosupp P = cosupp Q`. -/
theorem cosupp_eq (h : MemberRel P Q F S) : P.cosupp ∩ S = Q.cosupp := by
  rw [h.equiv.cosupp_eq, cosupp_withN]
  have hfam := h.fam
  have hm := h.d_pos
  ext x
  constructor
  · intro hx
    have hxS : x ∈ S := hx.2
    have hK : x ∈ (msum F P.d).cosupp := by
      rw [cosupp_msum_along hfam hm]
      exact fun i hi => h.cosupp_subset_F hi hx.1
    have hSK : S ⊆ (msum F P.d).N := by
      show S ⊆ (F 0).N
      rw [h.fN 0 hm]
      exact h.SN
    exact CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSK _ _ ⟨hK, hxS⟩
  · intro hx
    have hxS : x ∈ S := hx.1
    have hJ : ∀ i < P.d, ∀ y g, (idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)).mem y g →
        HolomorphicAt m g y := fun _ _ _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg
    have hx' : x ∈ cosupport m S (finSumIdeal (fun i => idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)) P.d)
        (msum F P.d).d := hx
    have hD : ∀ i < P.d, OrderGE m S (F i).ideal x (P.d - i) := by
      intro i hi
      have hx3 := ((mem_cosupport_finSumIdeal hJ).mp hx').2 i hi
      have hpow := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along h.sub.2
        (hol_of_isCoherent (h.fcoh i hi)) (one_le_sumExp (fun j hj => hfam.d j hj) i) (F i).d
      have hmark : (msum F P.d).d = (F i).d * sumExp (fun j => (F j).d) P.d i :=
        (mul_sumExp (fun j => (F j).d) hi).symm
      rw [hmark, hpow, h.fd i hi] at hx3
      exact hx3.2
    exact ⟨⟨h.SN hxS, (h.good x hxS).orderGE h.coh hD⟩, hxS⟩

/-- **One admissible blowup.** -/
theorem geoTransform (h : MemberRel P Q F S) {C : Set Y} {Z : CMfd.{u} m} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hC : P.IsAdmissibleCentre C) (hCS : C ⊆ S) :
    MemberRel (P.geoTransform C π) (Q.geoTransform C π) (fun i => (F i).geoTransform C π)
      (geoStrictTransform π C S) := by
  have hm := h.d_pos
  have hfam := h.fam
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hCF : ∀ i < P.d, (F i).IsAdmissibleCentre C := fun i hi =>
    ⟨hC.1, fun x hx => h.cosupp_subset_F hi (hC.2.1 hx), by rw [h.fE i hi]; exact hC.2.2⟩
  have hFN : ∀ i < P.d, IsClosedSubmanifold m (F i).N := fun i hi => by rw [h.fN i hi]; exact h.closed
  have hKN : (msum F P.d).N = P.N := h.fN 0 hm
  have hKcoh : (msum F P.d).ideal.IsCoherent := hfam.isCoherent_msum
  have hCK : (msum F P.d).IsAdmissibleCentre C := (isAdmissibleCentre_msum_along_iff hfam hm).mpr hCF
  have hSK : S ⊆ (msum F P.d).N := by rw [hKN]; exact h.SN
  have hCKS : (withN (msum F P.d) S).IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSK _ _
      ⟨hCK.2.1 hx, hCS hx⟩, hCK.2.2⟩
  have hQeq : Q.geoTransform C π = (withN (msum F P.d) S).geoTransform C π :=
    h.equiv.geoTransform_eq (by rw [h.equiv.N_eq]; exact h.sub.1) h.qcoh hKcoh hπ.contMDiff
  refine ⟨isClosedSubmanifold_geoTransform_N h.closed hC hπ,
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre h.closed h.coh hC hπ, hm,
    fun i hi => by simp only [geoTransform_N, h.fN i hi], fun i hi => by simp only [geoTransform_E, h.fE i hi],
    fun i hi => h.fd i hi,
    fun i hi => HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hFN i hi) (h.fcoh i hi)
      (hCF i hi) hπ,
    ?_, BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ h.sub hCS,
    geoStrictTransform_mono' π C h.SN, ?_, ?_, ?_⟩
  · -- the derivative inclusions (Giraud along `N`, monotonicity of the transform)
    intro i hi
    replace hi : i < P.d := hi
    have hCD' : (derivMarkedAlong P i).IsAdmissibleCentre C := by
      refine ⟨hC.1, fun y hy => ?_, hC.2.2⟩
      have h1 : y ∈ cosupport m P.N P.ideal ((P.d - i) + i) := by
        rw [Nat.sub_add_cancel hi.le]; exact hC.2.1 hy
      exact TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent h.coh)
        (P.d - i) i h1
    have h1 := restrictLe_geoTransform_of_restrictLe (𝔫₁ := F i) (𝔫₂ := derivMarkedAlong P i) (hFN i hi)
      (h.fN i hi) (h.fd i hi) (h.fcoh i hi) (isCoherent_iterDerivIdealAlong h.coh h.closed i) (hCF i hi) hCD' hπ
      (by rw [h.fN i hi]; exact h.fle i hi)
    have h2 := DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong P h.closed h.coh hC hπ
      (j := i) hi.le
    have hW : ((F i).geoTransform C π).N = geoStrictTransform π C P.N := by rw [geoTransform_N, h.fN i hi]
    rw [hW] at h1
    exact RestrictLe.trans h1 h2
  · -- every point of `S'` is good
    intro z hz
    have hpz : π z ∈ S := geoStrictTransform_subset_preimage hπc h.sub.1 hz
    by_cases hzC : π z ∈ C
    · exact goodAt_step_of_mem P F hπ h.closed h.coh h.fN h.fd h.fcoh hC hCF h.sub.1 h.SN hCS hz hzC (h.good _ hpz)
    · exact goodAt_step_of_notMem P F hπ h.closed.1 h.coh h.fcoh h.sub.1 hzC (h.good _ hpz)
  · rw [hQeq]
    exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := withN (msum F P.d) S) h.sub
      hKcoh hCKS hπ
  · rw [hQeq]
    have e1 := geoTransform_withN_restrictEquiv_along (𝔟 := msum F P.d) (by rw [hKN]; exact h.closed) hKcoh h.sub hSK
      hπ hCK hCKS
    have e2 := geoTransform_msum_restrictEquiv hfam hm hπ hCF
    have hS'sub : geoStrictTransform π C S ⊆ ((msum F P.d).geoTransform C π).N := geoStrictTransform_mono' π C hSK
    have e3 : RestrictEquiv (withN ((msum F P.d).geoTransform C π) (geoStrictTransform π C S))
        (withN (msum (fun i => (F i).geoTransform C π) P.d) (geoStrictTransform π C S)) :=
      ⟨rfl, e2.E_eq, e2.d_eq, restrictLe_mono hS'sub e2.le, restrictLe_mono hS'sub e2.ge⟩
    exact restrictEquiv_trans e1 e3

end MemberRel

end Rel

/-! ### Pullback along a holomorphic submersion -/

section Pullback

variable {n r : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} (n + r)} {f : Y' → Y}

/-- **Pullback along a holomorphic submersion** `f : Y' → Y` (`dim Y' = n + r`): the pulled-back data (any boundaries,
with `F' i` and `Q'` on the boundary of `P'`) are again related. -/
theorem MemberRel.pullback (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    {P Q : MarkedIdeal n Y} {F : ℕ → MarkedIdeal n Y} {S : Set Y} (h : MemberRel P Q F S)
    {P' Q' : MarkedIdeal (n + r) Y'} {F' : ℕ → MarkedIdeal (n + r) Y'}
    (hPN : P'.N = f ⁻¹' P.N) (hPI : P'.ideal = GermIdeal.pullback (m := n + r) f P.ideal) (hPd : P'.d = P.d)
    (hFN : ∀ i, (F' i).N = f ⁻¹' (F i).N) (hFE : ∀ i < P.d, (F' i).E = P'.E)
    (hFI : ∀ i, (F' i).ideal = GermIdeal.pullback (m := n + r) f (F i).ideal) (hFd : ∀ i, (F' i).d = (F i).d)
    (hQN : Q'.N = f ⁻¹' Q.N) (hQE : Q'.E = P'.E) (hQI : Q'.ideal = GermIdeal.pullback (m := n + r) f Q.ideal)
    (hQd : Q'.d = Q.d) : MemberRel P' Q' F' (f ⁻¹' S) := by
  have hfc := hf.contMDiff
  have hm := h.d_pos
  have hfam := h.fam
  have hKcoh : (msum F P.d).ideal.IsCoherent := hfam.isCoherent_msum
  have hI : (msum F' P'.d).ideal = GermIdeal.pullback (m := n + r) f (msum F P.d).ideal := by
    show finSumIdeal (fun i => idealPow (F' i).ideal (sumExp (fun j => (F' j).d) P'.d i)) P'.d =
      GermIdeal.pullback (m := n + r) f
        (finSumIdeal (fun i => idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)) P.d)
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal hfc _ _
      (fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.fcoh i hi) _), hPd]
    refine finSumIdeal_congr fun i hi => ?_
    rw [hFI i, HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hfc (h.fcoh i hi)]
    simp only [hFd]
  refine ⟨?_, ?_, by rw [hPd]; exact hm, fun i hi => ?_, fun i hi => hFE i (by rw [← hPd]; exact hi),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf h.sub, ?_,
    fun p hp => goodAt_pullback_submersion hf hPN hPI hPd (fun i _ => hFI i) h.coh h.fcoh (h.good _ hp), ?_, ?_⟩
  · rw [hPN]; exact HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf h.closed
  · rw [hPI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc h.coh
  · rw [hPd] at hi; rw [hFN, hPN, h.fN i hi]
  · rw [hPd] at hi ⊢; rw [hFd, h.fd i hi]
  · rw [hPd] at hi; rw [hFI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc (h.fcoh i hi)
  · rw [hPd] at hi
    rw [hFI, hPN, hPI, ← HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong hf P.ideal
      h.coh P.N h.closed i]
    exact restrictLe_pullback_map hfc (fun y hy => hy) (isCoherent_iterDerivIdealAlong h.coh h.closed i) (h.fle i hi)
  · rw [hPN]; exact preimage_mono h.SN
  · rw [hQI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc h.qcoh
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hQN, h.equiv.N_eq]; rfl
    · show Q'.E = (F' 0).E
      rw [hQE, hFE 0 hm]
    · show Q'.d = (Finset.range P'.d).prod fun j => (F' j).d
      rw [hQd, h.equiv.d_eq, hPd]
      show ((Finset.range P.d).prod fun j => (F j).d) = (Finset.range P.d).prod fun j => (F' j).d
      simp only [hFd]
    · show RestrictLe Q'.N Q'.ideal (msum F' P'.d).ideal
      rw [hI, hQI, hQN]
      exact restrictLe_pullback_map hfc (fun y hy => hy) hKcoh h.equiv.le
    · show RestrictLe Q'.N (msum F' P'.d).ideal Q'.ideal
      rw [hI, hQI, hQN]
      exact restrictLe_pullback_map hfc (fun y hy => hy) h.qcoh h.equiv.ge

end Pullback

 theorem memberRel_base {n : ℕ} {X : CMfd.{u} n} (P : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n P.N) (hI : P.ideal.IsCoherent) (hd : 1 ≤ P.d)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSN : S ⊆ P.N) :
    MemberRel P (withN (coeffMarkedAlong P) S) (fun i => derivMarkedAlong P i) S := by
  exact ⟨hN, hI, hd, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun i _ => isCoherent_iterDerivIdealAlong hI hN i,
    fun i _ => restrictLe_refl (isCoherent_iterDerivIdealAlong hI hN i), hS, hSN,
    fun p hp => goodAt_base P hN hI hS hSN hp, isCoherent_coeffMarkedAlong hI hN,
    RestrictEquiv.refl (isCoherent_coeffMarkedAlong hI hN)⟩

end
end Hironaka.HironakaG8MemberLocalRelation
