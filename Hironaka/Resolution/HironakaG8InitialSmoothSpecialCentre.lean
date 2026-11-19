import Hironaka.Resolution.HironakaG8ChronologicalRestartObstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace

namespace Hironaka.HironakaG8InitialSmoothSpecialCentre
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime BoundaryCount
  GeneralValue GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  CompanionRebase CompanionReductionAlong MarkedIdealBiholomorphism
  MonomialPartAlong RestrictLeCalculus MarkedIdealOperationsAlong.MarkedIdeal
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan CodimOneSupportAlong HironakaEmbeddedAnalytic RestrictedIdealExtension GermIdealPullbackCalculus

set_option maxHeartbeats 2200000 in
/-- For a boundary-free initial canonical evaluation with a uniform
positive order on its cosupport, a special actual masked companion
point is a global maximum of the original evaluator. -/
theorem initial_special_companion_is_original_maximum
    {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (hE : M.E = [])
    (o : ℕ) (ho : 0 < o) (hOrd : ∀ y ∈ M.cosupp, nmOrd M y = o)
    (x : X) (hx : x ∈ M.cosupp) (hp : x ∈ ordMask M o)
    (hSpecial : IsSpecial (compAt M o (.refl : BlowupTower X X))
      (.refl : BlowupTower (CMfd.of (n := n) (ordMask M o)) _) ⟨x,hp⟩) :
    x ∈ maxLocus ((invFamily hn (k+1)).inv M (.refl : BlowupTower X X)) M.cosupp := by
  let O := ordMask M o
  let R := invFamily hn k
  let F : ∀ {A : CMfd.{0} n}, MarkedIdeal n A → ∀ {B : CMfd.{0} n},
      BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy k) :=
    fun {_} J {_} T z => Seq.StepOneValueMasked.stepOneInvM R J T z
  let I : BlowupTower X X := .refl
  let C := compAt M o I
  let S : BlowupTower (CMfd.of (n := n) O) (CMfd.of (n := n) O) := .refl
  have hCE : C.E = [] := by
    change (companionOf n (M := CMfd.of (n := n) O) (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) M) o).E = []
    simp only [companionOf, companionAlong_E, MarkedIdealBiholomorphism.MarkedIdeal.pullback, hE, List.map_nil]
  have hLevel (z : O) : level C S z = 0 := by
    have hO : origMembers C S = [] := by simp [origMembers, hCE]
    rw [level, hO]
    simp [boundaryCount]
  have hTop : F C S ⟨x,hp⟩ = toLex (0,(⊤ : WithTop (ValTy k))) := by
    change Seq.StepOneValueMasked.stepOneInvL R C (lowerMarkedM C) S ⟨x,hp⟩ = _
    rw [Seq.StepOneValueMasked.stepOneInvL_of_isSpecial R C (lowerMarkedM C) S hSpecial, hLevel]
  have hRead (y : X) (hy : y ∈ M.cosupp) (hyO : y ∈ O) :
      (invFamily hn (k+1)).inv M I y =
        toLex (o,toLex (Sum.inr (F C S ⟨y,hyO⟩ : WithTop (ℕ ×ₗ WithTop (ValTy k))))) := by
    change genInv F M I y = _
    have hor : nmOrd (geoTransformAlong M I) y = o := hOrd y hy
    rw [genInv_of_nmOrd_ne_zero F M I hor (Nat.ne_of_gt ho)]
    change toLex (o,toLex (Sum.inr (genLowerValue F M o I I y))) = _
    rw [genLowerValue_eq_of_mem F M (T₀ := I) (T₁ := I) (y := y) hyO]
    rfl
  refine ⟨hx, fun y hy => ?_⟩
  have hyO : y ∈ O := by
    apply (mem_ordMask_iff hn hM.isWellFormed hM.isNonzeroAlongAt o y).mpr
    intro hBad
    have hOrdGe := (mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hy.1 (o+1)).mp hBad
    rw [hOrd y hy] at hOrdGe
    omega
  rw [hRead x hx hp, hRead y hy hyO, hTop]
  have hFst : (ofLex (F C S ⟨y,hyO⟩)).1 = 0 := by
    exact (Seq.StepOneValueMasked.stepOneInvL_fst R C (lowerMarkedM C) S ⟨y,hyO⟩).trans (hLevel _)
  have hLe : F C S ⟨y,hyO⟩ ≤ toLex (0,(⊤ : WithTop (ValTy k))) := by
    rw [← toLex_ofLex (F C S ⟨y,hyO⟩), Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨hFst,le_top⟩
  exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, by simpa using WithTop.coe_le_coe.mpr hLe⟩)

set_option maxHeartbeats 2300000 in
/-- A regular hypersurface point of the boundary-free original mark-one
cosupport is a global first maximizer when its nonmonomial order is
uniformly one. The special top is on the actual masked companion. -/
theorem initial_regular_hypersurface_is_original_maximum
    {n k : ℕ} (hn : 0<n) {X : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (hE : M.E = []) (hd : M.d = 1)
    (hOrd : ∀ y ∈ M.cosupp, nmOrd M y = 1)
    {j : ℕ} (x : X) (hN : RegularAtDim (n := n) M.N x (j+1))
    (hS : RegularAtDim (n := n) M.cosupp x j) :
    x ∈ maxLocus ((invFamily hn (k+1)).inv M (.refl : BlowupTower X X)) M.cosupp := by
  let O := ordMask M 1
  let X' := CMfd.of (n := n) O
  have hp : x ∈ O := by
    apply (mem_ordMask_iff hn hM.isWellFormed hM.isNonzeroAlongAt 1 x).mpr
    intro hBad
    have h := (mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hN.2.1 2).mp hBad
    rw [hOrd x hS.2.1] at h
    omega
  let z : X' := ⟨x,hp⟩
  let P : MarkedIdeal n X' := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) M
  let C := compAt M 1 (.refl : BlowupTower X X)
  have hPD := InvDomainTowerAlong.isInvDomain_pullback_val O hM
  have hPE : P.E = [] := by
    change M.E.map _ = []
    rw [hE,List.map_nil]
  have hPd : P.d = 1 := hd
  have hEq : RestrictEquiv C P := by
    change RestrictEquiv (companionAlong (X := X') P.N P.E
      (nonmonomialPartAlong n P.N P.ideal P.E)
      (monomialPartAlong n P.N P.ideal P.E) 1 P.d) P
    rw [companionAlong, hPd, if_neg (Nat.lt_irrefl 1)]
    have hNon : nonmonomialPartAlong n P.N P.ideal P.E = restrictOn n P.N P.ideal := by
      rw [hPE]
      exact nonmonomialPartAlong_nil_eq_restrictOn (X := X') P.N P.ideal
    rw [hNon]
    exact ⟨rfl,rfl,hPd.symm,restrictLe_restrictOn,
      restrictLe_self_restrictOn hPD.isWellFormed.isCoherent⟩
  have hCD := GeneralCompare.isInvDomain_compAt (X := X) hn (o := 1) le_rfl .refl hM
  have hBCos := StepOneLowerDomain.cosupp_barMarked C hCD.isWellFormed hCD.one_le_d
  have hPCos : P.cosupp = (Subtype.val : O → X) ⁻¹' M.cosupp :=
    MarkedIdealRestrictOpen.cosupp_pullback_val M
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) O
  have hEqCos := hEq.cosupp_eq
  have hzN : RegularAtDim (n := n) (barMarked C).N z (j+1) := by
    change RegularAtDim (n := n) C.N z (j+1)
    rw [hEq.N_eq]
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hN
  have hzS : RegularAtDim (n := n) (barMarked C).cosupp z j := by
    rw [hBCos,hEqCos,hPCos]
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hS
  have hCE : C.E = [] := hEq.E_eq.trans hPE
  have hL : level C (.refl : BlowupTower X' X') z = 0 := by
    have hOrig : origMembers C (.refl : BlowupTower X' X') = [] := by simp [origMembers,hCE]
    rw [level,hOrig]
    simp [boundaryCount]
  have hs : IsSpecial C (.refl : BlowupTower X' X') z :=
    Or.inl ⟨hL,j,hzN,hzS⟩
  exact initial_special_companion_is_original_maximum hn M hM hE 1 Nat.zero_lt_one
    hOrd x hS.2.1 hp hs

set_option maxHeartbeats 2300000 in
/-- For a boundary-free maximal mark-one source, a genuine regular
hypersurface point of the actual cosupport is an original first
maximizer. Every occupied original canonical first centre contains it. -/
theorem initial_regular_hypersurface_in_canonical_centre
    {n k : ℕ} (hn : 0<n) {X Z : CMfd.{0} n} (M : MarkedIdeal n X)
    (hM : IsInvDomain (k+1) M) (hE : M.E = []) (hd : M.d = 1)
    (hOrd : ∀ y ∈ M.cosupp, nmOrd M y = 1)
    {j : ℕ} (x : X) (hN : RegularAtDim (n := n) M.N x (j+1))
    (hS : RegularAtDim (n := n) M.cosupp x j)
    (D : Set X) (hD : D.Nonempty) (π : Z → X) (hπ : IsBlowupAlong n D π)
    (hCan : IsCanonical M ((invFamily hn (k+1)).inv M) (.step .refl D π hπ)) : x ∈ D := by
  have hMax := initial_regular_hypersurface_is_original_maximum hn M hM hE hd hOrd x hN hS
  have hCentre := hCan.2.resolve_left hD.ne_empty
  change D = maxLocus ((invFamily hn (k+1)).inv M (.refl : BlowupTower X X)) M.cosupp at hCentre
  exact hCentre.symm ▸ hMax

end
end Hironaka.HironakaG8InitialSmoothSpecialCentre
