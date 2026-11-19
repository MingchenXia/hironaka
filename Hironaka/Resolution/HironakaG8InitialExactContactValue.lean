import Hironaka.Resolution.HironakaDisjointCoherentNormalRecoding
import Hironaka.Resolution.HironakaG3CanonicalZeroContactChoice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8InitialExactContactValue

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealOperationsAlong.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneRegime StepOneValueMasked StepOneLowerDomain ContactStageKept TangentDirectionAlong
  GeneralValue NonmonomialOrderLocal NonmonomialOrderTail CompanionReductionAlong
  HironakaSharpOriginalProductTraceOrder RestrictedIdealExtension
  RelativePrincipalizationSpan GermIdealPullbackCalculus MonomialPartAlong HomogenizedIdealAlong

/-- Insert the fixed-contact value after the initial ordinary order and
zero boundary level. -/
def initialContactValue (n d : ℕ) (v : ValTy n) : ValTy (n+1) :=
  toLex (d, Sum.inrₗ (↑(toLex (0, (↑v : WithTop (ValTy n)))) :
    WithTop (ℕ ×ₗ WithTop (ValTy n))))

theorem initialContactValue_strictMono (n d : ℕ) : StrictMono (initialContactValue n d) := by
  intro a b hab
  change toLex (d, Sum.inrₗ (↑(toLex (0, (↑a : WithTop (ValTy n)))) :
      WithTop (ℕ ×ₗ WithTop (ValTy n)))) <
    toLex (d, Sum.inrₗ (↑(toLex (0, (↑b : WithTop (ValTy n)))) :
      WithTop (ℕ ×ₗ WithTop (ValTy n))))
  apply Prod.Lex.toLex_lt_toLex.mpr
  exact Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr
    (WithTop.coe_lt_coe.mpr (Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr hab⟩)))⟩

/-- The original initial value at an empty-boundary maximal-order point
reads the exact original predecessor value of any valid fixed contact. -/
theorem original_initial_value_of_fixed_contact {n : ℕ} {X : CMfd.{0} (n+1)}
    (M : MarkedIdeal (n+1) X) (hM : IsInvDomain (n+1) M)
    (hE : M.E = []) (hMax : IsMaximalOrderAlong M.N M.ideal M.d)
    (x : X) (hx : x ∈ M.cosupp)
    (hSpecial : ¬ IsSpecial M (.refl : BlowupTower X X) x)
    (w : X → ℂ) (V : Set X) (O : Opens X)
    (hw : IsTangentDirectionAlong M.N M.ideal M.d V w) (hOV : (O : Set X) ⊆ V) (hxO : x ∈ O)
    (hD : IsInvDomain n (contactMarkedKept M w (.refl : BlowupTower X X) O)) :
    let R := invFamily (Nat.succ_pos n) n
    let L := contactMarkedKept M w (.refl : BlowupTower X X) O
    (canonicalInvariant (n+1)).inv M (.refl : BlowupTower X X) x =
      initialContactValue n M.d
        (R.inv L (.refl : BlowupTower (CMfd.of (n := n+1) O) _) ⟨x,hxO⟩) := by
  intro R L
  have hThreshold (q : ℕ) : ordGe M q = GermIdealOrder.cosupport (n+1) M.N M.ideal q := by
    change GermIdealOrder.cosupport (n+1) M.N (nonmonomialPartAlong (n+1) M.N M.ideal M.E) q = _
    rw [hE]
    exact ordGe_ordinaryTraceMarked_eq_cosupport (X := X) M.N M.ideal hM.isWellFormed.isCoherent q
  have hEmpty : ordGe M (M.d+1) = ∅ := by
    rw [hThreshold]
    exact eq_empty_of_forall_notMem hMax
  have hMask : x ∈ ordMask M M.d := by
    change x ∈ (closure (ordGe M (M.d+1)))ᶜ
    simp only [hEmpty, closure_empty, compl_empty, mem_univ]
  have hOrd : nmOrd M x = M.d := by
    have hQ (q : ℕ) := mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt hx.1 q
    have hLower := (hQ M.d).mp (hThreshold M.d ▸ hx)
    have hUpper : ¬ M.d+1 ≤ nmOrd M x :=
      fun h => notMem_empty x (hEmpty ▸ (hQ (M.d+1)).mpr h)
    omega
  let d := M.d
  let F := fun {A : CMfd (n+1)} (K : MarkedIdeal (n+1) A) {B : CMfd (n+1)}
    (T : BlowupTower A B) (y : B) => Seq.StepOneValueMasked.stepOneInvM R K T y
  let A := ordMask M d
  let C : MarkedIdeal (n+1) A := compAt M d (.refl : BlowupTower X X)
  let P := MarkedIdeal.pullback (Subtype.val : A → X) M
  let p : A := ⟨x,hMask⟩
  have hC : IsInvDomain (n+1) C := GeneralCompare.isInvDomain_compAt (X := X)
    (Nat.succ_pos n) hM.one_le_d .refl hM
  have hCM : IsMaximalOrderAlong C.N C.ideal C.d :=
    GeneralCompare.isMaximalOrderAlong_compAt (X := X) (Nat.succ_pos n) d .refl hM
  have hP : IsInvDomain (n+1) P := InvDomainTowerAlong.isInvDomain_pullback_val A hM
  obtain ⟨_,_,hPM,_⟩ := StepOneRestrictOpen.hypotheses_restrict M A
    hM.isWellFormed hM.one_le_d hMax hM.dimLE
  have hPE : P.E = [] := by
    change M.E.map _ = []
    rw [hE,List.map_nil]
  have hEq : RestrictEquiv C P := by
    change RestrictEquiv (companionAlong (X := CMfd.of (n := n+1) A) P.N P.E
      (nonmonomialPartAlong (n+1) P.N P.ideal P.E)
      (monomialPartAlong (n+1) P.N P.ideal P.E) d P.d) P
    have hPd : P.d = d := rfl
    rw [companionAlong, hPd, if_neg (Nat.lt_irrefl d)]
    have hNon : nonmonomialPartAlong (n+1) P.N P.ideal P.E = restrictOn (n+1) P.N P.ideal := by
      rw [hPE]
      exact nonmonomialPartAlong_nil_eq_restrictOn (X := CMfd.of (n := n+1) A) P.N P.ideal
    rw [hNon]
    exact ⟨rfl,rfl,hPd.symm,restrictLe_restrictOn,
      restrictLe_self_restrictOn hP.isWellFormed.isCoherent⟩
  have hpP : p ∈ P.cosupp := by
    change p ∈ (MarkedIdeal.pullback (Subtype.val : A → X) M).cosupp
    rw [MarkedIdealRestrictOpen.cosupp_pullback_val M
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hM.isWellFormed.isCoherent) A]
    exact hx
  have hpC : p ∈ C.cosupp := hEq.cosupp_eq.symm ▸ hpP
  have hF := StepOneSeq.isMaxOrderValue_stepOneInvM (k := n+1) R (Nat.succ_pos n)
  have hRep := hF.representative (X := CMfd.of (n := n+1) A) C P hC hCM hP hPM
    hEq .refl trivial p hpC
  have hRest := hF.restrictOpen M hM hMax A (.refl : BlowupTower X X) trivial p hx
  have hbar : x ∈ (barMarked M).cosupp := by
    rw [cosupp_barMarked (𝔍 := M) hM.isWellFormed hM.one_le_d]
    exact hx
  have hLevel : level M (.refl : BlowupTower X X) x = 0 := by
    rw [level, origMembers, hE]
    rfl
  have hData := Seq.StepOneCanonicalTail.lowerDataL_refl M (k := n+1) R
    hM.isWellFormed hM.one_le_d (Nat.succ_pos n) hMax hM.dimLE .refl trivial hbar ⟨hLevel,hSpecial⟩
  have hAnchor := Seq.ContactLowerValue.lowerValueL_zero_eq R M hM.isWellFormed
    hM.one_le_d .refl .refl trivial hw O hOV
    (by intro H hH; simp only [origMembers, hE, List.length_nil, List.take_zero, List.not_mem_nil] at hH)
    hD trivial hxO hbar hData
  have hContact : F M (.refl : BlowupTower X X) x =
      toLex (0, (↑(R.inv L (.refl : BlowupTower (CMfd.of (n := n+1) O) _) ⟨x,hxO⟩) : WithTop (ValTy n))) := by
    change Seq.StepOneValueMasked.stepOneInvM R M (.refl : BlowupTower X X) x = _
    simp only [Seq.StepOneValueMasked.stepOneInvM, Seq.StepOneValueMasked.stepOneInvL,
      hSpecial, if_false, hLevel]
    change toLex (0, Seq.StepOneValueMasked.lowerValueL R M _ 0 .refl .refl x) = _
    rw [hAnchor]
    rfl
  change genInv F M (.refl : BlowupTower X X) x = _
  rw [genInv_of_nmOrd_ne_zero F M .refl hOrd (Nat.ne_of_gt hM.one_le_d)]
  change toLex (d, Sum.inrₗ (genLowerValue F M d .refl .refl x)) = _
  have hGen := genLowerValue_eq_of_mem (X := X) (T₀ := .refl) (T₁ := .refl) (y := x) F M hMask
  change genLowerValue F M d .refl .refl x = (↑(F C
    (.refl : BlowupTower (CMfd.of (n := n+1) A) _) p) : WithTop (ℕ ×ₗ WithTop (ValTy n))) at hGen
  change F C (.refl : BlowupTower (CMfd.of (n := n+1) A) _) p =
    F P (.refl : BlowupTower (CMfd.of (n := n+1) A) _) p at hRep
  change F P (.refl : BlowupTower (CMfd.of (n := n+1) A) _) p = F M (.refl : BlowupTower X X) x at hRest
  rw [hGen,hRep,hRest,hContact]
  rfl

/-- The actual twice-applied coefficient mark stays two for a mark-two
companion, on any fixed initial contact window. -/
theorem initial_contact_mark_two {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (h : M.d = 2) (w : X → ℂ) (O : Opens X) :
    (contactMarkedKept M w (.refl : BlowupTower X X) O).d = 2 := by
  change (coeffMarkedAlong (coeffMarkedAlong (homMarkedAlong M))).d = 2
  have hHom : (homMarkedAlong M).d = 2 := h
  have hBar : (coeffMarkedAlong (homMarkedAlong M)).d = 2 := by
    rw [coeffMarkedAlong_d (by rw [hHom]; decide), hHom]
    decide
  rw [coeffMarkedAlong_d (by rw [hBar]; decide), hBar]
  decide


/-- At positive recursive depth, a strict first-order difference of two
actual lower records is already strict in their original values. -/
theorem initial_lower_value_lt_of_nmOrd_lt {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (A : MarkedIdeal n X) (B : MarkedIdeal n Y) (x : X) (y : Y)
    (h : nmOrd A x < nmOrd B y) :
    (invFamily hn (k+1)).inv A (.refl : BlowupTower X X) x <
      (invFamily hn (k+1)).inv B (.refl : BlowupTower Y Y) y := by
  simp only [invFamily_succ, generalStep_inv, genInv, geoTransformAlong_refl]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end Hironaka.HironakaG8InitialExactContactValue
