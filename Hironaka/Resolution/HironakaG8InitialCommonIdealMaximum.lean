import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked

/-! The original initial maximum survives a change of mark on the same
boundary-free ideal, up to its attained top ordinary order. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8InitialCommonIdealMaximum

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  CompanionRebase CompanionReductionAlong GeneralValue StepOneRegime
  HironakaSharpOriginalProductTraceOrder HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression

variable {n : ℕ} {X : CMfd.{0} (n+1)}

private abbrev record (I : GermIdeal (n+1) X) (d : ℕ) : MarkedIdeal (n+1) X :=
  ⟨univ,[],I,d⟩

/-- On the positive order stratum at or above both marks, the original
initial values of the two records agree, using the literal same companion. -/
theorem initial_value_eq_of_common_ideal
    (I : GermIdeal (n+1) X) {d e o : ℕ} (hd : d ≤ o) (he : e ≤ o)
    (ho : o ≠ 0) {x : X} (hx : nmOrd (record I d) x = o) :
    (canonicalInvariant (n+1)).inv (record I d) .refl x =
      (canonicalInvariant (n+1)).inv (record I e) .refl x := by
  let P := record I d
  let Q := record I e
  have hxQ : nmOrd Q x = o := hx
  change genInv _ P .refl x = genInv _ Q .refl x
  rw [genInv_of_nmOrd_ne_zero _ P .refl hx ho,genInv_of_nmOrd_ne_zero _ Q .refl hxQ ho]
  simp only [regimeRun_refl]
  have hComp : compAt P o .refl = compAt Q o .refl := by
    change companionAlong _ _ _ _ o d = companionAlong _ _ _ _ o e
    unfold companionAlong
    rw [if_neg (Nat.not_lt.mpr hd),if_neg (Nat.not_lt.mpr he)]
    rfl
  let F : ∀ {A : CMfd.{0} (n+1)}, MarkedIdeal (n+1) A →
      ∀ {B : CMfd.{0} (n+1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy n) :=
    fun {_} M {_} T y => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) n) M T y
  have hLow : genLowerValue F P o .refl .refl x = genLowerValue F Q o .refl .refl x := by
    unfold genLowerValue
    rw [hComp]
    rfl
  exact congrArg (fun w => toLex (o, toLex (Sum.inr w))) hLow

/-- If the top ordinary order is attained, the actual reflexive original
maximum of the mark-one whole record equals that of the top-mark record.
Only the common positive top stratum uses the companion comparison. -/
theorem initial_maxLocus_markOne_eq_topMark
    (I : GermIdeal (n+1) X) (hI : IsInvDomain (n+1) (record I 1))
    {m : ℕ} (hm : 1 ≤ m)
    (hUpper : ∀ x : X, ordinaryTraceOrder univ I x ≤ m)
    (hTop : ∃ x : X, ordinaryTraceOrder univ I x = m) :
    maxLocus ((canonicalInvariant (n+1)).inv (record I 1) .refl) (record I 1).cosupp =
      maxLocus ((canonicalInvariant (n+1)).inv (record I m) .refl) (record I m).cosupp := by
  let P := record I 1
  let Q := record I m
  let o := ordinaryTraceOrder (univ : Set X) I
  let v := (canonicalInvariant (n+1)).inv P (.refl : BlowupTower X X)
  let w := (canonicalInvariant (n+1)).inv Q (.refl : BlowupTower X X)
  have hCos (d : ℕ) (x : X) : x ∈ (record I d).cosupp ↔ d ≤ o x :=
    ordinaryTraceOrder_cosupport_iff hI.isWellFormed.isClosedSubmanifold_N
      hI.isWellFormed.isCoherent hI.isNonzeroAlongAt (mem_univ x) d
  have hValue {x : X} (hx : o x = m) : v x = w x :=
    initial_value_eq_of_common_ideal I hm le_rfl (by omega) hx
  obtain ⟨a,ha⟩ := hTop
  change o a = m at ha
  have haP : a ∈ P.cosupp := (hCos 1 a).mpr (by rw [ha]; exact hm)
  have hlt {z y : X} (h : o z < o y) : v z < v y := by
    change genInv _ P .refl z < genInv _ P .refl y
    exact genInv_lt_of_nmOrd_lt _ P h
  change maxLocus v P.cosupp = maxLocus w Q.cosupp
  ext y
  constructor
  · intro hy
    have hyTop : o y = m := le_antisymm (hUpper y) (by
      by_contra hn
      exact (not_lt_of_ge (hy.2 a haP)) (hlt (by rw [ha]; exact Nat.lt_of_not_ge hn)))
    refine ⟨(hCos m y).mpr (le_of_eq hyTop.symm),fun z hz => ?_⟩
    have hzTop : o z = m := le_antisymm (hUpper z) ((hCos m z).mp hz)
    rw [← hValue hzTop,← hValue hyTop]
    exact hy.2 z ((hCos 1 z).mpr (by rw [hzTop]; exact hm))
  · intro hy
    have hyTop : o y = m := le_antisymm (hUpper y) ((hCos m y).mp hy.1)
    refine ⟨(hCos 1 y).mpr (by rw [hyTop]; exact hm),fun z hz => ?_⟩
    by_cases hzTop : o z = m
    · rw [hValue hzTop,hValue hyTop]
      exact hy.2 z ((hCos m z).mpr (le_of_eq hzTop.symm))
    · exact le_of_lt (hlt (by rw [hyTop]; exact lt_of_le_of_ne (hUpper z) hzTop))

/-- The literal weighted initialization with one actual generator has
that generator's own mark and its unpowered, whole principal ideal. -/
theorem singleton_weighted_initial_record
    {J : Type*} [Fintype J] [Subsingleton J] (i : J)
    (w : J → ℕ) (hw : 0 < w i) (f : J → X → ℂ) :
    (⟨univ, [], weightedFunctionIdeal (n := n+1) w f, weightedCommonMark w⟩ :
      MarkedIdeal (n+1) X) = record (finiteFunctionIdeal (fun _ : Unit => f i)) (w i) := by
  classical
  have hMark : weightedCommonMark w = w i := by
    unfold weightedCommonMark
    have hUniv : (Finset.univ : Finset J) = {i} := by
      ext j
      simp [Subsingleton.elim j i]
    rw [hUniv, Finset.prod_singleton]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ hMark
  unfold weightedFunctionIdeal
  rw [hMark]
  have hp (j : J) : (fun y => f j y ^ (w i / w j)) = f i := by
    rw [Subsingleton.elim j i, Nat.div_self hw]
    funext y
    exact pow_one _
  have hRange : range (fun (j : J) y => f j y ^ (w i / w j)) =
      range (fun _ : Unit => f i) := by
    ext g
    constructor
    · rintro ⟨j,rfl⟩
      exact ⟨(),(hp j).symm⟩
    · rintro ⟨u,rfl⟩
      exact ⟨i,hp i⟩
  ext y g
  change IsInSpanAt (n := n+1) (· ∈ range (fun (j : J) y => f j y ^ (w i / w j))) y g ↔
    IsInSpanAt (n := n+1) (· ∈ range (fun _ : Unit => f i)) y g
  rw [hRange]

/-- A native first blowup on a whole boundary-free record transfers to
the original mark-one vanishing record when its mark bounds the ordinary
order. The nonempty actual centre witnesses attainment. The underlying
ideal equality is an explicit input from the native presentation. -/
theorem initial_whole_markOne_canonical_of_native_same_ideal
    {Y : CMfd.{0} (n+1)} (W : Set X)
    (hW : IsInvDomain (n+1) (record (vanishingIdeal (n := n+1) W) 1))
    (Q : MarkedIdeal (n+1) X) (hN : Q.N = univ) (hE : Q.E = [])
    (hIdeal : Q.ideal = vanishingIdeal (n := n+1) W) (hm : 1 ≤ Q.d)
    (hUpper : ∀ x : X, ordinaryTraceOrder univ (vanishingIdeal (n := n+1) W) x ≤ Q.d)
    (C : Set X) (π : Y → X) (hπ : IsBlowupAlong (n+1) C π)
    (hCan : IsCanonical Q ((canonicalInvariant (n+1)).inv Q) (.step .refl C π hπ)) :
    let P := record (vanishingIdeal (n := n+1) W) 1
    IsCanonical P ((canonicalInvariant (n+1)).inv P) (.step .refl C π hπ) := by
  let I := vanishingIdeal (n := n+1) W
  have hRec : Q = record I Q.d :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of hN hE hIdeal rfl
  refine ⟨trivial,?_⟩
  rcases hCan.2 with hEmpty | hMax
  · exact Or.inl hEmpty
  · by_cases hNonempty : C.Nonempty
    · obtain ⟨a,ha⟩ := hNonempty
      have ha' : a ∈ Q.cosupp := (show a ∈ maxLocus ((canonicalInvariant (n+1)).inv Q .refl)
        Q.cosupp from hMax ▸ ha).1
      have haOrd : Q.d ≤ ordinaryTraceOrder univ I a := by
        apply (ordinaryTraceOrder_cosupport_iff hW.isWellFormed.isClosedSubmanifold_N
          hW.isWellFormed.isCoherent hW.isNonzeroAlongAt (mem_univ a) Q.d).mp
        rw [hRec] at ha'
        exact ha'
      have hTop : ∃ x : X, ordinaryTraceOrder univ I x = Q.d :=
        ⟨a,le_antisymm (hUpper a) haOrd⟩
      have hWhole := initial_maxLocus_markOne_eq_topMark I hW hm hUpper hTop
      change C = maxLocus ((canonicalInvariant (n+1)).inv Q .refl) Q.cosupp at hMax
      rw [hRec] at hMax
      exact Or.inr (hMax.trans hWhole.symm)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hNonempty)

end
end Hironaka.HironakaG8InitialCommonIdealMaximum
