import Hironaka.Resolution.HironakaActualDiagramStrictHSDrop
import Hironaka.Resolution.HironakaActualFormalIdealContraction
import Hironaka.Resolution.HironakaActualInvertibleIntrinsicHS
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder

/-! The first departure of the original HS profile from the free profile. -/

set_option autoImplicit false
open Set Classical
open scoped ENat

namespace Hironaka.HironakaG8InitialHSOrdinaryOrder

open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualFormalStandardMonomialHS HironakaActualOriginalFormalHSTransfer
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetRankLoci
  HironakaActualDiagramStrictHSDrop HironakaActualInvertibleIntrinsicHS GermIdealOrder
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan DivisorExponentAlong

private theorem formal_eq_free_of_le {n : ℕ} (J : Ideal (MvPowerSeries (Fin n) ℂ)) (l : ℕ)
    (hJ : J ≤ genuineFormalVariables n ^ (l+1)) :
    genuineFormalHilbertSamuelValue n J l = genuineFormalHilbertSamuelValue n ⊥ l := by
  apply genuineFormalHilbertSamuelValue_eq_of_bounded_diagram_eq
  intro β hβ
  rw [actualInitialDiagram_bot, Set.mem_empty_iff_false, iff_false]
  rintro ⟨f, hf, hf0, rfl⟩
  have hdeg := (mem_formal_variables_pow_iff_degree_initialExponent f hf0 (l+1)).mp (hJ hf)
  omega

private theorem formal_lt_free_of_not_le {n : ℕ} (J : Ideal (MvPowerSeries (Fin n) ℂ)) (l : ℕ)
    (hBefore : J ≤ genuineFormalVariables n ^ l)
    (hAt : ¬ J ≤ genuineFormalVariables n ^ (l+1)) :
    genuineFormalHilbertSamuelValue n J l < genuineFormalHilbertSamuelValue n ⊥ l := by
  change ¬ ∀ f ∈ J, f ∈ genuineFormalVariables n ^ (l+1) at hAt
  push Not at hAt
  obtain ⟨f, hf, hbad⟩ := hAt
  have hf0 : f ≠ 0 := fun h => hbad (h.symm ▸ Ideal.zero_mem _)
  let β := actualInitialExponent MonomialOrder.degLex f hf0
  have hLow : l ≤ normalExponentDegree β :=
    (mem_formal_variables_pow_iff_degree_initialExponent f hf0 l).mp (hBefore hf)
  have hHigh : ¬ (l+1) ≤ normalExponentDegree β :=
    fun h => hbad ((mem_formal_variables_pow_iff_degree_initialExponent f hf0 _).mpr h)
  have he : normalExponentDegree β = l := by omega
  have hSub : actualInitialDiagram MonomialOrder.degLex (⊥ : Ideal (MvPowerSeries (Fin n) ℂ)) ⊆
      actualInitialDiagram MonomialOrder.degLex J := by
    rw [actualInitialDiagram_bot]
    exact empty_subset _
  have h := genuineFormalHilbertSamuelValue_strict_lt_of_new_diagram_exponent
    ⊥ J hSub β ⟨f, hf, hf0, rfl⟩ (by rw [actualInitialDiagram_bot]; exact notMem_empty β)
  rwa [he] at h

private theorem taylor_le_variables_iff (n q : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) :
    Ideal.map (originalTaylorAlgHom n).toRingHom I ≤ genuineFormalVariables n ^ q ↔
      I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q := by
  unfold genuineFormalVariables
  rw [← map_original_maximal_pow_eq_formal_variables_pow n q]
  constructor
  · intro h f hf
    exact (mem_original_ideal_iff_formal_extension n _ f).mpr
      (h (Ideal.mem_map_of_mem _ hf))
  · exact Ideal.map_mono

/-- Whole analytic ideals agree with the free profile strictly below their
first nonvanishing degree and drop strictly at that degree. -/
theorem analytic_hilbertSamuel_first_drop {n d : ℕ} (I : Ideal (HolGerm (ComplexModel (0+n))))
    (hBefore : I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ d)
    (hAt : ¬ I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (d+1)) :
    (∀ l < d, hilbertSamuelValue I l = hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) l) ∧
    hilbertSamuelValue I d < hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) d := by
  constructor
  · intro l hl
    rw [hilbertSamuelValue_eq_genuine_formal_extension, hilbertSamuelValue_eq_genuine_formal_extension,
      Ideal.map_bot]
    exact formal_eq_free_of_le _ l ((taylor_le_variables_iff n _ I).mpr
      (hBefore.trans (Ideal.pow_le_pow_right (by omega))))
  · rw [hilbertSamuelValue_eq_genuine_formal_extension, hilbertSamuelValue_eq_genuine_formal_extension,
      Ideal.map_bot]
    exact formal_lt_free_of_not_le _ d ((taylor_le_variables_iff n _ I).mpr hBefore)
      (fun h => hAt ((taylor_le_variables_iff n _ I).mp h))

private theorem analytic_eq_free_of_le (n l : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n))))
    (hle : I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ (l+1)) :
    hilbertSamuelValue I l = hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) l := by
  rw [hilbertSamuelValue_eq_genuine_formal_extension, hilbertSamuelValue_eq_genuine_formal_extension,
    Ideal.map_bot]
  exact formal_eq_free_of_le _ l ((taylor_le_variables_iff n _ I).mpr hle)

/-- The first degree of strict inequality of the actual analytic
Hilbert--Samuel functions is the smaller ideal order whenever the orders
differ. The opposite order may be infinite. -/
theorem hilbertSamuelAt_lex_lt_of_order_lt {n : ℕ} {X Y : CMfd.{0} n}
    (A : GermIdeal n X) (B : GermIdeal n Y) (x : X) (y : Y)
    (hA : ∀ g, A.mem x g → HolomorphicAt n g x)
    (hB : ∀ g, B.mem y g → HolomorphicAt n g y)
    (hLt : order n univ A x < order n univ B y) :
    toLex (hilbertSamuelAt A x) < toLex (hilbertSamuelAt B y) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hLt)
  have hA_le (k : ℕ) :
      wholeChartStalkIdeal A x x (mem_chart_source _ x) ≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ k ↔
      (k : ℕ∞) ≤ order n univ A x :=
    (wholeChartStalkIdeal_le_maximal_pow_iff A x hA k).trans (le_order_iff hA).symm
  have hB_le (k : ℕ) :
      wholeChartStalkIdeal B y y (mem_chart_source _ y) ≤
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ k ↔
      (k : ℕ∞) ≤ order n univ B y :=
    (wholeChartStalkIdeal_le_maximal_pow_iff B y hB k).trans (le_order_iff hB).symm
  have hDropSpec := (show ∀ I : Ideal (HolGerm (ComplexModel n)),
      I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ d →
      (¬ I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (d+1)) →
      (∀ l < d, hilbertSamuelValue I l = hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel n))) l) ∧
      hilbertSamuelValue I d < hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel n))) d by
    rw [← Nat.zero_add n]
    exact @analytic_hilbertSamuel_first_drop n d)
  have hDrop := hDropSpec _ ((hA_le d).mpr hd.le) (fun h => by
    have hImpossible := (hA_le (d+1)).mp h
    rw [← hd] at hImpossible
    exact (Nat.not_succ_le_self d) (by exact_mod_cast hImpossible))
  have hBFree (l : ℕ) (hl : l ≤ d) :
      hilbertSamuelAt B y l = hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel n))) l := by
    have hEqSpec : ∀ I : Ideal (HolGerm (ComplexModel n)),
        I ≤ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (l+1) →
        hilbertSamuelValue I l = hilbertSamuelValue (⊥ : Ideal (HolGerm (ComplexModel n))) l := by
      rw [← Nat.zero_add n]
      exact analytic_eq_free_of_le n l
    apply hEqSpec _ ((hB_le (l+1)).mpr ?_)
    apply le_trans (show ((l+1 : ℕ) : ℕ∞) ≤ ((d+1 : ℕ) : ℕ∞) by exact_mod_cast Nat.succ_le_succ hl)
    exact not_lt.mp (fun h => (not_le.mpr hLt) (hd ▸ (ENat.lt_natCast_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using h))))
  exact ⟨d, fun l hl => (hDrop.1 l hl).trans (hBFree l hl.le).symm,
    (hDrop.2.trans_eq (hBFree d le_rfl).symm)⟩

/-- Lexicographic comparison of the actual whole Hilbert--Samuel profiles
preserves weak comparison of the original ambient ideal orders. -/
theorem order_le_of_hilbertSamuelAt_lex_le {n : ℕ} {X Y : CMfd.{0} n}
    (A : GermIdeal n X) (B : GermIdeal n Y) (x : X) (y : Y)
    (hA : ∀ g, A.mem x g → HolomorphicAt n g x)
    (hB : ∀ g, B.mem y g → HolomorphicAt n g y)
    (h : toLex (hilbertSamuelAt A x) ≤ toLex (hilbertSamuelAt B y)) :
    order n univ A x ≤ order n univ B y :=
  not_lt.mp (fun hlt => not_lt.mpr h (hilbertSamuelAt_lex_lt_of_order_lt B A y x hB hA hlt))


/-- A lexicographic whole-profile comparison gives the actual finite
ordinary trace-order comparison on the boundary-free ambient carrier. -/
theorem ordinaryTraceOrder_le_of_hilbertSamuelAt_lex_le {n : ℕ} {X : CMfd.{0} n}
    (A : GermIdeal n X) (hA : A.IsCoherent)
    (hNonzero : ∀ z : X, IsNonzeroAlongAt univ A z) (x y : X)
    (h : toLex (hilbertSamuelAt A x) ≤ toLex (hilbertSamuelAt A y)) :
    ordinaryTraceOrder (X := X) univ A x ≤ ordinaryTraceOrder (X := X) univ A y := by
  have hHol (z : X) (g : X → ℂ) (hg : A.mem z g) := GermIdeal.IsCoherent.holomorphicAt_mem hA hg
  have hOrd := order_le_of_hilbertSamuelAt_lex_le A A x y (hHol x) (hHol y) h
  let q := ordinaryTraceOrder (X := X) univ A x
  have hCos (z : X) : z ∈ cosupport n univ A q ↔ q ≤ ordinaryTraceOrder (X := X) univ A z :=
    ordinaryTraceOrder_cosupport_iff (X := X) HomogenizedGlueingTower.isClosedSubmanifold_univ
      hA (fun z _ => hNonzero z) (mem_univ z) q
  have hxOrder := (le_order_iff (hHol x)).mpr ((hCos x).mpr le_rfl).2
  exact (hCos y).mp ⟨mem_univ y, (le_order_iff (hHol y)).mp (hxOrder.trans hOrd)⟩


end Hironaka.HironakaG8InitialHSOrdinaryOrder
