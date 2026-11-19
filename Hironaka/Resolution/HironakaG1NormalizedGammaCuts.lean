import Hironaka.Resolution.HironakaG1NormalizedMonomialCuts
import Hironaka.Resolution.HironakaActualCoefficientNonmonomialHistoryOrder
import Hironaka.Resolution.HironakaG8MixedOrderInvariance
import Hironaka.Resolution.HironakaActualOriginalLowerRawOrder

/-! The original monomial invariant's raw keys need not be equal under a
change of mark, but their comparisons at two points are unchanged. -/
set_option autoImplicit false
open Set Finset
namespace Hironaka.HironakaG1NormalizedGammaCuts
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MonomialInvariant MonomialCase MonomialCaseAlong HironakaG1NormalizedMonomialCuts
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  ResolutionInvariantSpec HironakaActualProjectionTestRecord HironakaActualOriginalLowerChronologicalExponents.Generic

private theorem cross_sum (S K : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ)
    (hK : K ⊆ S) (h : ∀ i ∈ S, e * a i = d * b i) :
    e * ∑ i ∈ K, a i = d * ∑ i ∈ K, b i := by
  rw [Finset.mul_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => h i (hK hi)

/-- Complete key comparisons across two points are preserved, even when
both original raw keys change under the unequal native marks. -/
theorem normalized_keys_crosspoint_lt_iff (n : ℕ) (S₁ S₂ K L : Finset ℕ)
    (a₁ a₂ b₁ b₂ : ℕ → ℕ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hK : K ⊆ S₁) (hL : L ⊆ S₂)
    (h₁ : ∀ i ∈ S₁, e * a₁ i = d * b₁ i)
    (h₂ : ∀ i ∈ S₂, e * a₂ i = d * b₂ i) :
    key n a₁ K < key n a₂ L ↔ key n b₁ K < key n b₂ L := by
  have hsumK := cross_sum S₁ K a₁ b₁ d e hK h₁
  have hsumL := cross_sum S₂ L a₂ b₂ d e hL h₂
  have hlt : (∑ i ∈ K, a₁ i) < ∑ i ∈ L, a₂ i ↔ (∑ i ∈ K, b₁ i) < ∑ i ∈ L, b₂ i := by
    constructor <;> intro hcmp <;> nlinarith
  have heq : (∑ i ∈ K, a₁ i) = ∑ i ∈ L, a₂ i ↔ (∑ i ∈ K, b₁ i) = ∑ i ∈ L, b₂ i := by
    constructor <;> intro hcmp <;> nlinarith
  simp only [key_lt_key_iff, hlt, heq]

/-- If a feasible subset maximizes the key, the finite monomial invariant is
exactly its key. -/
private theorem inv_eq_of_max (n : ℕ) (S I : Finset ℕ) (a : ℕ → ℕ) (d : ℕ)
    (hI : I ∈ feasible S a d) (hmax : ∀ K ∈ feasible S a d, key n a K ≤ key n a I) :
    inv n S a d = key n a I := by
  refine le_antisymm (Finset.max_le fun v hv => ?_) (Finset.le_max (mem_image_of_mem _ hI))
  obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hv
  exact WithBot.coe_le_coe.mpr (hmax K hK)

/-- In the monomial regime at both points, positive cross-scaling preserves
strict comparisons of the whole original gamma values. -/
theorem normalized_inv_lt_iff (n : ℕ) (S₁ S₂ : Finset ℕ)
    (a₁ a₂ b₁ b₂ : ℕ → ℕ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (h₁ : ∀ i ∈ S₁, e * a₁ i = d * b₁ i)
    (h₂ : ∀ i ∈ S₂, e * a₂ i = d * b₂ i)
    (hf₁ : d ≤ ∑ i ∈ S₁, a₁ i) (hf₂ : d ≤ ∑ i ∈ S₂, a₂ i) :
    inv n S₁ a₁ d < inv n S₂ a₂ d ↔ inv n S₁ b₁ e < inv n S₂ b₂ e := by
  obtain ⟨K,hK,hA₁,hmaxK⟩ := exists_top (n := n) (a := a₁) hf₁
  obtain ⟨L,hL,hA₂,hmaxL⟩ := exists_top (n := n) (a := a₂) hf₂
  have hBK := (normalized_maximizing_key_iff n S₁ K a₁ b₁ d e hd he h₁).mp ⟨hK,hmaxK⟩
  have hBL := (normalized_maximizing_key_iff n S₂ L a₂ b₂ d e hd he h₂).mp ⟨hL,hmaxL⟩
  have hB₁ := inv_eq_of_max n S₁ K b₁ e hBK.1 hBK.2
  have hB₂ := inv_eq_of_max n S₂ L b₂ e hBL.1 hBL.2
  rw [hA₁,hA₂,hB₁,hB₂]
  exact_mod_cast normalized_keys_crosspoint_lt_iff n S₁ S₂ K L a₁ a₂ b₁ b₂ d e hd he
    (mem_feasible.mp hK).1 (mem_feasible.mp hL).1 h₁ h₂

/-- On a genuine common controlled history, chronological boundary
exponents preserve strict original gamma comparisons at two feasible points. -/
theorem chronological_gamma_lt_iff
    {n kA kB : ℕ} {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong n A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong n B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (z w : Y)
    (hz : (geoTransformAlong A T).d ≤ ∑ i ∈ memberIdx (geoTransformAlong A T).E z,
      expDataAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E z i)
    (hw : (geoTransformAlong A T).d ≤ ∑ i ∈ memberIdx (geoTransformAlong A T).E w,
      expDataAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E w i) :
    gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
        (geoTransformAlong A T).d z <
      gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
        (geoTransformAlong A T).d w ↔
    gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d z <
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d w := by
  obtain ⟨hAR,hBR,_hNR,hER,_hDA,_hDB,_hLA,_hLB,_hOldA,_hOldB,_hBorn,hExp,_hTrace⟩ :=
    all_chronological_boundary_exponents A B hA hB hN hE hProjected hInitial T hTA hTB
  have hIdx (x : Y) : memberIdx (geoTransformAlong A T).E x = memberIdx (geoTransformAlong B T).E x := by rw [hER]
  unfold gammaAlong
  rw [←hIdx z,←hIdx w]
  exact normalized_inv_lt_iff n _ _ _ _ _ _ _ _ hAR.one_le_d hBR.one_le_d
    (fun i _ => hExp z i) (fun i _ => hExp w i) hz hw

private theorem feasible_of_zero {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) {x : X} (hx : x ∈ M.cosupp)
    (hzero : NonmonomialOrderLocal.nmOrd M x = 0) :
    M.d ≤ ∑ i ∈ memberIdx M.E x, expDataAlong n M.N M.ideal M.E x i := by
  obtain ⟨_,_,hord,_⟩ := HironakaActualCoefficientNonmonomialHistoryOrder.whole_factor_order
    hn M hM.isWellFormed hM.isNonzeroAlongAt x (M.cosupp_subset_N hx)
  have hmark := HironakaG8MixedOrderInvariance.mark_le_ordinaryTraceOrder M hM hx
  rw [hord,hzero,Nat.add_zero] at hmark
  exact hmark

/-- The original raw nonmonomial orders remain cross-scaled at every point
of every common tested stage, including all transformed boundary members. -/
theorem chronological_raw_order_cross
    {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong n A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong n B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (x : Y) (hx : x ∈ (geoTransformAlong A T).cosupp) :
    (geoTransformAlong B T).d * NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) x =
      (geoTransformAlong A T).d * NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) x := by
  let AR := geoTransformAlong A T
  let BR := geoTransformAlong B T
  obtain ⟨hAR,hBR,hNR,hER,_hDA,_hDB,_hLA,_hLB,_hOldA,_hOldB,_hBorn,hExp,_hTrace⟩ :=
    all_chronological_boundary_exponents A B hA hB hN hE hProjected hInitial T hTA hTB
  have hProj := HironakaActualLocalProductHistory.current_projected_wEquiv A B
    hA.isWellFormed hB.isWellFormed hProjected T hTA hTB
  obtain ⟨_,_,_,_,_,_,_,hCA⟩ := projection_test_dictionary AR hAR
  obtain ⟨_,_,_,_,_,_,_,hCB⟩ := projection_test_dictionary BR hBR
  have hCos : AR.cosupp = BR.cosupp := by
    have hh := hProj.cosupp_eq
    rw [hCA,hCB] at hh
    ext y
    exact Iff.of_eq (congrArg (fun S : Set _ => (y,0) ∈ S) hh)
  have hTotal : ∀ y ∈ AR.cosupp,
      BR.d * HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder AR.N AR.ideal y =
        AR.d * HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder BR.N BR.ideal y := by
    intro y hy
    exact (HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv
      AR BR hAR hBR y hy (hCos ▸ hy) hNR.symm hER.symm hProj).2.2
  exact (HironakaActualOriginalLowerRawOrder.Generic.finite_whole_factor_raw_comparison hn AR BR
    hAR hBR hNR hER hCos hTotal hExp).1 x hx |>.2.2.2.2.2.2.2.2.2

/-- At two actual cosupport points in the zero-nonmonomial-order regime,
the original gamma values have the same strict cut along the entire
controlled common history, even for unequal native marks. -/
theorem chronological_gamma_lt_of_zero_iff
    {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong n A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong n B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (z w : Y) (hz : z ∈ (geoTransformAlong A T).cosupp) (hw : w ∈ (geoTransformAlong A T).cosupp)
    (hz0 : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) z = 0)
    (hw0 : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) w = 0) :
    gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
        (geoTransformAlong A T).d z <
      gammaAlong n (geoTransformAlong A T).N (geoTransformAlong A T).ideal (geoTransformAlong A T).E
        (geoTransformAlong A T).d w ↔
    gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d z <
      gammaAlong n (geoTransformAlong B T).N (geoTransformAlong B T).ideal (geoTransformAlong B T).E
        (geoTransformAlong B T).d w := by
  have hAR := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTA
  exact chronological_gamma_lt_iff A B hA hB hN hE hProjected hInitial T hTA hTB z w
    (feasible_of_zero hn _ hAR hz hz0) (feasible_of_zero hn _ hAR hw hw0)

/-- In the simultaneous zero-order branch, strict comparisons of the
actual original canonical invariant agree across the two tested histories. -/
theorem chronological_original_invariant_zero_cut_iff
    {r kA kB : ℕ} {X Y : CMfd.{0} (r+1)} (A B : MarkedIdeal (r+1) X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong (r+1) A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong (r+1) B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (z w : Y) (hz : z ∈ (geoTransformAlong A T).cosupp) (hw : w ∈ (geoTransformAlong A T).cosupp)
    (hzA : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) z = 0)
    (hwA : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) w = 0) :
    (CanonicalCentres.canonicalInvariant (r+1)).inv A T z < (CanonicalCentres.canonicalInvariant (r+1)).inv A T w ↔
      (CanonicalCentres.canonicalInvariant (r+1)).inv B T z < (CanonicalCentres.canonicalInvariant (r+1)).inv B T w := by
  have hAR := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTA
  have hzRaw := chronological_raw_order_cross (Nat.succ_pos r) A B hA hB hN hE hProjected hInitial T hTA hTB z hz
  have hwRaw := chronological_raw_order_cross (Nat.succ_pos r) A B hA hB hN hE hProjected hInitial T hTA hTB w hw
  have hzB : NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) z = 0 := by
    have hd := hAR.one_le_d
    rw [hzA, Nat.mul_zero] at hzRaw
    nlinarith
  have hwB : NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) w = 0 := by
    have hd := hAR.one_le_d
    rw [hwA, Nat.mul_zero] at hwRaw
    nlinarith
  let M := fun {X : CMfd.{0} (r+1)} (J : MarkedIdeal (r+1) X) {Y : CMfd.{0} (r+1)}
      (T : BlowupTower X Y) (y : Y) =>
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily (Nat.succ_pos r) r) J T y
  change GeneralValue.genInv M A T z < GeneralValue.genInv M A T w ↔
    GeneralValue.genInv M B T z < GeneralValue.genInv M B T w
  rw [GeneralValue.genInv_of_nmOrd_eq_zero M A T hzA,
    GeneralValue.genInv_of_nmOrd_eq_zero M A T hwA,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T hzB,
    GeneralValue.genInv_of_nmOrd_eq_zero M B T hwB]
  simpa only [Prod.Lex.toLex_lt_toLex, lt_irrefl, true_and, false_or, Sum.Lex.toLex_lt_toLex, Sum.lex_inl_inl] using
    chronological_gamma_lt_of_zero_iff (Nat.succ_pos r) A B hA hB hN hE hProjected hInitial T hTA hTB z w hz hw hzA hwA

/-- When the two actual raw orders differ, strict cuts of the literal
original canonical invariants agree, including positive-order points. -/
theorem chronological_original_invariant_distinct_raw_cut_iff
    {r kA kB : ℕ} {X Y : CMfd.{0} (r+1)} (A B : MarkedIdeal (r+1) X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hE : A.E = B.E)
    (hProjected : WEquiv (projectionTest A) (projectionTest B))
    (hInitial : ∀ (i : Fin A.E.length) (x : X),
      B.d * DivisorExponentAlong.divExpAlong (r+1) A.N A.ideal (A.E.get i) x =
        A.d * DivisorExponentAlong.divExpAlong (r+1) B.N B.ideal (A.E.get i) x)
    (T : BlowupTower X Y) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    (z w : Y) (hz : z ∈ (geoTransformAlong A T).cosupp) (hw : w ∈ (geoTransformAlong A T).cosupp)
    (hne : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) z ≠
      NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) w) :
    (CanonicalCentres.canonicalInvariant (r+1)).inv A T z < (CanonicalCentres.canonicalInvariant (r+1)).inv A T w ↔
      (CanonicalCentres.canonicalInvariant (r+1)).inv B T z < (CanonicalCentres.canonicalInvariant (r+1)).inv B T w := by
  have hAR := InvDomainTowerAlong.isInvDomain_geoTransformAlong hA T hTA
  have hBR := InvDomainTowerAlong.isInvDomain_geoTransformAlong hB T hTB
  have hzRaw := chronological_raw_order_cross (Nat.succ_pos r) A B hA hB hN hE hProjected hInitial T hTA hTB z hz
  have hwRaw := chronological_raw_order_cross (Nat.succ_pos r) A B hA hB hN hE hProjected hInitial T hTA hTB w hw
  have hd := hAR.one_le_d
  have he := hBR.one_le_d
  have hlt : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) z <
      NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) w ↔
    NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) z <
      NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) w := by
    constructor <;> intro hh <;> nlinarith
  have hgt : NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) w <
      NonmonomialOrderLocal.nmOrd (geoTransformAlong A T) z ↔
    NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) w <
      NonmonomialOrderLocal.nmOrd (geoTransformAlong B T) z := by
    constructor <;> intro hh <;> nlinarith
  let M := fun {X : CMfd.{0} (r+1)} (J : MarkedIdeal (r+1) X) {Y : CMfd.{0} (r+1)}
      (T : BlowupTower X Y) (y : Y) =>
    Seq.StepOneValueMasked.stepOneInvM (CanonicalCentres.invFamily (Nat.succ_pos r) r) J T y
  change GeneralValue.genInv M A T z < GeneralValue.genInv M A T w ↔
    GeneralValue.genInv M B T z < GeneralValue.genInv M B T w
  rcases lt_or_gt_of_ne hne with h | h
  · exact iff_of_true (GeneralValue.genInv_lt_of_nmOrd_lt M A h)
      (GeneralValue.genInv_lt_of_nmOrd_lt M B (hlt.mp h))
  · exact iff_of_false (not_lt_of_ge (le_of_lt (GeneralValue.genInv_lt_of_nmOrd_lt M A h)))
      (not_lt_of_ge (le_of_lt (GeneralValue.genInv_lt_of_nmOrd_lt M B (hgt.mp h))))
end Hironaka.HironakaG1NormalizedGammaCuts
