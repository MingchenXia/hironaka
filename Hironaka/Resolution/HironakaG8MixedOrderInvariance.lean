import Hironaka.Resolution.HironakaG8MixedEquiv
import Hironaka.Resolution.HironakaActualProjectedNormalizedOrderDetection
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Invariant.CanonicalCentres

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The first entry of the canonical invariant on mixed-test equivalence classes (G8 lane, run 0080, round 2; D01)

Blueprint: `hironaka-g8-resume-mixed-order-invariance.tex`.  Route note: `work/hironaka-resume-20261111/G8/D01-ROUTE-r2.md`.

D01 asks whether `CanonicalCentres.canonicalInvariant` is constant on mixed-test equivalence classes
(`HironakaG8MixedEquiv.MixedEquiv`) after common-mark normalization.  The first entry of the invariant in positive
dimension is the RAW order `NonmonomialOrderLocal.nmOrd (geoTransformAlong 𝔪 T) y` of the nonmonomial part of the
transform (`GeneralValue.genInv_fst`; `canonicalInvariant_fst` here).  This module proves:

* **the mark cannot be dropped** (`powerMarked_two_counterexample`, `canonicalInvariant_fst_powerMarked_two_ne`): for
  every `M` in the native domain and every point `x` of its cosupport off the boundary, `M ~ M²` but the first entries of
  `canonicalInvariant` at `x` are `ρ` and `2ρ ≠ ρ` (`ρ = ord_x(𝔞|_N) ≥ d ≥ 1`); so the invariant is NOT constant on
  equivalence classes, only (at best) on the classes of a fixed mark;
* off the boundary the first entry is the ordinary order: `nmOrd_eq_ordinaryTraceOrder_of_notMem`, and it scales with
  powers: `ordinaryTraceOrder_idealPow` (`ord(𝔞^e) = e ord 𝔞`), `nmOrd_powerMarked_of_notMem`;
* **normalized orders are invariants of the class along every common mixed test history**
  (`mixedEquiv_normalizedOrder`, `mixedEquiv_normalizedOrder_record`: `d' ord_y(𝔞_H) = d ord_y(𝔞'_H)`), from the
  existing Bierstone–Milman Prop. 4.8 analogue
  `HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv` and the stability of
  `MixedEquiv` under transforms;
* **the first concrete invariance lemma of D01** (`mixedEquiv_nmOrd_record_eq_of_notMem`,
  `mixedEquiv_nmOrd_geoTransformAlong_eq_of_notMem`, **`mixedEquiv_canonicalInvariant_fst_eq_of_notMem`**,
  `mixedEquiv_canonicalInvariant_fst_refl_eq`): for two equivalent marked ideals in the native domain with the same
  carrier and the SAME mark, along every common test tower, at every cosupport point off the exceptional boundary, the
  first entries of `canonicalInvariant` agree; with empty initial boundary they agree on the whole initial cosupport.

Not proved here: the first entry ON the boundary (needs BM97 Prop. 4.11, the invariance of the boundary exponents
`μ_H` via exceptional blowups) and the deeper entries (companion ideal, `γ`, masked Step 1 value); see the route note.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8MixedOrderInvariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal GermIdealOrder RelativePrincipalizationSpan DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.RestrictedIdealExtension (restrictOn restrictOn_mul_left)
open Hironaka.MonomialPartAlong (nonmonomialPartAlong monomialPartAlong)
open Hironaka.NonmonomialOrderLocal (nmOrd nmPart ordGe nmOrd_congr)
open Hironaka.HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder ordinaryTraceMarked
  nonmonomialPartAlong_nil_eq_restrictOn ordinaryTraceOrder_cosupport_iff)
open Hironaka.HironakaActualMixedTestPowerNormalization
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_isInvDomain
  cosupport_idealPow_mul_succ_eq_along isNonzeroAlongAt_idealPow)
open Hironaka.HironakaG8MixedEquiv
open Hironaka.CanonicalCentres (canonicalInvariant ValTy)

noncomputable section

/-! ### Off the boundary the nonmonomial order is the ordinary order -/

section Order

variable {n : ℕ} {X : CMfd.{u} n}

/-- Membership in a cosupport only depends on the germs at the point. -/
theorem mem_cosupport_congr {N : Set X} {J J' : GermIdeal n X} {y : X} (h : ∀ g, J.mem y g ↔ J'.mem y g) (q : ℕ) :
    y ∈ cosupport n N J q ↔ y ∈ cosupport n N J' q := by
  show y ∈ N ∧ (∀ g, J.mem y g → VanishesToOrderOn n N y q g) ↔ y ∈ N ∧ (∀ g, J'.mem y g → VanishesToOrderOn n N y q g)
  simp only [h]

/-- **Off the boundary the nonmonomial part has the germs of the restricted ideal**: at a point on no member of `E`
the monomial part is the whole ring of germs. -/
theorem nmPart_mem_iff_of_notMem (𝔪 : MarkedIdeal n X) {y : X} (hy : ∀ i : Fin 𝔪.E.length, y ∉ 𝔪.E.get i)
    (g : X → ℂ) : (nmPart 𝔪).mem y g ↔ (restrictOn n 𝔪.N 𝔪.ideal).mem y g := by
  constructor
  · rintro ⟨_hg, hcolon⟩
    have h1 := hcolon (fun _ => 1) ⟨holomorphicAt_const 1, fun i _ hyi => absurd hyi (hy i)⟩
    simpa only [one_mul] using h1
  · intro hg
    exact ⟨hg.1, fun a ha => restrictOn_mul_left ha.1 hg⟩

/-- **Off the boundary the first entry is the ordinary order**: `nmOrd 𝔪 y = ord_y(𝔞|_N)` at a point on no member of
`E`. -/
theorem nmOrd_eq_ordinaryTraceOrder_of_notMem (𝔪 : MarkedIdeal n X) {y : X}
    (hy : ∀ i : Fin 𝔪.E.length, y ∉ 𝔪.E.get i) : nmOrd 𝔪 y = ordinaryTraceOrder 𝔪.N 𝔪.ideal y := by
  refine nmOrd_congr fun q => ?_
  show y ∈ cosupport n 𝔪.N (nmPart 𝔪) q ↔ y ∈ cosupport n 𝔪.N (nonmonomialPartAlong n 𝔪.N 𝔪.ideal []) q
  rw [nonmonomialPartAlong_nil_eq_restrictOn]
  exact mem_cosupport_congr (nmPart_mem_iff_of_notMem 𝔪 hy) q

/-- With empty boundary the first entry is the ordinary order everywhere. -/
theorem nmOrd_eq_ordinaryTraceOrder_of_nil (𝔪 : MarkedIdeal n X) (hE : 𝔪.E = []) (y : X) :
    nmOrd 𝔪 y = ordinaryTraceOrder 𝔪.N 𝔪.ideal y :=
  nmOrd_eq_ordinaryTraceOrder_of_notMem 𝔪 fun i => absurd i.2 (by simp [hE])

/-- **The order of a power**: `ord_x((𝔞^e)|_N) = e · ord_x(𝔞|_N)` at the points of `N` (`e ≥ 1`, coherent `𝔞` not
vanishing identically along `N`). -/
theorem ordinaryTraceOrder_idealPow {N : Set X} (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hI : I.IsCoherent)
    (hne : ∀ y ∈ N, IsNonzeroAlongAt N I y) {e : ℕ} (he : 1 ≤ e) {x : X} (hx : x ∈ N) :
    ordinaryTraceOrder N (IdealWeightPowers.idealPow I e) x = e * ordinaryTraceOrder N I x := by
  have hIe := GermIdealPullbackCalculus.isCoherent_idealPow hI e
  have hneE : ∀ y ∈ N, IsNonzeroAlongAt N (IdealWeightPowers.idealPow I e) y :=
    fun y hy => isNonzeroAlongAt_idealPow hI (hne y hy) e
  set ρ := ordinaryTraceOrder N I x
  have hρ : x ∈ cosupport n N I ρ := (ordinaryTraceOrder_cosupport_iff hN hI hne hx ρ).mpr le_rfl
  have hρ1 : x ∉ cosupport n N I (ρ + 1) := fun h =>
    Nat.not_succ_le_self ρ ((ordinaryTraceOrder_cosupport_iff hN hI hne hx (ρ + 1)).mp h)
  have hlow : x ∈ cosupport n N (IdealWeightPowers.idealPow I e) (e * ρ) := by
    rw [Nat.mul_comm, MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN.2
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) he ρ]
    exact hρ
  have hhigh : x ∉ cosupport n N (IdealWeightPowers.idealPow I e) (e * ρ + 1) := by
    rw [cosupport_idealPow_mul_succ_eq_along hN hI he ρ]
    exact hρ1
  have h1 := (ordinaryTraceOrder_cosupport_iff hN hIe hneE hx (e * ρ)).mp hlow
  have h2 : ¬ e * ρ + 1 ≤ ordinaryTraceOrder N (IdealWeightPowers.idealPow I e) x :=
    fun h => hhigh ((ordinaryTraceOrder_cosupport_iff hN hIe hneE hx (e * ρ + 1)).mpr h)
  omega

/-- **The first entry scales with powers** off the boundary: `nmOrd (M^e) y = e · nmOrd M y`. -/
theorem nmOrd_powerMarked_of_notMem {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ} (he : 1 ≤ e)
    {y : X} (hyN : y ∈ M.N) (hy : ∀ i : Fin M.E.length, y ∉ M.E.get i) :
    nmOrd (powerMarked M e) y = e * nmOrd M y := by
  rw [nmOrd_eq_ordinaryTraceOrder_of_notMem (powerMarked M e) hy, nmOrd_eq_ordinaryTraceOrder_of_notMem M hy]
  exact ordinaryTraceOrder_idealPow hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent
    hM.isNonzeroAlongAt he hyN

/-- At a cosupport point the ordinary order is at least the mark. -/
theorem mark_le_ordinaryTraceOrder {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {x : X} (hx : x ∈ M.cosupp) :
    M.d ≤ ordinaryTraceOrder M.N M.ideal x :=
  (ordinaryTraceOrder_cosupport_iff hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent
    hM.isNonzeroAlongAt (M.cosupp_subset_N hx) M.d).mp hx

end Order

/-! ### The first entry of the canonical invariant -/

section FirstEntry

variable {k : ℕ} {X : CMfd.{u} (k + 1)}

/-- The first entry of a value of the canonical invariant in positive dimension. -/
def fstEntry (v : ValTy (k + 1)) : ℕ :=
  (ofLex (show ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy k))) from v)).1

/-- **The first entry of `canonicalInvariant` is the raw nonmonomial order of the transform**
(`GeneralValue.genInv_fst` through `invFamily` and `generalStep`). -/
theorem canonicalInvariant_fst (𝔪 : MarkedIdeal (k + 1) X) {Y : CMfd.{u} (k + 1)} (T : BlowupTower X Y) (y : Y) :
    fstEntry ((canonicalInvariant.{u} (k + 1)).inv 𝔪 T y) = nmOrd (geoTransformAlong 𝔪 T) y :=
  rfl

end FirstEntry

/-! ### The mark cannot be dropped -/

section Counterexample

variable {n : ℕ} {X : CMfd.{u} n}

/-- **`M ~ M²` but the first entries differ**: for `M` in the native domain and a cosupport point off the boundary,
`M` and `M² = (𝔞², 2d)` are mixed-test equivalent, while `nmOrd M² x = 2 nmOrd M x ≠ nmOrd M x` (`nmOrd M x ≥ d ≥ 1`). -/
theorem powerMarked_two_counterexample {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {x : X}
    (hx : x ∈ M.cosupp) (hxE : ∀ i : Fin M.E.length, x ∉ M.E.get i) :
    MixedEquiv M (powerMarked M 2) ∧ nmOrd (powerMarked M 2) x = 2 * nmOrd M x ∧
      nmOrd (powerMarked M 2) x ≠ nmOrd M x := by
  have hp := nmOrd_powerMarked_of_notMem M hM (le_succ 1) (M.cosupp_subset_N hx) hxE
  have hpos : 1 ≤ nmOrd M x := by
    rw [nmOrd_eq_ordinaryTraceOrder_of_notMem M hxE]
    exact hM.one_le_d.trans (mark_le_ordinaryTraceOrder M hM hx)
  refine ⟨mixedEquiv_powerMarked M hM (le_succ 1), hp, ?_⟩
  rw [hp]
  omega
where le_succ (a : ℕ) : a ≤ a + 1 := Nat.le_succ a

/-- **`canonicalInvariant` is not constant on mixed-test equivalence classes** (positive dimension): with `M`, `x` as
in `powerMarked_two_counterexample`, the values of `canonicalInvariant` at `x` for `M` and `M²` (empty tower) differ in
the first entry. -/
theorem canonicalInvariant_fst_powerMarked_two_ne {k : ℕ} {X : CMfd.{u} (k + 1)} {r : ℕ}
    (M : MarkedIdeal (k + 1) X) (hM : IsInvDomain r M) {x : X} (hx : x ∈ M.cosupp)
    (hxE : ∀ i : Fin M.E.length, x ∉ M.E.get i) :
    MixedEquiv M (powerMarked M 2) ∧
      fstEntry ((canonicalInvariant.{u} (k + 1)).inv (powerMarked M 2) .refl x) ≠
        fstEntry ((canonicalInvariant.{u} (k + 1)).inv M .refl x) := by
  obtain ⟨h1, -, h3⟩ := powerMarked_two_counterexample M hM hx hxE
  exact ⟨h1, h3⟩

end Counterexample

/-! ### Normalized orders along common mixed test histories, and the first entry -/

section Invariance

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Normalized orders agree at the base** (Bierstone–Milman 1997, Prop. 4.8, through
`normalized_ordinary_order_of_projected_wEquiv`): `d' ord_x(𝔞|_N) = d ord_x(𝔞'|_N)` on the common cosupport. -/
theorem mixedEquiv_normalizedOrder {kA kB : ℕ} {A B : MarkedIdeal n X} (h : MixedEquiv A B) (hA : IsInvDomain kA A)
    (hB : IsInvDomain kB B) (hN : B.N = A.N) {x : X} (hx : x ∈ A.cosupp) :
    B.d * ordinaryTraceOrder A.N A.ideal x = A.d * ordinaryTraceOrder B.N B.ideal x := by
  have hxB : x ∈ B.cosupp := h.cosupp_eq_base ▸ hx
  exact (HironakaActualProjectedNormalizedOrderDetection.normalized_ordinary_order_of_projected_wEquiv A B hA hB x hx
    hxB hN h.E_eq h.projectionTest_wEquiv).2.2

/-- **Normalized orders agree along every common mixed test history**: for a test history `H` of `A` and a point
`y` of the cosupport of the record `A_H`, `d_B · ord_y(A_H) = d_A · ord_y(B_H)`. -/
theorem mixedEquiv_normalizedOrder_record {kA kB : ℕ} {A B : MarkedIdeal n X} (h : MixedEquiv A B)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) {m : ℕ} {Y : CMfd.{u} m} {F : List (Set Y)}
    (H : History X A.E Y F) (hH : IsTest A H) {y : Y} (hy : y ∈ (record A H).cosupp) :
    B.d * ordinaryTraceOrder (record A H).N (record A H).ideal y =
      A.d * ordinaryTraceOrder (record (withBoundary B A.E) H).N (record (withBoundary B A.E) H).ideal y := by
  have hB' : IsInvDomain kB (withBoundary B A.E) := (withBoundary_eq h.E_eq).symm ▸ hB
  have hHB : IsTest (withBoundary B A.E) H := (h.isTest_iff H).mp hH
  have hRA := record_isInvDomain A hA H hH
  have hRB := record_isInvDomain (withBoundary B A.E) hB' H hHB
  have hNr : (record (withBoundary B A.E) H).N = (record A H).N := by
    show carrier B.N H = carrier A.N H
    rw [hN]
  exact mixedEquiv_normalizedOrder (h.record H hH) hRA hRB hNr hy

/-- **The first concrete invariance lemma (records)**: for equivalent marked ideals in the native domain with the same
carrier and the SAME mark, along every common mixed test history, at every cosupport point off the boundary, the first
entries `nmOrd` of the records agree. -/
theorem mixedEquiv_nmOrd_record_eq_of_notMem {kA kB : ℕ} {A B : MarkedIdeal n X} (h : MixedEquiv A B)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) {m : ℕ} {Y : CMfd.{u} m}
    {F : List (Set Y)} (H : History X A.E Y F) (hH : IsTest A H) {y : Y} (hy : y ∈ (record A H).cosupp)
    (hyF : ∀ i : Fin F.length, y ∉ F.get i) :
    nmOrd (record A H) y = nmOrd (record (withBoundary B A.E) H) y := by
  have h1 := mixedEquiv_normalizedOrder_record h hA hB hN H hH hy
  rw [hd] at h1
  rw [nmOrd_eq_ordinaryTraceOrder_of_notMem (record A H) hyF,
    nmOrd_eq_ordinaryTraceOrder_of_notMem (record (withBoundary B A.E) H) hyF]
  exact Nat.eq_of_mul_eq_mul_left (Nat.lt_of_lt_of_le Nat.zero_lt_one hA.one_le_d) h1

/-- **The first concrete invariance lemma (towers)**: the same along every common multiple test blowup. -/
theorem mixedEquiv_nmOrd_geoTransformAlong_eq_of_notMem {kA kB : ℕ} {A B : MarkedIdeal n X} (h : MixedEquiv A B)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (hN : B.N = A.N) (hd : B.d = A.d) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y} (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hyE : ∀ i : Fin (geoTransformAlong A T).E.length, y ∉ (geoTransformAlong A T).E.get i) :
    nmOrd (geoTransformAlong A T) y = nmOrd (geoTransformAlong B T) y := by
  have rA := record_towerHistory_refl A T
  have rB : record (withBoundary B A.E) (towerHistory (.refl : History X A.E X A.E) T) = geoTransformAlong B T :=
    (record_towerHistory_refl (withBoundary B A.E) T).trans
      (congrArg (fun M => geoTransformAlong M T) (withBoundary_eq h.E_eq))
  have hH : IsTest A (towerHistory (.refl : History X A.E X A.E) T) := (isTest_towerHistory_refl_iff A T).mpr hT
  have hyF : ∀ i : Fin (record A (towerHistory (.refl : History X A.E X A.E) T)).E.length,
      y ∉ (record A (towerHistory (.refl : History X A.E X A.E) T)).E.get i := by
    rw [rA]
    exact hyE
  have hy' : y ∈ (record A (towerHistory (.refl : History X A.E X A.E) T)).cosupp := by
    rw [rA]
    exact hy
  have h1 := mixedEquiv_nmOrd_record_eq_of_notMem h hA hB hN hd (towerHistory .refl T) hH hy' hyF
  rw [rA, rB] at h1
  exact h1

/-- **D01, first entry**: for `A ~ B` in the native domain with the same carrier and the same mark, along every common
multiple test blowup `T`, at every cosupport point off the exceptional boundary, the first entries of
`canonicalInvariant` agree. -/
theorem mixedEquiv_canonicalInvariant_fst_eq_of_notMem {k kA kB : ℕ} {X : CMfd.{u} (k + 1)}
    {A B : MarkedIdeal (k + 1) X} (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) {Y : CMfd.{u} (k + 1)} (T : BlowupTower X Y) (hT : IsGeoTestTower A T) {y : Y}
    (hy : y ∈ (geoTransformAlong A T).cosupp)
    (hyE : ∀ i : Fin (geoTransformAlong A T).E.length, y ∉ (geoTransformAlong A T).E.get i) :
    fstEntry ((canonicalInvariant.{u} (k + 1)).inv A T y) = fstEntry ((canonicalInvariant.{u} (k + 1)).inv B T y) :=
  mixedEquiv_nmOrd_geoTransformAlong_eq_of_notMem h hA hB hN hd T hT hy hyE

/-- **D01, first entry at the base with empty boundary** (the case of the initial window records, `E = []`): the first
entries of `canonicalInvariant` agree on the whole common cosupport. -/
theorem mixedEquiv_canonicalInvariant_fst_refl_eq {k kA kB : ℕ} {X : CMfd.{u} (k + 1)}
    {A B : MarkedIdeal (k + 1) X} (h : MixedEquiv A B) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : B.N = A.N) (hd : B.d = A.d) (hE : A.E = []) {x : X} (hx : x ∈ A.cosupp) :
    fstEntry ((canonicalInvariant.{u} (k + 1)).inv A .refl x) =
      fstEntry ((canonicalInvariant.{u} (k + 1)).inv B .refl x) :=
  mixedEquiv_canonicalInvariant_fst_eq_of_notMem h hA hB hN hd .refl trivial hx fun i => absurd i.2 (by simp [hE])

end Invariance

end

end Hironaka.HironakaG8MixedOrderInvariance
