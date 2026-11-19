import Hironaka.Invariant.GeneralPhaseCount
import Hironaka.Analytic.GrowingSeqTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The companion phase of the general value: one companion ideal for the whole phase, and finitely many centres

Hironaka phase H2 (TN3), for the per-sequence local finiteness (8') of the general step's value (human decision I-1139 (b));
requested by TN-CLASSICAL (I-0977 C-0217), claimed C-0218.  Blueprint `bcalc:general-companion-phase` (chapter
`blowup-calculus.tex`).  Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2a of Proposition `pr:resol` (while the order
of the nonmonomial part stays `o`, the canonical resolution is that of the companion ideal of maximal order, "then we repeat the
procedure"); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.B.

Let `𝔪` lie in the domain (`n > 0`), `M` be a value function for the marked ideals of maximal order
(`MaxOrderValue.IsMaxOrderValue`), and `genInv M 𝔪` the general value.  A **phase of order `o ≥ 1`** starts at a stage `T₀` of a
canonical segment if the order `ν` of the nonmonomial part is `≤ o` on the cosupport there (`h0`) and every centre before it
lies in `{ν ≥ o + 1}` (`NonmonomialOrderRegime.CentresOrdGt`); along the rest `S` of the segment every centre has order `o`
(`CentresOrdGe`).  Then every point of order `o` started its run at or before `T₀`, so its value is read off ONE companion ideal
`𝓞 = compAt 𝔪 o T₀` formed at `T₀` on the mask `W = {ν ≤ o}` (`genInv_eq_of_mem_cosupp_phase`, through TN-CLASSICAL's
`GeneralCanonicalTail.genLowerValue_eq_rebase_of_eq`), and **the restricted tail `S|_W` is a canonical segment of `𝓞` for `M`**
(`isCanonical_restrict_phase`).

Counting: `countPhase 𝔪 K o T` counts the steps of `T` whose centre has a point over `K` of order `o`
(`countPhase_le_countCentresMeeting`, `countPhase_append`, `countPhase_eq_zero_of_centresOrdGt`).  Along a canonical segment
the centres meeting `K` are counted by the phases `o ≤ q` (`countCentresMeeting_le_sum_countPhase`, under the hypothesis `hq` of
`GeneralPhaseCount`); the phase `0` is bounded by the order-`0` entries of the centre values (`countPhase_le_filter`, and
`GeneralPhaseCount.exists_bound_phase_zero`); and **for `o ≥ 1` the counts along every growing sequence of canonical segments
are bounded, given property (8) of `M` along growing sequences for the marked ideals of the domain of maximal order**
(`exists_bound_countPhase`, hypothesis `hM8` stated inline).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralCompanionPhase

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialInvariant
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen
  Hironaka.RestrictEmptyTower Hironaka.StepOneRegime
  Hironaka.StepOnePhase Hironaka.NonmonomialOrderLocal
  Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical
  Hironaka.NonmonomialOrderTail Hironaka.NonmonomialOrderGlobalPhase
  Hironaka.MaxOrderValue Hironaka.GeneralValue
  Hironaka.GeneralCompare Hironaka.GeneralCanonicalTail
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSeq (GrowingSeq)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)

noncomputable section

variable {n : ℕ}

/-! ### Tools: splits of a concatenation, centres along a concatenation -/

section Tools

variable {X : CMfd.{u} n}

/-- **The split of a concatenation `T₀ S` at `r ≥ |S|`**: the head followed by a middle part `Mt` is `T₀`, and `Mt` followed by
`S` is the tail. -/
theorem exists_split_append {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (r : ℕ), S.length ≤ r →
      ∃ Mt : BlowupTower (split (T₀.append S) r).1 Y₀,
        (head (T₀.append S) r).append Mt = T₀ ∧ Mt.append S = tail (T₀.append S) r
  | _, .refl, r, _ => ⟨tail T₀ r, head_append_tail T₀ r, rfl⟩
  | _, .step S C π hπ, 0, h => absurd h (by simp)
  | _, .step S C π hπ, r + 1, h => by
      obtain ⟨Mt, h₁, h₂⟩ := exists_split_append T₀ S r (by simpa using h)
      refine ⟨Mt, h₁, ?_⟩
      show Mt.append (.step S C π hπ) = .step (tail (T₀.append S) r) C π hπ
      rw [BlowupTower.append_step, h₂]

/-- **Centres in `{ν ≥ o + 1}` along a concatenation**: those of `A`, then those of `B` for the transform along `A`. -/
theorem centresOrdGt_append (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ : CMfd.{u} n} (A : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (B : BlowupTower Y₀ Y),
      CentresOrdGt 𝔪 o (A.append B) ↔ CentresOrdGt 𝔪 o A ∧ CentresOrdGt (geoTransformAlong 𝔪 A) o B
  | _, .refl => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | _, .step B C π hπ => by
      have ih := centresOrdGt_append 𝔪 o A B
      show (CentresOrdGt 𝔪 o (A.append B) ∧ C ⊆ ordGe (geoTransformAlong 𝔪 (A.append B)) (o + 1)) ↔
        CentresOrdGt 𝔪 o A ∧ (CentresOrdGt (geoTransformAlong 𝔪 A) o B ∧
          C ⊆ ordGe (geoTransformAlong (geoTransformAlong 𝔪 A) B) (o + 1))
      rw [ih, geoTransformAlong_append, and_assoc]

/-- **Every point of every centre of `S` (after `T₀`) has order at least `o`.** -/
def CentresOrdGe (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    {Y : CMfd.{u} n} → BlowupTower Y₀ Y → Prop
  | _, .refl => True
  | _, .step S C _ _ => CentresOrdGe 𝔪 o T₀ S ∧ ∀ c ∈ C, o ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append S)) c

end Tools

/-! ### One companion ideal for the whole phase -/

section Phase

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The value of a point of the companion's cosupport, in a phase**: let `T₀` be a multiple test blow-up with `ν ≤ o` on the
cosupport (`o ≥ 1`) and every centre in `{ν ≥ o + 1}`, `T₀ S` a canonical segment of the general value which is a multiple test
blow-up, and `S|_W` (`W = ordMask 𝔪_{T₀} o`) a canonical segment of the companion ideal `compAt 𝔪 o T₀` for `M`.  At every point
`q` of the cosupport of that companion ideal along `S|_W`, the general value is `(o, M(q))`: `q` has order `o`, its run started at
or before `T₀`, the steps from its start to `T₀` have centres in `{ν ≥ o + 1}` and miss its mask, and
`GeneralCanonicalTail.genLowerValue_eq_rebase_of_eq` re-bases its companion value to `T₀`. -/
theorem genInv_eq_of_mem_cosupp_phase (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔪 T₀)
    (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o) (hgt : CentresOrdGt 𝔪 o T₀)
    {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (hT : IsGeoTestTower 𝔪 (T₀.append S))
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) (T₀.append S))
    (hcanW : IsCanonical (compAt 𝔪 o T₀) (M (compAt 𝔪 o T₀)) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S))
    (q : openPreimage S (ordMask (geoTransformAlong 𝔪 T₀) o))
    (hq : q ∈ (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S)).cosupp) :
    genInv M 𝔪 (T₀.append S) q = toLex (o, (toLex (Sum.inr ((M (compAt 𝔪 o T₀)
      (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S) q : Λ) : WithTop Λ)) : WithBot Val ⊕ₗ WithTop Λ)) := by
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
  have hT₁ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) S := ((isGeoTestTower_append_iff 𝔪 T₀ S).mp hT).2
  have hTW : IsGeoTestTower (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S) :=
    hM.isGeoTestTower_of_isCanonical (isInvDomain_compAt hn ho T₀ hdom₀) (isMaximalOrderAlong_compAt hn o T₀ hdom₀)
      _ hcanW
  obtain ⟨hqcos, hqo⟩ := (mem_cosupp_compAt_iff hn h ho T₀ S hT₀ hT₁ hTW q).mp hq
  rw [← geoTransformAlong_append] at hqcos hqo
  -- the run of `q` started at or before `T₀`
  have hrun := (ordRegime_and_length_le_regimeRun_of_le hn h hf T₀ h0 S hT hcan (q : Y) hqcos hqo).2
  set r := regimeRun (OrdRegime 𝔪 o) (T₀.append S) (q : Y) with hr
  have hD := hasGenLowerData_of_isCanonical M hM hn h (T₀.append S) hT hcan
  have hdq := hD (q : Y) hqcos o hqo ho
  obtain ⟨Mt, h₀, h₁⟩ := exists_split_append T₀ S r hrun
  -- the steps from the start of `q` to `T₀` miss its mask
  have hTh : IsGeoTestTower 𝔪 ((head (T₀.append S) r).append Mt) := by rw [h₀]; exact hT₀
  obtain ⟨hTh₁, hMtT⟩ := (isGeoTestTower_append_iff 𝔪 _ Mt).mp hTh
  have hgt' : CentresOrdGt 𝔪 o ((head (T₀.append S) r).append Mt) := by rw [h₀]; exact hgt
  have hMtc := ((centresOrdGt_append 𝔪 o _ Mt).mp hgt').2
  have hdomh := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hTh₁
  have hMt : CentresAvoid (ordMask (geoTransformAlong 𝔪 (head (T₀.append S) r)) o) Mt :=
    (centresAvoid_of_centresOrdGt hn hdomh _ (fun x _ hx => (mem_ordMask_iff hn hdomh.isWellFormed
      hdomh.isNonzeroAlongAt o x).mp hx) Mt hMtT hMtc).1
  obtain ⟨hval, -⟩ := genLowerValue_eq_rebase_of_eq hM hn h ho (head (T₀.append S) r) Mt S h₀ h₁ hT₀ hMt hdq q.2 hcanW
  rw [genInv_of_nmOrd_ne_zero M 𝔪 (T₀.append S) hqo (by omega), hval]

/-- **One companion ideal for the whole phase**: let `T₀` be a multiple test blow-up with `ν ≤ o` on the cosupport (`o ≥ 1`) and
every centre in `{ν ≥ o + 1}`, and `T₀ S` a canonical segment of the general value every centre of whose part `S` has order `≥ o`.
Then the restriction of `S` to the mask `W = ordMask 𝔪_{T₀} o` is a canonical segment of the companion ideal `compAt 𝔪 o T₀` for
`M`: over `W` the cosupport of the companion's transform is the set of points of order `o`
(`GeneralCanonicalTail.mem_cosupp_compAt_iff`), the general value there is `(o, M)` (`genInv_eq_of_mem_cosupp_phase`), every
other point of the cosupport has smaller order (the phase is absorbing, `NonmonomialOrderGlobalPhase.nmOrd_le_append_of_le`), and a
nonempty centre has a point of order `o` over `W`; so the trace of the maximum locus of the general value is the maximum locus of
`M` (`MaxLocusLocal.preimage_maxLocus_eq_or`). -/
theorem isCanonical_restrict_phase (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ}
    (ho : 1 ≤ o) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower 𝔪 T₀)
    (h0 : ∀ y ∈ (geoTransformAlong 𝔪 T₀).cosupp, nmOrd (geoTransformAlong 𝔪 T₀) y ≤ o) (hgt : CentresOrdGt 𝔪 o T₀) :
    ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y), IsCanonical 𝔪 (genInv M 𝔪) (T₀.append S) → CentresOrdGe 𝔪 o T₀ S →
      IsCanonical (compAt 𝔪 o T₀) (M (compAt 𝔪 o T₀)) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S)
  | _, .refl, _, _ => trivial
  | _, .step S C π hπ, hcan, hge => by
      have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
      have hcan' : IsCanonical 𝔪 (genInv M 𝔪) (.step (T₀.append S) C π hπ) := hcan
      have hcanS : IsCanonical 𝔪 (genInv M 𝔪) (T₀.append S) := hcan'.1
      have hC : C = ∅ ∨ C = maxLocus (genInv M 𝔪 (T₀.append S)) (geoTransformAlong 𝔪 (T₀.append S)).cosupp := hcan'.2
      have hge' : CentresOrdGe 𝔪 o T₀ S ∧ ∀ c ∈ C, o ≤ nmOrd (geoTransformAlong 𝔪 (T₀.append S)) c := hge
      have ih := isCanonical_restrict_phase hM hn h ho T₀ hT₀ h0 hgt S hcanS hge'.1
      have hT : IsGeoTestTower 𝔪 (T₀.append S) :=
        GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcanS
      have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T₀ hT₀
      have hT₁ : IsGeoTestTower (geoTransformAlong 𝔪 T₀) S := ((isGeoTestTower_append_iff 𝔪 T₀ S).mp hT).2
      have hTW : IsGeoTestTower (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S) :=
        hM.isGeoTestTower_of_isCanonical (isInvDomain_compAt hn ho T₀ hdom₀) (isMaximalOrderAlong_compAt hn o T₀ hdom₀)
          _ ih
      show IsCanonical (compAt 𝔪 o T₀) (M (compAt 𝔪 o T₀)) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S) ∧
        (((Subtype.val : openPreimage S (ordMask (geoTransformAlong 𝔪 T₀) o) → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage S (ordMask (geoTransformAlong 𝔪 T₀) o) → _) ⁻¹' C) =
            maxLocus (M (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S))
              (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S)).cosupp)
      refine ⟨ih, ?_⟩
      by_cases hne : C.Nonempty
      · have hCm := hC.resolve_left hne.ne_empty
        obtain ⟨c, hcC⟩ := hne
        have hcm : c ∈ maxLocus (genInv M 𝔪 (T₀.append S)) (geoTransformAlong 𝔪 (T₀.append S)).cosupp := hCm ▸ hcC
        -- the point `c` has order `o` and lies over the mask
        obtain ⟨hcproj, -, hcle⟩ := nmOrd_le_append_of_le hn h hf T₀ h0 S hT hcanS hcm.1
        have hco : nmOrd (geoTransformAlong 𝔪 (T₀.append S)) c = o := le_antisymm hcle (hge'.2 c hcC)
        have hcW : S.proj c ∈ ordMask (geoTransformAlong 𝔪 T₀) o :=
          cosupp_subset_ordMask_of_le hn h T₀ hT₀ h0 hcproj
        have hcs' : (⟨c, hcW⟩ : openPreimage S (ordMask (geoTransformAlong 𝔪 T₀) o)) ∈
            (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) S)).cosupp := by
          refine (mem_cosupp_compAt_iff hn h ho T₀ S hT₀ hT₁ hTW _).mpr ⟨?_, ?_⟩
          · rw [← geoTransformAlong_append]; exact hcm.1
          · rw [← geoTransformAlong_append]; exact hco
        rw [hCm]
        refine MaxLocusLocal.preimage_maxLocus_eq_or Subtype.val
          (φ := fun l : Λ => (toLex (o, (toLex (Sum.inr (l : WithTop Λ)) : WithBot Val ⊕ₗ WithTop Λ)) :
            ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ))) ?_ ?_ ?_ ?_
        · intro a b hab
          rw [Prod.Lex.toLex_lt_toLex]
          exact Or.inr ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr hab)⟩
        · intro p hp
          have hp' := ((mem_cosupp_compAt_iff hn h ho T₀ S hT₀ hT₁ hTW p).mp hp).1
          rw [← geoTransformAlong_append] at hp'
          exact hp'
        · intro p hp
          exact genInv_eq_of_mem_cosupp_phase hM hn h ho T₀ hT₀ h0 hgt S hT hcanS ih p hp
        · intro p hp hps'
          refine ⟨⟨c, hcW⟩, hcs', genInv_lt_of_nmOrd_lt M 𝔪 ?_⟩
          have hple := (nmOrd_le_append_of_le hn h hf T₀ h0 S hT hcanS hp).2.2
          have hpne : nmOrd (geoTransformAlong 𝔪 (T₀.append S)) p.1 ≠ o := by
            intro heq
            refine hps' ((mem_cosupp_compAt_iff hn h ho T₀ S hT₀ hT₁ hTW p).mpr ⟨?_, ?_⟩)
            · rw [← geoTransformAlong_append]; exact hp
            · rw [← geoTransformAlong_append]; exact heq
          rw [hco]
          omega
      · left
        rw [not_nonempty_iff_eq_empty.mp hne]
        exact preimage_empty

end Phase

/-! ### Counting the centres of a phase -/

section Count

variable {X : CMfd.{u} n}

open Classical in
/-- **The number of steps of the phase `o` meeting `K`**: the steps of `T` whose centre has a point over `K` at which the
nonmonomial part of the transform has order `o`. -/
def countPhase (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → ℕ
  | _, .refl => 0
  | _, .step T C _ _ =>
      countPhase 𝔪 K o T + if ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o then 1 else 0

open Classical in
theorem countPhase_step (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    countPhase 𝔪 K o (.step T C π hπ) =
      countPhase 𝔪 K o T + if ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o then 1 else 0 := rfl

theorem countPhase_step_of (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o) :
    countPhase 𝔪 K o (.step T C π hπ) = countPhase 𝔪 K o T + 1 := by
  rw [countPhase_step, if_pos hc]

theorem countPhase_step_of_not (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hc : ¬ ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o) :
    countPhase 𝔪 K o (.step T C π hπ) = countPhase 𝔪 K o T := by
  rw [countPhase_step, if_neg hc, Nat.add_zero]

/-- **A step of a phase meets `K`**: the count of a phase is at most the count of all centres meeting `K`. -/
theorem countPhase_le_countCentresMeeting (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), countPhase 𝔪 K o T ≤ countCentresMeeting K T
  | _, .refl => le_rfl
  | _, .step T C π hπ => by
      classical
      have ih := countPhase_le_countCentresMeeting 𝔪 K o T
      show countPhase 𝔪 K o (.step T C π hπ) ≤
        countCentresMeeting K T + (if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0)
      by_cases hc : ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o
      · obtain ⟨c, hcC, hcK, hco⟩ := hc
        rw [countPhase_step_of 𝔪 K o T C π hπ ⟨c, hcC, hcK, hco⟩, if_pos ⟨c, hcC, hcK⟩]
        omega
      · rw [countPhase_step_of_not 𝔪 K o T C π hπ hc]
        omega

/-- **The count of a phase along a concatenation**: that along `A`, plus that along `B` for the transform along `A` and the
preimage of `K`. -/
theorem countPhase_append (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) {Y₀ : CMfd.{u} n} (A : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (B : BlowupTower Y₀ Y),
      countPhase 𝔪 K o (A.append B) = countPhase 𝔪 K o A + countPhase (geoTransformAlong 𝔪 A) (A.proj ⁻¹' K) o B
  | _, .refl => rfl
  | _, .step B C π hπ => by
      rw [BlowupTower.append_step, countPhase_step, countPhase_step, countPhase_append 𝔪 K o A B,
        geoTransformAlong_append, BlowupTower.proj_append, Nat.add_assoc]
      rfl

/-- **The count of a phase vanishes when every centre lies in `{ν ≥ o + 1}`** (`𝔪` in the domain, `T` a multiple test
blow-up). -/
theorem countPhase_eq_zero_of_centresOrdGt {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪) (K : Set X) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → CentresOrdGt 𝔪 o T → countPhase 𝔪 K o T = 0
  | _, .refl, _, _ => rfl
  | _, .step T C π hπ, hT, hgt => by
      obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      obtain ⟨hgtT, hC⟩ := (centresOrdGt_step_iff 𝔪 o T C π hπ).mp hgt
      have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
      rw [countPhase_step_of_not, countPhase_eq_zero_of_centresOrdGt h K o T hTT hgtT]
      rintro ⟨c, hcC, -, hco⟩
      have := (mem_ordGe_iff hdom.isWellFormed hdom.isNonzeroAlongAt (ordGe_subset_N _ _ (hC hcC)) (o + 1)).mp (hC hcC)
      omega

end Count

/-! ### The phases along canonical segments of the general value -/

section CountCanonical

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **The centres meeting `K` are counted by the phases `o ≤ q`**: along a canonical segment of the general value, under the
hypothesis `hq` of `GeneralPhaseCount.countCentresMeeting_le_length_filter` (every point of every nonempty canonical centre
meeting the preimage of `K` has order `≤ q`), the number of centres meeting `K` is at most the sum of the counts of the phases
`o = 0, …, q`. -/
theorem countCentresMeeting_le_sum_countPhase (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪)
    {K : Set X} {q : ℕ}
    (hq : ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower 𝔪 (.step T C π hπ) → IsCanonical 𝔪 (genInv M 𝔪) (.step T C π hπ) →
        (C ∩ T.proj ⁻¹' K).Nonempty → ∀ c ∈ C, nmOrd (geoTransformAlong 𝔪 T) c ≤ q) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (genInv M 𝔪) T →
      countCentresMeeting K T ≤ ∑ o ∈ Finset.range (q + 1), countPhase 𝔪 K o T
  | _, .refl, _ => Nat.zero_le _
  | _, .step T C π hπ, hcan => by
      classical
      have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
      have hT : IsGeoTestTower 𝔪 (.step T C π hπ) :=
        GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan
      have ih := countCentresMeeting_le_sum_countPhase hM hn h hq T hcanT
      show countCentresMeeting K T + (if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0) ≤ _
      rw [Finset.sum_congr rfl fun o _ => countPhase_step 𝔪 K o T C π hπ, Finset.sum_add_distrib]
      by_cases hK : (C ∩ T.proj ⁻¹' K).Nonempty
      · obtain ⟨c, hcC, hcK⟩ := hK
        have hcq : nmOrd (geoTransformAlong 𝔪 T) c ≤ q := hq T C π hπ hT hcan ⟨c, hcC, hcK⟩ c hcC
        have h1 : 1 ≤ ∑ o ∈ Finset.range (q + 1),
            (if ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o then 1 else 0) := by
          refine le_trans ?_ (Finset.single_le_sum (f := fun o =>
            if ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o then 1 else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hcq)))
          rw [if_pos ⟨c, hcC, hcK, rfl⟩]
        rw [if_pos ⟨c, hcC, hcK⟩]
        omega
      · rw [if_neg hK]
        omega

/-- **The count of a phase is at most its number of centre values**: along a canonical segment of the general value, the
steps of the phase `o` meeting `K` are at most the entries of `StepOnePhase.centreValues (genInv M 𝔪) T` of order `o` (the
points of a canonical centre have one value, whose first entry is their order).  With `o = 0` and
`GeneralPhaseCount.exists_bound_phase_zero`, the phase `0` is bounded along growing sequences. -/
theorem countPhase_le_filter (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) (K : Set X) (o : ℕ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (genInv M 𝔪) T →
      countPhase 𝔪 K o T ≤ ((centreValues (genInv M 𝔪) T).filter fun v => (ofLex v).1 = o).length
  | _, .refl, _ => Nat.zero_le _
  | _, .step T C π hπ, hcan => by
      classical
      have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
      have hcanT : IsCanonical 𝔪 (genInv M 𝔪) T := hcan.1
      have hT : IsGeoTestTower 𝔪 (.step T C π hπ) :=
        GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ hcan
      obtain ⟨hTT, -⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      have ih := countPhase_le_filter hM hn h K o T hcanT
      by_cases hc : ∃ c ∈ C, T.proj c ∈ K ∧ nmOrd (geoTransformAlong 𝔪 T) c = o
      · obtain ⟨c, hcC, hcK, hco⟩ := hc
        have hne : C.Nonempty := ⟨c, hcC⟩
        have hC : C = maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp :=
          (hcan.2 : C = ∅ ∨ C = maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).resolve_left hne.ne_empty
        have hc' : c ∈ maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := hC ▸ hcC
        have hs' : hne.some ∈ maxLocus (genInv M 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := hC ▸ hne.some_mem
        have hfst : (ofLex (genInv M 𝔪 T hne.some)).1 = o := by
          rw [genInv_fst, nmOrd_eq_of_mem_maxLocus hf hTT hc' hs', hco]
        rw [countPhase_step_of 𝔪 K o T C π hπ ⟨c, hcC, hcK, hco⟩,
          centreValues_step_of_nonempty _ T C π hπ hne, List.filter_append, List.length_append,
          List.filter_singleton, decide_eq_true hfst]
        simp only [cond_true, List.length_singleton]
        omega
      · rw [countPhase_step_of_not 𝔪 K o T C π hπ hc]
        by_cases hne : C.Nonempty
        · rw [centreValues_step_of_nonempty _ T C π hπ hne, List.filter_append, List.length_append]
          omega
        · rw [centreValues_step_of_eq_empty _ T C π hπ (not_nonempty_iff_eq_empty.mp hne)]
          exact ih

end CountCanonical

/-! ### The phases of positive order are finite along growing sequences, given (8) of `M` -/

section Seq

variable {X : CMfd.{u} n} {k : ℕ} {𝔪 : MarkedIdeal n X} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- Counts of a phase never decrease along a growing sequence. -/
theorem countPhase_le_of_le (𝔪 : MarkedIdeal n X) (K : Set X) (o : ℕ) (s : GrowingSeq X) {i j : ℕ} (hij : i ≤ j) :
    countPhase 𝔪 K o (s.stage i).2 ≤ countPhase 𝔪 K o (s.stage j).2 := by
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih =>
      obtain ⟨C, π, hπ, heq⟩ := s.succ j
      rw [heq, countPhase_step]
      exact ih.trans (Nat.le_add_right _ _)

/-- **The phase `o ≥ 1` is finite along every growing sequence, given property (8) of `M`**: let `M` be a value function for
the marked ideals of maximal order (`n > 0`), with property (8) in its per-sequence form for the marked ideals of the domain of
maximal order along their submanifold (`hM8`), `𝔪` in the domain and `K ⊆ X` compact.  Along every growing sequence of
canonical segments of `genInv M 𝔪`, the counts of the phase `o ≥ 1` meeting `K` are bounded.

Proof: if at some stage `b` the order is `< o` on the whole cosupport, it stays so (the phase is absorbing,
`NonmonomialOrderCanonical.nmOrd_step_le_of_canonical`) and the count is constant from `b` on.  Otherwise every canonical centre
has order `≥ o`.  If the order is `> o` somewhere on the cosupport at every stage, no centre has order `o`.  Otherwise let `a`
be the first stage with `ν ≤ o` on the cosupport: every centre before it lies in `{ν ≥ o + 1}`, and every centre after it has
order `o`; so the restricted tails `(s.tail a).restrict W` (`W = ordMask 𝔪_{T_a} o`) are canonical segments of the ONE
companion ideal `compAt 𝔪 o T_a` (`isCanonical_restrict_phase`), along which `hM8` bounds the counts of the compact part of
the cosupport over `K`; these bound the counts of `K` after `a` (`TowerPreimageCompact.countCentresMeeting_append_eq_restrict`). -/
theorem exists_bound_countPhase (hM : IsMaxOrderValue n k M) (hn : 0 < n) (h : IsInvDomain k 𝔪) {o : ℕ} (ho : 1 ≤ o)
    {K : Set X} (hK : IsCompact K)
    (hM8 : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
      ∀ K : Set X, IsCompact K → ∀ s : GrowingSeq X, (∀ i, IsCanonical 𝔍 (M 𝔍) (s.stage i).2) →
        ∃ m, ∀ i, countCentresMeeting K (s.stage i).2 ≤ m)
    (s : GrowingSeq X) (hs : ∀ i, IsCanonical 𝔪 (genInv M 𝔪) (s.stage i).2) :
    ∃ m : ℕ, ∀ i, countPhase 𝔪 K o (s.stage i).2 ≤ m := by
  classical
  have hf : OrdMonotone 𝔪 (genInv M 𝔪) := ordMonotone_genInv M 𝔪
  have hT : ∀ i, IsGeoTestTower 𝔪 (s.stage i).2 := fun i =>
    GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv hM hn h _ (hs i)
  -- the step `i` of the sequence, a canonical test step
  have hstep : ∀ i, ∃ (C : Set (s.stage i).1) (π : (s.stage (i + 1)).1 → (s.stage i).1) (hπ : IsBlowupAlong n C π),
      (s.stage (i + 1)).2 = .step (s.stage i).2 C π hπ ∧ IsGeoTestTower 𝔪 (.step (s.stage i).2 C π hπ) ∧
        IsCanonical 𝔪 (genInv M 𝔪) (.step (s.stage i).2 C π hπ) := by
    intro i
    obtain ⟨C, π, hπ, heq⟩ := s.succ i
    refine ⟨C, π, hπ, heq, ?_, ?_⟩
    · rw [← heq]; exact hT (i + 1)
    · rw [← heq]; exact hs (i + 1)
  -- a bound for the order on the cosupport propagates
  have hprop : ∀ p i : ℕ, (∀ y ∈ (geoTransformAlong 𝔪 (s.stage i).2).cosupp,
      nmOrd (geoTransformAlong 𝔪 (s.stage i).2) y ≤ p) →
      ∀ y ∈ (geoTransformAlong 𝔪 (s.stage (i + 1)).2).cosupp, nmOrd (geoTransformAlong 𝔪 (s.stage (i + 1)).2) y ≤ p := by
    intro p i hp
    obtain ⟨C, π, hπ, heq, hTs, hcs⟩ := hstep i
    rw [heq]
    intro z hz
    obtain ⟨h1, h2⟩ := nmOrd_step_le_of_canonical hn h hf _ C π hπ hTs hcs.2 hz
    exact h2.trans (hp _ h1)
  -- steps whose centre has no point of order `o` do not count
  have hnot_lt : ∀ i, (∀ y ∈ (geoTransformAlong 𝔪 (s.stage i).2).cosupp, nmOrd (geoTransformAlong 𝔪 (s.stage i).2) y < o) →
      countPhase 𝔪 K o (s.stage (i + 1)).2 = countPhase 𝔪 K o (s.stage i).2 := by
    intro i hp
    obtain ⟨C, π, hπ, heq, hTs, -⟩ := hstep i
    rw [heq, countPhase_step_of_not]
    rintro ⟨c, hcC, -, hco⟩
    have := hp c (((isGeoTestTower_step_iff 𝔪 _ C π hπ).mp hTs).2.2.1 hcC)
    omega
  have hnot_gt : ∀ i, (∃ y ∈ (geoTransformAlong 𝔪 (s.stage i).2).cosupp, o < nmOrd (geoTransformAlong 𝔪 (s.stage i).2) y) →
      countPhase 𝔪 K o (s.stage (i + 1)).2 = countPhase 𝔪 K o (s.stage i).2 := by
    rintro i ⟨y, hy, hyo⟩
    obtain ⟨C, π, hπ, heq, -, hcs⟩ := hstep i
    rw [heq, countPhase_step_of_not]
    rintro ⟨c, hcC, -, hco⟩
    have := nmOrd_le_of_mem_centre hf (hT i) hcs hcC hy
    omega
  by_cases hA : ∃ b, ∀ y ∈ (geoTransformAlong 𝔪 (s.stage b).2).cosupp, nmOrd (geoTransformAlong 𝔪 (s.stage b).2) y ≤ o - 1
  · -- the phase is over at the stage `b`
    obtain ⟨b, hb⟩ := hA
    have hle : ∀ d, ∀ y ∈ (geoTransformAlong 𝔪 (s.stage (b + d)).2).cosupp,
        nmOrd (geoTransformAlong 𝔪 (s.stage (b + d)).2) y ≤ o - 1 := by
      intro d
      induction d with
      | zero => exact hb
      | succ d ih => exact hprop (o - 1) (b + d) ih
    have heqd : ∀ d, countPhase 𝔪 K o (s.stage (b + d)).2 = countPhase 𝔪 K o (s.stage b).2 := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
          rw [← ih]
          exact hnot_lt (b + d) fun y hy => by have := hle d y hy; omega
    refine ⟨countPhase 𝔪 K o (s.stage b).2, fun i => ?_⟩
    rcases le_or_gt i b with hib | hbi
    · exact countPhase_le_of_le 𝔪 K o s hib
    · obtain ⟨d, rfl⟩ : ∃ d, i = b + d := ⟨i - b, by omega⟩
      exact (heqd d).le
  · simp only [not_exists, not_forall, not_le] at hA
    by_cases hP : ∃ a, ∀ y ∈ (geoTransformAlong 𝔪 (s.stage a).2).cosupp, nmOrd (geoTransformAlong 𝔪 (s.stage a).2) y ≤ o
    · -- the first stage `a` with `ν ≤ o` on the cosupport
      have h0 := Nat.find_spec hP
      have hmin : ∀ j < Nat.find hP, ∃ y ∈ (geoTransformAlong 𝔪 (s.stage j).2).cosupp,
          o < nmOrd (geoTransformAlong 𝔪 (s.stage j).2) y := by
        intro j hj
        have := Nat.find_min hP hj
        simp only [not_forall, not_le] at this
        obtain ⟨y, hy, hyo⟩ := this
        exact ⟨y, hy, hyo⟩
      have hgt : ∀ j, j ≤ Nat.find hP → CentresOrdGt 𝔪 o (s.stage j).2 := by
        intro j
        induction j with
        | zero =>
            intro _
            rw [s.zero]
            trivial
        | succ j ih =>
            intro hj
            obtain ⟨C, π, hπ, heq, hTs, hcs⟩ := hstep j
            rw [heq, centresOrdGt_step_iff]
            refine ⟨ih (by omega), fun c hc => ?_⟩
            obtain ⟨y, hy, hyo⟩ := hmin j (by omega)
            have hyc := nmOrd_le_of_mem_centre hf (hT j) hcs hc hy
            have hdom := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ (hT j)
            exact (mem_ordGe_iff hdom.isWellFormed hdom.isNonzeroAlongAt
              (((isGeoTestTower_step_iff 𝔪 _ C π hπ).mp hTs).2.subset_N hc) (o + 1)).mpr (by omega)
      -- every centre after `a` has order `o`
      have hge : ∀ d, CentresOrdGe 𝔪 o (s.stage (Nat.find hP)).2 (s.tailTower (Nat.find hP) d) := by
        intro d
        induction d with
        | zero => trivial
        | succ d ih =>
            show CentresOrdGe 𝔪 o (s.stage (Nat.find hP)).2 (s.tailTower (Nat.find hP) d) ∧
              ∀ c ∈ (s.succ (Nat.find hP + d)).choose,
                o ≤ nmOrd (geoTransformAlong 𝔪 ((s.stage (Nat.find hP)).2.append (s.tailTower (Nat.find hP) d))) c
            refine ⟨ih, fun c hc => ?_⟩
            have hcs : IsCanonical 𝔪 (genInv M 𝔪)
                (.step ((s.stage (Nat.find hP)).2.append (s.tailTower (Nat.find hP) d))
                  (s.succ (Nat.find hP + d)).choose (s.succ (Nat.find hP + d)).choose_spec.choose
                  (s.succ (Nat.find hP + d)).choose_spec.choose_spec.choose) := by
              have := hs (Nat.find hP + (d + 1))
              rw [s.stage_add_eq_append (Nat.find hP) (d + 1)] at this
              exact this
            have hTs : IsGeoTestTower 𝔪 ((s.stage (Nat.find hP)).2.append (s.tailTower (Nat.find hP) d)) := by
              rw [← s.stage_add_eq_append (Nat.find hP) d]
              exact hT _
            obtain ⟨y, hy, hyo⟩ := hA (Nat.find hP + d)
            rw [s.stage_add_eq_append (Nat.find hP) d] at hy hyo
            exact (show o ≤ _ by omega).trans (nmOrd_le_of_mem_centre hf hTs hcs hc hy)
      have hT₀ := hT (Nat.find hP)
      have hdom₀ := InvDomainTowerAlong.isInvDomain_geoTransformAlong h _ hT₀
      have hcanW : ∀ d, IsCanonical (compAt 𝔪 o (s.stage (Nat.find hP)).2) (M (compAt 𝔪 o (s.stage (Nat.find hP)).2))
          (((s.tail (Nat.find hP)).restrict (ordMask (geoTransformAlong 𝔪 (s.stage (Nat.find hP)).2) o)).stage d).2 :=
        fun d => isCanonical_restrict_phase hM hn h ho _ hT₀ h0 (hgt _ le_rfl) (s.tailTower (Nat.find hP) d)
          (by rw [← s.stage_add_eq_append (Nat.find hP) d]; exact hs _) (hge d)
      have hWsub : (s.stage (Nat.find hP)).2.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 (s.stage (Nat.find hP)).2).cosupp ⊆
          ordMask (geoTransformAlong 𝔪 (s.stage (Nat.find hP)).2) o :=
        fun y hy => cosupp_subset_ordMask_of_le hn h _ hT₀ h0 hy.2
      have hK' : IsCompact ((Subtype.val : ordMask (geoTransformAlong 𝔪 (s.stage (Nat.find hP)).2) o → _) ⁻¹'
          ((s.stage (Nat.find hP)).2.proj ⁻¹' K ∩ (geoTransformAlong 𝔪 (s.stage (Nat.find hP)).2).cosupp)) :=
        (TowerPreimageCompact.countCentresMeeting_append_eq_restrict h hK _ .refl hT₀ _ hWsub).1
      obtain ⟨m', hm'⟩ := hM8 (compAt 𝔪 o (s.stage (Nat.find hP)).2) (isInvDomain_compAt hn ho _ hdom₀)
        (isMaximalOrderAlong_compAt hn o _ hdom₀) _ hK' _ hcanW
      refine ⟨countCentresMeeting K (s.stage (Nat.find hP)).2 + m', fun i => ?_⟩
      refine (countPhase_le_countCentresMeeting 𝔪 K o _).trans ?_
      rcases le_or_gt i (Nat.find hP) with hia | hai
      · exact (s.count_mono K hia).trans (Nat.le_add_right _ _)
      · obtain ⟨d, rfl⟩ : ∃ d, i = Nat.find hP + d := ⟨i - Nat.find hP, by omega⟩
        have hTd : IsGeoTestTower 𝔪 ((s.stage (Nat.find hP)).2.append (s.tailTower (Nat.find hP) d)) := by
          rw [← s.stage_add_eq_append (Nat.find hP) d]
          exact hT _
        rw [s.stage_add_eq_append (Nat.find hP) d,
          (TowerPreimageCompact.countCentresMeeting_append_eq_restrict h hK _ (s.tailTower (Nat.find hP) d) hTd _
            hWsub).2]
        exact Nat.add_le_add_left (hm' d) _
    · -- the order is `> o` somewhere at every stage: no centre has order `o`
      simp only [not_exists, not_forall, not_le] at hP
      refine ⟨0, fun i => ?_⟩
      induction i with
      | zero =>
          rw [s.zero]
          exact le_rfl
      | succ i ih =>
          obtain ⟨y, hy, hyo⟩ := hP i
          rw [hnot_gt i ⟨y, hy, hyo⟩]
          exact ih

end Seq

end

end Hironaka.GeneralCompanionPhase
