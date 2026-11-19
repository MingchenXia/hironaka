import Hironaka.Resolution.HironakaG8ClassStep
import Hironaka.Resolution.HironakaG8ClassStepCut
import Hironaka.Resolution.HironakaG8ClassStepExp
import Hironaka.Resolution.HironakaG8StageExponents
import Hironaka.Resolution.HironakaG8LocalContactStage
import Hironaka.Resolution.HironakaG8SpecialLoci
import Hironaka.Resolution.HironakaG11InvBMLowerDomainSucc
import Hironaka.Invariant.ContactStageInvDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Independence of the hypersurface of maximal contact (repair (B'), plan module 6)

Blueprint: `hironaka-g8b-family-tangent.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 module 6, §6c, §6d
(module 6 is applied to the padded lower invariants `R := Rm m`; its statement is generic in `R`).  Inbox I-1363 (statement),
I-1370 C-0001 (released to lane G8B).  Source: Bierstone--Milman 2008, §5 Step I.A ("the marked ideals `𝒞_U(ℐ)` and `𝒞_V(ℐ)`
defined in two overlapping charts `U` and `V` are equivalent in `U ∩ V` ...; therefore, by functoriality in dimension `n − 1`,
their resolution sequences are the same over `U ∩ V`") and Step I.B.

Lane G11B's `HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R` says that the values of the lower invariant `R` on
Bierstone--Milman's lower ideals do not depend on the hypersurface of maximal contact.  For `R` class functorial for
`LocWPEquiv` it follows from the class data of the two lower ideals on the overlap (lane G8C's skeleton
`HironakaG8ClassStep.inv_eq_on_inter`):

* **`locWPEquiv_lowerIdealWBM`** (every level): the two restricted lower ideals are `LocWPEquiv` — at level `0` lane G8's port
  P4 at the stage (`HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM_two`) moved to the open
  (`HironakaG8LocalTransport.locWPEquiv_restrict_of_le`); at the levels `s + 1` lane G8C's Step I.B relation
  (`HironakaG8ClassStepCut.CutRel`, with no member to cut: the `ℰ`-term only involves original members through the anchor);
* **`sameCarrierDim_lowerIdealWBM`** (every level): both carriers are strict transforms of hypersurfaces of maximal contact,
  of dimension one less than `N_{T₀}` at every cosupport point (`ContactStageInvDomain.exists_regularAtDim_strictAlong_stage`);
* **`expAgree_lowerIdealWBM`**: the boundary exponents agree — at level `0` lane G8's stage-local P6
  (`HironakaG8StageExponents.expAgree_stage_contactCoeffBM_two_of_isInvDomain`); at the levels `s + 1`, at or above the mark by
  lane G8C's `HironakaG8ClassStepExp.expAgree_of_expAgreeBelowMark` (BM08 Theorem 6.1), below the mark this is the named input
  **`TangentExpAgreeSuccBM`** (in progress in lane G8 r7: the exponent along a born member of `𝒞 + ℰ_S` on the two carriers;
  Bierstone--Milman 2008, Theorem 6.2 with §5 Step I.A, see G8 `REPORT-r6.md` "Level s + 1");
* **`tangentIndepBM_of_classFunctorial_of_expAgreeSucc`**: plan module 6 (I-1363 statement) given `TangentExpAgreeSuccBM n k`
  (the only input; everything else, in particular the level-`0` case and the `LocWPEquiv`/`SameCarrierDim` parts at every level,
  is proved).  The Seq form consumed by `HironakaG8BFamily.TangentIndepStepBM` is in `HironakaG8BFamilyTangentSeq`.

Sorry-free.  Universe `0` for the manifolds (as lane G8's local equivalences), values in any universe.  Only `R.inv` and the
fields used by lane G8C's `inv_eq_on_inter` are used (not property (8)), so the Seq transport applies.  Import discipline
(Hironaka phase): no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8BFamilyTangent

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.MarkedIdealRestrictOpen
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMTangentIndep
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaG8LocalHistory (LocWPEquiv LocEquiv)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8ClassStepExp (ExpAgreeBelowMark)

noncomputable section

variable {n : ℕ}

/-! ### The named input: boundary exponents at the levels `s + 1` -/

variable (n) in
/-- **Boundary exponents of the lower ideals of levels `≥ 1` for two hypersurfaces of maximal contact** (input of plan module
6 at the levels `s + 1`; Bierstone--Milman 2008, §5 Step I.A with Theorem 6.2): for a marked ideal `𝔍` of the domain in
dimension `≤ k` of maximal order, along a multiple test blow-up `T₀` of `J̄`, at an anchor `a` of the cosupport of level
`s + 1`, for tangent directions `w` on `U` and `w'` on `U'` and an open `O` of the stage over `U ∩ U'` on which both restricted
lower ideals `𝒞_w + ℰ_S`, `𝒞_{w'} + ℰ_S` (`S` the original members through `a`) lie in the domain in dimension `≤ k - 1`, the two
restricted lower ideals have the same exponents along the (born) members of the divisor at the points of the cosupport where
the exponent of the first is BELOW the mark (lane G8C's `HironakaG8ClassStepExp.ExpAgreeBelowMark`; at or above the mark the
agreement is proved, `HironakaG8ClassStepExp.expAgree_of_expAgreeBelowMark`, BM08 Theorem 6.1).  At level `0` the full
agreement is proved (`HironakaG8StageExponents.expAgree_stage_contactCoeffBM_two_of_isInvDomain`); lane G8 r7 is proving the
levels `s + 1` (draft `HironakaG8SuccExponents`), which discharges this input through `HironakaG8ClassStepExp.ExpAgree.belowMark`. -/
def TangentExpAgreeSuccBM (k : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀), IsGeoTestTower (barMarked 𝔍) T₀ →
    ∀ (s : ℕ) (a : Y₀), a ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp → level 𝔍 T₀ a = s + 1 →
    ∀ (U U' : Set X) (w w' : X → ℂ), IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w →
      IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' w' →
    ∀ (O : Opens Y₀), (O : Set Y₀) ⊆ T₀.proj ⁻¹' U → (O : Set Y₀) ⊆ T₀.proj ⁻¹' U' →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 (s + 1) w T₀ (throughMembers 𝔍 T₀ a))) →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 (s + 1) w' T₀ (throughMembers 𝔍 T₀ a))) →
      ExpAgreeBelowMark (Y := CMfd.of (n := n) O)
        (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) w T₀ (throughMembers 𝔍 T₀ a)))
        (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 (s + 1) w' T₀ (throughMembers 𝔍 T₀ a)))

/-! ### The class data of the two lower ideals on a common open -/

section ClassData

variable {X : CMfd.{0} n} {𝔍 : MarkedIdeal n X} {Y₀ : CMfd.{0} n}

/-- The carrier of the lower ideal at every level is the strict transform of the hypersurface of maximal contact. -/
theorem lowerIdealWBM_N (s : ℕ) (w : X → ℂ) (T₀ : BlowupTower X Y₀) (S : List (Set Y₀)) :
    (lowerIdealWBM 𝔍 s w T₀ S).N = strictAlong T₀ (𝔍.N ∩ {x | w x = 0}) := by
  cases s <;> rfl

/-- **The two restricted lower ideals are `LocWPEquiv`** (every level; BM08 §5 Step I.A, and Step I.B at the levels `s + 1`). -/
theorem locWPEquiv_lowerIdealWBM (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔍) (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (s : ℕ) (a : Y₀) {U U' : Set X} {w w' : X → ℂ}
    (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) (hw' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' w')
    (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U) (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') :
    LocWPEquiv (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a))) := by
  have h𝔍 := h.isWellFormed
  have hd := h.one_le_d
  have hT₀a : IsGeoTestTower 𝔍 T₀ := HironakaG11InvBMStage.isGeoTestTower_of_barMarked h𝔍 hd T₀ hT₀
  have hcL : (contactCoeffBM 𝔍 w T₀).ideal.IsCoherent := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn 0 w T₀ hT₀ a
  have hcL' : (contactCoeffBM 𝔍 w' T₀).ideal.IsCoherent := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn 0 w' T₀ hT₀ a
  let W : Opens X := ⟨U ∩ U', hw.isOpen.inter hw'.isOpen⟩
  have hOV : O ≤ openPreimage T₀ W := fun y hy => ⟨hOU hy, hOU' hy⟩
  have hLV := HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM_two h𝔍 hd ⟨U, hw.isOpen⟩ T₀ hT₀a
    (U' := ⟨U', hw'.isOpen⟩) hw hw' W inter_subset_left inter_subset_right
  have hLO := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcL hcL' hOV hLV
  cases s with
  | zero => exact hLO
  | succ s =>
    have hJ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (StepOneLowerDomain.isWellFormed_barMarked 𝔍 h𝔍) T₀ hT₀
    have hSm : ∀ H ∈ (throughMembers 𝔍 T₀ a).map ((Subtype.val : O → Y₀) ⁻¹' ·), IsClosedSubmanifold n H := by
      intro H' hH'
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_take (mem_throughMembers.mp hH).1)
      exact BlowupRestrictOpen.isClosedSubmanifold_preimage_val
        (MonomialPart.isClosedSubmanifold_get hn hJ.isSNCDivisor i) O
    have hwf := (HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd ⟨U, hw.isOpen⟩ hw T₀
      h.dimLE hT₀ O fun _ hy => hOU hy).1
    have hwf' := (HironakaG11InvBMLowerDomainSucc.isWellFormed_dimLE_contactCoeffBM_of_le h𝔍 hd ⟨U', hw'.isOpen⟩ hw' T₀
      h.dimLE hT₀ O fun _ hy => hOU' hy).1
    have hPA := HironakaG8ClassStepCut.ExcRel.pullback_val'
      (HironakaG8LocalExcSum.excRel_sumIdeal (contactCoeffBM 𝔍 w T₀) hcL (throughMembers 𝔍 T₀ a))
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL) O
    have hPB := HironakaG8ClassStepCut.ExcRel.pullback_val'
      (HironakaG8LocalExcSum.excRel_sumIdeal (contactCoeffBM 𝔍 w' T₀) hcL' (throughMembers 𝔍 T₀ a))
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL') O
    have hdA : 1 ≤ (contactCoeffBM 𝔍 w T₀).d := by
      rw [contactCoeffBM_d]
      exact HironakaG8ClassStepCut.one_le_coeffEmptyBM_d 𝔍
    have hdB : 1 ≤ (contactCoeffBM 𝔍 w' T₀).d := by
      rw [contactCoeffBM_d]
      exact HironakaG8ClassStepCut.one_le_coeffEmptyBM_d 𝔍
    exact HironakaG8ClassStepCut.locEquiv_of_cutRel rfl ⟨_, _, [], _, hLO, rfl, hwf.isSNCDivisor,
      fun H hH => absurd hH List.not_mem_nil, hSm, hwf, hwf', hdA, hdB, hPA, hPB⟩

/-- **The two restricted lower ideals have carriers of the same dimension on the cosupport** (every level). -/
theorem sameCarrierDim_lowerIdealWBM (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔍) (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (s : ℕ) (a : Y₀) {U U' : Set X} {w w' : X → ℂ}
    (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) (hw' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' w')
    (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U) (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U') :
    SameCarrierDim (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a))) := by
  have h𝔍 := h.isWellFormed
  have hd := h.one_le_d
  have hT₀a : IsGeoTestTower 𝔍 T₀ := HironakaG11InvBMStage.isGeoTestTower_of_barMarked h𝔍 hd T₀ hT₀
  have hloc := locWPEquiv_lowerIdealWBM hn h T₀ hT₀ s a hw hw' O hOU hOU'
  have hcoh := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn s w T₀ hT₀ a
  have hcoh' := isCoherent_lowerIdealWBM 𝔍 h𝔍 hd hn s w' T₀ hT₀ a
  intro x hx j
  have hxB : x ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a))).cosupp := hloc.cosupp_eq_base ▸ hx
  have hxA' : (x : Y₀) ∈ (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)).cosupp := by
    have h1 := cosupp_pullback_val (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a))
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh) O
    have h2 : x ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀)
        (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a))).cosupp := hx
    rw [h1] at h2
    exact h2
  have hxB' : (x : Y₀) ∈ (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a)).cosupp := by
    have h1 := cosupp_pullback_val (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a))
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcoh') O
    have h2 := hxB
    rw [h1] at h2
    exact h2
  have hxNA : (x : Y₀) ∈ strictAlong T₀ (𝔍.N ∩ {z | w z = 0}) := by
    rw [← lowerIdealWBM_N s w T₀ (throughMembers 𝔍 T₀ a)]
    exact (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)).cosupp_subset_N hxA'
  have hxNB : (x : Y₀) ∈ strictAlong T₀ (𝔍.N ∩ {z | w' z = 0}) := by
    rw [← lowerIdealWBM_N s w' T₀ (throughMembers 𝔍 T₀ a)]
    exact (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a)).cosupp_subset_N hxB'
  obtain ⟨j₁, hNA, hPA⟩ := ContactStageInvDomain.exists_regularAtDim_strictAlong_stage 𝔍 h𝔍.isClosedSubmanifold_N
    h𝔍.isCoherent hd ⟨U, hw.isOpen⟩ hw T₀ hT₀a (hOU x.2) hxNA
  obtain ⟨j₂, hNB, hPB⟩ := ContactStageInvDomain.exists_regularAtDim_strictAlong_stage 𝔍 h𝔍.isClosedSubmanifold_N
    h𝔍.isCoherent hd ⟨U', hw'.isOpen⟩ hw' T₀ hT₀a (hOU' x.2) hxNB
  have hj : j₂ = j₁ := Nat.succ_injective (RegularPointDimension.eq_of_regularAtDim hNB hNA)
  rw [hj] at hPB
  show RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)).N) x j ↔
    RegularAtDim (n := n) ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a)).N) x j
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff, AnalyticSubsetOpens.regularAtDim_preimage_val_iff,
    lowerIdealWBM_N, lowerIdealWBM_N]
  exact HironakaG8SpecialLoci.regularAtDim_iff_of_regularAtDim hPA hPB j

/-- **The two restricted lower ideals have the same boundary exponents** (level `0`: proved; levels `s + 1`: the input
`TangentExpAgreeSuccBM`). -/
theorem expAgree_lowerIdealWBM (hn : 0 < n) {k : ℕ} (hsucc : TangentExpAgreeSuccBM n k) (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀)
    (s : ℕ) (a : Y₀) (ha : a ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) (hlev : level 𝔍 T₀ a = s)
    {U U' : Set X} {w w' : X → ℂ} (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w)
    (hw' : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U' w') (O : Opens Y₀) (hOU : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U)
    (hOU' : (O : Set Y₀) ⊆ T₀.proj ⁻¹' U')
    (hdom : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a))))
    (hdom' : IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O → Y₀)
      (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a)))) :
    ExpAgree (X := CMfd.of (n := n) O)
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealWBM 𝔍 s w' T₀ (throughMembers 𝔍 T₀ a))) := by
  cases s with
  | zero =>
    exact HironakaG8StageExponents.expAgree_stage_contactCoeffBM_two_of_isInvDomain h.isWellFormed h.one_le_d hw hw' T₀
      (HironakaG11InvBMStage.isGeoTestTower_of_barMarked h.isWellFormed h.one_le_d T₀ hT₀) O hOU hOU' hdom hdom'
  | succ s =>
    exact HironakaG8ClassStepExp.expAgree_of_expAgreeBelowMark hn
      (locWPEquiv_lowerIdealWBM hn h T₀ hT₀ (s + 1) a hw hw' O hOU hOU') hdom hdom'
      (sameCarrierDim_lowerIdealWBM hn h T₀ hT₀ (s + 1) a hw hw' O hOU hOU') rfl
      (hsucc 𝔍 h hmax T₀ hT₀ s a ha hlev U U' w w' hw hw' O hOU hOU' hdom hdom')

end ClassData

/-! ### Plan module 6 -/

section Module6

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Plan module 6: independence of the hypersurface of maximal contact** (BM08 §5 Step I.A; statement of inbox I-1363, with
the boundary exponents of the lower ideals of levels `≥ 1` as the input `TangentExpAgreeSuccBM`): for `0 < n` and a lower
invariant `R` in dimension `≤ k - 1` class functorial for `LocWPEquiv`, every marked ideal of the domain in dimension `≤ k` of
maximal order has `TangentIndepBM 𝔍 R`.  Proof: on `O₁ ⊓ O₂` the two restricted lower ideals carry the class data
(`locWPEquiv_lowerIdealWBM`, `sameCarrierDim_lowerIdealWBM`, `expAgree_lowerIdealWBM`; same mark and divisor), and lane G8C's
`HironakaG8ClassStep.inv_eq_on_inter` concludes. -/
theorem tangentIndepBM_of_classFunctorial_of_expAgreeSucc (hsucc : TangentExpAgreeSuccBM n k) (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv) {X : CMfd.{0} n}
    (𝔍 : MarkedIdeal n X) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) :
    TangentIndepBM 𝔍 R := by
  intro Y₀ Y T₀ T₁ hT s a ha hlev U₁ U₂ w₁ w₂ hw₁ hw₂ O₁ O₂ hO₁ hO₂ hd₁ hd₂ hc₁ hc₂ p hp₁ hp₂ hcos
  have hT₀ : IsGeoTestTower (barMarked 𝔍) T₀ := ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1
  have hcoh₁ := isCoherent_lowerIdealWBM 𝔍 h.isWellFormed h.one_le_d hn s w₁ T₀ hT₀ a
  have hcoh₂ := isCoherent_lowerIdealWBM 𝔍 h.isWellFormed h.one_le_d hn s w₂ T₀ hT₀ a
  obtain ⟨-, hdd, hEE⟩ := lowerIdealWBM_ideal_eq 𝔍 s w₂ w₁ T₀ (throughMembers 𝔍 T₀ a)
  refine (HironakaG8ClassStep.inv_eq_on_inter R hR T₁ hcoh₂ hcoh₁ hdd hEE hd₂ hd₁ hc₂ hc₁ ?_ hp₂ hp₁ hcos).symm
  intro hda hdb
  have hOU₂ : ((O₂ ⊓ O₁ : Opens Y₀) : Set Y₀) ⊆ T₀.proj ⁻¹' U₂ := fun _ hy => hO₂ hy.1
  have hOU₁ : ((O₂ ⊓ O₁ : Opens Y₀) : Set Y₀) ⊆ T₀.proj ⁻¹' U₁ := fun _ hy => hO₁ hy.2
  exact ⟨locWPEquiv_lowerIdealWBM hn h T₀ hT₀ s a hw₂ hw₁ _ hOU₂ hOU₁,
    sameCarrierDim_lowerIdealWBM hn h T₀ hT₀ s a hw₂ hw₁ _ hOU₂ hOU₁,
    expAgree_lowerIdealWBM hn hsucc h hmax T₀ hT₀ s a ha hlev hw₂ hw₁ _ hOU₂ hOU₁ hda hdb⟩

end Module6

end

end Hironaka.HironakaG8BFamilyTangent
