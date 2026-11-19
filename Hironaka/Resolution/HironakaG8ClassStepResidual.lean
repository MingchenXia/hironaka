import Hironaka.Resolution.HironakaG8ClassStepExp
import Hironaka.Resolution.HironakaG8StageExponents
import Hironaka.Resolution.HironakaG8SumExponents

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The boundary exponents of the lower ideals of class-equivalent marked ideals: the proved cases (G8C lane, run 0080,
round 3; (B') plan module 10)

Blueprint: `hironaka-g8-class-step-residual.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §6c (module 10), this lane's
`REPORT-r2.md` ("The remaining hypothesis `hExp`") and `REPORT-r3.md`.

For class-equivalent `A ≈ B` of maximal order, the restricted lower ideals `P = lower_A|_O`, `Q = lower_B|_O` on a common open
`O` of the masks (lane G11B's `HironakaG11InvBMLower.lowerIdealBM`, divisor = the members born along `T₀`) have the same boundary
exponents at every cosupport point `y` on a born member `H`, except possibly in the following situation (the RESIDUAL):

* the exponent of `P` along `H` at `y` is below the mark of the lower ideals (above it: `HironakaG8ClassStepExp`, BM08 Theorem
  6.1), and
* at level `0`: the base point of `y` lies on an original member (the history of `y` enters `E`); at the levels `s + 1`: the
  `ℰ`-term `Σ_{H' ∈ S} 𝓘_{H'}^{d_𝒞}` is divisible by `𝓘_H` along one of the two carriers near `y` (the trace of `H` on the
  carrier lies in the original member: `S = {H'}`, the degenerate case).

Proved here:

* **`base_contact_AB`**: on an open `W ⊆ U_A ∩ U_B` meeting no original member, BM's `𝒞_W(A_∅)` and `𝒞_W(B_∅)` on the two
  hypersurfaces of maximal contact are well formed, `LocWPEquiv` and have carriers of the same dimension;
* **`expAgreeAt_lowerIdealBM_zero_of_notMem`**: level `0` at points whose base point lies on no original member (lane G8's
  stage-local P6 `HironakaG8DomainExponents.expAgreeAt_geoTransformAlong_of_domain` for the base pair on such a `W`);
* **`divExpAlong_lowerIdealBM_succ_eq_zero`**: levels `s + 1`, where the `ℰ`-term is not divisible by `𝓘_H` along the carrier,
  the exponent is `0` (lane G8's `HironakaG8SumExponents.divExpAlong_sumIdeal_eq_zero`);
* `LowerExpResidual A B` (the residual) and **`lowerPairs_expAgree_of_residual`**,
  **`classFunctorialMaxOrder_stepOneInvBM_of_residual`**: (B') plan module 10 given only the residual.

Sorry-free.  Universe `0`.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe v

namespace Hironaka.HironakaG8ClassStepResidual

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.HomogenizedIdealAlong
  Hironaka.MarkedIdealOperationsAlong
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.ContactEquivalenceAlong Hironaka.TangentDirectionAlong
  Hironaka.NormalCrossings Hironaka.GermIdealOrder
  Hironaka.StepOneValue Hironaka.HironakaG11InvBMMask
  Hironaka.HironakaG11InvBMLower Hironaka.HironakaG11InvBMStage
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalContact
  Hironaka.HironakaG8DomainExponents Hironaka.CoefficientIdealRestriction
  Hironaka.CoefficientIdealAlongRestrictionTower Hironaka.RestrictedIdealWeight
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim ExpAgree ClassFunctorialFor)
open Hironaka.HironakaG8P1GenInv (ClassFunctorialMaxOrderFor)
open Hironaka.HironakaG8ClassStep (LowerPairs)
open Hironaka.RestrictedIdealExtension (sumIdeal)

noncomputable section

variable {n : ℕ} {X : CMfd.{0} n}

/-! ### Level `0`, history off the original members -/

section LevelZero

/-- The coefficient ideal of `𝔍_∅` on a hypersurface of maximal contact, restricted to an open `W` inside the open set of the
tangent direction: well formed, and its carrier has dimension one less than that of `𝔍`. -/
private theorem contact_facts {𝔍 : MarkedIdeal n X} (h𝔍 : 𝔍.IsWellFormed) {U : Set X} {w : X → ℂ}
    (hw : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) (W : Opens X) (hWU : (W : Set X) ⊆ U) :
    (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM 𝔍) (𝔍.N ∩ {x | w x = 0}))).IsWellFormed ∧
      ∀ x ∈ (Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0}), ∃ k,
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' 𝔍.N) x k ∧
        RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (𝔍.N ∩ {y | w y = 0})) x (k - 1) := by
  have hN := h𝔍.isClosedSubmanifold_N
  have h𝔞 := h𝔍.isCoherent
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have hwW := IsTangentDirectionAlong.mono_open hw W.isOpen hWU
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcU : (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have hwU := isTangentDirectionAlong_pullback_val W hhol hwW
  have h1 := isClosedSubmanifold_contact_along (X := CMfd.of (n := n) W)
    (𝔪 := MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)) hNU hcU hwU
  rw [preimage_val_contact_eq W] at h1
  have hwfc := isWellFormed_coeffEmptyBM h𝔍
  have hcohA := GermIdealPullbackCalculus.isCoherent_pullback hval hwfc.isCoherent
  refine ⟨⟨h1, hcohA, isSNCDivisor_nil, isTransverse_nil_of_isClosedSubmanifold h1⟩, fun x hx => ?_⟩
  have hx' : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary 𝔍)).N ∩
      {x : W | (w ∘ Subtype.val) x = 0} ∩ univ := by
    rw [preimage_val_contact_eq W]; exact hx
  obtain ⟨k, hk, hk'⟩ := IsTangentDirectionAlong.regularAtDim_contact
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcU) hNU hwU hx'
  rw [preimage_val_contact_eq W] at hk'
  exact ⟨k, hk, hk'⟩

/-- **The base objects for `A` and `B` off the original members**: for class-equivalent `A ≈ B` (`LocWPEquiv`, the same divisor,
carriers of the same dimension on the cosupport), tangent directions `u_A` on `U_A`, `u_B` on `U_B` and an open
`W ⊆ U_A ∩ U_B` meeting no member of the divisor, BM's `𝒞_W(A_∅)` and `𝒞_W(B_∅)` on the two hypersurfaces of maximal contact
are well formed, `LocWPEquiv`, and have carriers of the same dimension on the cosupport. -/
theorem base_contact_AB {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (h : LocWPEquiv A B) (hdim : SameCarrierDim A B) {UA UB : Set X} {uA uB : X → ℂ}
    (huA : IsTangentDirectionAlong A.N A.ideal A.d UA uA) (huB : IsTangentDirectionAlong B.N B.ideal B.d UB uB)
    (W : Opens X) (hWA : (W : Set X) ⊆ UA) (hWB : (W : Set X) ⊆ UB) (hWE : ∀ H ∈ A.E, ∀ x ∈ (W : Set X), x ∉ H) :
    (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0}))).IsWellFormed ∧
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0}))).IsWellFormed ∧
      LocWPEquiv (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0})))
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0}))) ∧
      SameCarrierDim (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0})))
        (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0}))) := by
  obtain ⟨hwfA, hregA⟩ := contact_facts hA.isWellFormed huA W hWA
  obtain ⟨hwfB, hregB⟩ := contact_facts hB.isWellFormed huB W hWB
  -- `𝒞_W(A_∅) ≈ A_∅|_W ≈ B_∅|_W ≈ 𝒞_W(B_∅)`
  have hcA := locWPEquiv_contact_open_along (emptyBoundary A) hA.isWellFormed.isClosedSubmanifold_N
    hA.isWellFormed.isCoherent hA.one_le_d W (IsTangentDirectionAlong.mono_open huA W.isOpen hWA)
  have hcB := locWPEquiv_contact_open_along (emptyBoundary B) hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isCoherent hB.one_le_d W (IsTangentDirectionAlong.mono_open huB W.isOpen hWB)
  have hrest := LocEquiv.restrict h W
  have hsplit : (MarkedIdeal.pullback (Subtype.val : W → X) A).E =
      (MarkedIdeal.pullback (Subtype.val : W → X) A).E ++ [] := (List.append_nil _).symm
  have hempty : ∀ H ∈ (MarkedIdeal.pullback (Subtype.val : W → X) A).E, H = ∅ := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => hWE H₀ hH₀ z z.2 hz
  have hdrop := HironakaG8ClassStepLower.locEquiv_drop rfl hrest hsplit hempty
  have hAB : LocWPEquiv (X := CMfd.of (n := n) W)
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0})))
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0}))) :=
    hcA.symm.trans (hdrop.trans hcB)
  refine ⟨hwfA, hwfB, hAB, ?_⟩
  intro x hx j
  -- `x` lies in the cosupport of `A`
  have hxA0 : x ∈ (MarkedIdeal.pullback (Subtype.val : W → X) (emptyBoundary A)).cosupp := hcA.cosupp_eq_base ▸ hx
  have hxA : (x : X) ∈ A.cosupp := by
    have h1 := cosupp_pullback_val (emptyBoundary A)
      (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hA.isWellFormed.isCoherent) W
    rw [h1] at hxA0
    exact hxA0
  have hxB := hAB.cosupp_eq_base ▸ hx
  obtain ⟨kA, hkA, hkSA⟩ := hregA x (MarkedIdeal.cosupp_subset_N _ hx)
  obtain ⟨kB, hkB, hkSB⟩ := hregB x (MarkedIdeal.cosupp_subset_N _ hxB)
  have hkA' : RegularAtDim (n := n) A.N (x : X) kA := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkA
  have hkB' : RegularAtDim (n := n) B.N (x : X) kB := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hkB
  have hkk : kA = kB := RegularPointDimension.eq_of_regularAtDim ((hdim (x : X) hxA kA).mp hkA') hkB'
  show RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (A.N ∩ {y | uA y = 0})) x j ↔
    RegularAtDim (n := n) ((Subtype.val : W → X) ⁻¹' (B.N ∩ {y | uB y = 0})) x j
  constructor
  · intro hj
    rw [← RegularPointDimension.eq_of_regularAtDim hkSA hj, hkk]; exact hkSB
  · intro hj
    rw [← RegularPointDimension.eq_of_regularAtDim hkSB hj, ← hkk]; exact hkSA

/-- **Level `0`, history off the original members**: for class-equivalent `A ≈ B` of the domain of maximal order and a common
open `O` of the level-`0` masks on which both restricted lower ideals lie in the domain, the two restricted lower ideals have
the same boundary exponents at every point of `O` whose base point lies on no original member. -/
theorem expAgreeAt_lowerIdealBM_zero_of_notMem {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : HomogenizedIdealAlong.IsMaximalOrderAlong A.N A.ideal A.d)
    (hmB : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B) (hd : A.d = B.d)
    (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hn : 0 < n) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked A) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp)
    (O : Opens Y₀) (hOA : O ≤ maskBM A 0 T₀ y₀) (hOB : O ≤ maskBM B 0 T₀ y₀) {r r' : ℕ}
    (hdA : IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)))
    (hdB : IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B 0 T₀ y₀)))
    (p : O) (hp : ∀ H ∈ A.E, T₀.proj (p : Y₀) ∉ H) :
    ExpAgreeAt (Y := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B 0 T₀ y₀)) p := by
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hyA : y₀ ∈ (geoTransformAlong A T₀).cosupp := (hWA.2 T₀).2 hT₀ ▸ hy₀
  have hyB : y₀ ∈ (geoTransformAlong (barMarked B) T₀).cosupp := by
    rw [(hWB.2 T₀).2 hTJB, ← (hW.2 T₀).2 hTA]
    exact hyA
  -- the tangent directions chosen at the base point of `y₀`
  obtain ⟨-, hwA⟩ := StepOneLowerDomain.tangentChoice_spec A
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T₀ hT₀ hy₀)
  obtain ⟨-, hwB⟩ := StepOneLowerDomain.tangentChoice_spec B
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T₀ hTJB hyB)
  set uA := (tangentChoice A (T₀.proj y₀)).2 with huA
  set uB := (tangentChoice B (T₀.proj y₀)).2 with huB
  -- the open set of the base: both tangent open sets, off the original members
  have hEo : IsOpen (⋂ H ∈ {H | H ∈ A.E}, Hᶜ) :=
    (List.finite_toSet A.E).isOpen_biInter fun H hH => (hA.isWellFormed.isSNCDivisor.1 H hH).isOpen_compl
  let W : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1 ∩ (tangentChoice B (T₀.proj y₀)).1 ∩ ⋂ H ∈ {H | H ∈ A.E}, Hᶜ,
    (hwA.isOpen.inter hwB.isOpen).inter hEo⟩
  have hWUA : (W : Set X) ⊆ (tangentChoice A (T₀.proj y₀)).1 := fun x hx => hx.1.1
  have hWUB : (W : Set X) ⊆ (tangentChoice B (T₀.proj y₀)).1 := fun x hx => hx.1.2
  have hWE : ∀ H ∈ A.E, ∀ x ∈ (W : Set X), x ∉ H := fun H hH x hx => mem_iInter₂.mp hx.2 H hH
  have hwAW : IsTangentDirectionAlong A.N A.ideal A.d (W : Set X) uA := IsTangentDirectionAlong.mono_open hwA W.isOpen hWUA
  have hwBW : IsTangentDirectionAlong B.N B.ideal B.d (W : Set X) uB := IsTangentDirectionAlong.mono_open hwB W.isOpen hWUB
  obtain ⟨hwfA, hwfB, hAB, hdimW⟩ := base_contact_AB hA hB h hdim hwA hwB W hWUA hWUB hWE
  obtain ⟨hTs, hRE⟩ := restrictEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d W hwAW T₀ hTA
  obtain ⟨-, hRE'⟩ := restrictEquiv_stage_contactCoeffBM hB.isWellFormed hB.one_le_d W hwBW T₀ hTB
  have hdA1 : 1 ≤ (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0}))).d :=
    ContactIndependenceAlong.one_le_coeffMarkedAlong_d (emptyBoundary A)
  have hdd : (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM B) (B.N ∩ {x | uB x = 0}))).d =
      (MarkedIdeal.pullback (Subtype.val : W → X) (withN (coeffEmptyBM A) (A.N ∩ {x | uA x = 0}))).d := by
    show (coeffEmptyBM B).d = (coeffEmptyBM A).d
    rw [coeffEmptyBM_d, coeffEmptyBM_d, hd]
  have hkey := expAgreeAt_geoTransformAlong_of_domain hAB hwfA hwfB hdA1 hdd hdimW
    (fun x _ _ _ => expAgreeAt_of_E_nil rfl x) (restrict W T₀) hTs
  -- coherence of the two lower ideals
  have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hcL' := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ 0
  have hholL := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL
  have hholL' := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcL'
  -- the two restricted lower ideals have the same cosupport on `O`
  have hloc := HironakaG8ClassStepLower.locWPEquiv_lowerIdealBM_zero hn hA hB hmA hmB h hE T₀ hT₀ hy₀ O hOA hOB
  have hcosO := hloc.cosupp_eq_base
  -- localize at `p`
  rw [expAgreeAt_pullback_val_iff hholL hholL' O p]
  have hpUA : T₀.proj (p : Y₀) ∈ (tangentChoice A (T₀.proj y₀)).1 := (interior_subset (hOA p.2)).1
  have hpUB : T₀.proj (p : Y₀) ∈ (tangentChoice B (T₀.proj y₀)).1 := (interior_subset (hOB p.2)).1
  have hpV : (p : Y₀) ∈ openPreimage T₀ W := ⟨⟨hpUA, hpUB⟩, mem_iInter₂.mpr fun H hH => hp H hH⟩
  rw [← expAgreeAt_pullback_val_iff hholL hholL' (openPreimage T₀ W) ⟨p, hpV⟩]
  intro H hH hy hyH
  -- `p` lies in the cosupports of both lower ideals, where both are nonzero along their carriers
  have hpc : (p : Y₀) ∈ (lowerIdealBM A 0 T₀ y₀).cosupp := by
    have h1 := cosupp_pullback_val (lowerIdealBM A 0 T₀ y₀) hholL (openPreimage T₀ W)
    have h2 : (⟨p, hpV⟩ : openPreimage T₀ W) ∈
        (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ W → Y₀) (lowerIdealBM A 0 T₀ y₀)).cosupp := hy
    rw [h1] at h2
    exact h2
  have hpO : p ∈ (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀)).cosupp := by
    rw [cosupp_pullback_val _ hholL O]
    exact hpc
  have hpO' := hcosO ▸ hpO
  have nz1 : IsNonzeroAlongAt (lowerIdealBM A 0 T₀ y₀).N (lowerIdealBM A 0 T₀ y₀).ideal (p : Y₀) :=
    (isNonzeroAlongAt_pullback_val_iff hcL O p).mp (hdA.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO))
  have nz2 : IsNonzeroAlongAt (lowerIdealBM B 0 T₀ y₀).N (lowerIdealBM B 0 T₀ y₀).ideal (p : Y₀) :=
    (isNonzeroAlongAt_pullback_val_iff hcL' O p).mp (hdB.isNonzeroAlongAt _ (MarkedIdeal.cosupp_subset_N _ hpO'))
  have hyA := hRE.cosupp_eq ▸ hy
  have hyAN := MarkedIdeal.cosupp_subset_N _ hyA
  have hcosAB := (hAB.geoTransformAlong (restrict W T₀) hTs).cosupp_eq_base
  have hyBN := MarkedIdeal.cosupp_subset_N _ (hcosAB ▸ hyA)
  have nzA := (isNonzeroAlongAt_iff_of_restrictEquiv hRE hyAN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz1)
  have nzB := (isNonzeroAlongAt_iff_of_restrictEquiv hRE' hyBN).mpr
    ((isNonzeroAlongAt_pullback_val_iff hcL' (openPreimage T₀ W) ⟨p, hpV⟩).mpr nz2)
  exact expAgreeAt_of_restrictEquiv hRE hRE' (hkey _ hyA nzA nzB) H hH hy hyH

end LevelZero

/-! ### Levels `s + 1` where the `ℰ`-term is not divisible -/

section LevelSucc

/-- The original members through a point depend only on the divisor. -/
theorem throughMembers_eq_of_E_eq {A B : MarkedIdeal n X} (hE : A.E = B.E) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (y₀ : Y₀) : throughMembers A T₀ y₀ = throughMembers B T₀ y₀ := by
  unfold throughMembers
  rw [HironakaG8MemberLoci.origMembers_eq_of_E_eq hE T₀]

/-- **Levels `s + 1` where the `ℰ`-term is not divisible by `𝓘_H` along the carrier: the exponent is `0`** (BM's "the `ℰ`-sum
has exponent `0` along born members", in the generic case). -/
theorem divExpAlong_lowerIdealBM_succ_eq_zero (hn : 0 < n) {A : MarkedIdeal n X} (hA : A.IsWellFormed) (hd : 1 ≤ A.d)
    {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked A) T₀) (y₀ : Y₀) (s : ℕ)
    {H : Set Y₀} {y : Y₀}
    (h : ¬ IsDivNearAlong n (lowerIdealBM A (s + 1) T₀ y₀).N
      (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 y) :
    divExpAlong n (lowerIdealBM A (s + 1) T₀ y₀).N (lowerIdealBM A (s + 1) T₀ y₀).ideal H y = 0 := by
  have hTa : IsGeoTestTower A T₀ := isGeoTestTower_of_barMarked hA hd _ hT₀
  have hTc : IsGeoTestTower (coeffEmptyBM A) T₀ :=
    isGeoTestTower_coeffEmptyBM hA hd _ (isGeoTestTower_emptyBoundary A _ hTa)
  have hwfc := isWellFormed_coeffEmptyBM hA
  obtain ⟨-, hC⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hwfc.isClosedSubmanifold_N
    hwfc.isCoherent T₀ hTc
  have hEc := HironakaG11InvBMLowerDomainSucc.isCoherent_exceptionalTermBM
    (HironakaG11InvBMLowerTailSucc.isClosedSubmanifold_of_mem_throughMembers A hA hn T₀ hT₀ y₀) (coeffEmptyBM A).d
  rw [lowerIdealBM_succ_ideal]
  exact HironakaG8SumExponents.divExpAlong_sumIdeal_eq_zero (hol_of_isCoherent hC) (hol_of_isCoherent hEc) h

end LevelSucc

/-! ### The residual and module 10 -/

section Residual

/-- **The residual of the boundary-exponent part of (B') plan module 10** (`R`-free): along every multiple test blow-up `T₀`
of `J̄_A`, at every `y₀` of the cosupport in the regime of level `s`, for every common open `O` of the two masks on which both
restricted lower ideals lie in the domain, the exponents of the lower ideals of `A` and `B` along a born member `H` agree at
the points `y ∈ O` of the cosupport on `H` where

* the exponent of the lower ideal of `A` along `H` at `y` is below the mark (`¬ IsDivNearAlong … d y`), and
* at level `0`: the base point `T₀.proj y` lies on an original member (the history of `y` enters the divisor of `A`), and at
  the levels `s + 1`: the `ℰ`-term `Σ_{H' ∈ S} 𝓘_{H'}^{d_𝒞}` is divisible by `𝓘_H` along one of the two carriers near `y`.

At all other points the agreement is proved (`lowerPairs_expAgree_of_residual`).  Not a named input: an explicit hypothesis
of the module-10 theorem below (the open part of module 10; see this lane's `REPORT-r3.md`). -/
def LowerExpResidual (A B : MarkedIdeal n X) : Prop :=
  ∀ {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀), IsGeoTestTower (barMarked A) T₀ →
    ∀ (s : ℕ) (y₀ : Y₀), y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp → stepRegime A s T₀ y₀ →
    ∀ (O : Opens Y₀), O ≤ maskBM A s T₀ y₀ → O ≤ maskBM B s T₀ y₀ → ∀ (r r' : ℕ),
      IsInvDomain r (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀)) →
      IsInvDomain r' (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀)) →
      ∀ y ∈ O, ∀ H ∈ (lowerIdealBM A s T₀ y₀).E, y ∈ (lowerIdealBM A s T₀ y₀).cosupp → y ∈ H →
        ¬ IsDivNearAlong n (lowerIdealBM A s T₀ y₀).N (lowerIdealBM A s T₀ y₀).ideal H (lowerIdealBM A s T₀ y₀).d y →
        (s = 0 → ∃ H' ∈ A.E, T₀.proj y ∈ H') →
        (0 < s → IsDivNearAlong n (lowerIdealBM A s T₀ y₀).N
            (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 y ∨
          IsDivNearAlong n (lowerIdealBM B s T₀ y₀).N
            (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 y) →
        divExpAlong n (lowerIdealBM A s T₀ y₀).N (lowerIdealBM A s T₀ y₀).ideal H y =
          divExpAlong n (lowerIdealBM B s T₀ y₀).N (lowerIdealBM B s T₀ y₀).ideal H y

/-- **The boundary-exponent part of the class data of the lower ideals, given the residual**: for class-equivalent marked
ideals `A ≈ B` of the domain of maximal order, `LowerExpResidual A B` gives the agreement of the boundary exponents of the lower
ideals on every common open of the masks (above the mark: `HironakaG8ClassStepExp`; level `0` off the original members:
`expAgreeAt_lowerIdealBM_zero_of_notMem`; levels `s + 1` with the `ℰ`-term not divisible: both exponents `0`). -/
theorem lowerPairs_expAgree_of_residual (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : HomogenizedIdealAlong.IsMaximalOrderAlong A.N A.ideal A.d)
    (hmB : HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d) (h : LocWPEquiv A B) (hd : A.d = B.d)
    (hE : A.E = B.E) (hdim : SameCarrierDim A B) (hres : LowerExpResidual A B) :
    LowerPairs A B fun {_} P Q => ExpAgree P Q := by
  refine HironakaG8ClassStepExp.lowerPairs_expAgree_of_belowMark hn hA hB hmA hmB h hd hE hdim ?_
  intro Y₀ T₀ hT₀ s y₀ hy₀ hreg O hOA hOB r r' hdA hdB
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hcL := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ s
  have hcL' := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ s
  have hholL := hol_of_isCoherent hcL
  have hholL' := hol_of_isCoherent hcL'
  intro H' hH' p hp hpH' hbelow
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
  have hmap : Filter.map (Subtype.val : O → Y₀) (𝓝 p) = 𝓝 (p : Y₀) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (O : Set Y₀)) p.2 (O.isOpen.mem_nhds p.2)
  have hcosA : ∀ e, cosupport n ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM A s T₀ y₀).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀).ideal) e =
        (Subtype.val : O → Y₀) ⁻¹' cosupport n (lowerIdealBM A s T₀ y₀).N (lowerIdealBM A s T₀ y₀).ideal e :=
    fun e => cosupp_pullback_val (⟨(lowerIdealBM A s T₀ y₀).N, [], (lowerIdealBM A s T₀ y₀).ideal, e⟩ :
      MarkedIdeal n Y₀) hholL O
  have hcosB : ∀ e, cosupport n ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM B s T₀ y₀).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀).ideal) e =
        (Subtype.val : O → Y₀) ⁻¹' cosupport n (lowerIdealBM B s T₀ y₀).N (lowerIdealBM B s T₀ y₀).ideal e :=
    fun e => cosupp_pullback_val (⟨(lowerIdealBM B s T₀ y₀).N, [], (lowerIdealBM B s T₀ y₀).ideal, e⟩ :
      MarkedIdeal n Y₀) hholL' O
  have hexpA := MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosA hmap H
  have hexpB := MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosB hmap H
  show divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM A s T₀ y₀).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowerIdealBM A s T₀ y₀).ideal) ((Subtype.val : O → Y₀) ⁻¹' H) p =
    divExpAlong n ((Subtype.val : O → Y₀) ⁻¹' (lowerIdealBM B s T₀ y₀).N)
      (GermIdeal.pullback (m := n) (Subtype.val : O → Y₀) (lowerIdealBM B s T₀ y₀).ideal) ((Subtype.val : O → Y₀) ⁻¹' H) p
  rw [hexpA, hexpB]
  have hpc : (p : Y₀) ∈ (lowerIdealBM A s T₀ y₀).cosupp := by
    have h1 := hp
    rw [cosupp_pullback_val _ hholL O] at h1
    exact h1
  have hbelow' : ¬ IsDivNearAlong n (lowerIdealBM A s T₀ y₀).N (lowerIdealBM A s T₀ y₀).ideal H
      (lowerIdealBM A s T₀ y₀).d p :=
    fun h' => hbelow ((MonomialInvariantFunctorialAlong.isDivNearAlong_pullback_iff hcosA hmap H _).mpr h')
  cases s with
  | zero =>
    by_cases hE0 : ∃ H'' ∈ A.E, T₀.proj (p : Y₀) ∈ H''
    · exact hres T₀ hT₀ 0 y₀ hy₀ hreg O hOA hOB r r' hdA hdB p p.2 H hH hpc hpH' hbelow' (fun _ => hE0)
        (fun h0 => absurd h0 (lt_irrefl 0))
    · push Not at hE0
      have h2 := expAgreeAt_lowerIdealBM_zero_of_notMem hA hB hmA hmB h hd hE hdim hn T₀ hT₀ hy₀ O hOA hOB hdA hdB p hE0
        ((Subtype.val : O → Y₀) ⁻¹' H) hH' hp hpH'
      exact hexpA.symm.trans (h2.trans hexpB)
  | succ s =>
    by_cases hdiv : IsDivNearAlong n (lowerIdealBM A (s + 1) T₀ y₀).N
        (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 p ∨
      IsDivNearAlong n (lowerIdealBM B (s + 1) T₀ y₀).N
        (exceptionalTermBM (throughMembers A T₀ y₀) (coeffEmptyBM A).d) H 1 p
    · exact hres T₀ hT₀ (s + 1) y₀ hy₀ hreg O hOA hOB r r' hdA hdB p p.2 H hH hpc hpH' hbelow'
        (fun h0 => absurd h0 (Nat.succ_ne_zero s)) (fun _ => hdiv)
    · rw [not_or] at hdiv
      have hEq : exceptionalTermBM (throughMembers B T₀ y₀) (coeffEmptyBM B).d =
          exceptionalTermBM (n := n) (throughMembers A T₀ y₀) (coeffEmptyBM A).d := by
        rw [throughMembers_eq_of_E_eq hE T₀ y₀, coeffEmptyBM_d B, coeffEmptyBM_d A, hd]
      rw [divExpAlong_lowerIdealBM_succ_eq_zero hn hA.isWellFormed hA.one_le_d T₀ hT₀ y₀ s hdiv.1,
        divExpAlong_lowerIdealBM_succ_eq_zero hn hB.isWellFormed hB.one_le_d T₀ hTJB y₀ s (hEq ▸ hdiv.2)]

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **(B') plan module 10, given only the residual**: lane G11B's statement (I-1361) with the extra hypothesis `hExp` of
`HironakaG8ClassStepDim.classFunctorialMaxOrder_stepOneInvBM_of_exp` reduced to `LowerExpResidual` (exponents below the mark,
at level `0` only with history inside the divisor, at the levels `s + 1` only where the `ℰ`-term is divisible). -/
theorem classFunctorialMaxOrder_stepOneInvBM_of_residual (hn : 0 < n)
    (R : ResolutionInvariant.{0, v} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv)
    (hTI : ∀ {X : CMfd.{0} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 →
      HomogenizedIdealAlong.IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d → HironakaG11InvBMTangentIndep.TangentIndepBM 𝔍 R)
    (hRes : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      HomogenizedIdealAlong.IsMaximalOrderAlong A.N A.ideal A.d →
      HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerExpResidual A B) :
    ClassFunctorialMaxOrderFor (fun {Y} A B => LocWPEquiv (X := Y) A B) k
      (fun {X} 𝔍 {Y} T y => HironakaG11InvBMLower.stepOneInvBM (X := X) R 𝔍 (Y := Y) T y) :=
  HironakaG8ClassStepDim.classFunctorialMaxOrder_stepOneInvBM_of_exp hn R hR hTI
    fun A B hA hB hmA hmB h hd hE hdim h0 =>
      lowerPairs_expAgree_of_residual hn hA hB hmA hmB h hd hE hdim (hRes A B hA hB hmA hmB h hd hE hdim h0)

/-- **The `R`-free bridge** (the form of lane G8B's `HironakaG8BFamilyClassStep.LowerClassStepBM`): `LowerClassBM` for every
pair of class-equivalent marked ideals of the domain of maximal order, given only the residual. -/
theorem lowerClassBM_of_residual (hn : 0 < n) {k : ℕ}
    (hRes : ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      HomogenizedIdealAlong.IsMaximalOrderAlong A.N A.ideal A.d →
      HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → LowerExpResidual A B) :
    ∀ {X : CMfd.{0} n} (A B : MarkedIdeal n X), IsInvDomain k A → IsInvDomain k B →
      HomogenizedIdealAlong.IsMaximalOrderAlong A.N A.ideal A.d →
      HomogenizedIdealAlong.IsMaximalOrderAlong B.N B.ideal B.d → LocWPEquiv A B →
      A.d = B.d → A.E = B.E → SameCarrierDim A B → ExpAgree A B → HironakaG8ClassStep.LowerClassBM A B :=
  HironakaG8ClassStepDim.lowerClassBM_of_exp hn fun A B hA hB hmA hmB h hd hE hdim h0 =>
    lowerPairs_expAgree_of_residual hn hA hB hmA hmB h hd hE hdim (hRes A B hA hB hmA hmB h hd hE hdim h0)

end Residual

end

end Hironaka.HironakaG8ClassStepResidual
