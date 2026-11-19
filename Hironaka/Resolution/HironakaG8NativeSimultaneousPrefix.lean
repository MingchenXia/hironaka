import Hironaka.Resolution.HironakaG8NativeSimultaneousComparison
import Hironaka.Resolution.HironakaG8NativeSimultaneousTransport
import Hironaka.Resolution.CanonicalResolution

/-! Comparison of actual synchronized native prefixes with no empty stages. -/

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeSimultaneousPrefix

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealBiholomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaStageCenters HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  NormalCrossings HironakaG8NativeRelativeClearing HironakaG8NativeSimultaneousCentre
  HironakaG8NativeSimultaneousComparison HironakaG8NativeSimultaneousTransport
  StepOneTangentChange BlowupTowerSplit

variable {n : ℕ} {X Y Z : CMfd.{0} n} {I J : Type}

local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
local notation "inv" => ResolutionInvariantSeq.ResolutionInvariant.inv (canonicalInvariant n)
local notation "reflAt" B => Diffeomorph.refl 𝓘(ℂ, ComplexModel n) B ∞
local notation "original[" W ";" E "]" =>
  (MarkedIdeal.mk univ E (vanishingIdeal (n := n) W) 1 : MarkedIdeal n _)

private theorem restrict_same_base_iso (U : Opens X)
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (reflAt X) T S χ) :
    ∃ φ : CMfd.of (n := n) (openPreimage T U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage S U),
      IsTowerIso (reflAt (CMfd.of (n := n) U)) (restrict U T) (restrict U S) φ := by
  have hU : ∀ x : X, x ∈ U ↔ (reflAt X) x ∈ U := fun _ => Iff.rfl
  have hχ := isTowerIso_mem_openPreimage_iff hIso hU
  have hLocal := isTowerIso_restrictOpens hU hIso hχ
  have hRefl : diffeoOpens (reflAt X) U U hU = reflAt (CMfd.of (n := n) U) :=
    Diffeomorph.ext (fun _ => Subtype.ext rfl)
  rw [hRefl] at hLocal
  exact ⟨_,hLocal⟩

/-- Under an actual tower isomorphism over the identical base, a literal
native window has the same initial marked record and the matching
canonical restriction. -/
theorem canonical_window_at_same_base_iso (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n (ValTy n))
    (U : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U)) (hP : IsInvDomain n P)
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (reflAt X) T S χ)
    (hCan : IsCanonical P (R.inv P) (restrict U S)) :
    IsCanonical P (R.inv P) (restrict U T) := by
  obtain ⟨φ,hLocal⟩ := restrict_same_base_iso U hIso
  have hCan' := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hP _ hLocal hCan
  have hPull : MarkedIdeal.pullback (reflAt (CMfd.of (n := n) U)) P = P :=
    ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent
  rw [hPull] at hCan'
  exact hCan'

/-- A terminal native window stays terminal under the actual comparison
with the same original open and marked record. -/
theorem window_cosupp_empty_at_same_base_iso
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n (ValTy n))
    (U : Opens X) (P : MarkedIdeal n (CMfd.of (n := n) U)) (hP : IsInvDomain n P)
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (reflAt X) T S χ)
    (hCan : IsCanonical P (R.inv P) (restrict U S))
    (hClear : (geoTransformAlong P (restrict U S)).cosupp = ∅) :
    (geoTransformAlong P (restrict U T)).cosupp = ∅ := by
  obtain ⟨φ,hLocal⟩ := restrict_same_base_iso U hIso
  have hTest := R.isInvValue.isGeoTestTower_of_isCanonical hP (restrict U S) hCan
  have hCos := IsTowerIso.cosupp_geoTransformAlong (reflAt (CMfd.of (n := n) U))
    hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hLocal hTest
  have hPull : MarkedIdeal.pullback (reflAt (CMfd.of (n := n) U)) P = P :=
    ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent
  rwa [hPull,hClear,preimage_empty] at hCos

/-- The actual centre certificate pulls back under an isomorphism over
the same base with literally the same native window family. -/
theorem simultaneous_centre_at_same_base_iso
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n (ValTy n))
    (U : I → Opens X) (P : ∀ i, MarkedIdeal n (CMfd.of (n := n) (U i)))
    (hP : ∀ i, IsInvDomain n (P i))
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    {χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (hIso : IsTowerIso (reflAt X) T S χ)
    (hCan : ∀ i, IsCanonical (P i) (R.inv (P i)) (restrict (U i) S))
    {C : Set Z} {m : ValTy n}
    (hC : NativeSimultaneousCentre R U P S C m) :
    NativeSimultaneousCentre R U P T (χ ⁻¹' C) m := by
  have hLocal := NativeSimultaneousCentre.of_isTowerIso (reflAt X) hIso hC hP hCan
  have hRecord : (fun i => transportedRecord (reflAt X) (U i) (P i)) = P := by
    funext i
    change MarkedIdeal.pullback (diffeoOpens (reflAt X) (U i) (U i) (fun _ => Iff.rfl)) (P i) = P i
    have hRefl : diffeoOpens (reflAt X) (U i) (U i) (fun _ => Iff.rfl) =
        reflAt (CMfd.of (n := n) (U i)) :=
      Diffeomorph.ext (fun _ => Subtype.ext rfl)
    rw [hRefl]
    exact ContactCanonicalAlong.pullback_id (P i) (hP i).isWellFormed.isCoherent
  change NativeSimultaneousCentre R U (fun i => transportedRecord (reflAt X) (U i) (P i)) T (χ ⁻¹' C) m at hLocal
  rwa [hRecord] at hLocal

section MatchedWindows

variable {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
variable (A : NativeWindows X I W E H D) (B : NativeWindows X J W E H D)

/-- Two genuinely nonempty synchronized native prefixes of the same
length have a stage by stage physical comparison over the identical
ambient base, even with independently chosen native records. -/
theorem exists_isTowerIso_of_simultaneous_length_eq (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W) :
    ∀ {Y Z : CMfd.{0} n} (T : BlowupTower X Y) (S : BlowupTower X Z),
      IsGeoTestTower original[W;E] T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      (∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T)) →
      (∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) S)) →
      NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered T →
      NativeSimultaneousStages (canonicalInvariant n) B.openSet B.powered S →
      StageCentres (fun _ C => C.Nonempty) T →
      StageCentres (fun _ C => C.Nonempty) S →
      T.length = S.length →
      ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, IsTowerIso (reflAt X) T S χ
  | _, _, .refl, .refl, _, _, _, _, _, _, _, _, _ => ⟨reflAt X,.refl⟩
  | _, _, .refl, .step _ _ _ _, _, _, _, _, _, _, _, _, hLen => by simp [BlowupTower.length] at hLen
  | _, _, .step _ _ _ _, .refl, _, _, _, _, _, _, _, _, hLen => by simp [BlowupTower.length] at hLen
  | _, _, .step T C π hπ, .step S F ρ hρ, hTest, hStage, hCanA, hCanB, hA, hB, hNeA, hNeB, hLen => by
    have hCanA₀ i := (hCanA i).1
    have hCanB₀ j := (hCanB j).1
    obtain ⟨χ,hIso⟩ := exists_isTowerIso_of_simultaneous_length_eq hn hW hE hExact hNot
      T S hTest.1 hStage.1 hCanA₀ hCanB₀ hA.1 hB.1 hNeA.1 hNeB.1 (by simpa [BlowupTower.length] using hLen)
    obtain ⟨m,hm⟩ := hA.2.resolve_left hNeA.2.ne_empty
    obtain ⟨v,hv⟩ := hB.2.resolve_left hNeB.2.ne_empty
    have hv' := simultaneous_centre_at_same_base_iso (canonicalInvariant n) B.openSet B.powered
      B.powered_domain hIso hCanB₀ hv
    have hCanB' j := canonical_window_at_same_base_iso (canonicalInvariant n) (B.openSet j) (B.powered j)
      (B.powered_domain j) hIso (hCanB₀ j)
    have hC : χ ⁻¹' F = C := (simultaneous_centres_agree_at_common_prefix A B T hn hW hE hExact hNot
      hTest.1 hStage.1 hCanA₀ hCanB' hm hv' hNeA.2 (hNeB.2.preimage χ.toEquiv.surjective)).symm
    have hB := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse χ.contMDiff χ.symm.contMDiff
      χ.apply_symm_apply χ.symm_apply_apply hρ
    rw [hC] at hB
    obtain ⟨e,f,he,hf,hπe,_,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over hπ hB
    refine ⟨⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩,.step hIso hπ hρ _ (fun p => ?_) hC⟩
    have hEq : χ.symm (ρ (e p)) = π p := congrFun hπe p
    show ρ (e p) = χ (π p)
    rw [← hEq,χ.apply_symm_apply]

/-- The two native window systems detect the same active points
over their exact original profile on the common actual prefix. -/
theorem native_windows_empty_at_common_prefix (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    (T : BlowupTower X Y)
    (hTest : IsGeoTestTower original[W;E] T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (hCanA : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T))
    (hCanB : ∀ j, IsCanonical (B.powered j) (inv (B.powered j)) (restrict (B.openSet j) T))
    (hClear : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp = ∅) :
    ∀ j, (geoTransformAlong (B.powered j) (restrict (B.openSet j) T)).cosupp = ∅ := by
  let R := HironakaG11InvBMClass.BMInvariant.mk (canonicalInvariant n)
    (HironakaG1OriginalInvariantClassFunctorial.classFunctorialFor_canonicalInvariant n)
  have hA := nativeWindows_active_replay hn R hW hE hExact hNot A T hTest hStage hCanA
  have hB := nativeWindows_active_replay hn R hW hE hExact hNot B T hTest hStage hCanB
  intro j
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hActive := (hB.support j y).mp hy
  obtain ⟨i,hi⟩ := A.covers (T.proj y.val) hActive.1
  have hyA := (hA.support i ⟨y.val,hi⟩).mpr hActive
  rw [hClear] at hyA
  exact hyA

/-- The physical ambient segment retains its native window histories
and a genuine maximum at each actual nonempty step. -/
structure NativeNonemptySegment (A : NativeWindows X I W E H D) (T : BlowupTower X Y) : Prop where
  test : IsGeoTestTower original[W;E] T
  singular : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  canonical : ∀ i, IsCanonical (A.powered i) (inv (A.powered i)) (restrict (A.openSet i) T)
  simultaneous : NativeSimultaneousStages (canonicalInvariant n) A.openSet A.powered T
  nonempty : StageCentres (fun _ C => C.Nonempty) T

private theorem NativeNonemptySegment.prefix {T : BlowupTower X Y} :
    ∀ {Z : CMfd.{0} n} (S : BlowupTower Y Z), NativeNonemptySegment A (T.append S) → NativeNonemptySegment A T
  | _, .refl, h => h
  | _, .step S _ _ _, h => NativeNonemptySegment.prefix S
      ⟨h.test.1,h.singular.1,fun i => (h.canonical i).1,h.simultaneous.1,h.nonempty.1⟩

private theorem NativeNonemptySegment.tail_length_eq_zero {T : BlowupTower X Y}
    (hClear : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp = ∅) :
    ∀ {Z : CMfd.{0} n} (S : BlowupTower Y Z), NativeNonemptySegment A (T.append S) → S.length = 0
  | _, .refl, _ => rfl
  | _, .step S C _ _, h => by
    have hLen := NativeNonemptySegment.tail_length_eq_zero hClear S
      ⟨h.test.1,h.singular.1,fun i => (h.canonical i).1,h.simultaneous.1,h.nonempty.1⟩
    cases S with
    | refl =>
      obtain ⟨q,hq⟩ := h.nonempty.2
      obtain ⟨m,hm⟩ := h.simultaneous.2.resolve_left h.nonempty.2.ne_empty
      obtain ⟨i,hi⟩ := hm.covered q hq
      have hz := ((Set.ext_iff.mp (hm.trace i)) ⟨q,hi⟩).mp hq
      have hz' : (⟨q,hi⟩ : openPreimage T (A.openSet i)) ∈
          (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp := hz.1
      rw [hClear] at hz'
      exact False.elim hz'
    | step S F π hπ => simp [BlowupTower.length] at hLen

variable {A B}

private theorem length_le_of_native_terminal (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (hT : NativeNonemptySegment A T) (hS : NativeNonemptySegment B S)
    (hClear : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp = ∅) :
    S.length ≤ T.length := by
  by_contra! hLt
  let r := S.length - T.length
  let P := head S r
  let Q := tail S r
  have hSplit : P.append Q = S := head_append_tail S r
  have hS' : NativeNonemptySegment B (P.append Q) := by rw [hSplit]; exact hS
  have hP := NativeNonemptySegment.prefix B Q hS'
  have hLen : P.length = T.length := by dsimp [P,r]; rw [length_head]; omega
  obtain ⟨χ,hIso⟩ := exists_isTowerIso_of_simultaneous_length_eq B A hn hW hE hExact hNot
    P T hP.test hP.singular hP.canonical hT.canonical hP.simultaneous hT.simultaneous
    hP.nonempty hT.nonempty hLen
  have hCan' i := canonical_window_at_same_base_iso (canonicalInvariant n) (A.openSet i)
    (A.powered i) (A.powered_domain i) hIso (hT.canonical i)
  have hClear' i := window_cosupp_empty_at_same_base_iso (canonicalInvariant n) (A.openSet i)
    (A.powered i) (A.powered_domain i) hIso (hT.canonical i) (hClear i)
  have hEmpty := native_windows_empty_at_common_prefix A B hn hW hE hExact hNot
    P hP.test hP.singular hCan' hP.canonical hClear'
  have hZero := NativeNonemptySegment.tail_length_eq_zero B hEmpty Q hS'
  change (tail S r).length = 0 at hZero
  rw [length_tail] at hZero
  dsimp [r] at hZero
  omega

/-- Two complete genuinely nonempty synchronized phases for the same
Hilbert--Samuel profile and full original boundary physically agree. -/
theorem exists_isTowerIso_of_simultaneous_terminal (hn : 0 < n)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
    (hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (hT : NativeNonemptySegment A T) (hS : NativeNonemptySegment B S)
    (hClearT : ∀ i, (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp = ∅)
    (hClearS : ∀ j, (geoTransformAlong (B.powered j) (restrict (B.openSet j) S)).cosupp = ∅) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z, IsTowerIso (reflAt X) T S χ := by
  have hLen := le_antisymm (length_le_of_native_terminal hn hW hE hExact hNot hS hT hClearS)
    (length_le_of_native_terminal hn hW hE hExact hNot hT hS hClearT)
  exact exists_isTowerIso_of_simultaneous_length_eq A B hn hW hE hExact hNot T S
    hT.test hT.singular hT.canonical hS.canonical hT.simultaneous hS.simultaneous hT.nonempty hS.nonempty hLen

end MatchedWindows

end
end Hironaka.HironakaG8NativeSimultaneousPrefix
