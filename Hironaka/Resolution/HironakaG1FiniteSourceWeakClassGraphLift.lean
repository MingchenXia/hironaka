import Hironaka.Resolution.HironakaG1NormalGraphFlags
import Hironaka.Resolution.HironakaG1NativeWeightedPrefixState
import Hironaka.Resolution.HironakaG1IteratedProperNormalNativeState

/-! Lifting a source weak test class through a finite block of normal coordinates. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1FiniteSourceWeakClassGraphLift

noncomputable section

open Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan GermIdealPullbackCalculus
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism BlowupTowers
  ResolutionInvariantSpec
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1NormalGraphFlags
  HironakaG1SourceWeakClassGraphLift HironakaG8LocalHistory
  HironakaG8LocalTransport HironakaG8LocalContactStage HironakaG8ClassStepCut
  MarkedIdealOperationsAlong.MarkedIdeal HironakaActualPowerBoundaryExponents

variable {n t k l : ℕ} {U : Opens (ComplexModel n)}

private abbrev base (U : Opens (ComplexModel n)) := CMfd.of (n := n) U
private abbrev ambient (U : Opens (ComplexModel n)) (t : ℕ) :=
  CMfd.of (n := n + t) (blockOpen U t)

private def zeroBlockTrace (P : MarkedIdeal n U) (t : ℕ) :
    MarkedIdeal (n + t) (ambient U t) :=
  ⟨blockGraph (0 : U → ComplexModel t) P.N,
    P.E.map (blockProjection ⁻¹' ·),
    GermIdeal.pullback (m := n + t) (blockProjection : blockOpen U t → U) P.ideal, P.d⟩

private def openEqDiffeo {m : ℕ} {V W : Opens (ComplexModel m)} (h : V = W) :
    V ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ W := by
  subst W
  exact Diffeomorph.refl _ V ∞

@[simp] private theorem openEqDiffeo_val {m : ℕ} {V W : Opens (ComplexModel m)}
    (h : V = W) (z : V) : (openEqDiffeo h z).val = z.val := by
  subst W
  rfl

private theorem tangentProjection_zero (z : ComplexModel n) :
    tangentProjection n 0 z = z := by
  ext i
  simp only [tangentProjection_apply]
  rw [show i.castAdd 0 = i from Fin.ext rfl]

private theorem tangentProjection_succ (z : ComplexModel (n + (t + 1))) :
    tangentProjection n t (tangentProjection (n + t) 1 z) =
      tangentProjection n (t + 1) z := by
  ext i
  simp only [tangentProjection_apply]
  rw [show (i.castAdd t).castAdd 1 = i.castAdd (t + 1) from Fin.ext rfl]

private theorem blockOpen_zero (U : Opens (ComplexModel n)) : blockOpen U 0 = U := by
  ext z
  change tangentProjection n 0 z ∈ U ↔ z ∈ U
  rw [tangentProjection_zero]

private theorem blockOpen_succ (U : Opens (ComplexModel n)) (t : ℕ) :
    blockOpen U (t + 1) = productOpen (blockOpen U t) := by
  ext z
  change tangentProjection n (t + 1) z ∈ U ↔
    tangentProjection n t (tangentProjection (n + t) 1 z) ∈ U
  rw [tangentProjection_succ]

private theorem projection_zero (U : Opens (ComplexModel n)) :
    (blockProjection : blockOpen U 0 → U) = openEqDiffeo (blockOpen_zero U) := by
  funext z
  apply Subtype.ext
  simp [blockProjection, tangentProjection_zero]

private theorem projection_succ (U : Opens (ComplexModel n)) (t : ℕ) :
    (blockProjection : blockOpen U t → U) ∘ projection (blockOpen U t) ∘
      openEqDiffeo (blockOpen_succ U t) = (blockProjection : blockOpen U (t + 1) → U) := by
  funext z
  apply Subtype.ext
  simp only [Function.comp_apply, blockProjection, projection, openEqDiffeo_val]
  exact tangentProjection_succ z.val

private theorem normalProjection_succ_zero (z : ComplexModel (n + (t + 1))) :
    (actualJointNormalProjection n t (tangentProjection (n + t) 1 z) = 0 ∧
      actualJointNormalProjection (n + t) 1 z = 0) ↔
      actualJointNormalProjection n (t + 1) z = 0 := by
  have hLast : (0 : Fin 1).natAdd (n + t) = (Fin.last t).natAdd n :=
    Fin.ext (by simp)
  have hOld (j : Fin t) : (j.natAdd n).castAdd 1 = j.castSucc.natAdd n :=
    Fin.ext rfl
  constructor
  · rintro ⟨hFirst, hNew⟩
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h := congrArg (fun v : ComplexModel 1 => v 0) hNew
      simpa only [actualJointNormalProjection_apply, hLast, PiLp.zero_apply] using h
    · have h := congrArg (fun v : ComplexModel t => v j) hFirst
      simpa only [actualJointNormalProjection_apply, tangentProjection_apply, hOld, PiLp.zero_apply] using h
  · intro h
    constructor
    · ext j
      have hj := congrArg (fun v : ComplexModel (t + 1) => v j.castSucc) h
      simpa only [actualJointNormalProjection_apply, tangentProjection_apply, hOld, PiLp.zero_apply] using hj
    · ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hj := congrArg (fun v : ComplexModel (t + 1) => v (Fin.last t)) h
      simpa only [actualJointNormalProjection_apply, hLast, PiLp.zero_apply] using hj

private theorem zeroBlockTrace_zero (P : MarkedIdeal n U) :
    zeroBlockTrace P 0 = MarkedIdeal.pullback (openEqDiffeo (blockOpen_zero U)) P := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext z
    change (blockProjection z ∈ P.N ∧ actualJointNormalProjection n 0 z.val = 0) ↔
      openEqDiffeo (blockOpen_zero U) z ∈ P.N
    rw [projection_zero U]
    exact and_iff_left (Subsingleton.elim _ _)
  · change P.E.map ((blockProjection : blockOpen U 0 → U) ⁻¹' ·) = _
    rw [projection_zero U]
    rfl
  · simp only [zeroBlockTrace, MarkedIdeal.pullback, projection_zero]
  · rfl

private theorem zeroBlockTrace_succ (P : MarkedIdeal n U) (hP : P.ideal.IsCoherent) :
    MarkedIdeal.pullback (openEqDiffeo (blockOpen_succ U t)) (sectionMarked (zeroBlockTrace P t)) =
      zeroBlockTrace P (t + 1) := by
  let W := blockOpen U t
  let e := openEqDiffeo (blockOpen_succ U t)
  have hp := projection_succ U t
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext z
    change ((blockProjection (projection W (e z)) ∈ P.N ∧
      actualJointNormalProjection n t (projection W (e z)).val = 0) ∧
      actualJointNormalProjection (n + t) 1 (e z).val = 0) ↔
        (blockProjection z ∈ P.N ∧ actualJointNormalProjection n (t + 1) z.val = 0)
    rw [and_assoc]
    change (((blockProjection : W → U) ∘ projection W ∘ e) z ∈ P.N ∧ _) ↔ _
    rw [hp]
    simp only [projection, e, openEqDiffeo_val]
    exact and_congr_right fun _ => normalProjection_succ_zero z.val
  · change ((P.E.map ((blockProjection : W → U) ⁻¹' ·)).map (projection W ⁻¹' ·)).map
      (e ⁻¹' ·) = P.E.map (blockProjection ⁻¹' ·)
    simp only [List.map_map, Function.comp_def, preimage_preimage]
    exact congrArg (fun p : blockOpen U (t + 1) → U => P.E.map (p ⁻¹' ·)) hp
  · change GermIdeal.pullback (m := n + (t + 1)) e
      (GermIdeal.pullback (m := (n + t) + 1) (projection W)
        (GermIdeal.pullback (m := n + t) (blockProjection : W → U) P.ideal)) =
      GermIdeal.pullback (m := n + (t + 1)) (blockProjection : blockOpen U (t + 1) → U) P.ideal
    rw [← coherent_pullback_comp (projection_contMDiff W) e.contMDiff _
      (isCoherent_pullback (blockProjection_contMDiff U t) hP),
      ← coherent_pullback_comp (blockProjection_contMDiff U t)
        ((projection_contMDiff W).comp e.contMDiff) P.ideal hP, hp]
  · rfl

set_option maxHeartbeats 500000 in
private theorem zeroBlockTrace_domains_and_class (P Q : MarkedIdeal n U)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P Q) (t : ℕ) :
    IsInvDomain k (zeroBlockTrace P t) ∧ IsInvDomain l (zeroBlockTrace Q t) ∧
      LocWPEquiv (X := ambient U t) (zeroBlockTrace P t) (zeroBlockTrace Q t) := by
  induction t with
  | zero =>
    rw [zeroBlockTrace_zero P, zeroBlockTrace_zero Q]
    let e := openEqDiffeo (blockOpen_zero U)
    exact ⟨InvDomainTowerAlong.isInvDomain_pullback e hP,
      InvDomainTowerAlong.isInvDomain_pullback e hQ,
      LocEquiv.pullback_diffeo (κ := Kinds.wp) (X := base U) (X' := ambient U 0) rfl e
        hP.isWellFormed.isCoherent hQ.isWellFormed.isCoherent h⟩
  | succ t ih =>
    obtain ⟨hPt, hQt, hPQ⟩ := ih
    have hPS : IsInvDomain k (sectionMarked (zeroBlockTrace P t)) :=
      section_projected_domain k _ _ _ _ hPt
    have hQS : IsInvDomain l (sectionMarked (zeroBlockTrace Q t)) :=
      section_projected_domain l _ _ _ _ hQt
    have hS := locWPEquiv_sectionMarked_of_source _ _ hPt hQt hPQ
    rw [← zeroBlockTrace_succ P hP.isWellFormed.isCoherent,
      ← zeroBlockTrace_succ Q hQ.isWellFormed.isCoherent]
    let e := openEqDiffeo (blockOpen_succ U t)
    exact ⟨InvDomainTowerAlong.isInvDomain_pullback e hPS,
      InvDomainTowerAlong.isInvDomain_pullback e hQS,
      LocEquiv.pullback_diffeo (κ := Kinds.wp)
        (X := base (productOpen (blockOpen U t))) (X' := ambient U (t + 1)) rfl e
        hPS.isWellFormed.isCoherent hQS.isWellFormed.isCoherent hS⟩

private theorem zeroBlockMarked_locWPEquiv_trace (P : MarkedIdeal n U) (hP : IsInvDomain k P) :
    LocWPEquiv (X := ambient U t) (blockMarked (0 : U → ComplexModel t) P [])
      (zeroBlockTrace P t) := by
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞
      (0 : U → ComplexModel t) := contMDiff_const
  have hI := hP.isWellFormed.isCoherent
  have hMarked := blockMarked_coherent hZero hI []
  have hRestr := restrictEquiv_blockPower_trace hZero P hI hP.one_le_d [] 1
  simp only [powerMarked, Nat.mul_one,
    FactorizationFromResolution.idealPow_one_of_isCoherent hI,
    FactorizationFromResolution.idealPow_one_of_isCoherent hMarked] at hRestr
  exact locEquiv_of_restrictEquiv_closed (κ := Kinds.wp) rfl hRestr
    (blockGraph_closed_submanifold hZero hP.isWellFormed.isClosedSubmanifold_N)
    hMarked (isCoherent_pullback (blockProjection_contMDiff U t) hI)

set_option maxHeartbeats 500000 in
/-- Source weak test equivalence survives independent finite normal graph
extensions and a source biholomorphism. All additional ambient boundary
slots are carried back in their given order. -/
theorem locWPEquiv_blockMarked_of_source {V : Opens (ComplexModel n)}
    (b : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V)
    (P : MarkedIdeal n U) (Q : MarkedIdeal n V)
    (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (h : LocWPEquiv (X := base U) P (MarkedIdeal.pullback b Q))
    {f : U → ComplexModel t} {g : V → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (F : List (Set (blockOpen V t))) :
    LocWPEquiv (X := ambient U t)
      (blockMarked f P (F.map (blockChartMap b f g ⁻¹' ·)))
      (MarkedIdeal.pullback (blockChartMap b f g) (blockMarked g Q F)) := by
  let Q' := MarkedIdeal.pullback b Q
  have hQ' : IsInvDomain l Q' := InvDomainTowerAlong.isInvDomain_pullback b hQ
  have hZero : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞
      (0 : U → ComplexModel t) := contMDiff_const
  have hZ := (zeroBlockMarked_locWPEquiv_trace (t := t) P hP).trans
    ((zeroBlockTrace_domains_and_class P Q' hP hQ' h t).2.2.trans
      (zeroBlockMarked_locWPEquiv_trace Q' hQ').symm)
  let idU := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞
  let e := blockChartEquiv idU hf hZero
  have hF := LocEquiv.pullback_diffeo (κ := Kinds.wp) (X := ambient U t) (X' := ambient U t) rfl e
    (blockMarked_coherent hZero hP.isWellFormed.isCoherent [])
    (blockMarked_coherent hZero hQ'.isWellFormed.isCoherent []) hZ
  change LocWPEquiv (X := ambient U t)
    (MarkedIdeal.pullback (blockChartMap id f 0) (blockMarked 0 P []))
    (MarkedIdeal.pullback (blockChartMap id f 0) (blockMarked 0 Q' [])) at hF
  rw [pullback_blockMarked contMDiff_id hf hZero P hP.isWellFormed.isCoherent [],
    pullback_blockMarked contMDiff_id hf hZero Q' hQ'.isWellFormed.isCoherent [],
    ContactCanonicalAlong.pullback_id P hP.isWellFormed.isCoherent,
    ContactCanonicalAlong.pullback_id Q' hQ'.isWellFormed.isCoherent] at hF
  rw [pullback_blockMarked b.contMDiff hf hg Q hQ.isWellFormed.isCoherent F]
  let F' := F.map (blockChartMap b f g ⁻¹' ·)
  have hExtra := locEquiv_addE (κ := Kinds.wp) rfl hF F'
  have hE : P.E = Q'.E := h.E_eq.symm
  have hRight : ({ blockMarked f Q' [] with E := F' ++ (blockMarked f P []).E } :
      MarkedIdeal (n + t) (ambient U t)) = blockMarked f Q' F' := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · rfl
    · change F' ++ P.E.map (blockProjection ⁻¹' ·) = F' ++ Q'.E.map (blockProjection ⁻¹' ·)
      rw [hE]
    · rfl
    · rfl
  change LocWPEquiv (X := ambient U t) (blockMarked f P F')
    { blockMarked f Q' [] with E := F' ++ (blockMarked f P []).E } at hExtra
  rwa [hRight] at hExtra

open HironakaG11PresLineState HironakaG11PresLineStable HironakaG1NativeWeightedPrefixState
  HironakaG8LocalHistory.LHist HironakaG8MixedEquiv

/-- A common native weak test prefix supplies the source comparison and
both domains for independently selected finite normal graphs at its
coordinate-open endpoint. -/
theorem locWPEquiv_blockMarked_after_native_test_prefix {a : ℕ} {X : CMfd.{0} a}
    (P Q : MarkedIdeal a X) (hPdom : IsInvDomain k P) (hQdom : IsInvDomain l Q)
    {W : Set X} {H : ℕ → ℕ} (hP : NativeHSState P W H) (hQ : NativeHSState Q W H)
    (hE : Q.E = P.E) {F : List (Set U)}
    (T : LHist X P.E (base U) F) (hk : InKinds Kinds.wp T) (ht : IsTest P T)
    {f g : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g)
    (G : List (Set (blockOpen U t))) :
    let R := record P T
    let S := record (withBoundary Q P.E) T
    LocWPEquiv (X := ambient U t) (blockMarked f R (G.map (blockChartMap id f g ⁻¹' ·)))
      (MarkedIdeal.pullback (blockChartMap id f g) (blockMarked g S G)) := by
  intro R S
  obtain ⟨hP', hQ'⟩ := independent_nativeHSStates_at_test_prefix hP hQ hE T hk ht
  obtain ⟨_, hRD⟩ := isInvDomain_at_native_test_prefix hPdom T hk ht
  have hQdom' : IsInvDomain l (withBoundary Q P.E) := by rwa [withBoundary_eq hE]
  have htQ := ((locWPEquiv_native hP hQ hE).isTest_iff T hk).mp ht
  obtain ⟨_, hSD⟩ := isInvDomain_at_native_test_prefix hQdom' T hk htQ
  let idU := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) U ∞
  have hClass : LocWPEquiv (X := base U) R (MarkedIdeal.pullback idU S) := by
    change LocWPEquiv (X := base U) R (MarkedIdeal.pullback (id : U → U) S)
    rw [ContactCanonicalAlong.pullback_id S hSD.isWellFormed.isCoherent]
    exact locWPEquiv_native hP' hQ' rfl
  exact locWPEquiv_blockMarked_of_source idU R S hRD hSD hClass hf hg G

open HironakaG1IteratedProperNormalNativeState

/-- Iterated actual line opens form the same coordinate open as the full
normal block. -/
theorem iteratedNormalOpen_eq_blockOpen (U : Opens (ComplexModel n)) (t : ℕ) :
    iteratedNormalOpen U t = blockOpen U t := by
  induction t with
  | zero => exact (blockOpen_zero U).symm
  | succ t ih =>
    exact (congrArg productOpen ih).trans (blockOpen_succ U t).symm

/-- The change between the full-block and iterated opens is the identity
on the actual ambient coordinates. -/
def iteratedNormalBlockEquiv (U : Opens (ComplexModel n)) (t : ℕ) :
    blockOpen U t ≃ₘ⟮𝓘(ℂ, ComplexModel (n + t)), 𝓘(ℂ, ComplexModel (n + t))⟯
      iteratedNormalOpen U t :=
  openEqDiffeo (iteratedNormalOpen_eq_blockOpen U t).symm

@[simp] theorem iteratedNormalBlockEquiv_val (z : blockOpen U t) :
    (iteratedNormalBlockEquiv U t z).val = z.val :=
  openEqDiffeo_val _ z

private theorem iteratedNormalProjection_val (z : iteratedNormalOpen U t) :
    (iteratedNormalProjection U t z).val = tangentProjection n t z.val := by
  induction t with
  | zero => exact (tangentProjection_zero z.val).symm
  | succ t ih =>
    change (iteratedNormalProjection U t (projection (iteratedNormalOpen U t) z)).val = _
    rw [ih]
    exact tangentProjection_succ z.val

/-- The actual base projection of the full block is the composite of the
iterated projections. -/
theorem iteratedNormalProjection_blockEquiv (z : blockOpen U t) :
    iteratedNormalProjection U t (iteratedNormalBlockEquiv U t z) = blockProjection z := by
  apply Subtype.ext
  rw [iteratedNormalProjection_val, iteratedNormalBlockEquiv_val]
  rfl

private theorem mem_iteratedNormalCarrier (W : Set U) (z : iteratedNormalOpen U t) :
    z ∈ iteratedNormalCarrier W t ↔
      iteratedNormalProjection U t z ∈ W ∧ actualJointNormalProjection n t z.val = 0 := by
  induction t with
  | zero =>
    change z ∈ W ↔ z ∈ W ∧ actualJointNormalProjection n 0 z.val = 0
    exact (and_iff_left (Subsingleton.elim _ _)).symm
  | succ t ih =>
    change (projection (iteratedNormalOpen U t) z ∈ iteratedNormalCarrier W t ∧
      actualJointNormalProjection (n + t) 1 z.val = 0) ↔ _
    rw [ih, and_assoc]
    exact and_congr_right fun _ => normalProjection_succ_zero z.val

/-- Imposing one zero equation at each step cuts out exactly the full
zero graph, with the literal closed source carrier. -/
theorem iteratedNormalCarrier_preimage_blockEquiv (W : Set U) :
    iteratedNormalBlockEquiv U t ⁻¹' iteratedNormalCarrier W t =
      blockGraph (0 : U → ComplexModel t) W := by
  ext z
  change iteratedNormalBlockEquiv U t z ∈ iteratedNormalCarrier W t ↔
    blockProjection z ∈ W ∧ actualJointNormalProjection n t z.val = 0
  rw [mem_iteratedNormalCarrier, iteratedNormalProjection_blockEquiv, iteratedNormalBlockEquiv_val]

end

end Hironaka.HironakaG1FiniteSourceWeakClassGraphLift
