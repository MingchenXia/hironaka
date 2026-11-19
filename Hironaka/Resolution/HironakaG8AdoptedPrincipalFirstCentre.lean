import Hironaka.Resolution.HironakaG8OriginalSingularPrefix
import Hironaka.Resolution.HironakaG8OriginalOverlapPrefixTransport
import Hironaka.Resolution.HironakaG8InitialCommonIdealMaximum

/-! The retained common-mark first centre on a literal principal overlap. -/

set_option autoImplicit false

open Set TopologicalSpace Classical
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8AdoptedPrincipalFirstCentre

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  BlowupTowerIsomorphism HironakaG3EmptyAwareHistory HironakaG8NativeSimultaneousCentre
  HironakaG8OriginalSingularPrefix HironakaG8OriginalOverlapPrefixTransport
  HironakaActualPowerBoundaryExponents HironakaG8InitialCommonIdealMaximum
  HironakaSharpOriginalProductTraceOrder MarkedIdealBiholomorphism

/-- At the initial clock of a retained native phase, an occupied simultaneous
window whose raw record has the literal vanishing ideal at its attained top mark identifies
its physical centre trace with the principal first centre. The two windows
are already shrunk to the literal overlap. -/
theorem retained_native_initial_trace_eq_principal_centre {n : ℕ} {X V Y : CMfd.{0} (n+1)}
    {I : Type} (U : I → Opens X)
    (P : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i))) (e : I → ℕ)
    (D : Set X) (m : ValTy (n+1))
    (hCentre : NativeSimultaneousCentre (canonicalInvariant (n+1)) U
      (fun i => powerMarked (P i) (e i)) (.refl : BlowupTower X X) D m)
    (i : I) (hP : IsInvDomain (n+1) (P i)) (he : 1 ≤ e i)
    (hMeet : ((Subtype.val : U i → X) ⁻¹' D).Nonempty)
    (W : Set V) (Wᵢ : Set (U i))
    (φ : (CMfd.of (n := n+1) (U i)) ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯ V)
    (hW : Wᵢ = φ ⁻¹' W) (hAnalytic : IsComplexAnalyticSubset (n := n+1) Wᵢ)
    (q : ℕ) (hRecord : P i = ⟨univ, [], vanishingIdeal (n := n+1) Wᵢ, q⟩)
    (hUpper : ∀ x : U i, ordinaryTraceOrder (X := CMfd.of (n := n+1) (U i)) univ (vanishingIdeal (n := n+1) Wᵢ) x ≤ q)
    (C : Set V) (π : Y → V) (hπ : IsBlowupAlong (n+1) C π) (hNonempty : C.Nonempty) :
    let A : MarkedIdeal (n+1) V := ⟨univ, [], vanishingIdeal (n := n+1) W, 1⟩
    IsInvDomain (n+1) A →
    IsCanonical A ((canonicalInvariant (n+1)).inv A) (.step .refl C π hπ) →
    let Dᵢ := (Subtype.val : U i → X) ⁻¹' D
    Dᵢ = φ ⁻¹' C ∧
    ∀ {Y' : CMfd.{0} (n+1)} (ρ : Y' → CMfd.of (n := n+1) (U i))
      (hρ : IsBlowupAlong (n+1) Dᵢ ρ),
      ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel (n+1)), 𝓘(ℂ, ComplexModel (n+1))⟯ Y,
        IsTowerIso φ (.step .refl Dᵢ ρ hρ) (.step .refl C π hπ) χ := by
  intro A hA hPrincipal Dᵢ
  have hMax : C = maxLocus ((canonicalInvariant (n+1)).inv A (.refl : BlowupTower V V)) A.cosupp := by
    rcases hPrincipal.2 with hEmpty | hMax
    · exact False.elim (hNonempty.ne_empty hEmpty)
    · simpa only [geoTransformAlong_refl] using hMax
  have hTrace := raw_maxLocus_eq_centre_trace U P e (.refl : BlowupTower X X)
    D m hCentre i hP he trivial hMeet
  change maxLocus ((canonicalInvariant (n+1)).inv (P i)
    (.refl : BlowupTower (CMfd.of (n := n+1) (U i)) (CMfd.of (n := n+1) (U i)))) (P i).cosupp =
    (Subtype.val : U i → X) ⁻¹' D at hTrace
  rw [hRecord] at hTrace
  rw [hRecord] at hP
  let I := vanishingIdeal (n := n+1) Wᵢ
  let Ai : MarkedIdeal (n+1) (U i) := ⟨univ, [], I, 1⟩
  have hAi : IsInvDomain (n+1) Ai :=
    ⟨⟨hP.isWellFormed.isClosedSubmanifold_N, hP.isWellFormed.isCoherent,
      hP.isWellFormed.isSNCDivisor, hP.isWellFormed.isTransverse⟩,
      hP.dimLE, le_rfl, hP.isNonzeroAlongAt⟩
  have hAttain : ∃ x : U i, ordinaryTraceOrder (X := CMfd.of (n := n+1) (U i)) univ I x = q := by
    obtain ⟨x, hx⟩ := hMeet
    have hxMax : x ∈ maxLocus ((canonicalInvariant (n+1)).inv
        (⟨univ, [], I, q⟩ : MarkedIdeal (n+1) (U i))
        (.refl : BlowupTower (CMfd.of (n := n+1) (U i)) (CMfd.of (n := n+1) (U i))))
        (⟨univ, [], I, q⟩ : MarkedIdeal (n+1) (U i)).cosupp := hTrace.symm ▸ hx
    have hOrd := ordinaryTraceOrder_cosupport_iff (X := CMfd.of (n := n+1) (U i)) (W := univ) (I := I) hAi.isWellFormed.isClosedSubmanifold_N
      hAi.isWellFormed.isCoherent hAi.isNonzeroAlongAt (mem_univ x) q
    exact ⟨x, le_antisymm (hUpper x) (hOrd.mp hxMax.1)⟩
  have hTopMax := initial_maxLocus_markOne_eq_topMark (X := CMfd.of (n := n+1) (U i))
    I hAi hP.one_le_d hUpper hAttain
  have hRead := original_native_overlap_prefix_read (Nat.succ_pos n) φ W Wᵢ [] [] hW hAnalytic rfl
    .refl .refl φ (.refl) hA
  have hReadMax := (hRead.2 trivial).2
  simp only [geoTransformAlong_refl] at hReadMax
  have hCentreEq : Dᵢ = φ ⁻¹' C :=
    hTrace.symm.trans (hTopMax.symm.trans (hReadMax.trans (congrArg (φ ⁻¹' ·) hMax.symm)))
  refine ⟨hCentreEq, fun {Y'} ρ hρ => ?_⟩
  have hπ' := isBlowupAlong_comp_inverse φ.contMDiff φ.symm.contMDiff
    φ.apply_symm_apply φ.symm_apply_apply hπ
  rw [← hCentreEq] at hπ'
  obtain ⟨e,f,he,hf,hρe,_,hfe,hef⟩ := BlowupUniqueness.exists_biholomorphism_over hρ hπ'
  refine ⟨⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩, .step .refl hρ hπ _ (fun p => ?_) hCentreEq.symm⟩
  have hEq : φ.symm (π (e p)) = ρ p := congrFun hρe p
  show π (e p) = φ (ρ p)
  rw [← hEq, φ.apply_symm_apply]

end Hironaka.HironakaG8AdoptedPrincipalFirstCentre
