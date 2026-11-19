import Hironaka.Resolution.HironakaG1IteratedProperNormalNativeState
import Hironaka.Resolution.HironakaG1NormalGraphFlags
import Hironaka.Resolution.HironakaG1FiniteSourceWeakClassGraphLift

set_option autoImplicit false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1IteratedNormalBlockIdeal
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealPullbackCalculus RestrictedIdealExtension DerivativeIdeal GiraudAlong InvertibleIdealQuotient
  HironakaActualCentreJointJets HironakaRelativeNormalIdeal HironakaActualZeroCoordinateContactSeed
  HironakaActualGraphFunctionalIdeal
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives
  HironakaSmoothSubmersionRelativeRestriction HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1IteratedProperNormalNativeState

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- The normal coordinates in the order they were adjoined. -/
def iteratedNormalCoordinate (U : Opens (ComplexModel n)) (t : ℕ)
    (i : Fin t) (z : iteratedNormalOpen U t) : ℂ :=
  actualJointNormalProjection n t z.val i

theorem iteratedNormalProjection_contMDiff (U : Opens (ComplexModel n)) (t : ℕ) :
    ContMDiff 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ComplexModel n) ∞ (iteratedNormalProjection U t) := by
  induction t with
  | zero => exact contMDiff_id
  | succ t ih => exact ih.comp (projection_contMDiff _)

theorem iteratedNormalCoordinate_mdifferentiable (U : Opens (ComplexModel n)) (t : ℕ) (i : Fin t) :
    MDifferentiable 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ℂ) (iteratedNormalCoordinate U t i) := by
  have h : ContMDiff 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ℂ) ∞
      (iteratedNormalCoordinate U t i) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp
      (actualJointNormalProjection n t).contMDiff).comp
      (contMDiff_subtype_val (U := iteratedNormalOpen U t))
  exact h.mdifferentiable (by simp)

private theorem sum_le {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel m) X] [IsComplexManifold m X]
    {A B D : GermIdeal m X} (hD : D.IsCoherent) (hA : A.Le D) (hB : B.Le D) :
    (sumIdeal A B).Le D := by
  intro x g hg
  change IsInSpanAt (n := m) (fun s => A.mem x s ∨ B.mem x s) x g at hg
  apply GermIdealTotalTransform.mem_of_isInSpanAt_mem hD
  exact IsInSpanAt.mono (fun s hs => hs.elim (hA x s) (hB x s)) hg

private theorem sum_assoc {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel m) X] [IsComplexManifold m X]
    {A B C : GermIdeal m X} (hA : A.IsCoherent) (hB : B.IsCoherent) (hC : C.IsCoherent) :
    sumIdeal (sumIdeal A B) C = sumIdeal A (sumIdeal B C) := by
  have hAB := isCoherent_sumIdeal hA hB
  have hBC := isCoherent_sumIdeal hB hC
  have hLeft := isCoherent_sumIdeal hAB hC
  have hRight := isCoherent_sumIdeal hA hBC
  have hLR := sum_le hRight (sum_le hRight (le_sumIdeal_left hA)
    (fun x g hg => le_sumIdeal_right hBC x g (le_sumIdeal_left hB x g hg)))
    (fun x g hg => le_sumIdeal_right hBC x g (le_sumIdeal_right hC x g hg))
  have hRL := sum_le hLeft (fun x g hg => le_sumIdeal_left hAB x g (le_sumIdeal_left hA x g hg))
    (sum_le hLeft (fun x g hg => le_sumIdeal_left hAB x g (le_sumIdeal_right hB x g hg))
      (le_sumIdeal_right hC))
  exact GermIdeal.ext (funext fun x => funext fun g => propext ⟨hLR x g, hRL x g⟩)

private theorem finiteIdeal_lastCases {m t : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel m) X] (c : Fin t → X → ℂ) (b : X → ℂ)
    (hc : ∀ i x, HolomorphicAt m (c i) x) (hb : ∀ x, HolomorphicAt m b x) :
    finiteFunctionIdeal (n := m) (Fin.lastCases b c) =
      sumIdeal (finiteFunctionIdeal c) (finiteFunctionIdeal (fun _ : Unit => b)) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨?_, ?_⟩)
  · intro hg
    change IsInSpanAt (n := m) (fun s =>
      (finiteFunctionIdeal c).mem x s ∨ (finiteFunctionIdeal (fun _ : Unit => b)).mem x s) x g
    refine IsInSpanAt.mono ?_ hg
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using
        (Or.inr (isInSpanAt_self ⟨(), rfl⟩ (hb x)) :
          (finiteFunctionIdeal c).mem x b ∨ (finiteFunctionIdeal (fun _ : Unit => b)).mem x b)
    · simpa only [Fin.lastCases_castSucc] using
        (Or.inl (isInSpanAt_self ⟨j, rfl⟩ (hc j x)) :
          (finiteFunctionIdeal c).mem x (c j) ∨ (finiteFunctionIdeal (fun _ : Unit => b)).mem x (c j))
  · intro hg
    change IsInSpanAt (n := m) (fun s =>
      (finiteFunctionIdeal c).mem x s ∨ (finiteFunctionIdeal (fun _ : Unit => b)).mem x s) x g at hg
    refine IsInSpanAt.trans ?_ hg
    rintro f (hf | hf)
    · refine IsInSpanAt.mono ?_ hf
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, Fin.lastCases_castSucc ..⟩
    · refine IsInSpanAt.mono ?_ hf
      rintro _ ⟨_, rfl⟩
      exact ⟨Fin.last t, Fin.lastCases_last ..⟩

set_option maxHeartbeats 1500000 in
/-- Every actual iterated normal row is the pullback of the original
ideal plus precisely one original-mark power per true normal coordinate. -/
theorem iteratedNormalMarked_ideal (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (t : ℕ) :
    (iteratedNormalMarked Q t).ideal =
      sumIdeal (GermIdeal.pullback (m := n+t) (iteratedNormalProjection U t) Q.ideal)
        (finiteFunctionIdeal (fun i z => iteratedNormalCoordinate U t i z ^ Q.d)) := by
  induction t with
  | zero =>
    change Q.ideal = sumIdeal (GermIdeal.pullback (m := n) (id : U → U) Q.ideal)
      (finiteFunctionIdeal (fun (i : Fin 0) (z : U) => iteratedNormalCoordinate U 0 i z ^ Q.d))
    rw [BlowupControlledTransform.pullback_id hQ]
    refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨le_sumIdeal_left hQ x g, ?_⟩)
    intro hg
    change IsInSpanAt (n := n) (fun s => Q.ideal.mem x s ∨
      (finiteFunctionIdeal (fun (i : Fin 0) (z : U) => iteratedNormalCoordinate U 0 i z ^ Q.d)).mem x s) x g at hg
    apply GermIdealTotalTransform.mem_of_isInSpanAt_mem hQ
    refine IsInSpanAt.trans ?_ hg
    rintro s (hs | hs)
    · exact isInSpanAt_self hs (GermIdeal.IsCoherent.holomorphicAt_mem hQ hs)
    · exact IsInSpanAt.mono (by rintro _ ⟨i, _⟩; exact Fin.elim0 i) hs
  | succ t ih =>
    let A := iteratedNormalOpen U t
    let p := projection A
    let c : Fin t → A → ℂ := fun i z => iteratedNormalCoordinate U t i z ^ Q.d
    let b : productOpen A → ℂ := fun z => relativeNormalCoordinate A z ^ Q.d
    have hp := projection_contMDiff A
    have hπ := iteratedNormalProjection_contMDiff U t
    have hc : ∀ i, MDifferentiable 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ℂ) (c i) :=
      fun i => (iteratedNormalCoordinate_mdifferentiable U t i).pow _
    have hb : MDifferentiable 𝓘(ℂ, ComplexModel (n+t+1)) 𝓘(ℂ, ℂ) b :=
      (normalCoordinate_mdifferentiable A).pow _
    change sumIdeal (GermIdeal.pullback p (iteratedNormalMarked Q t).ideal)
      (finiteFunctionIdeal (fun _ : Unit => fun z : productOpen A =>
        relativeNormalCoordinate A z ^ (iteratedNormalMarked Q t).d)) = _
    rw [(iteratedNormalMarked_data Q t).1, ih,
      pullback_sumIdeal_dimensions hp (isCoherent_pullback hπ hQ) (isCoherent_finiteFunctionIdeal c hc),
      ← coherent_pullback_comp hπ hp Q.ideal hQ, finiteFunctionIdeal_pullback c hc p hp]
    change sumIdeal (sumIdeal (GermIdeal.pullback (iteratedNormalProjection U t ∘ p) Q.ideal)
      (finiteFunctionIdeal (fun i => c i ∘ p))) (finiteFunctionIdeal (fun _ : Unit => b)) = _
    rw [sum_assoc (isCoherent_pullback (hπ.comp hp) hQ)
      (isCoherent_finiteFunctionIdeal _ (fun i => (hc i).comp (hp.mdifferentiable (by simp))))
      (isCoherent_finiteFunctionIdeal _ (fun _ => hb)),
      ← finiteIdeal_lastCases (fun i => c i ∘ p) b
        (fun i x => Eventually.of_forall fun y => (hc i).comp (hp.mdifferentiable (by simp)) y)
        (fun x => Eventually.of_forall hb)]
    congr 2
    funext i z
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hLast : (0 : Fin 1).natAdd (n + t) = (Fin.last t).natAdd n :=
        Fin.ext (by simp)
      rw [Fin.lastCases_last]
      simp only [b, relativeNormalCoordinate, addedCoordinate, graphFunction, zeroFunction,
        Function.comp_apply, PiLp.zero_apply, sub_zero, iteratedNormalCoordinate,
        actualJointNormalProjection_apply, hLast]
    · have hOld : (j.natAdd n).castAdd 1 = j.castSucc.natAdd n := Fin.ext rfl
      rw [Fin.lastCases_castSucc]
      change (actualJointNormalProjection n t (tangentProjection (n+t) 1 z.val) j) ^ Q.d =
        (actualJointNormalProjection n (t+1) z.val j.castSucc) ^ Q.d
      simp only [actualJointNormalProjection_apply, tangentProjection_apply, hOld]


open HironakaG1NormalGraphFlags HironakaG1FiniteSourceWeakClassGraphLift
  MarkedIdealBiholomorphism BlowupTowers HironakaG11PresLineState ResolutionInvariantSpec
  InvDomainTowerAlong

/-- The finite graph powers on the ambient cylinder, with the original
ordered boundary pulled back in full. -/
def blockAmbientMarked {t : ℕ} (f : U → ComplexModel t) (Q : MarkedIdeal n U) :
    MarkedIdeal (n+t) (blockOpen U t) :=
  { blockMarked f Q [] with N := blockProjection ⁻¹' Q.N }

theorem iteratedNormalMarked_carrier (Q : MarkedIdeal n U) (t : ℕ) :
    (iteratedNormalMarked Q t).N = iteratedNormalProjection U t ⁻¹' Q.N := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change projection (iteratedNormalOpen U t) ⁻¹' (iteratedNormalMarked Q t).N = _
    rw [ih]
    rfl

set_option maxHeartbeats 1600000 in
/-- The entire iterated record, including its ideal, true mark, and ordered
boundary, is exactly the finite zero graph equation record on the cylinder. -/
theorem iteratedNormalMarked_pullback_blockEquiv (Q : MarkedIdeal n U)
    (hQ : Q.ideal.IsCoherent) (t : ℕ) :
    MarkedIdeal.pullback (M := CMfd.of (n := n+t) (iteratedNormalOpen U t))
      (M' := CMfd.of (n := n+t) (blockOpen U t)) (iteratedNormalBlockEquiv U t) (iteratedNormalMarked Q t) =
      blockAmbientMarked (0 : U → ComplexModel t) Q := by
  let e := iteratedNormalBlockEquiv U t
  have hπ := iteratedNormalProjection_contMDiff U t
  have hπe : iteratedNormalProjection U t ∘ e = blockProjection :=
    funext (iteratedNormalProjection_blockEquiv (U := U) (t := t))
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change e ⁻¹' (iteratedNormalMarked Q t).N = blockProjection ⁻¹' Q.N
    rw [iteratedNormalMarked_carrier, preimage_preimage]
    exact congrArg (fun g => g ⁻¹' Q.N) hπe
  · change (iteratedNormalMarked Q t).E.map (e ⁻¹' ·) = Q.E.map (blockProjection ⁻¹' ·)
    rw [(iteratedNormalMarked_data Q t).2, List.map_map]
    simp only [Function.comp_def, preimage_preimage]
    exact congrArg (fun g => Q.E.map (g ⁻¹' ·)) hπe
  · change GermIdeal.pullback (m := n+t) e (iteratedNormalMarked Q t).ideal = _
    rw [iteratedNormalMarked_ideal Q hQ]
    let c : Fin t → iteratedNormalOpen U t → ℂ := fun i z => iteratedNormalCoordinate U t i z ^ Q.d
    have hc (i : Fin t) : MDifferentiable 𝓘(ℂ, ComplexModel (n+t)) 𝓘(ℂ, ℂ) (c i) :=
      (iteratedNormalCoordinate_mdifferentiable U t i).pow _
    change GermIdeal.pullback (m := n+t) e (sumIdeal
      (GermIdeal.pullback (m := n+t) (iteratedNormalProjection U t) Q.ideal) (finiteFunctionIdeal c)) = _
    rw [pullback_sumIdeal_dimensions e.contMDiff (isCoherent_pullback hπ hQ)
      (isCoherent_finiteFunctionIdeal c hc), ← coherent_pullback_comp hπ e.contMDiff Q.ideal hQ, hπe,
      finiteFunctionIdeal_pullback c hc _ e.contMDiff]
    change sumIdeal (GermIdeal.pullback (m := n+t) blockProjection Q.ideal)
      (finiteFunctionIdeal (fun i z => c i (e z))) =
        sumIdeal (GermIdeal.pullback (m := n+t) blockProjection Q.ideal)
          (finiteFunctionIdeal (fun (i : Fin t) (z : blockOpen U t) =>
            ((actualJointNormalProjection n t z.val - (0 : ComplexModel t)) i) ^ Q.d))
    simp only [sub_zero]
    congr 2
    funext i z
    change actualJointNormalProjection n t (e z).val i ^ Q.d =
      actualJointNormalProjection n t z.val i ^ Q.d
    rw [iteratedNormalBlockEquiv_val]
  · exact (iteratedNormalMarked_data Q t).1

set_option maxHeartbeats 1200000 in
/-- The literal finite graph record after a nonlinear shift over the same
source. The chart moves the zero graph to the given graph and preserves
the full inherited boundary and the original mark. -/
theorem blockAmbientMarked_pullback_shift {t : ℕ} (f : U → ComplexModel t)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) :
    let A := CMfd.of (n := n+t) (blockOpen U t)
    let e := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (↥U) ∞)
      hf (contMDiff_const (c := (0 : ComplexModel t)))
    MarkedIdeal.pullback (M := A) (M' := A) e (blockAmbientMarked (0 : U → ComplexModel t) Q) =
      blockAmbientMarked f Q := by
  intro A e
  let g : U → ComplexModel t := fun _ => 0
  have hz : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ g := contMDiff_const
  have h := pullback_blockMarked (b := (id : U → U)) contMDiff_id hf hz Q hQ []
  have hId : MarkedIdeal.pullback (M := CMfd.of (n := n) U) (M' := CMfd.of (n := n) U)
      (id : U → U) Q = Q :=
    ContactCanonicalAlong.pullback_id Q hQ
  rw [hId, List.map_nil] at h
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext z
    change blockProjection (blockChartMap id f g z) ∈ Q.N ↔ blockProjection z ∈ Q.N
    rw [blockProjection_chartMap]
    rfl
  · change (MarkedIdeal.pullback (M := A) (M' := A) (blockChartMap id f g) (blockMarked g Q [])).E =
      (blockMarked f Q []).E
    exact congrArg MarkedIdeal.E h
  · change (MarkedIdeal.pullback (M := A) (M' := A) (blockChartMap id f g) (blockMarked g Q [])).ideal =
      (blockMarked f Q []).ideal
    exact congrArg MarkedIdeal.ideal h
  · rfl

set_option maxHeartbeats 1400000 in
/-- A finite nonlinear normal graph carries the actual native state and
ordinary domain of the iterated padding. The record is the original
pullback plus all graph equation powers at the original mark. -/
theorem blockAmbientMarked_nativeHSState {t : ℕ} {W : Set U}
    (f : U → ComplexModel t)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (H : ℕ → ℕ)
    (hQ : NativeHSState (X := CMfd.of (n := n) U) Q W H) (hDomain : IsInvDomain n Q) :
    let A := CMfd.of (n := n+t) (blockOpen U t)
    IsInvDomain (n+t) (blockAmbientMarked f Q) ∧
      NativeHSState (X := A) (blockAmbientMarked f Q) (blockGraph f W) H := by
  intro A
  obtain ⟨hD, hS⟩ := iteratedNormalMarked_nativeHSState H hQ hDomain t
  let e := iteratedNormalBlockEquiv U t
  have hDE : IsInvDomain (n+t)
      (MarkedIdeal.pullback (M' := A) e (iteratedNormalMarked Q t)) := isInvDomain_pullback e hD
  have hSE := hS.pullback (X' := A) e
  rw [iteratedNormalMarked_pullback_blockEquiv Q hDomain.isWellFormed.isCoherent t] at hDE hSE
  rw [iteratedNormalCarrier_preimage_blockEquiv] at hSE
  let b := blockChartEquiv (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (↥U) ∞)
    hf (contMDiff_const (c := (0 : ComplexModel t)))
  have hDB := isInvDomain_pullback b hDE
  have hSB := hSE.pullback (X' := A) b
  have hB := blockAmbientMarked_pullback_shift f hf Q hDomain.isWellFormed.isCoherent
  change MarkedIdeal.pullback (M := A) (M' := A) b (blockAmbientMarked (0 : U → ComplexModel t) Q) =
    blockAmbientMarked f Q at hB
  rw [hB] at hDB hSB
  refine ⟨hDB, ?_⟩
  have hG : b ⁻¹' blockGraph (0 : U → ComplexModel t) W = blockGraph f W := by
    change blockChartMap (id : U → U) f (fun _ => 0) ⁻¹' blockGraph (fun _ => 0) W = _
    rw [blockChartMap_preimage_graph, preimage_id]
  rwa [hG] at hSB

end
end Hironaka.HironakaG1IteratedNormalBlockIdeal
