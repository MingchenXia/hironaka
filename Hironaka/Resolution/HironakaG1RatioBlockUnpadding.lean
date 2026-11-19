import Hironaka.Resolution.HironakaG1RatioBlockNativeStates
import Hironaka.Resolution.HironakaG8CoeffClass

/-! Literal unpadding on the holomorphic section of either normalized ratio cylinder. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1RatioBlockUnpadding
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG1NormalGraphFlags HironakaG1IteratedNormalBlockIdeal
  HironakaSmoothSubmersionCoefficientIdeals HironakaActualPowerBoundaryExponents
  HironakaG8CoeffClass IdealWeightPowers

/-- The exact nonlinear graph section recovers the whole normalized source
record, including its ambient carrier restriction, ordered boundary and mark. -/
theorem markedPullback_blockAmbientMarked_section {n t : ℕ}
    {U : Opens (ComplexModel n)} {f : U → ComplexModel t}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d) :
    markedPullback (m := n) (blockSection f) (blockAmbientMarked f Q) = Q := by
  have h1 := markedPullback_power_blockSection hf Q hQ hd [] 1
  have hIdeal := congrArg (fun P : MarkedIdeal n U => P.ideal) h1
  change GermIdeal.pullback (m := n) (blockSection f) (idealPow (blockMarked f Q []).ideal 1) =
    idealPow Q.ideal 1 at hIdeal
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · ext x
    change blockProjection (blockSection f x) ∈ Q.N ↔ x ∈ Q.N
    rw [blockProjection_blockSection]
  · change (Q.E.map (blockProjection ⁻¹' ·)).map (blockSection f ⁻¹' ·) = Q.E
    rw [List.map_map]
    have hRet : blockProjection ∘ blockSection f = id := funext (blockProjection_blockSection f)
    change Q.E.map (fun A => (blockProjection ∘ blockSection f) ⁻¹' A) = Q.E
    rw [hRet]
    simp
  · change GermIdeal.pullback (m := n) (blockSection f) (blockMarked f Q []).ideal = Q.ideal
    have hq : idealPow Q.ideal 1 = Q.ideal := by
      rw [idealPow_succ,idealPow_zero,BlowupControlledTransform.unitIdeal_mul hQ]
    calc
      _ = GermIdeal.pullback (m := n) (blockSection f) (idealPow (blockMarked f Q []).ideal 1) :=
        congrArg (GermIdeal.pullback (m := n) (blockSection f))
          (idealPow_one_eq (blockMarked_coherent hf hQ [])).symm
      _ = _ := hIdeal.trans hq
  · rfl

open HironakaSmoothSubmersionOrderedChoiceImageTrace

/-- For either actual cylinder open-image chart, the part of the graph
section lying in its image is an open of the normalized base. Its exact
holomorphic lift into the input common open pulls the padded ratio record
back to the normalized source record restricted to that base open. -/
theorem exists_openImage_section_unpadding {n t d : ℕ} {U : Opens (ComplexModel n)}
    {X : CMfd.{0} d}
    (e : X → blockOpen U t) (O : Opens (blockOpen U t))
    (b : X ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel (n+t))⟯ O)
    (hb : ∀ z, e z = (b z).val)
    (f : U → ComplexModel t)
    (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel t) ∞ f)
    (Q : MarkedIdeal n U) (hQ : Q.ideal.IsCoherent) (hd : 0 < Q.d) :
    let W : Opens U := ⟨blockSection f ⁻¹' O, O.isOpen.preimage (blockSection_contMDiff hf).continuous⟩
    ∃ s : W → X,
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ s ∧
      (∀ x : W, e (s x) = blockSection f x.val) ∧
      markedPullback (m := n) s (markedPullback (m := d) e (blockAmbientMarked f Q)) =
        markedPullback (m := n) (Subtype.val : W → U) Q := by
  intro W
  let j (x : W) : O := ⟨blockSection f x.val,x.property⟩
  have hj : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+t)) ∞ j :=
    (ContMDiff.subtypeVal_comp_iff O j).mp ((blockSection_contMDiff hf).comp contMDiff_subtype_val)
  let s : W → X := b.symm ∘ j
  have hs : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel d) ∞ s :=
    b.symm.contMDiff.comp hj
  have hFactor (x : W) : e (s x) = blockSection f x.val := by
    rw [hb]
    change (b (b.symm (j x))).val = _
    rw [b.apply_symm_apply]
  have heq : e = Subtype.val ∘ b := funext hb
  have he : ContMDiff 𝓘(ℂ,ComplexModel d) 𝓘(ℂ,ComplexModel (n+t)) ∞ e :=
    heq.symm ▸ contMDiff_subtype_val.comp b.contMDiff
  have hCo : (blockAmbientMarked f Q).ideal.IsCoherent := blockMarked_coherent hf hQ []
  let Z := CMfd.of (n := n) W
  let Y := CMfd.of (n := n+t) (blockOpen U t)
  let A := CMfd.of (n := n) U
  refine ⟨s,hs,hFactor,?_⟩
  rw [← whole_markedPullback_comp (X := Y) (Y := X) (Z := Z) he hs _ hCo,
    (funext hFactor : e ∘ s = blockSection f ∘ (Subtype.val : W → U)),
    whole_markedPullback_comp (X := Y) (Y := A) (Z := Z) (blockSection_contMDiff hf)
      contMDiff_subtype_val _ hCo,
    markedPullback_blockAmbientMarked_section hf Q hQ hd]

end
end Hironaka.HironakaG1RatioBlockUnpadding
