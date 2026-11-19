import Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
import Hironaka.Resolution.HironakaG10ChowRiemannExtension
import Hironaka.Resolution.HironakaG10ChowOpenHomeomorph
import Hironaka.Analytic.AnalyticSubsetPreimage

/-!
# Hironaka's Chow lemma for manifolds from flattening and openness of flat maps

A second reduction of goal G10a (blueprint `hironaka-g10-chowside-flattening-open-reduction.tex`)
which does NOT use the finite mapping theorem.  Flattening gives a tower `σ : X' ⟶ X` and a flat
strict transform `p : Y' ⟶ X'` of a proper modification `f : Y → X` of a compact complex
manifold; openness of flat maps makes `p` a homeomorphism (no stalk computation).  A manifold `W`
lifted through the tower by `γ` then maps continuously to `Y` by `q ∘ p⁻¹ ∘ γ`; this map is
holomorphic off the preimage of the exceptional set of `f`, where it is `f⁻¹ ∘ (σ ∘ γ)`, hence
holomorphic by the Riemann extension theorem (`HironakaG10ChowRiemannExtension`).

Main declarations:

* `isHomeomorph_of_isStrictTransform_of_isOpenMap` — an open strict transform of a map which is
  an isomorphism off a thin set is a homeomorphism.
* `hasStableBlowupDomination_of_flattening_of_open`,
  `hironakaChowLemmaManifold_of_flattening_of_open` — goal G10a from `HironakaFlattening` and
  `FlatMorphismsAreOpen` only.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningOpenReduction

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaG10ChowStrictSquare HironakaChowLemma
  HironakaG10ChowOpenHomeomorph AnalyticModificationLocalDiscrepancy SourceReducedComplexSpace
  OriginalNativeModification HironakaG10ChowNativeIsoCriterion HironakaG10ChowFlatBimeromorphicIso
  HironakaG10ChowTowerDomination HironakaG10ChowFlatteningReduction

noncomputable section

/-- **An open strict transform is a homeomorphism.**  Let `f : Y ⟶ X` be an isomorphism over the
complement of a set `T` with empty interior, `σ` an open immersion off a closed set `E` with empty
interior and `(Y', p, q)` a strict transform of `f` under `σ` relative to `E`.  If the point map
of `p` is open, it is a homeomorphism. -/
theorem isHomeomorph_of_isStrictTransform_of_isOpenMap {X X' Y Y' : SourceReducedComplexSpace}
    {f : Y ⟶ X} {σ : X' ⟶ X} {E : Set X'.obj.left} {p : Y' ⟶ X'} {q : Y' ⟶ Y}
    (hst : IsStrictTransform f σ E p q) (hEc : IsClosed E) (hEi : interior E = ∅)
    (hσ : IsOpenImmersionOn σ Eᶜ) {T : Set X.obj.left} (hTi : interior T = ∅)
    (hf : IsIsoOver f Tᶜ) (ho : IsOpenMap p.hom.left.base) : IsHomeomorph p.hom.left.base := by
  have : T2Space Y'.obj.left.toPresheafedSpace := Y'.property.1
  have hsq : ∀ y' : Y'.obj.left,
      f.hom.left.base (q.hom.left.base y') = σ.hom.left.base (p.hom.left.base y') := fun y' =>
    congrArg (fun H : Y' ⟶ X => H.hom.left.base y') hst.comm
  exact isHomeomorph_of_isOpenMap_of_isProperMap ho hst.proper
    (dense_compl_inter_preimage_compl hEc hEi (isOpen_image_of_isOpenImmersionOn hσ) hTi)
    ((injOn_of_square hsq hst.pair_injective (injOn_of_isIsoOver hf)).mono
      (fun y' hy' => hy'.2))
    (subset_range_of_square (subset_range_of_isIsoOver hf) hst.covers)

section ChowLemma

variable {n : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Stable domination from flattening and openness of flat maps** (no finite mapping theorem). -/
theorem hasStableBlowupDomination_of_flattening_of_open (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) [CompactSpace X] {f : Y → X}
    (hf : IsAnalyticModification (n := n) f) : HasStableBlowupDomination n f := by
  obtain ⟨hFproper, T, -, hTi, -, hFiso⟩ := nativeMorphism_isProperBimeromorphic hf
  have hcpt : CompactSpace (wholeModel (n := n) X).obj.left :=
    (Homeomorph.Set.univ X).symm.compactSpace
  obtain ⟨X', σ, E, hσ, hEc, hEi, hσE, Y', p, q, hst, hflat⟩ :=
    H₀ _ _ (nativeMorphism hf.1) hcpt hFproper
  have hhom : IsHomeomorph p.hom.left.base :=
    isHomeomorph_of_isStrictTransform_of_isOpenMap hst hEc hEi hσE hTi hFiso (H₁ _ _ p hflat)
  let ep := IsHomeomorph.homeomorph _ hhom
  obtain ⟨Af, Bf, s, -, -, -, hBfc, hBfa, hBfi, hpre, hs, -, hsf⟩ := hf.2.2
  intro V _ _ _ c hc
  have : CompactSpace V :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  obtain ⟨W, tW, cW, mW, ρ, hρ, γ, hγp, -⟩ :=
    exists_lift_of_isNativeBlowupTower hσ (nativeMorphism hc.1) (isOpenOffThin_nativeMorphism hc)
  let := tW
  let := cW
  let := mW
  let g : W → Y := fun w =>
    (q.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩))).val
  have hgc : Continuous g :=
    continuous_subtype_val.comp (q.hom.left.base.hom.continuous.comp (ep.symm.continuous.comp
      (γ.hom.left.base.hom.continuous.comp (continuous_id.subtype_mk (fun w => mem_univ w)))))
  have hfg : ∀ w : W, f (g w) = c (ρ w) := by
    intro w
    have h1 : p.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩)) =
        γ.hom.left.base ⟨w, mem_univ w⟩ := ep.apply_symm_apply _
    have h2 := congrArg (fun H : Y' ⟶ wholeModel (n := n) X =>
      (H.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩))).val) hst.comm
    have h3 := congrArg (fun H : wholeModel (n := n) W ⟶ wholeModel (n := n) X =>
      (H.hom.left.base ⟨w, mem_univ w⟩).val) hγp
    refine h2.trans ?_
    change (σ.hom.left.base (p.hom.left.base (ep.symm (γ.hom.left.base ⟨w, mem_univ w⟩)))).val =
      c (ρ w)
    rw [h1]
    exact h3
  have hcρ : IsAnalyticModification (n := n) (c ∘ ρ) :=
    AnalyticModificationComposition.isAnalyticModification_comp hc
      (isAnalyticModification_of_isBlowupSequence hρ)
  have hAa : IsComplexAnalyticSubset (n := n) ((c ∘ ρ) ⁻¹' Bf) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hcρ.1 hBfa
  have hAc : IsClosed ((c ∘ ρ) ⁻¹' Bf) := hBfc.preimage hcρ.1.continuous
  have hAi : interior ((c ∘ ρ) ⁻¹' Bf) = ∅ :=
    AnalyticModelDomination.interior_preimage_eq_empty_of_isAnalyticModification hcρ hBfi
  have hgA : ∀ w, w ∉ (c ∘ ρ) ⁻¹' Bf →
      MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) g w := by
    intro w hw
    have hev : ∀ᶠ w' in 𝓝 w, g w' = s (c (ρ w')) := by
      filter_upwards [hAc.isOpen_compl.mem_nhds hw] with w' hw'
      have h1 : f (g w') ∉ Bf := by
        rw [hfg w']
        exact hw'
      have h2 : g w' ∉ Af := by
        intro h
        rw [← hpre] at h
        exact h1 h
      calc
        g w' = s (f (g w')) := (hsf _ h2).symm
        _ = s (c (ρ w')) := by rw [hfg w']
    have hsat : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s (c (ρ w)) :=
      hs.contMDiffAt (hBfc.isOpen_compl.mem_nhds hw)
    have hsm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (s ∘ (c ∘ ρ)) w :=
      (hsat.mdifferentiableAt (by simp)).comp w (hcρ.1.contMDiffAt.mdifferentiableAt (by simp))
    exact hsm.congr_of_eventuallyEq hev
  have hℓ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    HironakaG10ChowRiemannExtension.contMDiff_of_continuous_of_isComplexAnalyticSubset hgc hAa
      hAc hAi hgA
  exact ⟨W, tW, cW, mW, ρ, g, hρ, hℓ, funext hfg⟩

end ChowLemma

/-- **Goal G10a from flattening and openness of flat maps.**  Hironaka's flattening theorem for
compact bases and the openness of flat morphisms imply Hironaka's Chow lemma for compact complex
manifolds; the finite mapping theorem is not used. -/
theorem hironakaChowLemmaManifold_of_flattening_of_open (H₀ : HironakaFlattening)
    (H₁ : FlatMorphismsAreOpen) : HironakaChowLemmaManifold.{0} := by
  intro n X _ _ _ _ Y _ _ _ f hf
  exact (hasStableBlowupDomination_of_flattening_of_open H₀ H₁ hf).hasBlowupDomination

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningOpenReduction
