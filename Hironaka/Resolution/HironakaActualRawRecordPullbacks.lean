import Hironaka.Resolution.HironakaActualRawCompanionNaturality
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen

/-! Literal entire-record restriction for arbitrary raw actual histories.
The source ideal needs holomorphic members only; global source coherence or
analyticity of the carrier is not assumed. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualRawRecordPullbacks
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan GermIdealPullbackCalculus
open DerivativeIdealAlongEtale InvertibleIdealQuotient IdealWeightPowers
open BlowupRestrictOpen RestrictedIdealQuotient BlowupStrictSubmanifold
noncomputable section
variable {n : ℕ}

section Compose
variable {P Q R : Type u} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
 [TopologicalSpace Q] [ChartedSpace (ComplexModel n) Q] [IsComplexManifold n Q]
 [TopologicalSpace R] [ChartedSpace (ComplexModel n) R] [IsComplexManifold n R]
theorem pullback_comp_hhol {f : P → R} {g : Q → P}
 (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
 {𝔞 : GermIdeal n R} (hhol : ∀ x v, 𝔞.mem x v → HolomorphicAt n v x) :
 GermIdeal.pullback (m := n) (f ∘ g) 𝔞 =
   GermIdeal.pullback (m := n) g (GermIdeal.pullback (m := n) f 𝔞) := by
  refine GermIdeal.ext (funext fun z => funext fun v => propext ⟨fun hv => ?_, fun hv => ?_⟩)
  · have hfat : ∀ᶠ y in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
      Eventually.of_forall fun y => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    have hchol : HolomorphicAt n c (f (g z)) :=
      hhol _ _ hc
    have hcfhol : HolomorphicAt n (c ∘ f) (g z) := hchol.comp_contMDiff hfat
    have hcf : (GermIdeal.pullback (m := n) f 𝔞).mem (g z) (c ∘ f) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨c, hc, rfl⟩ hcfhol
        (holomorphicAt_const 1) (Eventually.of_forall fun _ => (one_mul _).symm))
    exact ⟨c ∘ f, hcf, rfl⟩
  · refine GermIdeal.mem_pullback_iff.mpr
      (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hv))
    rintro u ⟨c, hc, rfl⟩
    refine IsInSpanAt.mono ?_
      (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro u' ⟨σ, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

theorem marked_pullback_comp_hhol {J : MarkedIdeal n R}
 (hhol : ∀ x v, J.ideal.mem x v → HolomorphicAt n v x) {a : P → R} {b : Q → P} {d : Q → R}
 (ha : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a)
 (hb : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ b) (h : ∀ q,a (b q)=d q) :
 MarkedIdeal.pullback b (MarkedIdeal.pullback a J) = MarkedIdeal.pullback d J := by
 have hfun : a ∘ b = d := funext h
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
 · show b ⁻¹' (a ⁻¹' J.N)=d ⁻¹' J.N
   rw [←preimage_comp,hfun]
 · show (J.E.map (a ⁻¹' ·)).map (b ⁻¹' ·)=J.E.map (d ⁻¹' ·)
   rw [List.map_map]
   refine List.map_congr_left fun S _ => ?_
   show b ⁻¹' (a ⁻¹' S)=d ⁻¹' S
   rw [←preimage_comp,hfun]
 · show GermIdeal.pullback (m := n) b (GermIdeal.pullback (m := n) a J.ideal)=GermIdeal.pullback (m := n) d J.ideal
   rw [←pullback_comp_hhol ha hb hhol,hfun]
end Compose

section Records
variable {X Y Z : CMfd.{u} n}

/-- Whole actual one-step restriction needs only holomorphic source ideal
members. Neither a globally regular carrier, a coherent source ideal, a
coherent output ideal nor an admissibility certificate is a premise. -/
theorem geoTransform_pullback_val_of_hhol
 {M : MarkedIdeal n X}
 (hhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x)
 {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
 (U : Opens X) (hV : IsOpen (π ⁻¹' (U : Set X))) :
 (MarkedIdeal.pullback (Subtype.val : U → X) M).geoTransform ((↑) ⁻¹' C : Set U)
   (fun p : (⟨π ⁻¹' (U : Set X),hV⟩ : Opens Y) => (⟨π p.val,p.property⟩ : U)) =
 MarkedIdeal.pullback (Subtype.val : (⟨π ⁻¹' (U : Set X),hV⟩ : Opens Y) → Y)
   (M.geoTransform C π) := by
 let V : Opens Y := ⟨π ⁻¹' (U : Set X),hV⟩
 let r : V → U := fun p => ⟨π p.val,p.property⟩
 have hr : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ r :=
   BlowupRestrictOpen.contMDiff_opens_mk (hπ.contMDiff.comp contMDiff_subtype_val) (fun p => p.property)
 have hvr : (Subtype.val ∘ r : V → X)=π ∘ Subtype.val := rfl
 have hIC := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
 have hpbA : GermIdeal.pullback (m := n) r (GermIdeal.pullback (m := n) (Subtype.val : U → X) M.ideal)=
     GermIdeal.pullback (m := n) (Subtype.val : V → Y) (GermIdeal.pullback (m := n) π M.ideal) := by
   rw [←pullback_comp_hhol contMDiff_subtype_val hr hhol,hvr,
     pullback_comp_hhol hπ.contMDiff contMDiff_subtype_val hhol]
 have hpbC : GermIdeal.pullback (m := n) r (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set U))=
     GermIdeal.pullback (m := n) (Subtype.val : V → Y)
       (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) := by
   rw [pullback_vanishingIdeal_opens U r C,hvr,
     pullback_comp_hhol hπ.contMDiff contMDiff_subtype_val
       (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hIC hg)]
 refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
   (MarkedIdealRestrictOpen.geoStrictTransform_restrict U hV M.N) ?_ ?_ rfl
 · simp only [geoTransform_E,MarkedIdeal.pullback,List.map_append,List.map_map,List.map_cons,List.map_nil]
   congr 1
   exact List.map_congr_left fun K _ => MarkedIdealRestrictOpen.geoStrictTransform_restrict U hV K
 · change colonAlong n (geoStrictTransform r ((↑) ⁻¹' C : Set U) ((↑) ⁻¹' M.N))
     (GermIdeal.pullback (m := n) r (GermIdeal.pullback (m := n) (Subtype.val : U → X) M.ideal))
     (idealPow (GermIdeal.pullback (m := n) r (vanishingIdeal (n := n) ((↑) ⁻¹' C : Set U))) M.d) =
     GermIdeal.pullback (m := n) (Subtype.val : V → Y)
       (colonAlong n (geoStrictTransform π C M.N) (GermIdeal.pullback (m := n) π M.ideal)
         (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d))
   rw [MarkedIdealRestrictOpen.geoStrictTransform_restrict U hV M.N,hpbA,hpbC,
     ←BlowupExceptionalDivisor.pullback_idealPow contMDiff_subtype_val
       (isCoherent_pullback hπ.contMDiff hIC)]
   have hNumClosed : ∀ x g,IsInSpanAt (n := n)
       ((GermIdeal.pullback (m := n) π M.ideal).mem x) x g →
       (GermIdeal.pullback (m := n) π M.ideal).mem x g := by
     intro x g hg
     dsimp only [GermIdeal.pullback] at hg ⊢
     exact IsInSpanAt.trans (fun _ hs => hs) hg
   have hDen : (idealPow (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)) M.d).IsCoherent :=
     isCoherent_idealPow (isCoherent_pullback hπ.contMDiff hIC) M.d
   exact HironakaActualRawCompanionNaturality.pullback_colonAlong
     (φ := (Subtype.val : V → Y)) (fun p => ⟨openInv V p,isLocalInverseAt_val V p⟩)
     (fun (x : Y) (g : Y → ℂ) (hg : (GermIdeal.pullback (m := n) π M.ideal).mem x g) => hg.1) hNumClosed
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDen hg)
     (fun _ _ hg => GermIdealTotalTransform.mem_of_isInSpanAt_mem hDen hg)

/-- Holomorphic germ members survive every raw actual prefix, independently
of admissibility or regularity of the strict carrier. -/
theorem holomorphic_geoTransformAlong (M : MarkedIdeal n X)
 (hhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x) :
 ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (x : Y) (g : Y → ℂ),
   (geoTransformAlong M T).ideal.mem x g → HolomorphicAt n g x
 | _,.refl,x,g,hg => hhol x g hg
 | _,.step _ _ _ _,_,_,hg => hg.1

/-- The entire raw original record commutes with actual restriction along
EVERY finite history. All ordered old and born boundary labels remain in the
same list positions; no global source-domain or coherence hypothesis is used. -/
theorem geoTransformAlong_restrict_of_hhol (M : MarkedIdeal n X)
 (hhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x) (U : Opens X) :
 ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
   geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)=
     MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong M T)
 | _,.refl => rfl
 | _,.step T C π hπ => by
   have ih := geoTransformAlong_restrict_of_hhol M hhol U T
   have hT := holomorphic_geoTransformAlong M hhol T
   change (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T)).geoTransform
     ((Subtype.val : openPreimage T U → _) ⁻¹' C)
     (fun p : openPreimage (.step T C π hπ) U => ⟨π p.val,p.property⟩) = _
   rw [ih]
   exact geoTransform_pullback_val_of_hhol hT hπ (openPreimage T U)
     (openPreimage (.step T C π hπ) U).isOpen
end Records

end
end Hironaka.HironakaActualRawRecordPullbacks
