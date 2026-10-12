/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ControlledTransformUniqueness
import Hironaka.Resolution.HironakaSmoothSubmersionDivisorExponents
import Hironaka.Blowup.BlowupControlledTransform
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionInvertibleQuotients
open Hironaka.HolomorphicIdealSheaves
open InvertibleIdealQuotient GermIdealPullbackCalculus RelativePrincipalizationSpan
open IdealWeightPowers MarkedIdeals GermIdealOrder
open HironakaSmoothSubmersionDivisorExponents HironakaSmoothSubmersionCoefficientIdeals
open Hironaka
noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
include hf

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- The actual original local generator stays nonzero on some point of EVERY genuine nonempty open preimage subset. -/
theorem exists_ne_zero_comp_on_open {U : Set X} {h : X → ℂ}
 (hnon : ∀ V : Set X, IsOpen V → V ⊆ U → V.Nonempty → ∃ x ∈ V, h x ≠ 0)
 {W : Set Y} (hW : IsOpen W) (hWU : W ⊆ f ⁻¹' U) (hWne : W.Nonempty) :
 ∃ y ∈ W, (h ∘ f) y ≠ 0 := by
 obtain ⟨w, hw⟩ := hWne
 have himage : f '' W ∈ 𝓝 (f w) := by
   rw [← map_nhds_submersion_eq (hf.isSubmersionAt w)]
   change f ⁻¹' (f '' W) ∈ 𝓝 w
   exact Filter.mem_of_superset (hW.mem_nhds hw) (fun z hz => ⟨z, hz, rfl⟩)
 obtain ⟨V, hVimage, hVopen, hfwV⟩ := mem_nhds_iff.mp himage
 have hVU : V ⊆ U := by
   intro z hz
   obtain ⟨y, hy, rfl⟩ := hVimage hz
   exact hWU hy
 obtain ⟨z, hz, hzne⟩ := hnon V hVopen hVU ⟨f w, hfwV⟩
 obtain ⟨y, hy, hfy⟩ := hVimage hz
 exact ⟨y, hy, by simpa only [Function.comp_apply, hfy] using hzne⟩

/-- The whole original invertible ideal pulls back to an actual invertible ideal in the true source dimension. -/
theorem isInvertible_pullback_submersion {L : GermIdeal n X} (hL : L.IsInvertible) :
 (GermIdeal.pullback (m := m) f L).IsInvertible := by
 intro y
 obtain ⟨U, hU, hfyU, h, hh, hnon, hgen⟩ := hL (f y)
 have hhhol : ∀ x ∈ U, HolomorphicAt n h x :=
   fun x hx => holomorphicAt_of_mdifferentiableOn hU hh hx
 have hfat : ∀ {z : Y}, ∀ᶠ w in 𝓝 z,
   ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f w :=
   fun {_} => Eventually.of_forall fun _ => hf.contMDiff.contMDiffAt
 refine ⟨f ⁻¹' U, hU.preimage hf.contMDiff.continuous, hfyU, h ∘ f, ?_, ?_, ?_⟩
 · intro z hz
   exact ((hhhol (f z) hz).comp_contMDiff hfat).mdifferentiableAt.mdifferentiableWithinAt
 · exact fun W hW hWU hWne => exists_ne_zero_comp_on_open hf hnon hW hWU hWne
 intro z hz g
 constructor
 · intro hg
   refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
   rintro a ⟨b, hb, rfl⟩
   refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hf.contMDiff
     ((hgen (f z) hz b).mp hb))
   rintro c ⟨d, rfl, rfl⟩
   rfl
 · intro hg
   refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.mono ?_ hg)
   rintro a rfl
   exact ⟨h, (hgen (f z) hz h).mpr
     (isInSpanAt_self rfl (hhhol (f z) hz)), rfl⟩

/-- Actual coherent division by an original invertible ideal commutes with the ENTIRE genuine submersion pullback. -/
theorem pullback_colon_eq {I L : GermIdeal n X} (hI : I.IsCoherent)
 (hL : L.IsInvertible) (hle : I.Le L) :
 GermIdeal.pullback (m := m) f (colon I L) =
   colon (GermIdeal.pullback (m := m) f I) (GermIdeal.pullback (m := m) f L) := by
 have hQ := isCoherent_colon hI hL hle
 have hLc := DivisorMetric.isCoherent_of_isInvertible hL
 have hEq : I = L.mul (colon I L) := by
   ext x g
   exact ⟨fun hg => le_mul_colon hI hL hle x g hg,
     fun hg => mul_colon_le hI x g hg⟩
 have hprod : GermIdeal.pullback (m := m) f I =
   (GermIdeal.pullback (m := m) f L).mul (GermIdeal.pullback (m := m) f (colon I L)) := by
   calc
    _ = GermIdeal.pullback (m := m) f (L.mul (colon I L)) := congrArg _ hEq
    _ = _ := HironakaSmoothSubmersionCoefficientIdeals.pullback_mul hf.contMDiff hLc hQ
 rw [hprod, BlowupControlledTransform.colon_mul_eq (isInvertible_pullback_submersion hf hL)
   (GermIdealPullbackCalculus.isCoherent_pullback hf.contMDiff hQ)]

/-- ALL natural powers of the SAME original invertible denominator, including the original unit denominator. -/
theorem pullback_colon_idealPow_eq {I L : GermIdeal n X} (hI : I.IsCoherent)
 (hL : L.IsInvertible) (q : ℕ) (hle : I.Le (idealPow L q)) :
 GermIdeal.pullback (m := m) f (colon I (idealPow L q)) =
   colon (GermIdeal.pullback (m := m) f I) (idealPow (GermIdeal.pullback (m := m) f L) q) := by
 rw [pullback_colon_eq hf hI (BlowupExceptionalDivisor.isInvertible_idealPow hL q) hle,
   pullback_idealPow hf.contMDiff (DivisorMetric.isCoherent_of_isInvertible hL)]

/-- Complete literal original marked data after division by the original invertible ideal. -/
theorem markedPullback_colon_record_eq (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
 {L : GermIdeal n X} (hL : L.IsInvertible) (hle : M.ideal.Le L) :
 markedPullback (m := m) f { M with ideal := colon M.ideal L } =
   { markedPullback (m := m) f M with
     ideal := colon (GermIdeal.pullback (m := m) f M.ideal) (GermIdeal.pullback (m := m) f L) } := by
 have heq := pullback_colon_eq hf hI hL hle
 cases M
 simp only [markedPullback]
 congr 1

/-- EVERY actual original natural cosupport threshold of the whole coherent quotient ideal. -/
theorem colon_cosupport_pullback_eq {I L : GermIdeal n X} (hI : I.IsCoherent)
 (hL : L.IsInvertible) (hle : I.Le L) (d : ℕ) :
 cosupport m univ (colon (GermIdeal.pullback (m := m) f I)
   (GermIdeal.pullback (m := m) f L)) d = f ⁻¹' cosupport n univ (colon I L) d := by
 rw [← pullback_colon_eq hf hI hL hle]
 exact HironakaSmoothSubmersionOrder.cosupport_pullback_eq hf (isCoherent_colon hI hL hle) d
end
end Hironaka.HironakaSmoothSubmersionInvertibleQuotients
