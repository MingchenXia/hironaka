/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionDerivativeEquality
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.CoefficientAmbientMarkedDataExact

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionCoefficientIdeals
open Hironaka.HolomorphicIdealSheaves
open GermIdealOrder IdealWeightPowers GermIdealPullbackCalculus InvertibleIdealQuotient
open RelativePrincipalizationSpan HomogenizedGlueing CoefficientIdeal DerivativeIdeal DerivativeIdealTower
open HironakaSmoothSubmersionDerivativeEquality MarkedIdeals
open Hironaka
noncomputable section
variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
variable {f : Y → X}

theorem pullback_mul
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
 GermIdeal.pullback (m := m) f (I.mul J) =
   (GermIdeal.pullback (m := m) f I).mul (GermIdeal.pullback (m := m) f J) := by
 have hholI : ∀ {x : X} {g : X → ℂ}, I.mem x g → HolomorphicAt n g x :=
   fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem hI h
 have hholJ : ∀ {x : X} {g : X → ℂ}, J.mem x g → HolomorphicAt n g x :=
   fun {_ _} h => GermIdeal.IsCoherent.holomorphicAt_mem hJ h
 refine GermIdeal.ext (funext fun y => funext fun g => propext
   ⟨fun hg => pullback_mul_le hf hholI hholJ y g hg, fun hg => ?_⟩)
 have hfat : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
   Eventually.of_forall fun z => hf.contMDiffAt
 refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
 rintro _ ⟨p, q, hp, hq, rfl⟩
 obtain ⟨-, K, s, γ, hs, hγ, hsum⟩ := GermIdeal.mem_pullback_iff.mp hp
 obtain ⟨-, L, s', δ, hs', hδ, hsum'⟩ := GermIdeal.mem_pullback_iff.mp hq
 choose a ha hsa using hs
 choose b hb hsb using hs'
 have hterm : ∀ r : Fin K × Fin L,
     IsInSpanAt (n := m) (fun u => ∃ c, (I.mul J).mem (f y) c ∧ u = c ∘ f) y
       (fun z => γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) := by
   rintro ⟨i, j⟩
   have hab : (I.mul J).mem (f y) (fun x => a i x * b j x) :=
     mem_mul_iff.mpr (isInSpanAt_self ⟨a i, b j, ha i, hb j, rfl⟩
       ((hholI (ha i)).mul (hholJ (hb j))))
   have heq : (fun z => s i z * s' j z) = (fun x => a i x * b j x) ∘ f := by
     funext z
     rw [hsa i, hsb j]
     rfl
   have hhol : HolomorphicAt m (fun z => s i z * s' j z) y := by
     rw [heq]
     exact ((hholI (ha i)).mul (hholJ (hb j))).comp_contMDiff hfat
   exact IsInSpanAt.mul_left ((hγ i).mul (hδ j)) (isInSpanAt_self ⟨_, hab, heq⟩ hhol)
 refine IsInSpanAt.congr' (IsInSpanAt.sum Finset.univ fun r _ => hterm r) ?_
 filter_upwards [hsum, hsum'] with z hz hz'
 show (∑ r : Fin K × Fin L, γ r.1 z * δ r.2 z * (s r.1 z * s' r.2 z)) = p z * q z
 rw [hz, hz', Finset.sum_mul_sum, Fintype.sum_prod_type]
 exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
theorem pullback_unitIdeal : GermIdeal.pullback (m := m) f (unitIdeal n X) = unitIdeal m Y := by
 ext y g
 constructor
 · intro hg
   exact (GermIdeal.mem_pullback_iff.mp hg).1
 · intro hg
   apply GermIdeal.mem_pullback_iff.mpr
   exact isInSpanAt_of_eq_mul ⟨(fun _ => 1), holomorphicAt_const 1, rfl⟩ hg hg
     (Eventually.of_forall fun _ => (mul_one _).symm)

theorem pullback_idealPow
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I : GermIdeal n X} (hI : I.IsCoherent) :
 ∀ q, GermIdeal.pullback (m := m) f (idealPow I q) = idealPow (GermIdeal.pullback (m := m) f I) q
 | 0 => pullback_unitIdeal
 | q+1 => by
   rw [idealPow_succ, pullback_mul hf (isCoherent_idealPow hI q) hI,
     pullback_idealPow hf hI q, idealPow_succ]

theorem pullback_finSumIdeal
 (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (J : ℕ → GermIdeal n X) (r : ℕ) (hJ : ∀ i < r, (J i).IsCoherent) :
 GermIdeal.pullback (m := m) f (finSumIdeal J r) =
   finSumIdeal (fun i => GermIdeal.pullback (m := m) f (J i)) r := by
 ext y g
 constructor
 · intro hg
   change IsInSpanAt (n := m) (fun s => ∃ i, i < r ∧ (GermIdeal.pullback (m := m) f (J i)).mem y s) y g
   refine IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg)
   rintro _ ⟨a, ha, rfl⟩
   change IsInSpanAt (n := n) (fun b => ∃ i, i < r ∧ (J i).mem (f y) b) (f y) a at ha
   refine IsInSpanAt.trans ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hf ha)
   rintro _ ⟨b, ⟨i, hi, hb⟩, rfl⟩
   exact isInSpanAt_self ⟨i, hi, GermIdeal.mem_pullback_iff.mpr
     (isInSpanAt_self ⟨b, hb, rfl⟩
       ((GermIdeal.IsCoherent.holomorphicAt_mem (hJ i hi) hb).comp_contMDiff
         (Eventually.of_forall fun _ => hf.contMDiffAt)))⟩
     ((GermIdeal.IsCoherent.holomorphicAt_mem (hJ i hi) hb).comp_contMDiff
         (Eventually.of_forall fun _ => hf.contMDiffAt))
 · intro hg
   apply GermIdeal.mem_pullback_iff.mpr
   change IsInSpanAt (n := m) (fun s => ∃ i, i < r ∧ (GermIdeal.pullback (m := m) f (J i)).mem y s) y g at hg
   refine IsInSpanAt.trans ?_ hg
   rintro a ⟨i, hi, ha⟩
   have hm : ∀ s, (∃ b, (J i).mem (f y) b ∧ s = b ∘ f) →
       (∃ b, (finSumIdeal J r).mem (f y) b ∧ s = b ∘ f) := by
     rintro _ ⟨b, hb, rfl⟩
     refine ⟨b, ?_, rfl⟩
     change IsInSpanAt (n := n) (fun c => ∃ j, j < r ∧ (J j).mem (f y) c) (f y) b
     exact isInSpanAt_self ⟨i, hi, hb⟩ (GermIdeal.IsCoherent.holomorphicAt_mem (hJ i hi) hb)
   exact IsInSpanAt.mono hm (GermIdeal.mem_pullback_iff.mp ha)

/-- Literal cross-dimensional pullback of the original marked data. -/
def markedPullback (f : Y → X) (M : MarkedIdeal n X) : MarkedIdeal m Y where
 N := f ⁻¹' M.N
 E := M.E.map (fun H => f ⁻¹' H)
 ideal := GermIdeal.pullback (m := m) f M.ideal
 d := M.d

theorem coeffMarked_pullback_eq
 (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
 coeffMarked (markedPullback (m := m) f M) = markedPullback (m := m) f (coeffMarked M) := by
 have hd (i : ℕ) := iterDerivIdeal_pullback_eq
   (fun y => hf.isSubmersionAt y) (fun y => hh.contMDiffAt.mdifferentiableAt (by simp))
   (fun x g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) i
 have he : (coeffMarked (markedPullback (m := m) f M)).ideal =
     GermIdeal.pullback (m := m) f (coeffMarked M).ideal := by
   change finSumIdeal
     (fun i => idealPow (iterDerivIdeal (GermIdeal.pullback (m := m) f M.ideal) i)
       (sumExp (fun j => M.d-j) M.d i)) M.d =
     GermIdeal.pullback (m := m) f
       (finSumIdeal (fun i => idealPow (iterDerivIdeal M.ideal i) (sumExp (fun j => M.d-j) M.d i)) M.d)
   rw [pullback_finSumIdeal hh _ _ (fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdeal hI i) _)]
   apply finSumIdeal_congr
   intro i _
   rw [hd i, pullback_idealPow hh (isCoherent_iterDerivIdeal hI i)]
 cases M
 simp only [coeffMarked, msum, markedPullback, derivMarked]
 congr 1

theorem coefficient_cosupport_pullback_eq
 (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (hh : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 (M : MarkedIdeal n X) (hN : M.N = univ) (hI : M.ideal.IsCoherent) :
 (coeffMarked (markedPullback (m := m) f M)).cosupp = f ⁻¹' (coeffMarked M).cosupp := by
 rw [coeffMarked_pullback_eq hf hh M hI]
 have hcoh : (coeffMarked M).ideal.IsCoherent :=
   (isAmbientFamily_derivMarked hN hI).isCoherent_msum
 have hNc : (coeffMarked M).N = univ := by
   change M.N = univ
   exact hN
 simpa only [MarkedIdeal.cosupp, markedPullback, hNc, preimage_univ] using
   HironakaSmoothSubmersionOrder.cosupport_pullback_eq hf hcoh (coeffMarked M).d
end
end Hironaka.HironakaSmoothSubmersionCoefficientIdeals
