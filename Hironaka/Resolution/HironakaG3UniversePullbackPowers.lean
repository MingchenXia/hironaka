import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniversePullbackPowers
open Hironaka.HolomorphicIdealSheaves IdealWeightPowers
  GermIdealPullbackCalculus InvertibleIdealQuotient RelativePrincipalizationSpan
noncomputable section
variable {n m : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X]
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

end
end Hironaka.HironakaG3UniversePullbackPowers
