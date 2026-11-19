import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Resolution.HironakaActualAnalyticBlowupTaylor

/-! Whole native ideal pullback in the SAME given adapted polynomial square.
Actual source finite generators derive both entire ideal inclusions. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualNativeAdaptedPullbackSquare
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothSubmersionGermIdealColon BlowupFlatCoordinates
  HironakaActualAnalyticBlowupTaylor HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem native_inverse_square
    (π : Y → X) (y : Y) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π y)).target)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y).target)
    (hSquare : ∀ z : Y, z ∈ (chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z)) =
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z)))
    (w : ComplexModel n) (hw : w ∈ Θ.target) :
    π ((chartAt (ComplexModel n) y).symm (Θ.invFun w)) =
      (chartAt (ComplexModel n) (π y)).symm
        (Φ.invFun (actualAnalyticBlowupMap A e b w)) := by
  let z := (chartAt (ComplexModel n) y).symm (Θ.invFun w)
  obtain ⟨hz, hΘz⟩ := flatInverse_mem Θ hw hΘsrc
  obtain ⟨hπz, hΦz⟩ := hSquare z hz.1 hz.2
  rw [hΘz] at hΦz
  have htar : actualAnalyticBlowupMap A e b w ∈ Φ.target := by
    rw [← hΦz]
    exact Φ.mapsTo_toFun hπz.2
  obtain ⟨hinv, hΦinv⟩ := flatInverse_mem Φ htar hΦsrc
  have hcoord := congrArg Φ.invFun (hΦz.trans hΦinv.symm)
  rw [Φ.left_inv _ hπz.2, Φ.left_inv _ hinv.2] at hcoord
  exact ((chartAt (ComplexModel n) (π y)).left_inv hπz.1).symm.trans
    ((congrArg (chartAt (ComplexModel n) (π y)).symm hcoord).trans
      ((chartAt (ComplexModel n) (π y)).left_inv hinv.1))

/-- Composition by the actual native map agrees on WHOLE germs with the
polynomial pullback in these SAME given source and target coordinates. -/
theorem adaptedGerm_native_pullback_square
    (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (y : Y) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y)) = 0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y) = 0)
    (hSquare : ∀ z : Y, z ∈ (chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z)) =
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z)))
    (F : X → ℂ) (hF : HolomorphicAt n F (π y)) :
    adaptedGerm y Θ hΘ0 (F ∘ π)
      (hF.comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt)) =
      actualAnalyticBlowupPullback A e b (adaptedGerm (π y) Φ hΦ0 F hF) := by
  change HolGerm.mk (fun w => F (π ((chartAt (ComplexModel n) y).symm
      (Θ.invFun w)))) _ = actualAnalyticBlowupPullback A e b
        (HolGerm.mk (fun v => F ((chartAt (ComplexModel n) (π y)).symm
          (Φ.invFun v))) _)
  rw [actualAnalyticBlowupPullback, compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  have htar : (0 : ComplexModel n) ∈ Θ.target := by
    simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds htar] with w hw
  exact congrArg F (native_inverse_square π y A e b Φ hΦsrc Θ hΘsrc hSquare w hw)

private theorem adaptedIdeal_eq_span_of_generation
    (J : GermIdeal n X) (hJ : J.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) {s : ℕ}
    (G : Fin s → X → ℂ) (hG : ∀ i, HolomorphicAt n (G i) x)
    (hgen : ∀ F, J.mem x F ↔ IsInSpanAt (n := n) (· ∈ range G) x F) :
    adaptedIdeal J x Φ h0 = Ideal.span (range fun i => adaptedGerm x Φ h0 (G i) (hG i)) := by
  ext g
  obtain ⟨F, hF, rfl⟩ := exists_original_adapted_representative x Φ h0 g
  rw [mem_adaptedIdeal_iff J hJ x Φ h0 F hF, hgen F]
  exact (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_adapted_iff x Φ h0 G F).trans
    (EuclideanHolomorphicGermSpan.isInSpanAt_iff_holGerm_mem_span _
      (fun i => (holomorphic_adapted_iff x Φ h0 (G i)).mpr (hG i))
      ((holomorphic_adapted_iff x Φ h0 F).mpr hF))

/-- ANY actual coherent source ideal has the exact entire adapted pullback
in a GIVEN actual native square; no target ideal identity is supplied. -/
theorem actual_native_adapted_pullback_square
    (I : GermIdeal n X) (hI : I.IsCoherent) (π : Y → X)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (y : Y) (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π y) (π y)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π y)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y)) = 0)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) y).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y) = 0)
    (hSquare : ∀ z : Y, z ∈ (chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z ∈ Θ.source → π z ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π y) (π z)) =
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) y z))) :
    adaptedIdeal (GermIdeal.pullback (m := n) π I) y Θ hΘ0 =
      Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
        (adaptedIdeal I (π y) Φ hΦ0) := by
  classical
  obtain ⟨U, hU, hy, s, G, hG, hgen⟩ := hI (π y)
  have hGh (i : Fin s) : HolomorphicAt n (G i) (π y) :=
    CoherentIdealColon.holomorphicAt_of_mdifferentiableOn hU (hG i) hy
  have hfat : ∀ᶠ z in 𝓝 y,
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π z :=
    Eventually.of_forall fun _ => hπ.contMDiffAt
  have hpb := FiniteGermIdealPullbackGenerators.mem_pullback_iff_of_finite_generation
    hfat I G hGh (hgen (π y) hy)
  rw [adaptedIdeal_eq_span_of_generation _
    (GermIdealPullbackCalculus.isCoherent_pullback hπ hI) y Θ hΘ0
    (fun i => G i ∘ π) (fun i => (hGh i).comp_contMDiff hfat) hpb,
    adaptedIdeal_eq_span_of_generation I hI (π y) Φ hΦ0 G hGh (hgen (π y) hy),
    Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg range
  funext i
  exact adaptedGerm_native_pullback_square π hπ y A e b Φ hΦsrc hΦ0 Θ hΘsrc hΘ0
    hSquare (G i) (hGh i)

end
end Hironaka.HironakaActualNativeAdaptedPullbackSquare
