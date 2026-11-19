import Hironaka.Analytic.HolomorphicCoordinatePrime

set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.HironakaG8PlaneLineGerms
noncomputable section
open HolomorphicGermReducednessBridge

def lineLinear (s : ℂ) : ComplexModel 2 →L[ℂ] ℂ :=
  s • EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2) + EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)

def lineGerm (s : ℂ) : HolGerm (ComplexModel 2) :=
  HolGerm.mk (lineLinear s) (Eventually.of_forall fun _ => (lineLinear s).differentiableAt)

private theorem lineLinear_apply (s : ℂ) (z : ComplexModel 2) :
    lineLinear s z = s * z 0 + z 1 := rfl

theorem prime_lineGerm (s : ℂ) : Prime (lineGerm s) := by
  let := ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean 2
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  constructor
  · intro hu
    have hv := (HolGerm.isUnit_iff_eval_ne_zero _).mp hu
    exact hv (by rw [lineGerm, HolGerm.eval_mk, map_zero])
  · intro a b hab
    by_contra hunit
    push Not at hunit
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
    obtain ⟨g,hg,rfl⟩ := HolGerm.exists_eq_mk b
    have hf0 : f 0 = 0 := by
      by_contra hn
      exact hunit.1 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk]))
    have hg0 : g 0 = 0 := by
      by_contra hn
      exact hunit.2 ((HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk]))
    have heq : (lineLinear s : ComplexModel 2 → ℂ) =ᶠ[𝓝 0] fun z => f z * g z :=
      HolGerm.mk_eq_mk_iff.mp (hab.trans (HolGerm.mk_mul f g hf hg).symm)
    have hd : fderiv ℂ (lineLinear s : ComplexModel 2 → ℂ) 0 =
        fderiv ℂ (f * g) 0 := heq.fderiv_eq
    rw [(lineLinear s).fderiv, (hf.self_of_nhds.hasFDerivAt.mul hg.self_of_nhds.hasFDerivAt).fderiv] at hd
    have hv := DFunLike.congr_fun hd (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
    simp [lineLinear_apply,hf0,hg0] at hv

theorem lineGerm_not_dvd {s t : ℂ} (hne : s ≠ t) : ¬ lineGerm t ∣ lineGerm s := by
  rintro ⟨a,ha⟩
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
  have heq : (lineLinear s : ComplexModel 2 → ℂ) =ᶠ[𝓝 0] fun z => lineLinear t z * f z :=
    HolGerm.mk_eq_mk_iff.mp (ha.trans (HolGerm.mk_mul _ _ _ _).symm)
  have hd : fderiv ℂ (lineLinear s : ComplexModel 2 → ℂ) 0 =
      fderiv ℂ ((lineLinear t : ComplexModel 2 → ℂ) * f) 0 := heq.fderiv_eq
  rw [(lineLinear s).fderiv, ((lineLinear t).hasFDerivAt.mul hf.self_of_nhds.hasFDerivAt).fderiv] at hd
  have hv := DFunLike.congr_fun hd
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ) + EuclideanSpace.single (1 : Fin 2) (-t))
  have hs : s - t = 0 := by
    simpa [lineLinear_apply, sub_eq_add_neg] using hv
  exact hne (sub_eq_zero.mp hs)

theorem lineGerm_not_associated {s t : ℂ} (hne : s ≠ t) :
    ¬ Associated (lineGerm s) (lineGerm t) :=
  fun h => lineGerm_not_dvd hne h.symm.dvd

end
end Hironaka.HironakaG8PlaneLineGerms
