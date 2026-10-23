import DeJongAlterations.Geometry.ProperSteinProjectiveCechSheafEqualizer
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Tactic

/-!
# Actual ORIGINAL quasicoherent affine section denominator clearing

Native-only extraction from same-workspace `BingWangEntropy/ProjectiveSectionExtension.lean`,
SHA256 e50e0f49d0d38a9b072e1dab24ba6a16cd713184b4575bd97539e253831de2d8.
The native quasicoherent sheaf property produces the actual localizing-module property.
No extension, localized-exactness, or target cohomology output is assumed.
-/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace DeJongAlterations.Geometry.ProperSteinProjectiveCech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {R : CommRingCat.{u}}

/-- Native affine sheaf restriction retains the actual structural scalar action. -/
def affineSectionRestriction (M : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) →ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
  ((modulesSpecToSheaf.obj M).obj.map
    (homOfLE (show (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ ⊤ from le_top)).op).hom

/-- Quasicoherence produces localization of the actual affine section restriction. -/
theorem affineSectionRestriction_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) : IsLocalizedModule.Away f (affineSectionRestriction M f) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- A genuine section on D(f) lifts to a true global section after multiplying by f^n. -/
theorem affineSection_clearDenominator (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) (s : Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)), affineSectionRestriction M f t = f ^ n • s := by
  let := affineSectionRestriction_isLocalized M f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj (affineSectionRestriction M f) f s
  exact ⟨n, t, ht.symm⟩

/-- Genuine global sections equal on D(f) become equal after an actual power of f. -/
theorem affineSection_eq_after_power (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) {s t : Γ(M, ⊤)}
    (h : affineSectionRestriction M f s = affineSectionRestriction M f t) :
    ∃ n : ℕ, f ^ n • s = f ^ n • t := by
  let := affineSectionRestriction_isLocalized M f
  exact IsLocalizedModule.Away.exists_of_eq f h

/-- A genuine global section vanishing on D(f) is killed by an actual power of f. -/
theorem affineSection_zero_after_power (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) {s : Γ(M, ⊤)} (h : affineSectionRestriction M f s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  obtain ⟨n, hn⟩ := affineSection_eq_after_power M f
    (t := 0) (h.trans (affineSectionRestriction M f).map_zero.symm)
  exact ⟨n, hn.trans (smul_zero _)⟩

/-- Finitely many actual D(f)-sections share one clearing exponent; the lifts
are explicit higher-power scalar multiples of their individual actual lifts. -/
theorem affineSections_clearDenominators {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : I → Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : I → Γ(M, ⊤)), ∀ i,
      affineSectionRestriction M f (t i) = f ^ n • s i := by
  classical
  choose n t ht using fun i => affineSection_clearDenominator M f (s i)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => f ^ (N - n i) • t i, ?_⟩
  intro i
  have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  rw [(affineSectionRestriction M f).map_smul, ht i, ← mul_smul, ← pow_add]
  congr 2
  omega

/-- Finitely many equalities on D(f) share one actual annihilating exponent. -/
theorem affineSections_eq_after_power {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s t : I → Γ(M, ⊤))
    (h : ∀ i, affineSectionRestriction M f (s i) = affineSectionRestriction M f (t i)) :
    ∃ n : ℕ, ∀ i, f ^ n • s i = f ^ n • t i := by
  classical
  choose n hn using fun i => affineSection_eq_after_power M f (h i)
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro i
  have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have he : N = (N - n i) + n i := by omega
  rw [he, pow_add, mul_smul, mul_smul, hn i]

/-- Finite overlap errors vanishing on D(f) have one actual common power
that kills all of them before sheaf gluing. -/
theorem affineSections_zero_after_power {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : I → Γ(M, ⊤)) (h : ∀ i, affineSectionRestriction M f (s i) = 0) :
    ∃ n : ℕ, ∀ i, f ^ n • s i = 0 := by
  obtain ⟨n, hn⟩ := affineSections_eq_after_power M f s (fun _ => 0)
    (fun i => (h i).trans (affineSectionRestriction M f).map_zero.symm)
  exact ⟨n, fun i => (hn i).trans (smul_zero _)⟩


end

end DeJongAlterations.Geometry.ProperSteinProjectiveCech
