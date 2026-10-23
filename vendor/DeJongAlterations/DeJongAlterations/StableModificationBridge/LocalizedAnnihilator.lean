/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The original finite module annihilator commutes with actual localization

This identity supplies quasi-coherence for the intrinsic conductor of the original finite
normalization algebra. All maps are the original scalar map and localized module map.

Blueprint: `localized-annihilator.tex`.
-/

universe u v w

namespace DeJongAlterations.StableModificationBridge.LocalizedAnnihilator

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (A : Type v) [CommRing A] [Algebra R A] [IsLocalization S A]
  {M : Type w} [AddCommGroup M] [Module R M]
  {M' : Type w} [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f]

include S f

omit [IsLocalization S A] in
theorem map_annihilator_le :
    (Module.annihilator R M).map (algebraMap R A) ≤ Module.annihilator A M' := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro x
  rw [IsScalarTower.algebraMap_smul A]
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S f x
  apply (IsLocalizedModule.smul_inj f s _ _).mp
  rw [smul_zero, smul_comm, hs, ← f.map_smul, (Module.mem_annihilator.mp hr m), map_zero]

theorem comap_annihilator_le_comap_map [Module.Finite R M] :
    (Module.annihilator A M').comap (algebraMap R A) ≤
      ((Module.annihilator R M).map (algebraMap R A)).comap (algebraMap R A) := by
  classical
  intro r hr
  have hr' : ∀ m : M, f (r • m) = f 0 := by
    intro m
    rw [f.map_smul, map_zero]
    exact (IsScalarTower.algebraMap_smul A r (f m)) ▸ (Module.mem_annihilator.mp hr (f m))
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := R) (M := M)
  have hden : ∀ m : F, ∃ s : S, (s : R) • (r • (m : M)) = 0 := by
    intro m
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S f).mp (hr' m)
    exact ⟨s, by simpa only [smul_zero, Submonoid.smul_def] using hs⟩
  choose s hs using hden
  let d : S := F.attach.prod s
  have hdr : (d : R) * r ∈ Module.annihilator R M := by
    rw [← Submodule.annihilator_top, ← hF, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_attach _ m)
    have hd : (d : R) = (s m : R) * (c : R) := congrArg Subtype.val hc
    rw [mul_smul, hd, mul_smul, smul_comm, hs, smul_zero]
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff S A (Module.annihilator R M) r).mpr
    ⟨d, d.property, hdr⟩

theorem map_annihilator_eq [Module.Finite R M] :
    (Module.annihilator R M).map (algebraMap R A) = Module.annihilator A M' := by
  apply le_antisymm (map_annihilator_le S A f)
  calc
    Module.annihilator A M' =
        ((Module.annihilator A M').under R).map (algebraMap R A) :=
      (IsLocalization.map_under S A _).symm
    _ ≤ (((Module.annihilator R M).map (algebraMap R A)).under R).map (algebraMap R A) :=
      Ideal.map_mono (comap_annihilator_le_comap_map S A f)
    _ = (Module.annihilator R M).map (algebraMap R A) := IsLocalization.map_under S A _

end DeJongAlterations.StableModificationBridge.LocalizedAnnihilator
