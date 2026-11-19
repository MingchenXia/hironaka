import Mathlib.RingTheory.Smooth.Quotient

/-! # Flatness lifts relations modulo arbitrary ideals

The algebraic kernel-lifting step used by Frisch persistence. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift

/-- If the target and the cokernel of a presentation are flat over the
  parameter ring, every relation modulo an arbitrary parameter ideal lifts
  to an actual relation. No finiteness or Artinian hypothesis is needed. -/
theorem exists_relation_lift_mod_of_flat {A P N : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    (f : P →ₗ[A] N) [Module.Flat A N]
    [Module.Flat A (N ⧸ LinearMap.range f)] (I : Ideal A) (p : P)
    (hp : f p ∈ I • (⊤ : Submodule A N)) :
    ∃ k ∈ LinearMap.ker f, p - k ∈ I • (⊤ : Submodule A P) := by
  let K := LinearMap.range f
  have hflat := LinearMap.ker_inf_smul_top_eq_smul_of_flat I K.mkQ K.mkQ_surjective
  rw [Submodule.ker_mkQ] at hflat
  have hfp : f p ∈ I • K := by
    rw [← hflat]
    exact ⟨⟨p,rfl⟩,hp⟩
  have hmap : (I • (⊤ : Submodule A P)).map f = I • K := by
    rw [Submodule.map_smul'', Submodule.map_top]
  rw [← hmap, Submodule.mem_map] at hfp
  obtain ⟨z,hz,hzEq⟩ := hfp
  refine ⟨p - z,?_,?_⟩
  · change f (p - z) = 0
    rw [map_sub,hzEq,sub_self]
  · simpa using hz

/-- All columns of any family of relations modulo `I` can be lifted
  simultaneously to actual relations. -/
theorem exists_family_relation_lift_mod_of_flat {A P N : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    (f : P →ₗ[A] N) [Module.Flat A N]
    [Module.Flat A (N ⧸ LinearMap.range f)] (I : Ideal A) {ι : Type*} (p : ι → P)
    (hp : ∀ i, f (p i) ∈ I • (⊤ : Submodule A N)) :
    ∃ k : ι → P, (∀ i, f (k i) = 0) ∧
      ∀ i, p i - k i ∈ I • (⊤ : Submodule A P) := by
  choose k hk hkmod using fun i => exists_relation_lift_mod_of_flat f I (p i) (hp i)
  exact ⟨k,fun i => hk i, hkmod⟩

end Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift
