import Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift

/-! # Infinitesimal persistence of projected relations

The algebraic non-reduced kernel-lifting step for a nilpotent parameter ideal. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatArtinianProjection
open Hironaka.Analytic.Unibranch.HironakaG10FlatRelationLift

/-- Nakayama for a nilpotent ideal, without a finite-generation hypothesis:
  if `K ≤ L + I K` and `I` is nilpotent, then `K ≤ L`. -/
theorem le_of_le_sup_smul_of_nilpotent {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (K L : Submodule A M)
    (hnil : ∃ n : ℕ, I ^ n = ⊥) (h : K ≤ L ⊔ I • K) : K ≤ L := by
  have hpow : ∀ n : ℕ, K ≤ L ⊔ (I ^ n) • K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        K ≤ L ⊔ I • K := h
        _ ≤ L ⊔ I • (L ⊔ (I ^ n) • K) := sup_le_sup_left (smul_mono_right I ih) L
        _ = L ⊔ (I • L ⊔ (I ^ (n + 1)) • K) := by
          rw [Submodule.smul_sup, ← mul_smul, pow_succ', mul_comm]
        _ ≤ L ⊔ (I ^ (n + 1)) • K := by
          apply sup_le
          · exact le_sup_left
          · exact sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right
  obtain ⟨n,hn⟩ := hnil
  have hN := hpow n
  rw [hn] at hN
  simpa using hN

/-- Flatness lifts the kernel of the special fibre sufficiently to cover
  the whole reference projection over any nilpotent parameter ideal. This
  is the algebraic non-reduced persistence step: no finite-generation or
  topological splitting assumption is made. -/
theorem projected_kernel_surjective_of_flat_nilpotent {A P N : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup N] [Module A N]
    (f : P →ₗ[A] N) [Module.Flat A N]
    [Module.Flat A (N ⧸ LinearMap.range f)] (π : P →ₗ[A] P)
    (hπ : ∀ x, π (π x) = π x) (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (hres : ∀ x, f (π x) ∈ I • (⊤ : Submodule A N)) :
    ∀ x, ∃ y, f y = 0 ∧ π y = π x := by
  let K := LinearMap.range π
  let L := (LinearMap.ker f).map π
  have hK : K ≤ L ⊔ I • K := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,hyI⟩ := exists_relation_lift_mod_of_flat f I (π x) (hres x)
    have hmap : (I • (⊤ : Submodule A P)).map π ≤ I • K := by
      rw [Submodule.map_smul'',Submodule.map_top]
    have hdiff : π (π x - y) ∈ I • K := hmap (Submodule.mem_map_of_mem hyI)
    have hyL : π y ∈ L := Submodule.mem_map_of_mem hy
    have hsum := Submodule.add_mem_sup hyL hdiff
    simpa only [map_sub,hπ,add_sub_cancel] using hsum
  have hKL := le_of_le_sup_smul_of_nilpotent I K L hnil hK
  intro x
  have hx : π x ∈ L := hKL ⟨x,rfl⟩
  obtain ⟨y,hy,heq⟩ := Submodule.mem_map.mp hx
  exact ⟨y,hy,heq⟩

end Hironaka.Analytic.Unibranch.HironakaG10FlatArtinianProjection
