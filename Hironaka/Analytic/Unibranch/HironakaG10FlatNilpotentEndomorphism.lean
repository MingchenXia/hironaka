import Hironaka.Analytic.Unibranch.HironakaG10FlatArtinianProjection

/-! # Endomorphisms with image in a nilpotent parameter ideal -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism

/-- A parameter-linear endomorphism taking every vector into `I M` is
  nilpotent whenever the parameter ideal `I` is nilpotent. -/
theorem endomorphism_nilpotent_of_range {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (u : Module.End A M)
    (hnil : ∃ n : ℕ, I ^ n = ⊥) (hu : ∀ x, u x ∈ I • (⊤ : Submodule A M)) :
    IsNilpotent u := by
  have hrange : LinearMap.range u ≤ I • (⊤ : Submodule A M) := by
    rintro _ ⟨x,rfl⟩
    exact hu x
  have hstep (n : ℕ) : (I ^ n • (⊤ : Submodule A M)).map u ≤
      I ^ (n + 1) • (⊤ : Submodule A M) := by
    rw [Submodule.map_smul'',Submodule.map_top, pow_succ, mul_smul]
    exact smul_mono_right (I ^ n) hrange
  have hpow : ∀ n : ℕ, ∀ x : M, (u ^ n) x ∈ I ^ n • (⊤ : Submodule A M) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [show u ^ (n + 1) = u * u ^ n from pow_succ' u n]
      change u ((u ^ n) x) ∈ I ^ (n + 1) • (⊤ : Submodule A M)
      exact hstep n (Submodule.mem_map_of_mem (ih x))
  obtain ⟨n,hn⟩ := hnil
  refine ⟨n,?_⟩
  ext x
  have hx := hpow n x
  rw [hn] at hx
  simpa using hx

end Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism
