import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! A flat quotient of an actual relatively infinitesimal remainder submodule
has zero kernel. The separating ambient Noetherian local ring is ordinary
source data; no finiteness over the base or adic-separation certificate is used.
Blueprint first: hironaka-g10-relative-flat-kernel.tex. -/
set_option autoImplicit false

namespace Hironaka.HironakaChowRelativeFlatKernel

open IsLocalRing

variable {R S M : Type*} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [AddCommGroup M] [Module R M]

/-- An ordinary local ambient embedding supplies the separation required by
the actual flat quotient, even when the remainder module is not finite over R. -/
theorem eq_bot_of_flat_quotient (K : Submodule R M)
    (e : M →ₗ[R] S) (he : Function.Injective e)
    (hK : K ≤ maximalIdeal R • (⊤ : Submodule R M))
    [Module.Flat R (M ⧸ K)] : K = ⊥ := by
  let m := maximalIdeal R
  have hSelf : K = m • K := by
    have hK' : K ≤ m • (⊤ : Submodule R M) := hK
    have hPure :=
      LinearMap.ker_inf_smul_top_eq_smul_of_flat m K.mkQ K.mkQ_surjective
    rw [Submodule.ker_mkQ, inf_eq_left.mpr hK'] at hPure
    exact hPure
  have hPower : ∀ j : ℕ, K ≤ m ^ j • (⊤ : Submodule R M) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        K = m • K := hSelf
        _ ≤ m • (m ^ j • (⊤ : Submodule R M)) := smul_mono_right m ih
        _ = m ^ (j + 1) • (⊤ : Submodule R M) := by
          rw [pow_succ', Submodule.mul_smul]
  have hProper : m.map (algebraMap R S) ≠ ⊤ :=
    ne_of_lt (map_maximalIdeal_lt_top (algebraMap R S))
  apply le_antisymm _ bot_le
  intro x hx
  have hAll : ∀ j : ℕ, e x ∈ (m.map (algebraMap R S)) ^ j := by
    intro j
    have hMap : e x ∈ (m ^ j • (⊤ : Submodule R M)).map e :=
      Submodule.mem_map_of_mem (hPower j hx)
    rw [Submodule.map_smul''] at hMap
    have hLE : m ^ j • (⊤ : Submodule R M).map e ≤
        m ^ j • (⊤ : Submodule R S) := smul_mono_right (m ^ j) le_top
    have hTop : e x ∈ m ^ j • (⊤ : Submodule R S) := hLE hMap
    rw [Ideal.smul_top_eq_map] at hTop
    change e x ∈ (m ^ j).map (algebraMap R S) at hTop
    simpa only [Ideal.map_pow] using hTop
  have hInf : e x ∈ ⨅ j : ℕ, (m.map (algebraMap R S)) ^ j :=
    Ideal.mem_iInf.mpr hAll
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hProper] at hInf
  change x = 0
  apply he
  simpa only [map_zero, Submodule.mem_bot] using hInf

/-- For a flat actual remainder module the zero-kernel condition is equivalent
to flatness of the literal quotient, under the same ordinary local hypotheses. -/
theorem flat_quotient_iff_eq_bot (K : Submodule R M)
    (e : M →ₗ[R] S) (he : Function.Injective e)
    (hK : K ≤ maximalIdeal R • (⊤ : Submodule R M))
    [Module.Flat R M] : Module.Flat R (M ⧸ K) ↔ K = ⊥ := by
  constructor
  · intro hFlat
    let := hFlat
    exact eq_bot_of_flat_quotient K e he hK
  · intro hZero
    exact Module.Flat.of_linearEquiv (K.quotEquivOfEqBot hZero)

end Hironaka.HironakaChowRelativeFlatKernel
