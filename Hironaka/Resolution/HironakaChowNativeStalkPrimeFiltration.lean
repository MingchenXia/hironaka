import Hironaka.Resolution.HironakaChowNativePrimeSupportContinuation
import Hironaka.Resolution.HironakaChowNativeFiniteTypeSpreading
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! Actual prime quotients of the SAME original native module stalk.
Blueprint FIRST: `hironaka-g10-native-stalk-prime-filtration.tex`.
No nearby filtration, support reduction or continuation is asserted. -/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

namespace Hironaka.HironakaChowNativeStalkPrimeFiltration

open HironakaSingularModuleSheafStalk
  HironakaChowNativePrimeSupportContinuation
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaChowNativeFiniteTypeSpreading

noncomputable section

private theorem exists_prime_series (A M : Type) [CommRing A] [AddCommGroup M]
    [Module A M] [IsNoetherianRing A] [Module.Finite A M] :
    ∃ (s : RelSeries {(N₀, N₁) |
          Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₀ N₁})
      (P : Fin s.length → PrimeSpectrum A)
      (_e : ∀ i : Fin s.length,
        (↥(s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A] A ⧸ (P i).1),
      s.head = ⊥ ∧ s.last = ⊤ ∧
      (∀ i : Fin s.length, s i.castSucc ≤ s i.succ) ∧
      (Subsingleton M → s.length = 0) := by
  classical
  by_cases hM : Subsingleton M
  · let : Subsingleton M := hM
    let s : RelSeries {(N₀, N₁) |
        Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₀ N₁} :=
      RelSeries.singleton _ ⊥
    refine ⟨s, Fin.elim0, (fun i => Fin.elim0 i), rfl, ?_, ?_, ?_⟩
    · change (⊥ : Submodule A M) = ⊤
      ext m
      simp only [Submodule.mem_bot, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
    · exact fun i => Fin.elim0 i
    · intro _
      rfl
  · obtain ⟨s, hhead, hlast⟩ :=
      IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A M
    choose P hP using fun i : Fin s.length => (s.step i).2
    let e : ∀ i : Fin s.length,
        (↥(s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A] A ⧸ (P i).1 :=
      fun i => Classical.choice (hP i)
    refine ⟨s, P, e, hhead, hlast, (fun i => (s.step i).1), ?_⟩
    exact fun h => False.elim (hM h)

/-- Ordinary native finite presentation internally gives the SAME original
stalk ring/module, a full actual prime series and every indexed quotient
isomorphism. Only a genuinely zero stalk receives the length-zero choice. -/
theorem exists_original_stalk_prime_filtration
    (n : ℕ) (U : Opens (ComplexModel n))
    (F : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    [F.IsFinitePresentation] (p : U) :
    let A : Type := ↑(TopCat.Presheaf.stalk
      (originalOpenStructureSheaf U).presheaf p)
    let M : Type := ↑(TopCat.Presheaf.stalk F.val.presheaf p)
    let _ : Module A M := nativeSheafStalkModule (originalOpenStructureSheaf U) F p
    IsNoetherianRing A ∧ Module.Finite A M ∧
    ∃ (s : RelSeries {(N₀, N₁) |
          Submodule.IsQuotientEquivQuotientPrime (A := A) (M := M) N₀ N₁})
      (P : Fin s.length → PrimeSpectrum A)
      (_e : ∀ i : Fin s.length,
        (↥(s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[A] A ⧸ (P i).1),
      s.head = ⊥ ∧ s.last = ⊤ ∧
      (∀ i : Fin s.length, s i.castSucc ≤ s i.succ) ∧
      (Subsingleton M → s.length = 0) := by
  classical
  dsimp only
  let A : Type := ↑(TopCat.Presheaf.stalk (originalOpenStructureSheaf U).presheaf p)
  let M : Type := ↑(TopCat.Presheaf.stalk F.val.presheaf p)
  let : Module A M := nativeSheafStalkModule (originalOpenStructureSheaf U) F p
  let eA : HolGerm (ComplexModel n) ≃+* A :=
    (actualStalkChartEquiv (n := n) p.val).symm.trans (originalRestrictionStalkEquiv U p)
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ eA
  let : Module.Finite A M := moduleFinite_stalk_of_isFiniteType
    (M := F) (originalOpenStructureSheaf U) p
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact exists_prime_series A M

end

end Hironaka.HironakaChowNativeStalkPrimeFiltration
