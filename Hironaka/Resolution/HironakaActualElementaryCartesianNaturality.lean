/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalFunctor

/-!
# Literal functor laws for actual elementary final Cartesian arrows

The existing genuine finite-projection uniqueness and whole-square pasting
cores require no CAN or terminal history. They therefore give literal laws for
arbitrary actual elementary final arrows without changing their stage recipe.
Blueprint: `hironaka-actual-elementary-cartesian-naturality-extension.tex`.
-/
set_option autoImplicit false
open Set Function
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualElementaryCartesianNaturality
noncomputable section
open BlowupTowers HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOriginalTerminalFunctor
variable {n m ℓ : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m} {Z F : CMfd.{u} ℓ}

/-- A genuine Cartesian self-arrow over the identity is the literal identity,
for any actual finite tower, without any marked-history premise. -/
theorem upperMap_identity (T : BlowupTower X D) (g : D → D)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hp : ∀ z,T.proj (g z)=T.proj z)
    (hU : HolomorphicSquarePullback (id : X → X) g T.proj T.proj) : g=id := by
  have hUid : HolomorphicSquarePullback (id : X → X) (id : D → D) T.proj T.proj := by
    intro k W u v _hu hv hcone
    refine ⟨v,⟨hv,fun z => (hcone z).symm,fun _ => rfl⟩,?_⟩
    intro w hw
    exact funext hw.2.2
  exact final_holomorphic_pullback_map_eq T T.proj g id hg contMDiff_id hp
    (fun _ => rfl) hU hUid

/-- Independently constructed actual elementary Cartesian arrows compose
literally; no canonical, terminal, or common-history premise is needed. -/
theorem upperMap_composition {f : Y → X} {h : Z → Y}
    (T : BlowupTower X D) (S : BlowupTower Y E) (Q : BlowupTower Z F)
    (g : E → D) (k : F → E) (c : F → D)
    (hh : ContMDiff 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) ∞ h)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hk : ContMDiff 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) ∞ k)
    (hc : ContMDiff 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel n) ∞ c)
    (hpg : ∀ z,T.proj (g z)=f (S.proj z))
    (hpk : ∀ z,S.proj (k z)=h (Q.proj z))
    (hpc : ∀ z,T.proj (c z)=(f ∘ h) (Q.proj z))
    (hUg : HolomorphicSquarePullback f g S.proj T.proj)
    (hUk : HolomorphicSquarePullback h k Q.proj S.proj)
    (hUc : HolomorphicSquarePullback (f ∘ h) c Q.proj T.proj) : c=g ∘ k := by
  have hUcomp := holomorphicSquarePullback_pasting S.proj Q.proj T.proj hh hk hpk hUg hUk
  exact final_holomorphic_pullback_map_eq Q T.proj c (g ∘ k) hc (hg.comp hk) hpc
    (fun z => (hpg (k z)).trans (congrArg f (hpk z))) hUc hUcomp

end
end Hironaka.HironakaActualElementaryCartesianNaturality
