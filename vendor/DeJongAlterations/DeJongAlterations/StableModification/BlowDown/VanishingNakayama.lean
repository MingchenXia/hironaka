/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.RiemannRochAlgebra
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Vanishing of `H¹` from the closed fibre by Nakayama (Temkin, Prop. 4.4.6, T:3214–3219)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6: "`H¹(𝒪_{Y_s}(m ∑ pᵢ)) = 0` […] hence `h_s` lifts to a section `h` of
`𝒪_Y(m ∑ P̄ᵢ)`" (by cohomology and base change, Temkin reducing to the Noetherian case). For a
two-chart cover the first cohomology is the cokernel of the twisted difference map
(`CurvesField.H1`), cokernels commute with `⊗_V κ`, and so the vanishing on the closed fibre
gives `H¹ = 𝔪 H¹` over `V`, hence `H¹ = 0` by Nakayama's lemma as soon as `H¹` is finitely
generated. This needs neither flatness nor noetherian approximation: only that the charts of the
closed fibre are the base changes of the charts of `Y` (`Γ(W_s) = Γ(W) ⧸ 𝔪Γ(W)` for affine `W`).

* `subsingleton_H1_of_subsingleton`: the Nakayama transfer for the two-chart complexes
  `(a, b) ↦ γ(a|) - b|` of `CurvesField.RiemannRochAlgebra` along compatible maps `π` that are
  onto on the charts and whose kernel on the overlap lies in `𝔪 · Γ(W)`.
* `finite_H1_of_surjective`: finite generation of `H¹` passes to the closed fibre.
* `surjective_and_ker_of_isPushout`: for a pushout square of commutative rings
  `R → R'`, `R → S`, `R' → S'`, `S → S'` with `R → R'` surjective, `S → S'` is surjective with
  kernel `ker(R → R') · S`.

Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-nakayama`.
-/

namespace DeJongAlterations.StableModification.BlowDown.VanishingNakayama

open CategoryTheory DeJongAlterations.StableModification.CurvesField

set_option autoImplicit false

section Transfer

variable {R : Type*} [CommRing R]
  {MU MV MW MU' MV' MW' : Type*} [AddCommGroup MU] [Module R MU] [AddCommGroup MV] [Module R MV]
  [AddCommGroup MW] [Module R MW] [AddCommGroup MU'] [Module R MU'] [AddCommGroup MV']
  [Module R MV'] [AddCommGroup MW'] [Module R MW']
  (ρU : MU →ₗ[R] MW) (ρV : MV →ₗ[R] MW) (γ : MW →ₗ[R] MW)
  (ρU' : MU' →ₗ[R] MW') (ρV' : MV' →ₗ[R] MW') (γ' : MW' →ₗ[R] MW')
  (πU : MU →ₗ[R] MU') (πV : MV →ₗ[R] MV') (πW : MW →ₗ[R] MW')
  (hU : πW ∘ₗ ρU = ρU' ∘ₗ πU) (hV : πW ∘ₗ ρV = ρV' ∘ₗ πV) (hγ : πW ∘ₗ γ = γ' ∘ₗ πW)

include hU hV hγ in
/-- The maps `π` intertwine the twisted difference maps. -/
lemma twistDiff_comp (p : MU × MV) :
    πW (twistDiff ρU ρV γ p) = twistDiff ρU' ρV' γ' (πU p.1, πV p.2) := by
  rw [twistDiff_apply, twistDiff_apply, map_sub]
  have h1 := LinearMap.congr_fun hγ (ρU p.1)
  have h2 := LinearMap.congr_fun hU p.1
  have h3 := LinearMap.congr_fun hV p.2
  simp only [LinearMap.comp_apply] at h1 h2 h3
  rw [h1, h2, h3]

include hU hV hγ in
/-- **Finite generation of `H¹` passes to the closed fibre** when `πW` is onto. -/
theorem finite_H1_of_surjective (hπW : Function.Surjective πW)
    [Module.Finite R (H1 ρU ρV γ)] : Module.Finite R (H1 ρU' ρV' γ') := by
  have hle : LinearMap.range (twistDiff ρU ρV γ) ≤
      (LinearMap.range (twistDiff ρU' ρV' γ')).comap πW := by
    rintro _ ⟨p, rfl⟩
    rw [Submodule.mem_comap, twistDiff_comp ρU ρV γ ρU' ρV' γ' πU πV πW hU hV hγ]
    exact ⟨_, rfl⟩
  let F := Submodule.mapQ _ _ πW hle
  have hF : Function.Surjective F := by
    intro x
    obtain ⟨w', rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := hπW w'
    exact ⟨Submodule.Quotient.mk w, rfl⟩
  exact Module.Finite.of_surjective F hF

variable [IsLocalRing R]

include hU hV hγ in
/-- **Nakayama transfer of the vanishing of `H¹`**: if the maps `π` are onto on the charts, the
kernel of `πW` lies in `𝔪 · MW`, `H¹` is finitely generated and `H¹` of the target complex
vanishes, then `H¹` vanishes. -/
theorem subsingleton_H1_of_subsingleton (hπU : Function.Surjective πU)
    (hπV : Function.Surjective πV)
    (hker : ∀ w, πW w = 0 → w ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R MW))
    [Module.Finite R (H1 ρU ρV γ)] [Subsingleton (H1 ρU' ρV' γ')] :
    Subsingleton (H1 ρU ρV γ) := by
  set Q := LinearMap.range (twistDiff ρU ρV γ) with hQ
  set 𝔪 := IsLocalRing.maximalIdeal R
  have htop' : LinearMap.range (twistDiff ρU' ρV' γ') = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp inferInstance
  -- every element of `MW` lies in `Q + 𝔪 MW`
  have hmem : ∀ w : MW, ∃ q ∈ Q, w - q ∈ 𝔪 • (⊤ : Submodule R MW) := by
    intro w
    have hw : πW w ∈ LinearMap.range (twistDiff ρU' ρV' γ') := by rw [htop']; trivial
    obtain ⟨⟨a', b'⟩, hab⟩ := hw
    obtain ⟨a, rfl⟩ := hπU a'
    obtain ⟨b, rfl⟩ := hπV b'
    refine ⟨twistDiff ρU ρV γ (a, b), ⟨_, rfl⟩, hker _ ?_⟩
    rw [map_sub, twistDiff_comp ρU ρV γ ρU' ρV' γ' πU πV πW hU hV hγ, hab, sub_self]
  -- so `H¹ = 𝔪 H¹`
  have hle : (⊤ : Submodule R (MW ⧸ Q)) ≤ 𝔪 • (⊤ : Submodule R (MW ⧸ Q)) := by
    intro x _
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective Q x
    obtain ⟨q, hq, hwq⟩ := hmem w
    have hx : Submodule.Quotient.mk w = Q.mkQ (w - q) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub,
        (Submodule.Quotient.mk_eq_zero Q).mpr hq, sub_zero]
    rw [hx]
    have : Q.mkQ (w - q) ∈ (𝔪 • (⊤ : Submodule R MW)).map Q.mkQ := ⟨_, hwq, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    exact this
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔪 ⊤ (Module.Finite.fg_top) hle
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact (Submodule.subsingleton_iff R).mp (subsingleton_of_bot_eq_top hbot.symm)

end Transfer

section Pushout

open CommRingCat

/-- **Base change along a surjection of rings**: for a pushout square of commutative rings
`R → R'`, `R → S`, `R' → S'`, `S → S'` with `R → R'` surjective, `S → S'` is surjective with
kernel the extension of `ker(R → R')`. -/
theorem surjective_and_ker_of_isPushout {R R' S S' : CommRingCat} {f : R ⟶ R'} {g : R ⟶ S}
    {h : R' ⟶ S'} {k : S ⟶ S'} (H : IsPushout f g h k) (hf : Function.Surjective f) :
    Function.Surjective k ∧ RingHom.ker k.hom = Ideal.map g.hom (RingHom.ker f.hom) := by
  set I := Ideal.map g.hom (RingHom.ker f.hom) with hI
  have hIk : I ≤ RingHom.ker k.hom := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change (g ≫ k) x = 0
    rw [← H.w]
    change h (f x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]
  let q : S ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let e : CommRingCat.of (S ⧸ I) ⟶ S' := CommRingCat.ofHom (Ideal.Quotient.lift I k.hom hIk)
  have hqe : q ≫ e = k := by
    ext x
    rfl
  have hker : RingHom.ker f.hom ≤ RingHom.ker (q.hom.comp g.hom) := fun x hx => by
    rw [RingHom.mem_ker, RingHom.comp_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem _ hx)
  let h' : R' ⟶ CommRingCat.of (S ⧸ I) :=
    CommRingCat.ofHom (f.hom.liftOfSurjective hf ⟨q.hom.comp g.hom, hker⟩)
  have hfh' : f ≫ h' = g ≫ q := by
    ext x
    exact f.hom.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hf)
      ⟨q.hom.comp g.hom, hker⟩ x
  let d : S' ⟶ CommRingCat.of (S ⧸ I) := H.desc h' q hfh'
  have hkd : k ≫ d = q := H.inr_desc h' q hfh'
  have hhd : h ≫ d = h' := H.inl_desc h' q hfh'
  -- `d ≫ e = 𝟙`
  have hde : d ≫ e = 𝟙 S' := by
    apply H.hom_ext
    · rw [← Category.assoc, hhd, Category.comp_id]
      ext y
      obtain ⟨x, rfl⟩ := hf y
      change e (h' (f x)) = h (f x)
      have e1 : h' (f x) = q (g x) := congrArg (fun φ => φ x) (congrArg CommRingCat.Hom.hom hfh')
      rw [e1]
      change (q ≫ e) (g x) = h (f x)
      rw [hqe]
      change (g ≫ k) x = (f ≫ h) x
      rw [H.w]
    · rw [← Category.assoc, hkd, hqe, Category.comp_id]
  refine ⟨fun y => ?_, le_antisymm (fun x hx => ?_) hIk⟩
  · obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I := I) (d y)
    refine ⟨s, ?_⟩
    have : e (d y) = y := by
      change (d ≫ e) y = y
      rw [hde]
      rfl
    rw [← this, ← hs]
    rfl
  · have : q x = 0 := by
      rw [← hkd]
      change d (k x) = 0
      rw [RingHom.mem_ker.mp hx, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp this

end Pushout

end DeJongAlterations.StableModification.BlowDown.VanishingNakayama
