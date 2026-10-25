/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3E)
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveEngine

/-!
# Sections with prescribed residues on a curve with two sections

Let `Y` be projective over a field and `𝓛` line-bundle data with two global sections `s₀`, `s₁`
of `𝓛^N` without common zero and with affine non-vanishing loci `U = D(s₀)`, `V = D(s₁)` (a
`TwoSectionCover`; lane OM3B produces one from a section of positive degree,
`CurvesField.Ample.exists_section_sup_eq_top`, `CurvesField.Ample.isAffineOpen_nonvanishingLocus`).
On this cover the transition function of `𝓛^N` is `g = s₀ / s₁`, regular on `V` with
`D(g) = U ∩ V`, and its inverse is regular on `U`. This file proves:

* `exists_section_of_pair`: global sections of `𝓛^{N k}` from pairs `(a, b)` of local
  coefficients with `b = g^k a` on `U ∩ V` (for any two local generators);
* `exists_cobdy_idealSheaf`: the engine of `AmplePositiveEngine` for quasi-coherent ideal sheaves
  (`Scheme.IdealSheafData`) on any two-chart cover with `U ∩ V = D(h)` in `U`;
* `TwoSectionCover.serre_vanishing`: `H¹(𝒪 ⊗ 𝓛^{Nk}) = 0` for `k ≫ 0` on the two-term complex
  (lane COH4's Serre vanishing);
* `TwoSectionCover.exists_section_vanishing`: for disjoint finite sets `T₀`, `T₁` of closed points
  and all `k ≫ 0`, a global section of `𝓛^{Nk}` vanishing on `T₀` and not vanishing on `T₁`
  (Hartshorne II.7.3 / III.5.3 in the curve case: an ample line bundle separates points).

Blueprint `sm-curves-fields-ample-positive.tex`, `lem:sm-ample-positive-prescribe`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Positive

noncomputable section

open Ample Ample.LineBundleData Projectivity.LineBundleData

variable {Y : Scheme.{u}}

/-- Restriction `Γ(U) → Γ(U ∩ V)`. -/
abbrev resL (U V : Y.Opens) : Γ(Y, U) →+* Γ(Y, U ⊓ V) :=
  (Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom

/-- Restriction `Γ(V) → Γ(U ∩ V)`. -/
abbrev resR (U V : Y.Opens) : Γ(Y, V) →+* Γ(Y, U ⊓ V) :=
  (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom

/-! ### Global sections from pairs of local coefficients -/

section Pairs

variable {M : Projectivity.LineBundleData Y} {N : ℤ} {U V : Y.Opens} {τ : M.Sections N U}
  {σ : M.Sections N V}

/-- **Gluing a global section from local coefficients**: if `τ`, `σ` generate `𝓛^N` on `U`, `V`
and `b = g^k a` on `U ∩ V` (`g = τ / σ`), the sections `a τ^k` and `b σ^k` glue to a global
section of `𝓛^{N k}`. -/
theorem exists_section_of_pair (hσ : σ.nonvanishingLocus = V) (hUV : U ⊔ V = ⊤) (k : ℕ)
    (a : Γ(Y, U)) (b : Γ(Y, V))
    (hab : resR U V b = transFun τ hσ ^ k * resL U V a) :
    ∃ t : M.Sections (N * k) ⊤, t.restrict (le_top : U ≤ ⊤) = a • τ.npow k ∧
      t.restrict (le_top : V ≤ ⊤) = b • σ.npow k := by
  have hxy : (a • τ.npow k).restrict (inf_le_left : U ⊓ V ≤ U) =
      (b • σ.npow k).restrict (inf_le_right : U ⊓ V ≤ V) := by
    rw [Sections.restrict_smul, Sections.restrict_smul]
    have e := npow_restrict_eq' (τ := τ) hσ k (le_rfl : U ⊓ V ≤ U ⊓ V)
    have e₁ : (τ.npow k).restrict (inf_le_left : U ⊓ V ≤ U) =
        Y.presheaf.map (homOfLE (le_rfl : U ⊓ V ≤ U ⊓ V)).op (transFun τ hσ ^ k) •
          (σ.npow k).restrict (inf_le_right : U ⊓ V ≤ V) := e
    have hid : (Y.presheaf.map (homOfLE (le_rfl : U ⊓ V ≤ U ⊓ V)).op) (transFun τ hσ ^ k) =
        transFun τ hσ ^ k := presheaf_map_self (unitModule Y) _ _
    rw [e₁, smul_smul, hid]
    congr 1
    rw [mul_comm]
    exact hab.symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_glue₂ (twistSheafAb (M.twist (unitModule Y) (N * k)))
    (le_top : U ≤ ⊤) (le_top : V ≤ ⊤) (by rw [hUV]) (a • τ.npow k) (b • σ.npow k) hxy
  exact ⟨t, ht₁, ht₂⟩

end Pairs

/-! ### The engine for quasi-coherent ideal sheaves -/

section IdealSheaf

variable {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))

/-- **The engine for ideal sheaves** (blueprint `lem:sm-ample-positive-engine`): on a two-chart
cover with `U ∩ V = D(h)` in the affine `U`, transition function `g` with `h g ≡ 1` modulo the
ideal sheaf `𝒩`, and ideal sheaves `𝓘 ⊇ 𝓙 ⊇ 𝒩 𝓘`, if `H¹_k(𝒪/𝒩) = 0` for `k ≫ 0` then every
section of `𝓘` over `U ∩ V` is a coboundary of `𝓘 ⊗ 𝓛^k` modulo `𝓙` for `k ≫ 0`. -/
theorem exists_cobdy_idealSheaf (g : Γ(Y, U ⊓ V)ˣ) {h : Γ(Y, U)} (hh : Y.basicOpen h = U ⊓ V)
    (Nn I J : Y.IdealSheafData) (hgh : resL U V h * (g : Γ(Y, U ⊓ V)) - 1 ∈ Nn.ideal ⟨_, hUV⟩)
    (hNIJ : Nn * I ≤ J) [IsNoetherianRing Γ(Y, V)]
    (hO : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : Γ(Y, U ⊓ V), ∃ a : Γ(Y, U), ∃ b : Γ(Y, V),
      x - (resR U V b + (g : Γ(Y, U ⊓ V)) ^ k * resL U V a) ∈ Nn.ideal ⟨_, hUV⟩) :
    ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → ∀ w ∈ I.ideal ⟨_, hUV⟩,
      IsCobdy (resL U V) (resR U V) g (I.ideal ⟨U, hU⟩) (I.ideal ⟨V, hV⟩) (J.ideal ⟨_, hUV⟩) k w := by
  have hmapU : (I.ideal ⟨U, hU⟩).map (resL U V) = I.ideal ⟨_, hUV⟩ :=
    I.map_ideal (U := ⟨_, hUV⟩) (V := ⟨U, hU⟩) (inf_le_left : U ⊓ V ≤ U)
  have hmapV : (I.ideal ⟨V, hV⟩).map (resR U V) = I.ideal ⟨_, hUV⟩ :=
    I.map_ideal (U := ⟨_, hUV⟩) (V := ⟨V, hV⟩) (inf_le_right : U ⊓ V ≤ V)
  have hJ : Nn.ideal ⟨_, hUV⟩ * I.ideal ⟨_, hUV⟩ ≤ J.ideal ⟨_, hUV⟩ := by
    have := hNIJ ⟨_, hUV⟩
    rwa [AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul] at this
  apply exists_forall_mem_of_engine hgh
  · intro a ha
    rw [← hmapU]
    exact Ideal.mem_map_of_mem _ ha
  · intro b hb
    rw [← hmapV]
    exact Ideal.mem_map_of_mem _ hb
  · exact hJ
  · rw [hmapV]
  · intro b hb
    let := (resL U V).toAlgebra
    have hloc : IsLocalization.Away h Γ(Y, U ⊓ V) :=
      hU.isLocalization_of_eq_basicOpen h (homOfLE inf_le_left) hh.symm
    have hb' : resR U V b ∈ (I.ideal ⟨U, hU⟩).map (algebraMap Γ(Y, U) Γ(Y, U ⊓ V)) := by
      rw [show algebraMap Γ(Y, U) Γ(Y, U ⊓ V) = resL U V from rfl, hmapU, ← hmapV]
      exact Ideal.mem_map_of_mem _ hb
    obtain ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, hx⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h) Γ(Y, U ⊓ V)).mp hb'
    change resR U V b * resL U V (h ^ n) = resL U V a at hx
    refine ⟨n, a, ha, ?_⟩
    have hpow : (resL U V h * (g : Γ(Y, U ⊓ V))) ^ n - 1 ∈ Nn.ideal ⟨_, hUV⟩ := by
      have hd := sub_dvd_pow_sub_pow (resL U V h * (g : Γ(Y, U ⊓ V))) 1 n
      rw [one_pow] at hd
      exact Ideal.mem_of_dvd _ hd hgh
    have hbI : resR U V b ∈ I.ideal ⟨_, hUV⟩ := by
      rw [← hmapV]; exact Ideal.mem_map_of_mem _ hb
    have e : resR U V b - (g : Γ(Y, U ⊓ V)) ^ n * resL U V a =
        -(((resL U V h * (g : Γ(Y, U ⊓ V))) ^ n - 1) * resR U V b) := by
      rw [← hx, map_pow]; ring
    rw [e]
    exact J.ideal _ |>.neg_mem (hJ (Ideal.mul_mem_mul hpow hbI))
  · exact IsNoetherian.noetherian _
  · exact hO

end IdealSheaf

/-! ### Coefficients of sections in two local generators -/

section Coeff

variable {M : Projectivity.LineBundleData Y} {N : ℤ} {U V : Y.Opens} {τ : M.Sections N U}
  {σ : M.Sections N V} (hτ : τ.nonvanishingLocus = U) (hσ : σ.nonvanishingLocus = V) (k : ℕ)

/-- The coefficient `w / τ^k` of a global section `w` of `𝓛^{N k}` on the chart `U`. -/
def coefU (w : M.Sections (N * k) ⊤) : Γ(Y, U) :=
  (mulSecEquiv (unitModule Y) (Sections.nonvanishingLocus_npow_of_eq τ hτ k)).symm
    (w.restrict (le_top : U ≤ ⊤))

lemma restrict_eq_coefU_smul (w : M.Sections (N * k) ⊤) :
    w.restrict (le_top : U ≤ ⊤) = coefU hτ k w • τ.npow k := by
  rw [← mulSec_unit]
  exact (mulSec_mulSecEquiv_symm (unitModule Y) _ _).symm

/-- On the chart `U`, the non-vanishing locus of `w` is that of its coefficient. -/
lemma nonvanishingLocus_inf_eq_basicOpen_coefU (w : M.Sections (N * k) ⊤) :
    w.nonvanishingLocus ⊓ U = Y.basicOpen (coefU hτ k w) := by
  have h := congrArg Sections.nonvanishingLocus (restrict_eq_coefU_smul hτ k w)
  rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_smul,
    Sections.nonvanishingLocus_npow_of_eq τ hτ k] at h
  rw [inf_comm, h]
  exact inf_eq_left.mpr (Y.basicOpen_le _)

/-- On `U ∩ V`, the coefficients of a global section are related by the transition function:
`w / σ^k = g^k · (w / τ^k)`. -/
lemma resR_coefU_coefU (w : M.Sections (N * k) ⊤) :
    resR U V (coefU hσ k w) = transFun τ hσ ^ k * resL U V (coefU hτ k w) := by
  have hD : ((σ.npow k).restrict (inf_le_right : U ⊓ V ≤ V)).nonvanishingLocus = U ⊓ V := by
    rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_npow_of_eq σ hσ k]
    exact inf_eq_left.mpr inf_le_right
  apply (mulSec_bijective (unitModule Y) hD).1
  rw [mulSec_unit, mulSec_unit]
  have e₁ := congrArg (Sections.restrict (inf_le_right : U ⊓ V ≤ V))
    (restrict_eq_coefU_smul hσ k w)
  have e₂ := congrArg (Sections.restrict (inf_le_left : U ⊓ V ≤ U))
    (restrict_eq_coefU_smul hτ k w)
  rw [Sections.restrict_restrict, Sections.restrict_smul] at e₁ e₂
  rw [← e₁, e₂, npow_restrict_eq' hσ k (le_rfl : U ⊓ V ≤ U ⊓ V), smul_smul]
  congr 1
  rw [show (Y.presheaf.map (homOfLE (le_rfl : U ⊓ V ≤ U ⊓ V)).op) (transFun τ hσ ^ k) =
    transFun τ hσ ^ k from presheaf_map_self (unitModule Y) _ _]
  ring

end Coeff

end

end DeJongAlterations.StableModification.CurvesField.Positive
