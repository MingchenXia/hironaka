/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveTwoSection

/-!
# Finite-point prescription from an actual two-section affine cover

Two actual sections of the same power of a line bundle, with affine nonvanishing loci covering
the original scheme, produce sections of every sufficiently high multiple which vanish on one
finite set of closed points and do not vanish on a disjoint finite set. The proof clears
denominators in the original chart rings and glues actual sections on the same scheme.

The two-section hypothesis alone suffices; projectivity, an infinite coefficient field, and the
curve dimension bound need not be added. This supplies finite-point prescription used in the
component assembly argument. It does not assert componentwise-positive-degree assembly,
`PositiveSection`, or descent of sections from an algebraically closed coefficient field.

Blueprint: `finite-point-prescription.tex`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModificationBridge.FinitePointPrescription

noncomputable section

open CurvesField CurvesField.Ample CurvesField.Ample.LineBundleData
open Projectivity.LineBundleData

variable {X : Scheme.{u}} {L : LineBundleData X} {N : ℤ}

/-- An original function on `D(s₀)` times a sufficiently high power of `s₀` extends to an actual
global section of the same line bundle on the same scheme. -/
theorem exists_section_extending_coefficient (s₀ s₁ : L.Sections N ⊤)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₁ : IsAffineOpen s₁.nonvanishingLocus) (a : Γ(X, s₀.nonvanishingLocus)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : L.Sections (N * k) ⊤,
      t.restrict (le_top : s₀.nonvanishingLocus ≤ ⊤) =
        a • (s₀.npow k).restrict (le_top : s₀.nonvanishingLocus ≤ ⊤) := by
  let U := s₀.nonvanishingLocus
  let a₀ : Γ(unitModule X, U) := a
  let V := s₁.nonvanishingLocus
  let σ : L.Sections N V := s₁.restrict (le_top : V ≤ ⊤)
  have hσ : σ.nonvanishingLocus = V := by
    rw [Sections.nonvanishingLocus_restrict]
    exact inf_idem V
  have hU : U ≤ s₀.nonvanishingLocus := le_rfl
  have hf := isUnit_ratio s₀ hσ hU
  have hUV : U ⊓ V = X.basicOpen (ratio s₀ hσ) := by
    rw [basicOpen_ratio]
    exact inf_comm U V
  obtain ⟨k₀, hk₀⟩ := exists_global_section_extending (unitModule X) U V
    (RingHom.id Γ(X, ⊤)) hf h₁ hUV a₀
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨p, hp⟩ := hk₀ k hk
  let e := twoChartIso s₀ hσ (unitModule X) hU k hcov
  let t : L.Sections (N * k) ⊤ := e.inv.app ⊤ p
  have htp : e.hom.app ⊤ t = p := by
    change (e.inv ≫ e.hom).app ⊤ p = p
    rw [e.inv_hom_id]
    rfl
  have hfirst : (toPair s₀ (unitModule X) hσ hU k ⊤ t).1 =
      (unitModule X).presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ U ≤ U)).op a₀ := by
    have hpair : toPair s₀ (unitModule X) hσ hU k ⊤ t =
        (show twistSubgroup (unitModule X) U V
          ((isUnit_ratio s₀ hσ hU).unit ^ (k : ℤ)) ⊤ from p).1 := by
      rw [← twoChartHom_app s₀ hσ (unitModule X) hU k ⊤ t]
      exact congrArg (fun z => (show twistSubgroup (unitModule X) U V
        ((isUnit_ratio s₀ hσ hU).unit ^ (k : ℤ)) ⊤ from z).1) htp
    rw [hpair, ← hp]
    exact (presheaf_map_map_self (unitModule X) _ _ _).symm
  have hmul := mulSec_toPair_fst s₀ hσ (unitModule X) hU k ⊤ t
  rw [hfirst] at hmul
  have hres := congrArg
    (L.twistRestrict (unitModule X) _ (le_inf le_top le_rfl : U ≤ ⊤ ⊓ U)) hmul
  rw [mulSec_restrict, presheaf_map_map_self, Sections.restrict_restrict] at hres
  refine ⟨t, ?_⟩
  rw [← mulSec_unit]
  exact (hres.trans (twistRestrict_twistRestrict (unitModule X) _ _ _ t)).symm

/-- Vanishing at an original point is preserved by a finite sum of sections of the same power. -/
lemma not_mem_nonvanishingLocus_sum {ι : Type*} (S : Finset ι)
    (t : ι → L.Sections N ⊤) {x : X} (ht : ∀ i ∈ S, x ∉ (t i).nonvanishingLocus) :
    x ∉ (∑ i ∈ S, t i).nonvanishingLocus := by
  obtain ⟨j, hj⟩ := L.exists_mem_U x
  rw [Sections.mem_nonvanishingLocus_iff _ hj, Sections.coeff_sum]
  exact CurvesField.Positive.not_mem_basicOpen_sum S (fun i => (t i).coeff j)
    (fun i hi h => ht i hi ((t i).basicOpen_coeff_le j h))

/-- If exactly one summand is a unit at an original point, the sum is a unit there. -/
lemma mem_nonvanishingLocus_sum_of_unique {ι : Type*} (S : Finset ι)
    (t : ι → L.Sections N ⊤) {i : ι} (hi : i ∈ S) {x : X}
    (hit : x ∈ (t i).nonvanishingLocus)
    (ht : ∀ j ∈ S, j ≠ i → x ∉ (t j).nonvanishingLocus) :
    x ∈ (∑ j ∈ S, t j).nonvanishingLocus := by
  obtain ⟨a, ha⟩ := L.exists_mem_U x
  have hx : x ∈ (⊤ : X.Opens) ⊓ L.U a := ⟨trivial, ha⟩
  rw [Sections.mem_nonvanishingLocus_iff _ ha, Sections.coeff_sum,
    X.mem_basicOpen _ x hx, map_sum]
  apply isUnit_sum_of_eq S _ hi
  · exact (X.mem_basicOpen _ x hx).mp ((t i).mem_nonvanishingLocus_iff ha |>.mp hit)
  · intro j hj hji
    exact germ_mem_maximalIdeal ((t j).coeff a) hx
      (fun h => ht j hj hji ((t j).basicOpen_coeff_le a h))

/-- A global section in every sufficiently high multiple which is nonzero at one original closed
point and zero at a prescribed finite set of other original closed points. -/
theorem exists_section_separating_one (s₀ s₁ : L.Sections N ⊤)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₀ : IsAffineOpen s₀.nonvanishingLocus) (h₁ : IsAffineOpen s₁.nonvanishingLocus)
    (z : X) (hz : z ∈ s₀.nonvanishingLocus) (hzcl : IsClosed ({z} : Set X))
    (T : Finset X) (hTcl : ∀ w ∈ T, IsClosed ({w} : Set X)) (hzT : z ∉ T) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : L.Sections (N * (k + 1 : ℕ)) ⊤,
      z ∈ t.nonvanishingLocus ∧ ∀ w ∈ T, w ∉ t.nonvanishingLocus := by
  classical
  obtain ⟨a, ha, haT⟩ := CurvesField.Positive.exists_separating h₀ {z} T
    (by simpa using hz) (by simpa using hzcl) hTcl (by simpa using hzT)
  have hza : z ∈ X.basicOpen a := ha z (Finset.mem_singleton_self z)
  obtain ⟨k₀, hk₀⟩ := exists_section_extending_coefficient s₀ s₁ hcov h₁ a
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨t, ht⟩ := hk₀ k hk
  have hD : t.nonvanishingLocus ⊓ s₀.nonvanishingLocus = X.basicOpen a := by
    have h := congrArg Sections.nonvanishingLocus ht
    rw [Sections.nonvanishingLocus_restrict, Sections.nonvanishingLocus_smul,
      Sections.nonvanishingLocus_restrict] at h
    have hn : s₀.nonvanishingLocus ≤ (s₀.npow k).nonvanishingLocus :=
      Sections.le_nonvanishingLocus_npow s₀ le_rfl k
    rw [inf_eq_left.mpr hn] at h
    exact (inf_comm _ _).trans (h.trans (inf_eq_left.mpr (X.basicOpen_le a)))
  have hpower : N * k + N = N * (k + 1 : ℕ) := by push_cast; ring
  let t' : L.Sections (N * (k + 1 : ℕ)) ⊤ := (t.mul s₀).cast hpower
  have ht' : t'.nonvanishingLocus = X.basicOpen a := by
    rw [Sections.nonvanishingLocus_cast, Sections.nonvanishingLocus_mul]
    exact hD
  exact ⟨t', ht' ▸ hza, fun w hw => ht' ▸ haT w hw⟩

/-- Actual finite-point prescription on the original scheme, in every sufficiently high multiple
of the original power. No section, vanishing, or coboundary certificate is an input. -/
theorem exists_sections_prescribing_finite_closed_points (s₀ s₁ : L.Sections N ⊤)
    (hcov : s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus = ⊤)
    (h₀ : IsAffineOpen s₀.nonvanishingLocus) (h₁ : IsAffineOpen s₁.nonvanishingLocus)
    (T₀ T₁ : Finset X) (hcl : ∀ z, z ∈ T₀ ∨ z ∈ T₁ → IsClosed ({z} : Set X))
    (hdisj : Disjoint T₀ T₁) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : L.Sections (N * (k + 1 : ℕ)) ⊤,
      (∀ z ∈ T₀, z ∉ t.nonvanishingLocus) ∧ (∀ z ∈ T₁, z ∈ t.nonvanishingLocus) := by
  classical
  have hsingle : ∀ z : T₁, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ t : L.Sections (N * (k + 1 : ℕ)) ⊤,
        (z : X) ∈ t.nonvanishingLocus ∧
          ∀ w ∈ T₀ ∪ T₁.erase (z : X), w ∉ t.nonvanishingLocus := by
    intro z
    have hzcl := hcl z (Or.inr z.property)
    have hTcl : ∀ w ∈ T₀ ∪ T₁.erase (z : X), IsClosed ({w} : Set X) := by
      intro w hw
      exact hcl w (Finset.mem_union.mp hw |>.elim Or.inl
        (fun h => Or.inr (Finset.mem_of_mem_erase h)))
    have hzT : (z : X) ∉ T₀ ∪ T₁.erase (z : X) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.disjoint_left.mp hdisj h z.property
      · exact (Finset.ne_of_mem_erase h) rfl
    have hzcover : (z : X) ∈ s₀.nonvanishingLocus ⊔ s₁.nonvanishingLocus := by
      rw [hcov]
      trivial
    rcases Opens.mem_sup.mp hzcover with hz | hz
    · exact exists_section_separating_one s₀ s₁ hcov h₀ h₁ z hz hzcl _ hTcl hzT
    · exact exists_section_separating_one s₁ s₀ (by rw [sup_comm]; exact hcov)
        h₁ h₀ z hz hzcl _ hTcl hzT
  choose k₀ hk₀ using hsingle
  refine ⟨Finset.univ.sup k₀, fun k hk => ?_⟩
  have hchoice : ∀ z : T₁, ∃ t : L.Sections (N * (k + 1 : ℕ)) ⊤,
      (z : X) ∈ t.nonvanishingLocus ∧
        ∀ w ∈ T₀ ∪ T₁.erase (z : X), w ∉ t.nonvanishingLocus :=
    fun z => hk₀ z k ((Finset.le_sup (Finset.mem_univ z)).trans hk)
  choose t htz htzero using hchoice
  refine ⟨∑ z : T₁, t z, ?_, ?_⟩
  · intro z hz
    exact not_mem_nonvanishingLocus_sum Finset.univ t
      (fun w _ => htzero w z (Finset.mem_union_left _ hz))
  · intro z hz
    apply mem_nonvanishingLocus_sum_of_unique Finset.univ t (i := ⟨z, hz⟩)
      (Finset.mem_univ _) (htz ⟨z, hz⟩)
    intro w _ hw
    apply htzero w z
    refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hz⟩)
    intro h
    exact hw (Subtype.ext h.symm)

end

end DeJongAlterations.StableModificationBridge.FinitePointPrescription
