/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.StableModificationBridge.IntegralPositiveFiniteZero
import DeJongAlterations.StableModification.Projectivity.RelativeFinite
import DeJongAlterations.Geometry.FiniteProjectivePreservation

/-!
# Actual positive integral clopen pieces produce original good sections

The natural geometric component cover and original positive degrees internally produce every
component section, exponent, original image section and native sheaf gluing.

Blueprint: `positive-integral-clopen-assembly.tex`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification
open DeJongAlterations.StableModification.Projectivity
open DeJongAlterations.StableModification.CurvesField.Ample

namespace DeJongAlterations.StableModificationBridge.PositiveIntegralClopenAssembly

noncomputable section

open LineBundleData

variable {X : Scheme.{u}}

theorem subsingleton_sections_bot (L : LineBundleData X) (m : ℤ) : Subsingleton (L.Sections m ⊥) := by
  constructor
  intro s t
  apply Sections.ext
  intro i
  have : Subsingleton Γ(X, (⊥ : X.Opens) ⊓ L.U i) := by
    rw [bot_inf_eq]
    infer_instance
  exact Subsingleton.elim _ _

theorem exists_good_section_zero_of_positive_integral_clopen_cover
    {K : Type u} [Field K] [Infinite K] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    {J : Type u} [Fintype J] (Z : J → Scheme.{u}) (j : ∀ i, Z i ⟶ X)
    [∀ i, IsIntegral (Z i)] [∀ i, IsFinite (j i)] [∀ i, IsOpenImmersion (j i)]
    (hdisj : Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange))
    (hcov : ⨆ i, (j i).opensRange = ⊤) (L : LineBundleData X)
    (hdeg : ∀ i, (∃ z : Z i, ¬ IsClosed ({z} : Set (Z i))) →
      haveI : CompactSpace (Z i) := CurvesField.Genus.compactSpace_of_isAffineHom (j i)
      haveI : IsAffineHom (pullback.diagonal (terminal.from (Z i))) :=
        CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (j i)
      0 < CurvesField.Positive.degree (L.pullback (j i)) (Cohomology.structureCoeff (j i ≫ p)))
    (T : Finset X) (hcl : ∀ x ∈ T, IsClosed ({x} : Set X)) :
    ∃ (N : ℕ) (s : L.Sections N ⊤), 0 < N ∧
      (∀ x ∈ T, x ∉ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  classical
  let : IsProper p := hp.isProper
  let : CompactSpace X := compactSpace_of_quasiCompact p
  let : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated p
  let hcpt (i : J) : CompactSpace (Z i) := CurvesField.Genus.compactSpace_of_isAffineHom (j i)
  let hdiag (i : J) : IsAffineHom (pullback.diagonal (terminal.from (Z i))) :=
    CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (j i)
  let Ti (i : J) : Finset (Z i) :=
    (T.finite_toSet.preimage (j i).isOpenEmbedding.injective.injOn).toFinset
  have hTi (i : J) : ∀ z ∈ Ti i, IsClosed ({z} : Set (Z i)) := by
    intro z hz
    have hx : j i z ∈ T := by
      simpa only [Ti, Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] using hz
    have h := (hcl (j i z) hx).preimage (j i).continuous
    simpa only [← Set.image_singleton, Set.preimage_image_eq _ (j i).isOpenEmbedding.injective] using h
  have hlocal : ∀ i : J, ∃ (n : ℕ) (s : (L.pullback (j i)).Sections n ⊤), 0 < n ∧
      (∀ z ∈ Ti i, z ∉ s.nonvanishingLocus) ∧
      (∀ z : Z i, ¬ IsClosed ({z} : Set (Z i)) → z ∈ s.nonvanishingLocus) ∧
      (∀ z : Z i, ¬ IsClosed ({z} : Set (Z i)) → ∃ w, z ⤳ w ∧ w ∉ s.nonvanishingLocus) := by
    intro i
    by_cases hnc : ∃ z : Z i, ¬ IsClosed ({z} : Set (Z i))
    · exact IntegralPositiveFiniteZero.exists_good_section_zero_on_finite_closed_points_of_degree_pos
        (Geometry.FiniteProjective.isProjectiveOver_comp_of_isFinite p hp (j i))
        ((j i).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
        (L.pullback (j i)) (hdeg i hnc) (Ti i) (hTi i)
    · refine ⟨1, 0, Nat.one_pos, ?_, ?_, ?_⟩
      · intro z _ hz
        obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hz
        change z ∈ (Z i).basicOpen (0 : Γ(Z i, ⊤ ⊓ (L.pullback (j i)).U a)) at ha
        simp only [Scheme.basicOpen_zero, Opens.mem_bot] at ha
      · intro z hz
        exact False.elim (hnc ⟨z, hz⟩)
      · intro z hz
        exact False.elim (hnc ⟨z, hz⟩)
  choose n t hn htzero htgen htspec using hlocal
  let N := Finset.univ.prod n
  have hN : 0 < N := Finset.prod_pos fun i _ => hn i
  have hdvd (i : J) : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  choose e he using hdvd
  have hepos (i : J) : 0 < e i := Nat.pos_of_mul_pos_left (he i ▸ hN)
  let t' (i : J) : (L.pullback (j i)).Sections N ⊤ :=
    ((t i).npow (e i)).cast (by exact_mod_cast (he i).symm)
  have ht'D (i : J) : (t' i).nonvanishingLocus = (t i).nonvanishingLocus :=
    (Sections.nonvanishingLocus_cast _ _).trans (Sections.nonvanishingLocus_npow _ (hepos i))
  have himg (i : J) : ∃ a : L.Sections N (j i).opensRange,
      a.pullback (j i) = (t' i).restrict le_top :=
    (L.bijective_pullback_of_isOpenImmersion N (j i) le_rfl).2 ((t' i).restrict le_top)
  choose a ha using himg
  let F := L.twist (unitModule X) N
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hagree : TopCat.Presheaf.IsCompatible G.1 (fun i => (j i).opensRange) a := by
    intro i k
    by_cases hik : i = k
    · subst k
      rfl
    · have hbot : (j i).opensRange ⊓ (j k).opensRange = ⊥ := disjoint_iff.mp (hdisj hik)
      have hsub : Subsingleton Γ(F, (j i).opensRange ⊓ (j k).opensRange) := by
        rw [hbot]
        exact subsingleton_sections_bot L N
      exact Subsingleton.elim _ _
  obtain ⟨s₀, hs₀, -⟩ := G.existsUnique_gluing' (fun i => (j i).opensRange) ⊤
    (fun _ => homOfLE le_top) hcov.ge a hagree
  let s : L.Sections N ⊤ := s₀
  have hs (i : J) : s.restrict le_top = a i := hs₀ i
  have hD (i : J) (z : Z i) : j i z ∈ s.nonvanishingLocus ↔ z ∈ (t i).nonvanishingLocus := by
    have hzimg : j i z ∈ (j i).opensRange := ⟨z, rfl⟩
    have hDs := congrArg (fun w : L.Sections N (j i).opensRange => w.nonvanishingLocus) (hs i)
    rw [Sections.nonvanishingLocus_restrict] at hDs
    have hDa := congrArg
      (fun w : (L.pullback (j i)).Sections N ((j i) ⁻¹ᵁ (j i).opensRange) => w.nonvanishingLocus) (ha i)
    rw [Sections.nonvanishingLocus_pullback, Sections.nonvanishingLocus_restrict, ht'D] at hDa
    have hmem := SetLike.ext_iff.mp hDa z
    have hmem' := SetLike.ext_iff.mp hDs (j i z)
    exact (show j i z ∈ s.nonvanishingLocus ↔ j i z ∈ (a i).nonvanishingLocus from by
      simpa only [Opens.mem_inf, hzimg, true_and] using hmem').trans (by
        simpa only [Scheme.Hom.mem_preimage, Opens.mem_inf, hzimg, true_and] using hmem)
  have hpoint (x : X) : ∃ (i : J) (z : Z i), j i z = x := by
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    exact ⟨i, z, hz⟩
  have hnonclosed (i : J) {z : Z i} (hz : ¬ IsClosed ({j i z} : Set X)) :
      ¬ IsClosed ({z} : Set (Z i)) := by
    intro hz'
    apply hz
    simpa only [Set.image_singleton] using (j i).isClosedMap _ hz'
  refine ⟨N, s, hN, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, z, rfl⟩ := hpoint x
    have hz : z ∈ Ti i := by
      simpa only [Ti, Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] using hx
    exact fun h => htzero i z hz ((hD i z).mp h)
  · intro x hx
    obtain ⟨i, z, rfl⟩ := hpoint x
    exact (hD i z).mpr (htgen i z (hnonclosed i hx))
  · intro x hx
    obtain ⟨i, z, rfl⟩ := hpoint x
    obtain ⟨w, hzw, hw⟩ := htspec i z (hnonclosed i hx)
    exact ⟨j i w, hzw.map (j i).continuous, fun h => hw ((hD i w).mp h)⟩

end

end DeJongAlterations.StableModificationBridge.PositiveIntegralClopenAssembly
