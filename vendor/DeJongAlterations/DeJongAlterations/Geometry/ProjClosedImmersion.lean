/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions from surjective graded homomorphisms

The native `Proj.map` associated to a surjective graded homomorphism is a closed immersion.
The required irrelevant-ideal containment and the surjectivity on affine charts are produced
from ring surjectivity by homogeneous lifting.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal
open scoped HomogeneousIdeal

set_option autoImplicit false

namespace DeJongAlterations.Geometry.ProjClosedImmersion

noncomputable section

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Surjectivity of a graded homomorphism gives preimages of the same homogeneous degree. -/
theorem exists_homogeneous_preimage (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f)
    {n : ℕ} {b : B} (hb : b ∈ ℬ n) : ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨(DirectSum.decompose 𝒜 a n : A), (DirectSum.decompose 𝒜 a n).property, ?_⟩
  rw [f.map_directSumDecompose]
  exact DirectSum.decompose_of_mem_same ℬ hb

/-- The irrelevant-ideal hypothesis required by native `Proj.map` follows from surjectivity. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage f hsurj hb
  exact Ideal.mem_map_of_mem f.toRingHom (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)

/-- A surjective graded map is surjective on every degree-zero homogeneous localization. -/
theorem away_map_surjective (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f)
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map f s) := by
  intro x
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) x
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage f hsurj hb
  refine ⟨Away.mk 𝒜 hs n a ha, ?_⟩
  simp only [Away.map_mk]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- On a standard affine target open, native `Proj.map` is a closed immersion. -/
theorem isClosedImmersion_map_restrict (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f)
    (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} (hd : 0 < d) (s : A) (hs : s ∈ 𝒜 d) :
    IsClosedImmersion ((Proj.map f hf) ∣_ Proj.basicOpen 𝒜 s) := by
  let eA := Proj.basicOpenIsoSpec 𝒜 s hs hd
  let eB := Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hd
  let g := Spec.map (CommRingCat.ofHom (Away.map f s))
  have : IsClosedImmersion g :=
    IsClosedImmersion.spec_of_surjective _ (away_map_surjective f hsurj hs)
  have heq : (Proj.map f hf) ∣_ Proj.basicOpen 𝒜 s = eB.hom ≫ g ≫ eA.inv := by
    apply (cancel_mono (Proj.basicOpen 𝒜 s).ι).mp
    rw [morphismRestrict_ι]
    have h := Proj.awayι_comp_map f hf hd s hs
    change eB.inv ≫ (Proj.basicOpen ℬ (f s)).ι ≫ Proj.map f hf =
      g ≫ eA.inv ≫ (Proj.basicOpen 𝒜 s).ι at h
    have h' := congrArg (fun z => eB.hom ≫ z) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Proj.map_preimage_basicOpen] using h'
  rw [heq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Every native `Proj.map` induced by a surjective graded homomorphism is a closed immersion.
The irrelevant-ideal proof may be any proof, so this composes with existing native morphisms. -/
theorem isClosedImmersion_map (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f)
    (hf : ℬ₊ ≤ 𝒜₊.map f) : IsClosedImmersion (Proj.map f hf) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun s : Σ i : PNat, 𝒜 i => Proj.basicOpen 𝒜 s.2)
  · apply Proj.iSup_basicOpen_eq_top
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi a ha
    exact Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨a, ha⟩⟩, rfl⟩
  · intro s
    exact isClosedImmersion_map_restrict f hsurj hf s.1.2 s.2 s.2.2

/-- A graded ring surjection produces its own global `Proj` morphism and proves it is a closed
immersion, without requiring a separately supplied irrelevant-ideal containment. -/
theorem isClosedImmersion_projMap (f : 𝒜 →+*ᵍ ℬ) (hsurj : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hsurj)) :=
  isClosedImmersion_map f hsurj _

end

end DeJongAlterations.Geometry.ProjClosedImmersion
