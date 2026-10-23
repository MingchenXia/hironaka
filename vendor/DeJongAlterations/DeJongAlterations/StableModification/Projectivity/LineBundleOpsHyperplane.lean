/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleOps
import DeJongAlterations.StableModification.Cohomology.FiniteCoordinates

/-!
# The hyperplane bundle `𝒪(1)` of projective coordinates

Blueprint `sm-projectivity-core.tex`, `lem:sm-lbd-hyperplane` (PLAN-OM3 M1). COH2's projective
coordinates `D : Cohomology.ProjectiveCoordinates X A c` on `X` (charts `U i = D₊(x_i)`, functions
`ratio i j = x_j / x_i ∈ Γ(U i, 𝒪_X)`; every closed subscheme of `ℙⁿ_A` carries them,
`Cohomology.nonempty_projectiveCoordinates_of_isProjectiveOver`) define the line-bundle data
`LineBundleData.hyperplane D` of `𝒪_X(1)`: the generator of `𝒪(1)` on `U i` is `x_i`, and
`x_j = (x_j / x_i) · x_i`, so the transition units are `u i j = ratio i j` on `U i ∩ U j`
(a unit there because `U i ∩ U j = D(ratio i j)`). The coordinates give global sections
`coordSection D k` of `𝒪(1)` (coefficients `x_k / x_i`), whose non-vanishing loci are the charts
(`nonvanishingLocus_coordSection`), so they generate `𝒪(1)` (`coordSection_generates`). The
convention agrees with COH2's twisted sections `ProjectiveCoordinates.gstar`
(`(e_i)_k = (ratio i j)^k (e_j)_k`). Pulled back along `β : X' ⟶ X`, this is `β^* 𝒪(1)`, the
twisting bundle of Serre's extension step of the local-to-global theorem (PLAN-OM3 §3, step 3).

We also record powers `Sections.npow`, the transport `Sections.cast` of sections along an
equality of exponents, and the identification `Sections.toPow`/`Sections.ofPow` of sections of
`(𝓛^{⊗ n})^m` and `𝓛^{n m}` (to form products of sections of `𝓛^m ⊗ 𝓜^r` via
`LineBundleData.mul` and `Sections.tensor`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}}

namespace LineBundleData

/-! ### Powers and casts of sections -/

section SectionsPow

variable {L : LineBundleData X} {m : ℤ}

/-- Transport of sections of `𝓛^m` along an equality of exponents. -/
def Sections.cast {m' : ℤ} (h : m = m') {W : X.Opens} (s : L.Sections m W) : L.Sections m' W :=
  h ▸ s

@[simp]
lemma Sections.coeff_cast {m' : ℤ} (h : m = m') {W : X.Opens} (s : L.Sections m W) (i : L.ι) :
    (s.cast h).coeff i = s.coeff i := by
  subst h
  rfl

lemma Sections.nonvanishingLocus_cast {m' : ℤ} (h : m = m') {W : X.Opens} (s : L.Sections m W) :
    (s.cast h).nonvanishingLocus = s.nonvanishingLocus := by
  subst h
  rfl

/-- The `k`-th power of a section of `𝓛^m`, a section of `𝓛^{m k}`. -/
def Sections.npow {W : X.Opens} (s : L.Sections m W) (k : ℕ) : L.Sections (m * k) W :=
  Sections.mk (fun i => s.coeff i ^ k) (by
    intro i j
    rw [map_pow, s.coeff_compat, mul_pow, map_pow]
    congr 1
    simp only [transPow, zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val])

@[simp]
lemma Sections.coeff_npow {W : X.Opens} (s : L.Sections m W) (k : ℕ) (i : L.ι) :
    (s.npow k).coeff i = s.coeff i ^ k :=
  rfl

lemma Sections.nonvanishingLocus_npow {W : X.Opens} (s : L.Sections m W) {k : ℕ} (hk : 0 < k) :
    (s.npow k).nonvanishingLocus = s.nonvanishingLocus := by
  simp only [Sections.nonvanishingLocus, Sections.coeff_npow, Scheme.basicOpen_pow _ _ hk]

/-- A section of `𝓛^{n m}` as a section of `(𝓛^{⊗ n})^m`. -/
def Sections.toPow {n : ℤ} {W : X.Opens} (s : L.Sections (n * m) W) : (L.pow n).Sections m W :=
  Sections.mk (L := L.pow n) (fun i => s.coeff i) (by
    intro i j
    rw [transPow_pow]
    exact s.coeff_compat i j)

/-- A section of `(𝓛^{⊗ n})^m` as a section of `𝓛^{n m}`. -/
def Sections.ofPow {n : ℤ} {W : X.Opens} (s : (L.pow n).Sections m W) : L.Sections (n * m) W :=
  Sections.mk (fun i => s.coeff i) (by
    intro i j
    rw [← transPow_pow]
    exact s.coeff_compat i j)

@[simp]
lemma Sections.coeff_toPow {n : ℤ} {W : X.Opens} (s : L.Sections (n * m) W) (i : L.ι) :
    s.toPow.coeff i = s.coeff i :=
  rfl

@[simp]
lemma Sections.coeff_ofPow {n : ℤ} {W : X.Opens} (s : (L.pow n).Sections m W) (i : L.ι) :
    s.ofPow.coeff i = s.coeff i :=
  rfl

lemma Sections.nonvanishingLocus_toPow {n : ℤ} {W : X.Opens} (s : L.Sections (n * m) W) :
    s.toPow.nonvanishingLocus = s.nonvanishingLocus :=
  rfl

lemma Sections.nonvanishingLocus_ofPow {n : ℤ} {W : X.Opens} (s : (L.pow n).Sections m W) :
    s.ofPow.nonvanishingLocus = s.nonvanishingLocus :=
  rfl

end SectionsPow

/-! ### The hyperplane bundle -/

section Hyperplane

variable {A : Type u} [CommRing A] {c : A →+* Γ(X, ⊤)}
  (D : Cohomology.ProjectiveCoordinates X A c)

/-- The ratio `x_j / x_i` restricted to `U i ∩ U j`. -/
abbrev ratioRes (i j : D.ι) : Γ(X, D.U i ⊓ D.U j) :=
  X.presheaf.map (homOfLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).op (D.ratio i j)

lemma isUnit_ratioRes (i j : D.ι) : IsUnit (ratioRes D i j) := by
  apply isUnit_of_basicOpen_eq
  rw [Scheme.basicOpen_res, ← D.inf_eq_basicOpen, inf_idem]

/-- **The hyperplane bundle** `𝒪(1)` of projective coordinates (blueprint
`lem:sm-lbd-hyperplane`): charts `U i = D₊(x_i)`, transition units `u i j = x_j / x_i`. -/
abbrev hyperplane : LineBundleData X where
  ι := D.ι
  U := D.U
  iSup_eq_top := D.iSup_eq_top
  u i j := (isUnit_ratioRes D i j).unit
  cocycle i j k := by
    change X.presheaf.map (homOfLE _).op (ratioRes D i j) *
        X.presheaf.map (homOfLE _).op (ratioRes D j k) =
      X.presheaf.map (homOfLE _).op (ratioRes D i k)
    have e := congrArg (X.presheaf.map (homOfLE (inf_le_left :
      D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i ⊓ D.U j)).op) (D.ratio_mul i j k)
    rw [map_mul, ringMap_map_trans, ringMap_map_trans, ringMap_map_trans] at e
    simp only [ratioRes]
    rw [ringMap_map_trans, ringMap_map_trans, ringMap_map_trans]
    exact e

lemma hyperplane_trans {i j : D.ι} {V : X.Opens} (h : V ≤ D.U i ⊓ D.U j) :
    ((hyperplane D).trans (i := i) (j := j) h : Γ(X, V)) =
      X.presheaf.map (homOfLE (h.trans inf_le_left)).op (D.ratio i j) := by
  change X.presheaf.map (homOfLE h).op (ratioRes D i j) = _
  rw [ringMap_map_trans]

/-- The **coordinate section** `x_k` of `𝒪(1)`: its coefficient on `U i` is `x_k / x_i`. -/
def coordSection (k : D.ι) : (hyperplane D).Sections 1 ⊤ :=
  Sections.mk (L := hyperplane D)
    (fun i => X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ D.U i ≤ D.U i)).op (D.ratio i k)) (by
    intro i j
    have hle : ⊤ ⊓ (D.U i ⊓ D.U j) ≤ D.U i ⊓ D.U j := inf_le_right
    have e := congrArg (X.presheaf.map (homOfLE hle).op) (D.ratio_mul i j k)
    rw [map_mul, ringMap_map_trans, ringMap_map_trans, ringMap_map_trans] at e
    simp only [transPow, zpow_one]
    rw [hyperplane_trans, ringMap_map_trans, ringMap_map_trans]
    exact e.symm)

lemma coeff_coordSection (k i : D.ι) :
    (coordSection D k).coeff i =
      X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ D.U i ≤ D.U i)).op (D.ratio i k) :=
  rfl

/-- The coordinate section `x_k` does not vanish exactly on the chart `U k = D₊(x_k)`. -/
lemma nonvanishingLocus_coordSection (k : D.ι) :
    (coordSection D k).nonvanishingLocus = D.U k := by
  have key : ∀ i : D.ι, (coordSection D k).nonvanishingLocus ⊓ D.U i = D.U i ⊓ D.U k := by
    intro i
    rw [Sections.nonvanishingLocus_inf (L := hyperplane D), coeff_coordSection,
      Scheme.basicOpen_res, ← D.inf_eq_basicOpen]
    exact le_antisymm (inf_le_right) (le_inf (le_inf le_top inf_le_left) le_rfl)
  ext x
  obtain ⟨i, hi⟩ := (hyperplane D).exists_mem_U x
  have hx := congrArg (fun V : X.Opens => x ∈ V) (key i)
  simp only [eq_iff_iff] at hx
  constructor
  · intro h
    exact (hx.mp ⟨h, hi⟩).2
  · intro h
    exact (hx.mpr ⟨hi, h⟩).1

/-- The coordinate sections generate `𝒪(1)`. -/
lemma coordSection_generates (x : X) : ∃ k, x ∈ (coordSection D k).nonvanishingLocus := by
  obtain ⟨k, hk⟩ := (hyperplane D).exists_mem_U x
  exact ⟨k, by rw [nonvanishingLocus_coordSection]; exact hk⟩

end Hyperplane

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
