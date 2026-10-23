/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3E)
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveDegree

/-!
# Auxiliary facts on curves for the positivity criterion

Elementary facts used by lane OM3E (blueprint `sm-curves-fields-ample-positive.tex`):

* `exists_separating`: on an affine open, finitely many closed points can be separated from
  finitely many other closed points by one function (prime avoidance in the form of a sum of
  products, as in OM3B's semilocal triviality `CurvesField.Ample.exists_section_nonvanishing`);
* `exists_isAffineOpen_mem_of_isProjectiveOver`: on a projective scheme over an infinite field,
  finitely many points lie in a common affine open (a linear form not vanishing at them);
* `nonvanishingLocus_ofLocal_one`: the local generator of line-bundle data on an open inside a
  chart vanishes nowhere;
* `eq_genericPoint_of_not_isClosed`: on an integral scheme of dimension at most one, the generic
  point is the only non-closed point.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Positive

noncomputable section

open Ample Ample.LineBundleData Projectivity.LineBundleData

variable {X : Scheme.{u}}

/-- A function whose germs at a point all lie in the maximal ideal, as a sum. -/
lemma not_mem_basicOpen_sum {U : X.Opens} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, U)) {x : X}
    (h : ∀ i ∈ s, x ∉ X.basicOpen (f i)) : x ∉ X.basicOpen (∑ i ∈ s, f i) := by
  intro hx
  have hxU : x ∈ U := X.basicOpen_le _ hx
  apply (X.mem_basicOpen _ x hxU).mp hx |> fun hu => ?_
  rw [map_sum] at hu
  have hmem : ∑ i ∈ s, X.presheaf.germ U x hxU (f i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    Ideal.sum_mem _ fun i hi => germ_mem_maximalIdeal (f i) hxU (h i hi)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

/-- **Separating finitely many closed points from finitely many others** by one function on an
affine open `W`: if `S ⊆ W` and `T` are finite sets of closed points with `S ∩ T = ∅`, some
`h ∈ Γ(W, 𝒪)` is a unit at the points of `S` and vanishes at the points of `T`. -/
theorem exists_separating {W : X.Opens} (hW : IsAffineOpen W) (S T : Finset X)
    (hSW : ∀ z ∈ S, z ∈ W) (hScl : ∀ z ∈ S, IsClosed ({z} : Set X))
    (hTcl : ∀ w ∈ T, IsClosed ({w} : Set X)) (hST : ∀ z ∈ S, z ∉ T) :
    ∃ h : Γ(X, W), (∀ z ∈ S, z ∈ X.basicOpen h) ∧ ∀ w ∈ T, w ∉ X.basicOpen h := by
  classical
  -- separating one point from one other closed point
  have hsep : ∀ z ∈ S, ∀ w : X, IsClosed ({w} : Set X) → w ≠ z →
      ∃ h : Γ(X, W), z ∈ X.basicOpen h ∧ w ∉ X.basicOpen h := by
    intro z hz w hw hne
    let O : X.Opens := ⟨({w} : Set X)ᶜ, hw.isOpen_compl⟩
    obtain ⟨h, hle, hzh⟩ := hW.exists_basicOpen_le (V := O) ⟨z, fun h => hne h.symm⟩ (hSW z hz)
    exact ⟨h, hzh, fun hwh => hle hwh rfl⟩
  choose! sp hsp₁ hsp₂ using hsep
  -- `g z` vanishes on `T` and is a unit at `z`; `e z` vanishes on `S ∖ {z}` and is a unit at `z`
  let g : X → Γ(X, W) := fun z => ∏ w ∈ T, sp z w
  let e : X → Γ(X, W) := fun z => ∏ z' ∈ S.erase z, sp z z'
  have hTz : ∀ z ∈ S, ∀ w ∈ T, w ≠ z := fun z hz w hw h => hST z hz (h ▸ hw)
  have hgz : ∀ z ∈ S, z ∈ X.basicOpen (g z) := fun z hz =>
    mem_basicOpen_prod _ _ (hSW z hz) fun w hw => hsp₁ z hz w (hTcl w hw) (hTz z hz w hw)
  have hgw : ∀ z ∈ S, ∀ w ∈ T, w ∉ X.basicOpen (g z) := fun z hz w hw =>
    not_mem_basicOpen_prod T (sp z) hw (hsp₂ z hz w (hTcl w hw) (hTz z hz w hw))
  have hez : ∀ z ∈ S, z ∈ X.basicOpen (e z) := fun z hz =>
    mem_basicOpen_prod _ _ (hSW z hz) fun z' hz' =>
      hsp₁ z hz z' (hScl z' (Finset.mem_of_mem_erase hz')) (Finset.ne_of_mem_erase hz')
  have hez' : ∀ z ∈ S, ∀ z' ∈ S, z' ≠ z → z' ∉ X.basicOpen (e z) := fun z hz z' hz' hne =>
    not_mem_basicOpen_prod (S.erase z) (sp z) (Finset.mem_erase.mpr ⟨hne, hz'⟩)
      (hsp₂ z hz z' (hScl z' hz') hne)
  refine ⟨∑ z ∈ S, e z * g z, fun z hz => ?_, fun w hw => ?_⟩
  · rw [X.mem_basicOpen _ z (hSW z hz), map_sum]
    apply isUnit_sum_of_eq S _ hz
    · rw [← X.mem_basicOpen _ z (hSW z hz), X.basicOpen_mul]
      exact ⟨hez z hz, hgz z hz⟩
    · intro z'' hz'' hne
      apply germ_mem_maximalIdeal
      rw [X.basicOpen_mul]
      exact fun h => hez' z'' hz'' z hz (Ne.symm hne) h.1
  · apply not_mem_basicOpen_sum
    intro z hz h
    rw [X.basicOpen_mul] at h
    exact hgw z hz w hw h.2

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Finitely many points of a projective scheme over an infinite field lie in a common affine
open** (the complement of a hyperplane avoiding them). -/
theorem exists_isAffineOpen_mem_of_isProjectiveOver {K : Type u} [Field K] [Infinite K]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (S : Finset X) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by
  obtain ⟨N', i, hi, -⟩ := hp
  have : IsClosedImmersion i := hi
  have hiA : IsAffineHom i := inferInstance
  have : Infinite (IsLocalRing.ResidueField K) := infinite_residueField K
  obtain ⟨ℓ, hℓ, hℓS⟩ := exists_linearForm_mem_basicOpen S
    (fun x => (i x : Proj (projectiveSpaceGrading K N')))
  exact ⟨i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading K N') ℓ,
    @IsAffineOpen.preimage _ _ _ (Proj.isAffineOpen_basicOpen _ ℓ hℓ one_pos) i hiA, hℓS⟩

/-- The local generator of `𝓛^m` on an open inside a chart vanishes nowhere. -/
lemma nonvanishingLocus_ofLocal_one {L : Projectivity.LineBundleData X} (m : ℤ) {W : X.Opens}
    {i : L.ι} (hW : W ≤ L.U i) :
    (show L.Sections m W from ofLocal (unitModule X) m hW (1 : Γ(X, W))).nonvanishingLocus = W := by
  apply le_antisymm (Sections.nonvanishingLocus_le _)
  intro x hx
  rw [Sections.mem_nonvanishingLocus_iff _ (hW hx)]
  have hc : (show L.Sections m W from ofLocal (unitModule X) m hW (1 : Γ(X, W))).coeff i =
      ((L.trans (le_inter_of_le hW i) ^ m : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i)) *
        X.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U i ≤ W)).op 1 :=
    rfl
  rw [hc, map_one, mul_one, X.basicOpen_of_isUnit (Units.isUnit _)]
  exact ⟨hx, hW hx⟩

/-- A point which is not closed has a specialization different from itself. -/
lemma exists_specializes_ne_of_not_isClosed {T : Type*} [TopologicalSpace T] {x : T}
    (hx : ¬ IsClosed ({x} : Set T)) : ∃ y, x ⤳ y ∧ y ≠ x := by
  by_contra h
  push Not at h
  apply hx
  have : closure ({x} : Set T) = {x} := by
    apply le_antisymm _ subset_closure
    intro y hy
    exact h y (specializes_iff_mem_closure.mpr hy)
  rw [← this]
  exact isClosed_closure

/-- **On an integral scheme of dimension at most one, the generic point is the only non-closed
point.** -/
lemma eq_genericPoint_of_not_isClosed [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) {x : X}
    (hx : ¬ IsClosed ({x} : Set X)) : x = genericPoint X := by
  obtain ⟨y, hxy, hyx⟩ := exists_specializes_ne_of_not_isClosed hx
  have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
  rcases eq_or_eq_of_topologicalKrullDim_le_one hdim _ _ _ hηx hxy with h | h
  · exact h.symm
  · exact absurd h.symm hyx

/-- On an integral scheme, a nonempty open contains the generic point. -/
lemma genericPoint_mem_of_nonempty [IsIntegral X] {W : X.Opens} (hW : (W : Set X).Nonempty) :
    genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)

/-- On a reduced scheme, a function on an open `W` vanishes if it vanishes at every point. -/
lemma eq_zero_of_basicOpen_eq_bot [IsReduced X] {W : X.Opens} {f : Γ(X, W)}
    (h : X.basicOpen f = ⊥) : f = 0 :=
  (AlgebraicGeometry.basicOpen_eq_bot_iff f).mp h

/-- **A section of `𝓛^m` on an integral scheme which vanishes at the generic point is zero.** -/
lemma Sections.eq_zero_of_genericPoint_not_mem [IsIntegral X] {L : Projectivity.LineBundleData X}
    {m : ℤ} {W : X.Opens} (s : L.Sections m W) (h : genericPoint X ∉ s.nonvanishingLocus) :
    s = 0 := by
  ext i
  apply eq_zero_of_basicOpen_eq_bot
  by_contra hne
  have hne' : ((X.basicOpen (s.coeff i) : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hne (Opens.ext he)
  exact h (s.basicOpen_coeff_le i (genericPoint_mem_of_nonempty hne'))

end

end DeJongAlterations.StableModification.CurvesField.Positive
