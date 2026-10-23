/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.FiniteCoordinates

/-!
# Serre's extension lemma for projective coordinates

Let `D` be projective coordinates on `X` (`ProjectiveCoordinates`) and `F` a quasi-coherent module.
For `t ∈ Γ(U_j, F)` some multiple `x_j^N t` extends to a global section of `F(N)`: there is a
compatible family `σ` concentrated in degree `N` with `σ_j = t` (`exists_extension`;
Hartshorne II.5.14(b), EGA I 9.3.1). In the language of `FiniteCoordinates.lean`: the element
`single N σ` of the ambient module lies in `Γ_*(F)` (`gstar`) and its `j`-th dehomogenization is
`t`. Blueprint `lem:sm-serre-extension`.

The proof uses only that `U_i ∩ U_j = D(x_j/x_i)` inside the affine `U_i`, so that restriction
`Γ(U_i, F) → Γ(U_i ∩ U_j, F)` is a localization at `ratio i j` (COH1's
`isLocalizedModule_restrictLinearNative`; `exists_res_eq_smul`, `exists_pow_smul_eq_zero`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}} {A : Type u} [CommRing A]

namespace ProjectiveCoordinates

section Localization

variable (F : X.Modules) [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine open `W`, every section over `D(g) ⊆ W` becomes the restriction of a section over
`W` after multiplication by a power of `g`. -/
theorem exists_res_eq_smul {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {V : X.Opens}
    (hV : V = X.basicOpen g) (t : Γ(F, V)) :
    ∃ (n : ℕ) (s : Γ(F, W)), resM F (hV.le.trans (X.basicOpen_le g)) s =
      resR (hV.le.trans (X.basicOpen_le g)) g ^ n • t := by
  subst hV
  let := Module.compHom Γ(F, X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have hN := isLocalizedModule_restrictLinearNative F hW g
  obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hm⟩ := hN.surj t
  refine ⟨n, m, ?_⟩
  change (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ n) • t =
    F.presheaf.map (homOfLE (X.basicOpen_le g)).op m at hm
  rw [map_pow] at hm
  exact hm.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine open `W`, a section over `W` vanishing on `D(g)` is killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {V : X.Opens}
    (hV : V = X.basicOpen g) (s : Γ(F, W))
    (hs : resM F (hV.le.trans (X.basicOpen_le g)) s = 0) : ∃ n : ℕ, g ^ n • s = 0 := by
  subst hV
  let := Module.compHom Γ(F, X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have hN := isLocalizedModule_restrictLinearNative F hW g
  have h : restrictLinearNative F (X.basicOpen_le g) s =
      restrictLinearNative F (X.basicOpen_le g) 0 := by
    rw [map_zero]
    exact hs
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hN.exists_of_eq h
  refine ⟨n, ?_⟩
  change g ^ n • s = g ^ n • (0 : Γ(F, W)) at hn
  rw [hn, smul_zero]

end Localization

variable {c : A →+* Γ(X, ⊤)} (D : ProjectiveCoordinates X A c)

section Extension

variable (F : X.Modules)

lemma single_coeff (n : ℕ) (s : ∀ i, Γ(F, D.U i)) (i : D.ι) (m : ℕ) :
    ((single n s : D.Ambient F) i).coeff m = if n = m then s i else 0 :=
  Finsupp.single_apply

/-- Basic opens of the restricted ratios: `U i ∩ U k ∩ U j = D(ratio i j)` inside `U i ∩ U k`. -/
lemma inf_inf_eq_basicOpen_res (i j k : D.ι) :
    D.U i ⊓ D.U k ⊓ D.U j =
      X.basicOpen (resR (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (D.ratio i j)) := by
  rw [Scheme.basicOpen_res, ← D.inf_eq_basicOpen]
  ext x
  simp only [Opens.coe_inf, Set.mem_inter_iff]
  tauto

lemma isAffineOpen_inf (i k : D.ι) : IsAffineOpen (D.U i ⊓ D.U k) := by
  rw [D.inf_eq_basicOpen]
  exact (D.isAffineOpen i).basicOpen _

variable [F.IsQuasicoherent]

/-- **Serre's extension lemma** (blueprint `lem:sm-serre-extension`): for `t ∈ Γ(U_j, F)` there
are `N` and a compatible family `σ` concentrated in degree `N` (a section of `F(N)`) with
`σ_j = t`. -/
theorem exists_extension (j : D.ι) (t : Γ(F, D.U j)) :
    ∃ (N : ℕ) (σ : ∀ i, Γ(F, D.U i)), D.IsCompatible (single N σ : D.Ambient F) ∧ σ j = t := by
  classical
  -- Step 1: lift `t|_{U_i ∩ U_j}` to `U_i` after multiplying by a power of `ratio i j`.
  have h1 : ∀ i, ∃ (n : ℕ) (s : Γ(F, D.U i)),
      resM F (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) s =
        resR (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.ratio i j) ^ n •
          resM F (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) t := fun i =>
    exists_res_eq_smul F (D.isAffineOpen i) (D.ratio i j) (D.inf_eq_basicOpen i j) _
  choose n s hs using h1
  obtain ⟨N₀, hn⟩ : ∃ N₀ : ℕ, ∀ i, n i ≤ N₀ :=
    ⟨Finset.univ.sup n, fun i => Finset.le_sup (Finset.mem_univ i)⟩
  obtain ⟨s', hs'⟩ : ∃ s' : ∀ i, Γ(F, D.U i), ∀ i,
      resM F (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (s' i) =
        resR (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (D.ratio i j) ^ N₀ •
          resM F (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) t := by
    refine ⟨fun i => D.ratio i j ^ (N₀ - n i) • s i, fun i => ?_⟩
    rw [resM_smul, hs i, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel (hn i)]
  -- Step 2: the defect on `U i ∩ U k` vanishes on `U i ∩ U k ∩ U j`.
  have h2 : ∀ i k, ∃ M : ℕ,
      resR (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (D.ratio i j) ^ M •
        (resM F (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (s' i) -
          resR (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (D.ratio i k) ^ N₀ •
            resM F (inf_le_right : D.U i ⊓ D.U k ≤ D.U k) (s' k)) = 0 := by
    intro i k
    refine exists_pow_smul_eq_zero F (D.isAffineOpen_inf i k) _
      (D.inf_inf_eq_basicOpen_res i j k) _ ?_
    have hVi : D.U i ⊓ D.U k ⊓ D.U j ≤ D.U i ⊓ D.U j := fun x hx => ⟨hx.1.1, hx.2⟩
    have hVk : D.U i ⊓ D.U k ⊓ D.U j ≤ D.U k ⊓ D.U j := fun x hx => ⟨hx.1.2, hx.2⟩
    have ei := congrArg (resM F hVi) (hs' i)
    have ek := congrArg (resM F hVk) (hs' k)
    rw [resM_resM, resM_smul, resM_resM, map_pow, resR_resR] at ei ek
    rw [resM_sub, resM_resM, resM_smul, resM_resM, map_pow, resR_resR]
    rw [ei, ek, smul_smul, ← mul_pow]
    rw [D.ratio_mul_res i k j (hVi.trans inf_le_left) (hVk.trans inf_le_left), sub_self]
  choose M hM using h2
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ i k, M i k ≤ M₀ :=
    ⟨Finset.univ.sup fun ik : D.ι × D.ι => M ik.1 ik.2, fun i k =>
      Finset.le_sup (f := fun ik : D.ι × D.ι => M ik.1 ik.2) (Finset.mem_univ (i, k))⟩
  -- Step 3: multiply by `ratio i j ^ M₀`.
  refine ⟨N₀ + M₀, fun i => D.ratio i j ^ M₀ • s' i, ?_, ?_⟩
  · intro i k m
    rw [single_coeff, single_coeff]
    split_ifs with hm
    · subst hm
      rw [resM_smul, resM_smul, smul_smul, map_pow, map_pow, pow_add, mul_assoc, ← mul_pow,
        D.ratio_mul_res i k j inf_le_left inf_le_right, mul_comm, ← smul_smul]
      have h := hM i k
      have h' : resR (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (D.ratio i j) ^ M₀ •
          (resM F (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (s' i) -
            resR (inf_le_left : D.U i ⊓ D.U k ≤ D.U i) (D.ratio i k) ^ N₀ •
              resM F (inf_le_right : D.U i ⊓ D.U k ≤ D.U k) (s' k)) = 0 := by
        rw [← Nat.sub_add_cancel (hM₀ i k), pow_add, mul_smul, h, smul_zero]
      rw [smul_sub, sub_eq_zero] at h'
      rw [h', smul_comm]
    · rw [resM_zero, resM_zero, smul_zero]
  · have hjj : resM F (inf_le_left : D.U j ⊓ D.U j ≤ D.U j) (s' j) =
        resM F (inf_le_right : D.U j ⊓ D.U j ≤ D.U j) t := by
      rw [hs' j, D.ratio_self, map_one, one_pow, one_smul]
    have : s' j = t := resM_injective_of_eq (inf_idem (D.U j)) hjj
    simp only [this, D.ratio_self, one_pow, one_smul]

end Extension

end ProjectiveCoordinates

end

end DeJongAlterations.StableModification.Cohomology
