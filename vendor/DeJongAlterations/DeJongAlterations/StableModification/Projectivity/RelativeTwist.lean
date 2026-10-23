/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3C)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundleOpsHyperplane

/-!
# Sections of `𝓐 ⊗ 𝓝^n`

Blueprint `sm-projectivity-relative.tex`, preliminaries of `lem:sm-ltg-serre`. For line-bundle
data `A`, `N` on `X` we use the line-bundle data `A.mul (N.pow n)` of `𝓐 ⊗ 𝓝^{⊗ n}` (OM3A's
`LineBundleData.mul`, `LineBundleData.pow`). We record:

* `Sections.mulPow`: the product `σ · g` of a section `σ` of `𝓐 ⊗ 𝓝^n` with a section `g` of
  `𝓝^e`, a section of `𝓐 ⊗ 𝓝^{n + e}` (coefficientwise);
* `Sections.castPow`: transport along an equality of exponents;
* `Sections.diag`: a section of `𝓝 ⊗ 𝓝^r` as a section of `𝓝^{1 + r}` (restriction of the
  coefficients to the diagonal charts);
* `Sections.toPowOne`: a section of `𝓛^m` as a section of `(𝓛^{⊗ m})^1`;

each with its non-vanishing locus. These are the bookkeeping of Serre's extension step
(Hartshorne II.5.14) in `RelativeSerre.lean`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

namespace LineBundleData

section MulPow

variable {A N : LineBundleData X}

lemma mulPow_le (W : X.Opens) (p : A.ι × N.ι) :
    W ⊓ (A.U p.1 ⊓ N.U p.2) ≤ W ⊓ N.U p.2 :=
  inf_le_inf_left W inf_le_right

/-- The **product** of a section `σ` of `𝓐 ⊗ 𝓝^n` with a section `g` of `𝓝^e`: a section of
`𝓐 ⊗ 𝓝^{n + e}`, with coefficients `σ_p · g_{p.2}`. -/
def Sections.mulPow {n e : ℤ} {W : X.Opens} (σ : (A.mul (N.pow n)).Sections 1 W)
    (g : N.Sections e W) : (A.mul (N.pow (n + e))).Sections 1 W :=
  Sections.mk (L := A.mul (N.pow (n + e)))
    (fun p => σ.coeff p * X.presheaf.map (homOfLE (mulPow_le W p)).op (g.coeff p.2)) (by
    intro p q
    have hV : W ⊓ ((A.U p.1 ⊓ N.U p.2) ⊓ (A.U q.1 ⊓ N.U q.2)) ≤ W ⊓ (N.U p.2 ⊓ N.U q.2) :=
      fun _ hx => ⟨hx.1, hx.2.1.2, hx.2.2.2⟩
    have e₁ := σ.coeff_compat p q
    have e₂ := congrArg (X.presheaf.map (homOfLE hV).op) (g.coeff_compat p.2 q.2)
    rw [ringMap_map_trans, map_mul, ringMap_map_trans, N.map_res_trans_zpow] at e₂
    rw [map_mul, ringMap_map_trans, map_mul, ringMap_map_trans, e₁, e₂]
    simp only [transPow, zpow_one, mul_trans, pow_trans, Units.val_mul, zpow_add]
    ring)

@[simp]
lemma Sections.coeff_mulPow {n e : ℤ} {W : X.Opens} (σ : (A.mul (N.pow n)).Sections 1 W)
    (g : N.Sections e W) (p : A.ι × N.ι) :
    (σ.mulPow g).coeff p = σ.coeff p * X.presheaf.map (homOfLE (mulPow_le W p)).op (g.coeff p.2) :=
  rfl

lemma Sections.nonvanishingLocus_mulPow {n e : ℤ} {W : X.Opens}
    (σ : (A.mul (N.pow n)).Sections 1 W) (g : N.Sections e W) :
    (σ.mulPow g).nonvanishingLocus = σ.nonvanishingLocus ⊓ g.nonvanishingLocus := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    rw [Sections.coeff_mulPow, X.basicOpen_mul, Scheme.basicOpen_res]
    exact inf_le_inf (σ.basicOpen_coeff_le p) (inf_le_right.trans (g.basicOpen_coeff_le p.2))
  · rintro x ⟨hσ, hg⟩
    obtain ⟨p, hp⟩ := (A.mul (N.pow n)).exists_mem_U x
    have h₁ := (σ.mem_nonvanishingLocus_iff hp).mp hσ
    have h₂ := (g.mem_nonvanishingLocus_iff hp.2).mp hg
    have hxW : x ∈ W := (X.basicOpen_le _ h₁).1
    rw [Sections.mem_nonvanishingLocus_iff (L := A.mul (N.pow (n + e))) _ (i := p) hp,
      Sections.coeff_mulPow, X.basicOpen_mul, Scheme.basicOpen_res]
    exact ⟨h₁, ⟨hxW, hp⟩, h₂⟩

lemma Sections.restrict_mulPow {n e : ℤ} {W W' : X.Opens} (h : W' ≤ W)
    (σ : (A.mul (N.pow n)).Sections 1 W) (g : N.Sections e W) :
    (σ.mulPow g).restrict h = (σ.restrict h).mulPow (g.restrict h) := by
  ext p
  simp only [Sections.coeff_restrict, Sections.coeff_mulPow, map_mul, ringMap_map_trans]

lemma Sections.sub_mulPow {n e : ℤ} {W : X.Opens} (σ σ' : (A.mul (N.pow n)).Sections 1 W)
    (g : N.Sections e W) : (σ - σ').mulPow g = σ.mulPow g - σ'.mulPow g := by
  ext p
  change (σ.coeff p - σ'.coeff p) * _ = σ.coeff p * _ - σ'.coeff p * _
  ring

/-- The **tensor product** `t ⊗ g` of a section `t` of `𝓐` and a section `g` of `𝓝^e`, a section
of `𝓐 ⊗ 𝓝^e`. -/
def Sections.tensorN {e : ℤ} {W : X.Opens} (t : A.Sections 1 W) (g : N.Sections e W) :
    (A.mul (N.pow e)).Sections 1 W :=
  t.tensor (g.cast (mul_one e).symm).toPow

@[simp]
lemma Sections.coeff_tensorN {e : ℤ} {W : X.Opens} (t : A.Sections 1 W) (g : N.Sections e W)
    (p : A.ι × N.ι) :
    (t.tensorN g).coeff p = X.presheaf.map (homOfLE (inf_le_inf_left W inf_le_left :
        W ⊓ (A.U p.1 ⊓ N.U p.2) ≤ W ⊓ A.U p.1)).op (t.coeff p.1) *
      X.presheaf.map (homOfLE (mulPow_le W p)).op (g.coeff p.2) := by
  simp only [Sections.tensorN, Sections.coeff_tensor, Sections.coeff_toPow, Sections.coeff_cast]

lemma Sections.nonvanishingLocus_tensorN {e : ℤ} {W : X.Opens} (t : A.Sections 1 W)
    (g : N.Sections e W) :
    (t.tensorN g).nonvanishingLocus = t.nonvanishingLocus ⊓ g.nonvanishingLocus := by
  rw [Sections.tensorN, Sections.nonvanishingLocus_tensor, Sections.nonvanishingLocus_toPow,
    Sections.nonvanishingLocus_cast]

lemma Sections.restrict_tensorN {e : ℤ} {W W' : X.Opens} (h : W' ≤ W) (t : A.Sections 1 W)
    (g : N.Sections e W) : (t.tensorN g).restrict h = (t.restrict h).tensorN (g.restrict h) := by
  ext p
  simp only [Sections.coeff_restrict, Sections.coeff_tensorN, map_mul, ringMap_map_trans]

/-- Transport of sections of `𝓐 ⊗ 𝓝^n` along an equality of exponents. -/
def Sections.castPow {n n' : ℤ} (h : n = n') {W : X.Opens}
    (σ : (A.mul (N.pow n)).Sections 1 W) : (A.mul (N.pow n')).Sections 1 W :=
  h ▸ σ

lemma Sections.nonvanishingLocus_castPow {n n' : ℤ} (h : n = n') {W : X.Opens}
    (σ : (A.mul (N.pow n)).Sections 1 W) : (σ.castPow h).nonvanishingLocus = σ.nonvanishingLocus := by
  subst h
  rfl

lemma Sections.restrict_castPow {n n' : ℤ} (h : n = n') {W W' : X.Opens} (hW : W' ≤ W)
    (σ : (A.mul (N.pow n)).Sections 1 W) :
    (σ.castPow h).restrict hW = (σ.restrict hW).castPow h := by
  subst h
  rfl

lemma Sections.castPow_sub {n n' : ℤ} (h : n = n') {W : X.Opens}
    (σ τ : (A.mul (N.pow n)).Sections 1 W) :
    (σ - τ).castPow h = σ.castPow h - τ.castPow h := by
  subst h
  rfl

end MulPow

section Npow

variable {L : LineBundleData X} {m : ℤ}

lemma Sections.restrict_npow {W W' : X.Opens} (h : W' ≤ W) (s : L.Sections m W) (k : ℕ) :
    (s.npow k).restrict h = (s.restrict h).npow k := by
  ext i
  simp only [Sections.coeff_restrict, Sections.coeff_npow, map_pow]

lemma Sections.nonvanishingLocus_smul_eq {W : X.Opens} (r : Γ(X, W)) (s : L.Sections m W) :
    (r • s).nonvanishingLocus = X.basicOpen r ⊓ s.nonvanishingLocus := by
  have key : ∀ x : X, x ∈ (r • s).nonvanishingLocus ↔ x ∈ X.basicOpen r ⊓ s.nonvanishingLocus := by
    intro x
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_smul, X.basicOpen_mul]
    change x ∈ X.basicOpen (X.presheaf.map (homOfLE inf_le_left).op r) ⊓ _ ↔ _
    rw [Scheme.basicOpen_res]
    constructor
    · rintro ⟨⟨-, hr⟩, hs⟩
      exact ⟨hr, (s.mem_nonvanishingLocus_iff hi).mpr hs⟩
    · rintro ⟨hr, hs⟩
      have hs' := (s.mem_nonvanishingLocus_iff hi).mp hs
      exact ⟨⟨(X.basicOpen_le _ hs'), hr⟩, hs'⟩
  exact le_antisymm (fun x hx => (key x).mp hx) (fun x hx => (key x).mpr hx)

lemma Sections.nonvanishingLocus_le_npow {W : X.Opens} (s : L.Sections m W) (k : ℕ) :
    s.nonvanishingLocus ≤ (s.npow k).nonvanishingLocus := by
  intro x hx
  obtain ⟨i, hi⟩ := L.exists_mem_U x
  have hx' := (s.mem_nonvanishingLocus_iff hi).mp hx
  rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_npow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Scheme.basicOpen_one]
    exact X.basicOpen_le _ hx'
  · rw [Scheme.basicOpen_pow _ _ hk]
    exact hx'

end Npow

section Diag

variable {N : LineBundleData X}

lemma diag_le (W : X.Opens) (i : N.ι) : W ⊓ N.U i ≤ W ⊓ (N.U i ⊓ N.U i) :=
  fun _ hx => ⟨hx.1, hx.2, hx.2⟩

/-- A section of `𝓝 ⊗ 𝓝^r` as a section of `𝓝^{1 + r}`: the coefficients on the diagonal
charts `U i ∩ U i = U i`. -/
def Sections.diag {r : ℤ} {W : X.Opens} (σ : (N.mul (N.pow r)).Sections 1 W) :
    N.Sections (1 + r) W :=
  Sections.mk (fun i => X.presheaf.map (homOfLE (diag_le W i)).op (σ.coeff (i, i))) (by
    intro i j
    have hV : W ⊓ (N.U i ⊓ N.U j) ≤ W ⊓ ((N.U i ⊓ N.U i) ⊓ (N.U j ⊓ N.U j)) :=
      fun _ hx => ⟨hx.1, ⟨hx.2.1, hx.2.1⟩, hx.2.2, hx.2.2⟩
    have e := congrArg (X.presheaf.map (homOfLE hV).op) (σ.coeff_compat (i, i) (j, j))
    rw [ringMap_map_trans, map_mul, ringMap_map_trans] at e
    rw [ringMap_map_trans, ringMap_map_trans]
    refine e.trans ?_
    congr 1
    simp only [transPow]
    rw [(N.mul (N.pow r)).map_res_trans_zpow]
    simp only [zpow_one, mul_trans, pow_trans, zpow_add, Units.val_mul])

@[simp]
lemma Sections.coeff_diag {r : ℤ} {W : X.Opens} (σ : (N.mul (N.pow r)).Sections 1 W)
    (i : N.ι) : σ.diag.coeff i = X.presheaf.map (homOfLE (diag_le W i)).op (σ.coeff (i, i)) :=
  rfl

lemma Sections.nonvanishingLocus_diag {r : ℤ} {W : X.Opens}
    (σ : (N.mul (N.pow r)).Sections 1 W) : σ.diag.nonvanishingLocus = σ.nonvanishingLocus := by
  have key : ∀ x : X, x ∈ σ.diag.nonvanishingLocus ↔ x ∈ σ.nonvanishingLocus := by
    intro x
    obtain ⟨i, hi⟩ := N.exists_mem_U x
    rw [Sections.mem_nonvanishingLocus_iff _ hi,
      Sections.mem_nonvanishingLocus_iff (L := N.mul (N.pow r)) _ (i := (i, i)) ⟨hi, hi⟩,
      Sections.coeff_diag, Scheme.basicOpen_res]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨(X.basicOpen_le _ h).1, hi⟩, h⟩
  exact le_antisymm (fun x hx => (key x).mp hx) (fun x hx => (key x).mpr hx)

end Diag

section ToPowOne

variable {L : LineBundleData X} {m : ℤ}

/-- A section of `𝓛^m` as a section of `(𝓛^{⊗ m})^1`. -/
def Sections.toPowOne {W : X.Opens} (s : L.Sections m W) : (L.pow m).Sections 1 W :=
  (s.cast (mul_one m).symm).toPow

lemma Sections.nonvanishingLocus_toPowOne {W : X.Opens} (s : L.Sections m W) :
    s.toPowOne.nonvanishingLocus = s.nonvanishingLocus := by
  rw [Sections.toPowOne, Sections.nonvanishingLocus_toPow, Sections.nonvanishingLocus_cast]

end ToPowOne

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
