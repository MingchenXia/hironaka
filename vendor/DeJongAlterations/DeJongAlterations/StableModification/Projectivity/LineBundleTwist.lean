/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3A)
-/
import DeJongAlterations.StableModification.Projectivity.LineBundle

/-!
# The twist `F ⊗ 𝓛^m` is locally `F`; sections of `𝓛^m`

Blueprint `sm-projectivity-core.tex`, `def:sm-lbd-twist` and `lem:sm-lbd-ops` (PLAN-OM3 M1).
For line-bundle data `L` (`LineBundle.lean`) with trivializing cover `U i`:

* `LineBundleData.localEquiv`: for `W ⊆ U i`, the sections of `F ⊗ 𝓛^m` over `W` are the
  sections of `F` over `W` (through the `i`-th coefficient), `Γ(X, W)`-linearly;
* `LineBundleData.twistRestrictIso`: `(F ⊗ 𝓛^m)|_{U i} ≅ F|_{U i}`;
* `LineBundleData.isQuasicoherent_twist`: the twist of a quasi-coherent module is
  quasi-coherent (quasi-coherence is local, Mathlib's `IsQuasicoherent.of_coversTop`);
* `LineBundleData.Sections L m W`: the sections of `𝓛^m = 𝒪 ⊗ 𝓛^m` over `W`, with coefficients
  `coeff s i ∈ Γ(W ∩ U i, 𝒪_X)` (functions), the non-vanishing locus `nonvanishingLocus s`,
  products `mulSections` (`𝓛^m × 𝓛^n → 𝓛^{m+n}`), the action `smulSections` on twists, and the
  pullback of sections `pullbackSections` along a morphism.

The local computations follow COH4's two-chart twist (`CurvesField.CohomologyTwistLocal`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Projectivity

noncomputable section

variable {X : Scheme.{u}}

/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

namespace LineBundleData

variable (L : LineBundleData X) (F : X.Modules) (m : ℤ)

lemma map_res_trans_zpow {i j : L.ι} {V V' : X.Opens} (h : V ≤ L.U i ⊓ L.U j) (h' : V' ≤ V) :
    X.presheaf.map (homOfLE h').op ((L.trans h ^ m : Γ(X, V)ˣ) : Γ(X, V)) =
      ((L.trans (h'.trans h) ^ m : Γ(X, V')ˣ) : Γ(X, V')) :=
  L.res_trans_zpow h h' m

lemma coe_trans_zpow_mul {i j k : L.ι} {V : X.Opens} (h₁ : V ≤ L.U i ⊓ L.U j)
    (h₂ : V ≤ L.U j ⊓ L.U k) (h₃ : V ≤ L.U i ⊓ L.U k) (n : ℤ) :
    ((L.trans h₁ ^ n : Γ(X, V)ˣ) : Γ(X, V)) * ((L.trans h₂ ^ n : Γ(X, V)ˣ) : Γ(X, V)) =
      ((L.trans h₃ ^ n : Γ(X, V)ˣ) : Γ(X, V)) := by
  rw [← Units.val_mul, ← mul_zpow, L.trans_mul_trans h₁ h₂ h₃]

lemma coe_trans_self_zpow {i : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U i) (n : ℤ) :
    ((L.trans h ^ n : Γ(X, V)ˣ) : Γ(X, V)) = 1 := by
  rw [L.trans_self, one_zpow, Units.val_one]

/-! ### Sections over opens inside a chart -/

section Local

variable {L} {W : X.Opens} {i : L.ι} (hW : W ≤ L.U i)

include hW in
lemma le_inter_of_le (j : L.ι) : W ⊓ L.U j ≤ L.U j ⊓ L.U i :=
  fun _ hx => ⟨hx.2, hW hx.1⟩

/-- The `i`-th coefficient of a section of `F ⊗ 𝓛^m` over `W ⊆ U i`. -/
def toLocal (t : L.twistSubgroup F m W) : Γ(F, W) :=
  F.presheaf.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ L.U i)).op (t.1 i)

/-- The section of `F ⊗ 𝓛^m` over `W ⊆ U i` with `i`-th coefficient `s`: its `j`-th
coefficient is `(u j i)^m · s`. -/
def ofLocal (s : Γ(F, W)) : L.twistSubgroup F m W :=
  ⟨fun j => ((L.trans (le_inter_of_le hW j) ^ m : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) •
      F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U j ≤ W)).op s, by
    intro a b
    simp only
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_smul,
      Cohomology.presheaf_map_map F _ _ ((L.le_left W a b).trans inf_le_left),
      Cohomology.presheaf_map_map F _ _ ((L.le_left W a b).trans inf_le_left),
      L.map_res_trans_zpow, L.map_res_trans_zpow]
    congr 1
    exact (L.coe_trans_zpow_mul _ _ _ m).symm⟩

lemma ofLocal_apply (s : Γ(F, W)) (j : L.ι) :
    (ofLocal F m hW s).1 j =
      ((L.trans (le_inter_of_le hW j) ^ m : Γ(X, W ⊓ L.U j)ˣ) : Γ(X, W ⊓ L.U j)) •
        F.presheaf.map (homOfLE (inf_le_left : W ⊓ L.U j ≤ W)).op s :=
  rfl

lemma toLocal_ofLocal (s : Γ(F, W)) : toLocal F m hW (ofLocal F m hW s) = s := by
  change F.presheaf.map _ (_ • F.presheaf.map _ s) = s
  rw [Scheme.Modules.map_smul, Cohomology.presheaf_map_map_self, L.map_res_trans_zpow,
    L.coe_trans_self_zpow, one_smul]

lemma ofLocal_toLocal (t : L.twistSubgroup F m W) : ofLocal F m hW (toLocal F m hW t) = t := by
  apply Subtype.ext
  funext j
  have ht := t.2 j i
  have hle : W ⊓ L.U j ≤ W ⊓ (L.U j ⊓ L.U i) := fun x hx => ⟨hx.1, hx.2, hW hx.1⟩
  have e := congrArg (F.presheaf.map (homOfLE hle).op) ht
  have h₃ : W ⊓ L.U j ≤ W ⊓ L.U i := fun x hx => ⟨hx.1, hW hx.1⟩
  rw [Cohomology.presheaf_map_map_self, Scheme.Modules.map_smul,
    Cohomology.presheaf_map_map F _ _ h₃, L.map_res_trans_zpow] at e
  change _ • F.presheaf.map _ (F.presheaf.map _ (t.1 i)) = t.1 j
  rw [Cohomology.presheaf_map_map F _ _ h₃, e]

lemma toLocal_add (t t' : L.twistSubgroup F m W) :
    toLocal F m hW (t + t') = toLocal F m hW t + toLocal F m hW t' :=
  map_add _ _ _

lemma toLocal_smul (r : Γ(X, W)) (t : L.twistSubgroup F m W) :
    toLocal F m hW (r • t) = r • toLocal F m hW t := by
  change F.presheaf.map _ (res _ r • t.1 i) = r • F.presheaf.map _ (t.1 i)
  rw [Scheme.Modules.map_smul]
  congr 1
  exact (res_res _ _ le_rfl r).trans (res_self _ r)

lemma toLocal_restrict {W' : X.Opens} (h : W' ≤ W) (t : L.twistSubgroup F m W) :
    toLocal F m (h.trans hW) (L.twistRestrict F m h t) =
      F.presheaf.map (homOfLE h).op (toLocal F m hW t) := by
  change F.presheaf.map _ (F.presheaf.map _ (t.1 i)) = F.presheaf.map _ (F.presheaf.map _ (t.1 i))
  rw [Cohomology.presheaf_map_map F _ _ (le_inf h (h.trans hW)),
    Cohomology.presheaf_map_map F _ _ (le_inf h (h.trans hW))]

/-- **Sections over an open inside a chart** (blueprint `def:sm-lbd-twist`): for `W ⊆ U i`, the
sections of `F ⊗ 𝓛^m` over `W` are the sections of `F` over `W`, through the `i`-th
coefficient. -/
def localEquiv : L.twistSubgroup F m W ≃ₗ[Γ(X, W)] Γ(F, W) where
  toFun := toLocal F m hW
  invFun := ofLocal F m hW
  left_inv := ofLocal_toLocal F m hW
  right_inv := toLocal_ofLocal F m hW
  map_add' := toLocal_add F m hW
  map_smul' := toLocal_smul F m hW

lemma localEquiv_apply (t : L.twistSubgroup F m W) :
    localEquiv F m hW t = toLocal F m hW t :=
  rfl

end Local

/-! ### The twist is locally the module; quasi-coherence -/

section RestrictIso

/-- **`(F ⊗ 𝓛^m)|_{U i} ≅ F|_{U i}`** through the `i`-th coefficient. -/
def twistRestrictIso (i : L.ι) : (L.twist F m).restrict (L.U i).ι ≅ F.restrict (L.U i).ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W' => ModuleCat.isoMk (AddEquiv.toAddCommGrpIso
      { toFun := fun t => toLocal F m ((L.U i).ι_image_le W'.unop) t
        invFun := fun s => ofLocal F m ((L.U i).ι_image_le W'.unop) s
        left_inv := ofLocal_toLocal F m ((L.U i).ι_image_le W'.unop)
        right_inv := toLocal_ofLocal F m ((L.U i).ι_image_le W'.unop)
        map_add' := toLocal_add F m ((L.U i).ι_image_le W'.unop) }) (fun r => by
        ext t
        exact (toLocal_smul F m ((L.U i).ι_image_le W'.unop)
          (((L.U i).ι.appIso W'.unop).inv r) t).symm))
      (fun W₁ W₂ j => by
        ext t
        exact toLocal_restrict F m ((L.U i).ι_image_le W₁.unop)
          ((L.U i).ι.image_mono (leOfHom j.unop)) t))

/-- `F ⊗ 𝓛^m` and `F` agree over `U i` (as sheaves on the site over `U i`). -/
def twistOverIso (i : L.ι) : (L.twist F m).over (L.U i) ≅ F.over (L.U i) :=
  (Scheme.Modules.overEquiv (L.U i)).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (L.U i)).app _ ≪≫ L.twistRestrictIso F m i ≪≫
      ((Scheme.Modules.overFunctorEquiv (L.U i)).app F).symm)

/-- **The twist of a quasi-coherent module is quasi-coherent** (blueprint `def:sm-lbd-twist`). -/
instance isQuasicoherent_twist [F.IsQuasicoherent] : (L.twist F m).IsQuasicoherent := by
  have : ∀ i, ((L.twist F m).over (L.U i)).IsQuasicoherent := by
    intro i
    obtain ⟨⟨q⟩⟩ := SheafOfModules.isQuasicoherent_over F (L.U i)
    exact (SheafOfModules.QuasicoherentData.ofIsIso (L.twistOverIso F m i).inv q).isQuasicoherent
  have hcov : (Opens.grothendieckTopology X).CoversTop L.U := by
    rw [Opens.coversTop_iff, IsOpenCover, L.iSup_eq_top]
  exact SheafOfModules.IsQuasicoherent.of_coversTop (L.twist F m) L.U hcov

end RestrictIso

/-! ### Sections of `𝓛^m` -/

section Sections

/-- The sections of `𝓛^m = 𝒪_X ⊗ 𝓛^m` over `W`: families of functions `t i ∈ Γ(W ∩ U i, 𝒪_X)`
with `t i = (u i j)^m · t j` on `W ∩ U i ∩ U j` (definitionally the sections of the twist of the
structure sheaf, `Γ(L.twist (unitModule X) m, W)`). -/
def Sections (W : X.Opens) : Type u := L.twistSubgroup (unitModule X) m W

instance (W : X.Opens) : AddCommGroup (L.Sections m W) :=
  inferInstanceAs (AddCommGroup (L.twistSubgroup (unitModule X) m W))

instance (W : X.Opens) : Module Γ(X, W) (L.Sections m W) :=
  inferInstanceAs (Module Γ(X, W) (L.twistSubgroup (unitModule X) m W))

variable {L m}

/-- A section of `𝓛^m` as a section of the twist `𝒪_X ⊗ 𝓛^m`. -/
def Sections.toTwist {W : X.Opens} (s : L.Sections m W) : L.twistSubgroup (unitModule X) m W :=
  s

/-- A section of the twist `𝒪_X ⊗ 𝓛^m` as a section of `𝓛^m`. -/
def Sections.ofTwist {W : X.Opens} (s : L.twistSubgroup (unitModule X) m W) : L.Sections m W :=
  s

/-- The `i`-th coefficient of a section of `𝓛^m`, a function on `W ∩ U i`. -/
def Sections.coeff {W : X.Opens} (s : L.Sections m W) (i : L.ι) : Γ(X, W ⊓ L.U i) :=
  s.toTwist.1 i

lemma Sections.coeff_compat {W : X.Opens} (s : L.Sections m W) (i j : L.ι) :
    X.presheaf.map (homOfLE (L.le_left W i j)).op (s.coeff i) =
      L.transPow m W i j * X.presheaf.map (homOfLE (L.le_right W i j)).op (s.coeff j) :=
  s.toTwist.2 i j

/-- A compatible family of functions is a section of `𝓛^m`. -/
def Sections.mk {W : X.Opens} (t : ∀ i, Γ(X, W ⊓ L.U i))
    (ht : ∀ i j, X.presheaf.map (homOfLE (L.le_left W i j)).op (t i) =
      L.transPow m W i j * X.presheaf.map (homOfLE (L.le_right W i j)).op (t j)) :
    L.Sections m W :=
  (⟨t, ht⟩ : L.twistSubgroup (unitModule X) m W)

@[simp]
lemma Sections.coeff_mk {W : X.Opens} (t : ∀ i, Γ(X, W ⊓ L.U i)) (ht) (i : L.ι) :
    (Sections.mk (L := L) (m := m) t ht).coeff i = t i :=
  rfl

@[ext]
lemma Sections.ext {W : X.Opens} {s s' : L.Sections m W} (h : ∀ i, s.coeff i = s'.coeff i) :
    s = s' :=
  Subtype.ext (funext h)

@[simp]
lemma Sections.coeff_add {W : X.Opens} (s s' : L.Sections m W) (i : L.ι) :
    (s + s').coeff i = s.coeff i + s'.coeff i :=
  rfl

@[simp]
lemma Sections.coeff_smul {W : X.Opens} (r : Γ(X, W)) (s : L.Sections m W) (i : L.ι) :
    (r • s).coeff i = res (inf_le_left : W ⊓ L.U i ≤ W) r * s.coeff i :=
  rfl

/-- The **non-vanishing locus** `D(s) = ⋃ D(s_i)` of a section of `𝓛^m` over `W`. -/
def Sections.nonvanishingLocus {W : X.Opens} (s : L.Sections m W) : X.Opens :=
  ⨆ i, X.basicOpen (s.coeff i)

lemma Sections.nonvanishingLocus_le {W : X.Opens} (s : L.Sections m W) :
    s.nonvanishingLocus ≤ W :=
  iSup_le fun _ => (X.basicOpen_le _).trans inf_le_left

lemma Sections.basicOpen_coeff_le {W : X.Opens} (s : L.Sections m W) (i : L.ι) :
    X.basicOpen (s.coeff i) ≤ s.nonvanishingLocus :=
  le_iSup (fun i => X.basicOpen (s.coeff i)) i

lemma Sections.basicOpen_res_coeff {W : X.Opens} (s : L.Sections m W) (i j : L.ι) :
    X.basicOpen (X.presheaf.map (homOfLE (L.le_left W i j)).op (s.coeff i)) =
      X.basicOpen (X.presheaf.map (homOfLE (L.le_right W i j)).op (s.coeff j)) := by
  rw [s.coeff_compat, X.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)]
  exact inf_eq_right.mpr (X.basicOpen_le _)

/-- On a chart, the non-vanishing locus is the basic open of the coefficient. -/
lemma Sections.nonvanishingLocus_inf {W : X.Opens} (s : L.Sections m W) (i : L.ι) :
    s.nonvanishingLocus ⊓ L.U i = X.basicOpen (s.coeff i) := by
  apply le_antisymm
  · rintro x ⟨hx, hxi⟩
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    have hxW : x ∈ W := (X.basicOpen_le (s.coeff j) hj).1
    have hxj : x ∈ L.U j := (X.basicOpen_le (s.coeff j) hj).2
    have h1 : x ∈ X.basicOpen (X.presheaf.map (homOfLE (L.le_right W i j)).op (s.coeff j)) := by
      rw [Scheme.basicOpen_res]
      exact ⟨⟨hxW, hxi, hxj⟩, hj⟩
    rw [← s.basicOpen_res_coeff, Scheme.basicOpen_res] at h1
    exact h1.2
  · exact le_inf (s.basicOpen_coeff_le i) ((X.basicOpen_le _).trans inf_le_right)

lemma Sections.mem_nonvanishingLocus_iff {W : X.Opens} (s : L.Sections m W) {i : L.ι} {x : X}
    (hx : x ∈ L.U i) : x ∈ s.nonvanishingLocus ↔ x ∈ X.basicOpen (s.coeff i) := by
  rw [← s.nonvanishingLocus_inf i]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

lemma exists_mem_U (x : X) : ∃ i, x ∈ L.U i := by
  have hx : x ∈ (⊤ : X.Opens) := trivial
  rw [← L.iSup_eq_top] at hx
  exact Opens.mem_iSup.mp hx

/-- **Products of sections**: `𝓛^m ⊗ 𝓛^n → 𝓛^{m+n}`, coefficientwise. -/
def Sections.mul {n : ℤ} {W : X.Opens} (s : L.Sections m W) (t : L.Sections n W) :
    L.Sections (m + n) W :=
  Sections.mk (fun i => s.coeff i * t.coeff i) (by
    intro i j
    rw [map_mul, s.coeff_compat, t.coeff_compat, map_mul]
    simp only [transPow]
    rw [zpow_add, Units.val_mul]
    ring)

@[simp]
lemma Sections.coeff_mul {n : ℤ} {W : X.Opens} (s : L.Sections m W) (t : L.Sections n W)
    (i : L.ι) : (s.mul t).coeff i = s.coeff i * t.coeff i :=
  rfl

lemma Sections.nonvanishingLocus_mul {n : ℤ} {W : X.Opens} (s : L.Sections m W)
    (t : L.Sections n W) :
    (s.mul t).nonvanishingLocus = s.nonvanishingLocus ⊓ t.nonvanishingLocus := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [Sections.coeff_mul, X.basicOpen_mul]
    exact inf_le_inf (s.basicOpen_coeff_le i) (t.basicOpen_coeff_le i)
  · rintro x ⟨hs, ht⟩
    obtain ⟨i, hi⟩ := L.exists_mem_U x
    have hs' := (s.mem_nonvanishingLocus_iff hi).mp hs
    have ht' := (t.mem_nonvanishingLocus_iff hi).mp ht
    rw [Sections.mem_nonvanishingLocus_iff _ hi, Sections.coeff_mul, X.basicOpen_mul]
    exact ⟨hs', ht'⟩

/-- **Sections act on twists**: `𝓛^m ⊗ (F ⊗ 𝓛^n) → F ⊗ 𝓛^{m+n}`, coefficientwise. -/
def Sections.smulTwist {n : ℤ} {W : X.Opens} (s : L.Sections m W) (t : L.twistSubgroup F n W) :
    L.twistSubgroup F (m + n) W :=
  ⟨fun i => s.coeff i • t.1 i, by
    intro i j
    simp only
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, t.2 i j, s.coeff_compat, smul_smul,
      smul_smul]
    congr 1
    simp only [transPow]
    rw [zpow_add, Units.val_mul]
    ring⟩

@[simp]
lemma Sections.smulTwist_apply {n : ℤ} {W : X.Opens} (s : L.Sections m W)
    (t : L.twistSubgroup F n W) (i : L.ι) : (s.smulTwist F t).1 i = s.coeff i • t.1 i :=
  rfl

/-- Restriction of sections of `𝓛^m`. -/
def Sections.restrict {W W' : X.Opens} (h : W' ≤ W) (s : L.Sections m W) : L.Sections m W' :=
  L.twistRestrict (unitModule X) m h s.toTwist

@[simp]
lemma Sections.coeff_restrict {W W' : X.Opens} (h : W' ≤ W) (s : L.Sections m W) (i : L.ι) :
    (s.restrict h).coeff i =
      X.presheaf.map (homOfLE (inf_le_inf_right (L.U i) h)).op (s.coeff i) :=
  rfl

lemma Sections.nonvanishingLocus_restrict {W W' : X.Opens} (h : W' ≤ W) (s : L.Sections m W) :
    (s.restrict h).nonvanishingLocus = W' ⊓ s.nonvanishingLocus := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [Sections.coeff_restrict, Scheme.basicOpen_res]
    exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (s.basicOpen_coeff_le i))
  · rintro x ⟨hxW', hx⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hxi : x ∈ L.U i := (X.basicOpen_le _ hi).2
    rw [Sections.mem_nonvanishingLocus_iff _ hxi, Sections.coeff_restrict, Scheme.basicOpen_res]
    exact ⟨⟨hxW', hxi⟩, hi⟩

end Sections

/-! ### Pullback of sections -/

section PullbackSections

variable {X' : Scheme.{u}} (f : X' ⟶ X)

lemma pullback_trans {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) :
    ((L.pullback f).trans (f.preimage_mono h) : Γ(X', f ⁻¹ᵁ V)) =
      f.app V (L.trans h : Γ(X, V)) :=
  (app_res f h _).symm

lemma pullback_trans_zpow {i j : L.ι} {V : X.Opens} (h : V ≤ L.U i ⊓ L.U j) :
    (((L.pullback f).trans (f.preimage_mono h) ^ m : Γ(X', f ⁻¹ᵁ V)ˣ) : Γ(X', f ⁻¹ᵁ V)) =
      f.app V ((L.trans h ^ m : Γ(X, V)ˣ) : Γ(X, V)) := by
  have : (L.pullback f).trans (f.preimage_mono h) =
      Units.map (f.app V).hom.toMonoidHom (L.trans h) :=
    Units.ext (L.pullback_trans f h)
  rw [this, ← map_zpow]
  rfl

variable {L m}

/-- The **pullback** `f^* s` of a section `s` of `𝓛^m` over `W`: a section of `(f^* 𝓛)^m` over
`f⁻¹ W` with coefficients `f^♯ (s i)`. -/
def Sections.pullback {W : X.Opens} (s : L.Sections m W) :
    (L.pullback f).Sections m (f ⁻¹ᵁ W) :=
  Sections.mk (L := L.pullback f) (fun i => f.app (W ⊓ L.U i) (s.coeff i)) (by
    intro i j
    have e := congrArg (f.app _) (s.coeff_compat i j)
    rw [app_res, map_mul, app_res] at e
    refine e.trans ?_
    congr 1
    exact (L.pullback_trans_zpow m f _).symm)

@[simp]
lemma Sections.coeff_pullback {W : X.Opens} (s : L.Sections m W) (i : L.ι) :
    (s.pullback f).coeff i = f.app (W ⊓ L.U i) (s.coeff i) :=
  rfl

lemma Sections.nonvanishingLocus_pullback {W : X.Opens} (s : L.Sections m W) :
    (s.pullback f).nonvanishingLocus = f ⁻¹ᵁ s.nonvanishingLocus := by
  simp only [Sections.nonvanishingLocus, Scheme.preimage_basicOpen, Scheme.Hom.preimage_iSup]
  rfl

end PullbackSections

end LineBundleData

end

end DeJongAlterations.StableModification.Projectivity
