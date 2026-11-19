/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Scheme.BlowUp.AffineBlowUpAlgebra
public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.Glue.Global
import Hironaka.Scheme.BlowUp.Glue.GlobalCharts
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A composite of two blow-ups is a single blow-up: the descended centre

A morphism obtained by a finite succession of monoidal transformations is a single monoidal
transformation with a suitably chosen centre [Hir64, Ch. 0, §3, pp. 132–133]; [Sta, Tag 080B]:
for `b = IdealSheafData.blowUpπ I : X' ⟶ X` and an ideal sheaf `J'` on `X'`, the blow-up of `X'`
along `J'` followed by `b` is the blow-up of `X` along the single centre `I * K_m`, where `K_m` is
Hironaka's `J(m)`,

  `descendCenter I J' m := I ^ m ⊓ (J' * E ^ m).map b`,

the ideal sheaf of the functions `x ∈ I^m` whose pullback `b^*x` lies in `J'·E^m` (`E` the
exceptional ideal).  Hironaka's `J(m)` is a coherent ideal sheaf with `f₀⁻¹(J(m)) = f₀⁻¹(J₀)^m J₁`
for `m` large, and the single centre `D'` is defined by `J(m) J₀`.  This module holds the
definition and the generic parts of the argument; `Hironaka.Scheme.BlowUp.Composite.Main` proves
`K_m.comap b = J' * E^m` for `m` large and `Hironaka.Scheme.BlowUp.Composite.Iso` assembles the
isomorphism of blow-ups.

* `blowUp.exists_mul_isInvertible_iso` (the trivial factor): blowing up `J * L` with `L`
  invertible is blowing up `J` — the blow-up of a product centre
  (`Hironaka.Scheme.BlowUp.Glue.Product`) with the second blow-up trivial.
* `descendCenter`, `descendCenter_le_pow`, `comap_descendCenter_le` (the easy half): `K_m ≤ I^m`
  and `K_m.comap b ≤ J' * E^m`, the Galois connection `map ⊣ comap`.
* `mem_ideal_map_iff_of_le_iSup` (the pushforward criterion): for a quasi-compact `f : X ⟶ Y`, an
  affine open `U` of `Y` and affine opens `V i ⊆ f⁻¹U` covering `f⁻¹U`, `x ∈ (L.map f).ideal U`
  iff each `f.appLE U (V i) x ∈ L.ideal (V i)` — Mathlib's `Hom.ker_apply` for the kernel of
  `V(L) → Y`, `ker_subschemeι_app` on the affine pieces, and the sheaf condition of `V(L)`.
* `support_mul_descendCenter`: the support of `I * K_m` is `|Z| ∪ b(|Z'|)` once
  `K_m.comap b = J' * E^m`.
* `blowUp.isLocallyNoetherian`, `blowUp.isNoetherian`: the blow-up of a (locally) Noetherian
  scheme is (locally) Noetherian, through the Noetherianity of the chart rings `R[I/a]`.

The definition and these lemmas are also imported by the sequence modules
(`Hironaka.Scheme.BlowUpSequence.Triple`, `Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary`,
`Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral`) and by the worked examples.
-/

@[expose] public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData TopologicalSpace

universe u

section MulInvertible

variable {Y : Scheme.{u}} (J L : Y.IdealSheafData)

/-- The trivial factor ([Sta, Tag 080B]: a power of the exceptional ideal cuts out an
effective Cartier divisor, and blowing up an effective Cartier divisor changes nothing): blowing
up `J * L` with `L` invertible is blowing up `J`, canonically over `Y`.  The blow-up of `J * L` is
the blow-up of `B_J Y` along `L.comap (IdealSheafData.blowUpπ J)` (`blowUp.exists_mulIso`), which is
invertible (`blowUp.isInvertible_comap_of_isInvertible`), so that second blow-up map is an
isomorphism (`blowUp.isIso_π_of_isInvertible`). -/
theorem Scheme.IdealSheafData.blowUp.exists_mul_isInvertible_iso (hL : L.IsInvertible) :
    ∃ e : blowUp (J * L) ≅ blowUp J, e.hom ≫ blowUpπ J = blowUpπ (J * L) ∧
      ∀ ψ : blowUp (J * L) ⟶ blowUp J, ψ ≫ blowUpπ J = blowUpπ (J * L) → ψ = e.hom := by
  have hinv : (L.comap (blowUpπ J)).IsInvertible :=
    blowUp.isInvertible_comap_of_isInvertible J L hL
  have : IsIso (blowUpπ (L.comap (blowUpπ J))) := blowUp.isIso_π_of_isInvertible _ hinv
  obtain ⟨e₁, he₁, -⟩ := blowUp.exists_mulIso J L
  set e : blowUp (J * L) ≅ blowUp J :=
    e₁.symm ≪≫ asIso (blowUpπ (L.comap (blowUpπ J))) with he_def
  have he : e.hom ≫ blowUpπ J = blowUpπ (J * L) := by
    simp only [he_def, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [← he₁, Iso.inv_hom_id_assoc]
  refine ⟨e, he, fun ψ hψ => ?_⟩
  have h := blowUp.isInvertible_comap_π (J * L)
  rw [comap_mul] at h
  exact blowUp.hom_ext J (blowUpπ (J * L)) (IsInvertible.of_mul h).1 ψ e.hom hψ he

end MulInvertible

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (L : X.IdealSheafData)

/-- The pushforward criterion: for `f` quasi-compact, `U` an affine open of `Y` and affine opens
`V i ⊆ f⁻¹U` covering `f⁻¹U`, a function `x` on `U` lies in the pushforward `L.map f` iff its
pullback to every `V i` lies in `L`.  (`L.map f` is the kernel of `V(L) → Y`; on the affine pieces
that kernel is `L`, and a section of `𝒪_{V(L)}` vanishing on a cover vanishes.) -/
theorem mem_ideal_map_iff_of_le_iSup {ι : Type*} (U : Y.affineOpens) (V : ι → X.affineOpens)
    (hV : ∀ i, (V i).1 ≤ f ⁻¹ᵁ U.1) (hcov : f ⁻¹ᵁ U.1 ≤ ⨆ i, (V i).1) (x : Γ(Y, U)) :
    x ∈ (L.map f).ideal U ↔ ∀ i, f.appLE U.1 (V i).1 (hV i) x ∈ L.ideal (V i) := by
  -- naturality of `V(L) → X` along `V i ⊆ f⁻¹U`
  have key : ∀ i, L.subschemeι.app (V i).1 (f.appLE U.1 (V i).1 (hV i) x) =
      L.subscheme.presheaf.map ((Opens.map L.subschemeι.base).map (homOfLE (hV i))).op
        (L.subschemeι.app (f ⁻¹ᵁ U.1) (f.app U.1 x)) := by
    intro i
    have h := congrArg (fun φ : Γ(X, f ⁻¹ᵁ U.1) ⟶ Γ(L.subscheme, _) => φ.hom (f.app U.1 x))
      (L.subschemeι.naturality (homOfLE (hV i)).op)
    simp only [CommRingCat.comp_apply] at h
    exact h
  have hker : ∀ i, (f.appLE U.1 (V i).1 (hV i) x ∈ L.ideal (V i) ↔
      L.subschemeι.app (V i).1 (f.appLE U.1 (V i).1 (hV i) x) = 0) := fun i => by
    rw [← ker_subschemeι_app L (V i), RingHom.mem_ker]
  change x ∈ (L.subschemeι ≫ f).ker.ideal U ↔ _
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change L.subschemeι.app (f ⁻¹ᵁ U.1) (f.app U.1 x) = 0 ↔ _
  constructor
  · intro h i
    rw [hker, key, h, map_zero]
  · intro h
    refine L.subscheme.sheaf.eq_of_locally_eq' (fun i => L.subschemeι ⁻¹ᵁ (V i).1)
      (L.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U.1)) (fun i => homOfLE fun z hz => hV i hz) ?_ _ 0 fun i => ?_
    · intro z hz
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hz)
      exact Opens.mem_iSup.mpr ⟨i, hi⟩
    · exact ((key i).symm.trans ((hker i).mp (h i))).trans
        ((L.subscheme.sheaf.1.map (homOfLE fun z hz => hV i hz).op).hom.map_zero).symm

end Pushforward

section Descend

variable {X : Scheme.{u}} (I : X.IdealSheafData) (J' : (blowUp I).IdealSheafData)

/-- **Hironaka's descended centre** `J(m)` [Hir64, Ch. 0, §3, p. 133] in intrinsic form: the
functions of `I^m` whose pullback along the blow-up map lies in `J' · E^m`, `E` the exceptional
ideal.  On the chart of `a ∈ I(U)` the exceptional ideal is `(a)` with `a` a nonzerodivisor
(`affineBlowUp.comap_exceptionalIdeal_chart`), so `b^*x ∈ J'·(a^m)` iff `x/a^m ∈ J'` there:
`K_m = {x ∈ I^m : x/a^m ∈ J'_a on every chart}`. -/
noncomputable def descendCenter (m : ℕ) : X.IdealSheafData :=
  I ^ m ⊓ (J' * I.exceptionalDivisor ^ m).map (blowUpπ I)

/-- `K_m ≤ I^m`. -/
theorem descendCenter_le_pow (m : ℕ) : descendCenter I J' m ≤ I ^ m := inf_le_left

/-- The easy half of `K_m.comap b = J' * E^m`: `K_m.comap b ≤ J' * E^m` (the Galois connection
`map ⊣ comap`). -/
theorem comap_descendCenter_le (m : ℕ) :
    (descendCenter I J' m).comap (blowUpπ I) ≤ J' * I.exceptionalDivisor ^ m :=
  (comap_mono (blowUpπ I) inf_le_right).trans (comap_map_le _ _)

end Descend

section OffCenter

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Off the centre the blow-up map is a bijection on points (it is an isomorphism over the
complement of the centre, `Hironaka.Scheme.BlowUp.Glue.Trivial`): every `x ∉ V(I)` has exactly one
preimage. -/
theorem Scheme.IdealSheafData.blowUp.existsUnique_preimage_of_notMem_support {x : X}
    (hx : x ∉ I.support) :
    ∃! x' : blowUp I, blowUpπ I x' = x := by
  set W : X.Opens := I.support.compl with hW
  have hxW : x ∈ (W : Set X) := hx
  have := blowUp.isIso_π_restrict_compl_support I
  let e : (blowUpπ I ⁻¹ᵁ W : Scheme.{u}) ≃ₜ (W : Scheme.{u}) :=
    Scheme.homeoOfIso (asIso (blowUpπ I ∣_ W))
  have hez : ∀ z : (blowUpπ I ⁻¹ᵁ W : Scheme.{u}), (e z).1 = blowUpπ I z.1 := fun z =>
    morphismRestrict_base_coe (blowUpπ I) W z
  let p : (W : Scheme.{u}) := ⟨x, hxW⟩
  refine ⟨(e.symm p).1, ?_, fun y hy => ?_⟩
  · have h1 : (e (e.symm p)).1 = x := congrArg Subtype.val (e.apply_symm_apply p)
    exact (hez _).symm.trans h1
  · have hyW : y ∈ ((blowUpπ I ⁻¹ᵁ W : (blowUp I).Opens) : Set (blowUp I)) := by
      change blowUpπ I y ∈ W
      rw [hy]
      exact hxW
    let q : (blowUpπ I ⁻¹ᵁ W : Scheme.{u}) := ⟨y, hyW⟩
    have h2 : e q = p := Subtype.ext ((hez q).trans hy)
    have h3 := congrArg (fun z => (e.symm z).1) h2
    simp only [Homeomorph.symm_apply_apply] at h3
    exact h3

variable (J' : (blowUp I).IdealSheafData)

/-- **The support of the descended centre** [Sta, Tag 080B]: if `K_m.comap b = J' * E^m`, the
support of `I * K_m` is `|Z| ∪ b(|Z'|)` set-theoretically.  `V(I K_m) =
V(I) ∪ V(K_m)`; `b⁻¹V(K_m) = V(J') ∪ V(E^m)` with `V(E^m) ⊆ b⁻¹V(I)`; off `Z` every point has a
unique preimage, so `x ∉ Z` lies in `V(K_m)` iff its preimage lies in `Z'`. -/
theorem support_mul_descendCenter (m : ℕ)
    (hm : (descendCenter I J' m).comap (blowUpπ I) = J' * I.exceptionalDivisor ^ m) :
    ((I * descendCenter I J' m).support : Set X) =
      (I.support : Set X) ∪ blowUpπ I '' (J'.support : Set (blowUp I)) := by
  rw [support_mul, Closeds.coe_sup]
  have hpre : ((descendCenter I J' m).comap (blowUpπ I)).support =
      J'.support ⊔ (I.exceptionalDivisor ^ m).support := by
    rw [hm, support_mul]
  have hEm : ((I.exceptionalDivisor ^ m).support : Set (blowUp I)) ⊆
      blowUpπ I ⁻¹' (I.support : Set X) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [pow_zero, one_eq_top, support_top]
      exact Set.empty_subset _
    · rw [support_pow _ _ hm0.ne', Scheme.IdealSheafData.exceptionalDivisor, support_comap]
      exact le_rfl
  ext x
  constructor
  · rintro (hxI | hxK)
    · exact Or.inl hxI
    · by_cases hxI : x ∈ (I.support : Set X)
      · exact Or.inl hxI
      · right
        obtain ⟨x', hx', -⟩ := blowUp.existsUnique_preimage_of_notMem_support I hxI
        refine ⟨x', ?_, hx'⟩
        have h1 : x' ∈ ((descendCenter I J' m).comap (blowUpπ I)).support := by
          rw [support_comap]
          change blowUpπ I x' ∈ (descendCenter I J' m).support
          rw [hx']
          exact hxK
        rw [hpre] at h1
        have h1' : x' ∈ (J'.support : Set (blowUp I)) ∪
            ((I.exceptionalDivisor ^ m).support : Set (blowUp I)) := by
          rw [← Closeds.coe_sup]
          exact h1
        rcases h1' with h | h
        · exact h
        · exfalso
          apply hxI
          have h' : blowUpπ I x' ∈ (I.support : Set X) := hEm h
          rwa [hx'] at h'
  · rintro (hxI | ⟨x', hx', rfl⟩)
    · exact Or.inl hxI
    · by_cases hxI : blowUpπ I x' ∈ (I.support : Set X)
      · exact Or.inl hxI
      · right
        have h1 : x' ∈ ((descendCenter I J' m).comap (blowUpπ I)).support := by
          rw [hpre]
          exact (le_sup_left : J'.support ≤ _) hx'
        rw [support_comap] at h1
        exact h1

end OffCenter

section Noetherian

variable {R : Type u} [CommRing R]

/-- The affine blow-up algebra of `span s` is generated by the fractions `x/a`, `x ∈ s`: a fraction
`y/a` with `y = Σ rᵢ xᵢ` is `Σ rᵢ (xᵢ/a)`. -/
theorem affineBlowUpAlgebra_span_eq_adjoin (s : Set R) (a : R) :
    affineBlowUpAlgebra (Ideal.span s) a =
      Algebra.adjoin R ((fun x => Localization.mk x ⟨a, Submonoid.mem_powers a⟩) '' s) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction (p := fun x _ =>
      Localization.mk x ⟨a, Submonoid.mem_powers a⟩ ∈
        Algebra.adjoin R ((fun x => Localization.mk x ⟨a, Submonoid.mem_powers a⟩) '' s))
      ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    · rw [Localization.mk_zero]
      exact zero_mem _
    · intro y z _ _ hy hz
      rw [← Localization.add_mk_self]
      exact add_mem hy hz
    · intro r y _ hy
      rw [← Localization.smul_mk]
      exact Subalgebra.smul_mem _ hy r
  · exact Algebra.adjoin_mono (Set.image_mono Ideal.subset_span)

/-- The affine blow-up algebra of a finitely generated ideal is a finitely generated algebra. -/
theorem affineBlowUpAlgebra_fg {I : Ideal R} (hI : I.FG) (a : R) :
    (affineBlowUpAlgebra I a).FG := by
  obtain ⟨s, rfl⟩ := hI
  rw [affineBlowUpAlgebra_span_eq_adjoin]
  exact Subalgebra.fg_def.mpr ⟨_, s.finite_toSet.image _, rfl⟩

/-- Over a Noetherian ring the chart rings `R[I/a]` are Noetherian (Hilbert's basis theorem for
the finitely generated algebra `R[I/a]`). -/
theorem isNoetherianRing_affineBlowUpAlgebra [IsNoetherianRing R] (I : Ideal R) (a : R) :
    IsNoetherianRing (affineBlowUpAlgebra I a) :=
  isNoetherianRing_of_fg (affineBlowUpAlgebra_fg (IsNoetherian.noetherian I) a)

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The blow-up of a locally Noetherian scheme is locally Noetherian: its charts are the spectra
of the Noetherian rings `Γ(X, U)[I(U)/a]`. -/
theorem Scheme.IdealSheafData.blowUp.isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (blowUp I) := by
  refine (isLocallyNoetherian_iff_of_iSup_eq_top
    (S := fun p : (U : X.affineOpens) × I.ideal U =>
      ⟨(blowUp.chart I p.1 p.2).opensRange, isAffineOpen_opensRange _⟩) ?_).mpr fun p => ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨U, hU⟩ := exists_affineOpens_mem (blowUpπ I y)
    have hy : y ∈ ⋃ a : I.ideal U, Set.range (blowUp.chart I U a) := by
      rw [blowUp.iUnion_range_chart]
      exact hU
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
    exact Opens.mem_iSup.mpr ⟨⟨U, a⟩, ha⟩
  · have := IsLocallyNoetherian.component_noetherian p.1
    have h1 := isNoetherianRing_affineBlowUpAlgebra (I.ideal p.1) p.2
    change IsNoetherianRing Γ(blowUp I, (blowUp.chart I p.1 p.2).opensRange)
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact isNoetherianRing_of_ringEquiv _
      ((Scheme.ΓSpecIso (.of (affineBlowUpAlgebra (I.ideal p.1) p.2))).symm ≪≫
        ((blowUp.chart I p.1 p.2).appIso ⊤).symm).commRingCatIsoToRingEquiv

/-- The blow-up of a Noetherian scheme is Noetherian (locally Noetherian, and quasi-compact as the
source of the proper map `π` to a quasi-compact scheme). -/
theorem Scheme.IdealSheafData.blowUp.isNoetherian [IsNoetherian X] : IsNoetherian (blowUp I) := by
  have := blowUp.isLocallyNoetherian I
  have := blowUp.isProper_π I
  have : CompactSpace (blowUp I) := QuasiCompact.compactSpace_of_compactSpace (blowUpπ I)
  exact { }

end Noetherian

end AlgebraicGeometry
