import Hironaka.Resolution.HironakaG10ChowArtinReesCentre
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback

/-!
# Geometric strict points force proper algebraic strict ideals

Actual stalk representatives of the original vanishing ideal and openness of
unit-germ loci suffice. No full sheaf/radical correspondence or reduced-source
certificate is assumed. The exceptional equation is a section which is a unit
off the specified exceptional set; the ordinary blowup consumer constructs it.

Blueprint: `hironaka-g10-geometric-strict-ideal.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.HironakaG10GeometricStrictIdeal

open HironakaG10ChowArtinReesCentre HironakaIntrinsicReducedCentreIdealSheaf
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenPullback
  HironakaIntrinsicReducedCentreOpenSections

noncomputable section

universe u

variable {X Y : LocallyRingedSpace.{u}}

/-- A divided germ is a nonunit at every point of the geometric strict
closure, provided its numerator actually vanishes on the original subset. -/
theorem divided_germ_mem_maximal_of_mem_closure
    (σ : Y ⟶ X) (W : Set X) (E : Set Y) (x : Y)
    (hx : x ∈ closure (σ.base ⁻¹' W \ E))
    (U : Opens Y.toTopCat) (hxU : x ∈ U) (a : (Y.presheaf.obj (op U)).carrier)
    (haunit : ∀ (y : Y) (hy : y ∈ U), y ∉ E →
      IsUnit (Y.presheaf.germ U y hy a))
    (k : ℕ) (h : (X.presheaf.stalk (σ.base x)).carrier)
    (hh : h ∈ intrinsicCentreStalkRange X W (σ.base x))
    (b : (Y.presheaf.stalk x).carrier)
    (heq : σ.stalkMap x h = (Y.presheaf.germ U x hxU a) ^ k * b) :
    b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x).carrier := by
  apply (IsLocalRing.mem_maximalIdeal _).mpr
  intro hbunit
  obtain ⟨m,hm⟩ := hh
  obtain ⟨V,hxV,t,rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (intrinsicReducedCentreIdealModule X W).val.presheaf m
  have ht : X.presheaf.germ V (σ.base x) hxV t.val = h :=
    (intrinsicReducedCentreStalkInclusion_germ X W (σ.base x) V hxV t).symm.trans hm
  obtain ⟨Vb,hxVb,s,hs⟩ := Y.presheaf.exists_germ_eq b
  let Vh : Opens Y.toTopCat := (Opens.map σ.base).obj V
  let tY : (Y.presheaf.obj (op Vh)).carrier := σ.c.app (op V) t.val
  have hxVh : x ∈ Vh := hxV
  have htY : Y.presheaf.germ Vh x hxVh tY = σ.stalkMap x h :=
    (LocallyRingedSpace.stalkMap_germ_apply σ V x hxV t.val).symm.trans
      (congrArg (σ.stalkMap x) ht)
  let O : Opens Y.toTopCat := (U ⊓ Vb) ⊓ Vh
  have hxO : x ∈ O := ⟨⟨hxU,hxVb⟩,hxVh⟩
  let iU : O ⟶ U := homOfLE (fun _ hy => hy.1.1)
  let iB : O ⟶ Vb := homOfLE (fun _ hy => hy.1.2)
  let iH : O ⟶ Vh := homOfLE (fun _ hy => hy.2)
  have hO : Y.presheaf.germ O x hxO (Y.presheaf.map iH.op tY) =
      Y.presheaf.germ O x hxO
        ((Y.presheaf.map iU.op a) ^ k * Y.presheaf.map iB.op s) := by
    rw [map_mul,map_pow,Y.presheaf.germ_res_apply iH x hxO tY,
      Y.presheaf.germ_res_apply iU x hxO a,Y.presheaf.germ_res_apply iB x hxO s,htY,hs]
    exact heq
  obtain ⟨N,hxN,iN,jN,hN⟩ := Y.presheaf.germ_eq x hxO hxO _ _ hO
  have hij : jN = iN := Subsingleton.elim _ _
  rw [hij] at hN
  let T : Opens Y.toTopCat := N ⊓ Y.toRingedSpace.basicOpen s
  have hxT : x ∈ T := ⟨hxN,(Y.toRingedSpace.mem_basicOpen s x hxVb).mpr
    (hs.symm ▸ hbunit)⟩
  obtain ⟨y,hyT,hyW,hyE⟩ := mem_closure_iff.mp hx (T : Set Y) T.isOpen hxT
  have hyO : y ∈ O := leOfHom iN hyT.1
  have hyU : y ∈ U := leOfHom iU hyO
  have hyB : y ∈ Vb := leOfHom iB hyO
  have hyH : σ.base y ∈ V := leOfHom iH hyO
  have hrelation := congrArg (Y.presheaf.germ N y hyT.1) hN
  simp only [map_mul,map_pow,Y.presheaf.germ_res_apply] at hrelation
  have hrelation' : σ.stalkMap y (X.presheaf.germ V (σ.base y) hyH t.val) =
      (Y.presheaf.germ U y hyU a) ^ k * Y.presheaf.germ Vb y hyB s := by
    change Y.presheaf.germ Vh y hyH tY = _ at hrelation
    exact (LocallyRingedSpace.stalkMap_germ_apply σ V y hyH t.val).trans hrelation
  have hsource : X.presheaf.germ V (σ.base y) hyH t.val ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (σ.base y)).carrier := t.property _ hyH hyW
  have hpulled := (stalkMap_mem_maximalIdeal_iff σ y _).mpr hsource
  have hunitA := haunit y hyU hyE
  have hunitB := (Y.toRingedSpace.mem_basicOpen s y hyB).mp hyT.2
  have hunit : IsUnit (σ.stalkMap y (X.presheaf.germ V (σ.base y) hyH t.val)) :=
    hrelation'.symm ▸ (hunitA.pow k).mul hunitB
  exact (IsLocalRing.mem_maximalIdeal _).mp hpulled hunit

/-- Every algebraic strict-ideal generator vanishes at a geometric strict
point, without asserting the reverse geometric correspondence. -/
theorem strictIdeal_le_maximal_of_mem_closure
    (σ : Y ⟶ X) (W : Set X) (E : Set Y) (x : Y)
    (hx : x ∈ closure (σ.base ⁻¹' W \ E))
    (U : Opens Y.toTopCat) (hxU : x ∈ U) (a : (Y.presheaf.obj (op U)).carrier)
    (haunit : ∀ (y : Y) (hy : y ∈ U), y ∉ E →
      IsUnit (Y.presheaf.germ U y hy a))
    (I D : Ideal (X.presheaf.stalk (σ.base x)).carrier)
    (hI : I ≤ intrinsicCentreStalkRange X W (σ.base x)) :
    strictIdeal (σ.stalkMap x).hom I D (Y.presheaf.germ U x hxU a) ≤
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x).carrier := by
  apply Ideal.span_le.mpr
  rintro b ⟨k,h,hh,heq⟩
  exact divided_germ_mem_maximal_of_mem_closure σ W E x hx U hxU a haunit k h
    (hI (Ideal.mem_inf.mp hh).1) b heq

end

end Hironaka.HironakaG10GeometricStrictIdeal
