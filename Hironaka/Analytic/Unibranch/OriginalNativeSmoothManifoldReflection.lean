import Hironaka.Analytic.Unibranch.OriginalNativeSmoothWholeWindow
import Hironaka.Resolution.HironakaSmoothSubmersionGlobalBlowupSubmersion

/-! Ordinary native smooth whole-manifold maps reflect genuine global submersions.
Blueprint first: `original-native-smooth-manifold-reflection.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothManifoldReflection
noncomputable section
open Hironaka Hironaka BlowupTowers
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaSmoothSubmersionGlobalBlowupSubmersion HironakaAuxiliaryGraphGeometry
  SourceReducedComplexSpace OriginalNativeModification OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeManifoldOpenImage OriginalNativeSmoothWholeWindow
open scoped ProductComplexManifold

section InverseCharts
variable {k : ℕ} {S T : Type}
  [TopologicalSpace S] [ChartedSpace (ComplexModel k) S] [IsComplexManifold k S]
  [TopologicalSpace T] [ChartedSpace (ComplexModel k) T] [IsComplexManifold k T]

/-- The genuine inverse chart of an actual open-image biholomorphism. -/
def inverseImageChart (R : Opens T) (D : S ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ R) (p : S) :
    OpenPartialHomeomorph T S :=
  (R.openPartialHomeomorphSubtypeCoe ⟨D p⟩).symm.trans D.symm.toHomeomorph.toOpenPartialHomeomorph

omit [IsComplexManifold k S] [IsComplexManifold k T] in
private theorem inverseImageChart_source (R : Opens T)
    (D : S ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ R) (p : S) :
    (inverseImageChart R D p).source = (R : Set T) := by simp [inverseImageChart]

omit [IsComplexManifold k S] [IsComplexManifold k T] in
private theorem inverseImageChart_apply (R : Opens T)
    (D : S ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ R) (p : S) (q : R) :
    inverseImageChart R D p q.val = D.symm q := by
  let a := R.openPartialHomeomorphSubtypeCoe ⟨D p⟩
  change D.symm (a.symm q.val) = D.symm q
  exact congrArg D.symm (a.left_inv (mem_univ q))

omit [IsComplexManifold k S] [IsComplexManifold k T] in
private theorem inverseImageChart_symm_apply (R : Opens T)
    (D : S ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ R) (p q : S) :
    (inverseImageChart R D p).symm q = (D q).val := rfl

omit [IsComplexManifold k S] [IsComplexManifold k T] in
theorem inverseImageChart_holomorphic (R : Opens T)
    (D : S ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ R) (p : S) :
    ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (inverseImageChart R D p)
        (inverseImageChart R D p).source ∧
      ContMDiffOn 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞ (inverseImageChart R D p).symm
        (inverseImageChart R D p).target := by
  have heq : (fun q : R => inverseImageChart R D p q.val) = D.symm :=
    funext (inverseImageChart_apply R D p)
  have hrestrict : ContMDiff 𝓘(ℂ,ComplexModel k) 𝓘(ℂ,ComplexModel k) ∞
      (fun q : R => inverseImageChart R D p q.val) := heq.symm ▸ D.symm.contMDiff
  constructor
  · intro q hq
    have hqR : q ∈ R := (Set.ext_iff.mp (inverseImageChart_source R D p) q).mp hq
    exact (contMDiffAt_subtype_iff.mp (hrestrict ⟨q,hqR⟩)).contMDiffWithinAt
  · have heqInv : ((inverseImageChart R D p).symm : S → T) = (Subtype.val : R → T) ∘ D :=
      funext (inverseImageChart_symm_apply R D p)
    exact (heqInv.symm ▸ (contMDiff_subtype_val.comp D.contMDiff)).contMDiffOn

end InverseCharts

/-- The actual first projection on an open product has the literal fixed free complement. -/
theorem windowProjection_fixedComplement {d r : ℕ} {A : Type}
    [TopologicalSpace A] [ChartedSpace (ComplexModel d) A] [IsComplexManifold d A]
    (W : Opens (A × ComplexModel r)) :
    Manifold.IsSubmersionOfComplement (ComplexModel r)
      𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel d) ∞ (fun w : W => w.val.1) := by
  intro w
  let b := W.openPartialHomeomorphSubtypeCoe ⟨w⟩
  have hb : ContMDiffOn 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel (d+r)) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel (d+r)) ∞ b.symm b.target := by
    constructor
    · exact contMDiff_subtype_val.contMDiffOn
    · have hval : ContMDiffOn 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel (d+r)) ∞
          ((Subtype.val : W → A × ComplexModel r) ∘ b.symm) b.target := by
        apply contMDiffOn_id.congr
        intro z hz
        exact b.right_inv hz
      intro z hz
      exact (ContMDiffWithinAt.subtypeVal_comp_iff W b.symm b.target z).mp (hval z hz)
  have hproj : ContMDiff 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel d) ∞ (fun w : W => w.val.1) :=
    (ProductComplexManifold.contMDiff_fst (n := d) (m := r) (X := A) (Y := ComplexModel r)).comp
      contMDiff_subtype_val
  exact isSubmersionAtOfComplement_local_square
    (X := CMfd.of (n := d) A) (X' := CMfd.of (n := d) A)
    (Y := CMfd.of (n := d+r) (A × ComplexModel r)) (Y' := CMfd.of (n := d+r) W)
    (OpenPartialHomeomorph.refl A) b ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩ hb
    continuous_fst (isSubmersionOfComplement_fst (n := d) (m := r) (X := A) (Y := ComplexModel r) (b w))
    hproj.continuous.continuousAt
    (mem_univ _) (fun _ _ => mem_univ _) (fun _ _ => rfl)

section ProductSquares
variable {m n d r : ℕ} {M N A : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  [TopologicalSpace A] [ChartedSpace (ComplexModel d) A] [IsComplexManifold d A]

/-- True native whole-product OI squares reflect actual fixed-complement submersion charts. -/
theorem native_product_square_submersionAt (W : Opens (A × ComplexModel r))
    (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (i : wholeModel (n := d+r) W ⟶ wholeModel (n := m) M)
    (j : wholeModel (n := d) A ⟶ wholeModel (n := n) N)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hsq : i ≫ F = nativeMorphism (n := d+r) (m := d) (M := W) (N := A)
      ((ProductComplexManifold.contMDiff_fst (n := d) (m := r) (X := A) (Y := ComplexModel r)).comp
        contMDiff_subtype_val) ≫ j) (w : W) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel (m-n))
      𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (pointMap F) (pointMap i w) := by
  have hm := open_dimension_eq i hi w
  have hn := open_dimension_eq j hj w.val.1
  subst m
  subst n
  obtain ⟨R,Di,hDi⟩ := exists_open_image_diffeomorph i hi
  obtain ⟨P,Dj,hDj⟩ := exists_open_image_diffeomorph j hj
  let a := inverseImageChart P Dj w.val.1
  let b := inverseImageChart R Di w
  have hpoint (v : W) : pointMap F (pointMap i v) = pointMap j v.val.1 :=
    congrArg (fun h => (h.hom.left.base ⟨v,mem_univ _⟩).val) hsq
  have himage (q : M) (hq : q ∈ b.source) :
      pointMap F q = (Dj (b q).val.1).val := by
    have hieq : pointMap i (b q) = q := (hDi (b q)).symm.trans
      ((inverseImageChart_symm_apply R Di w (b q)).symm.trans (b.left_inv hq))
    exact ((congrArg (pointMap F) hieq).symm.trans (hpoint (b q))).trans (hDj (b q).val.1).symm
  have hpR : pointMap i w ∈ R := Eq.mp (congrArg (fun q => q ∈ R) (hDi w)) (Di w).property
  have hp : pointMap i w ∈ b.source :=
    (Set.ext_iff.mp (inverseImageChart_source R Di w) _).mpr hpR
  have hsource : b.source ⊆ pointMap F ⁻¹' a.source := by
    intro q hq
    have hmem : pointMap F q ∈ P := Eq.mpr
      (congrArg (fun z => z ∈ P) (himage q hq)) (Dj (b q).val.1).property
    exact (Set.ext_iff.mp (inverseImageChart_source P Dj w.val.1) _).mpr hmem
  have hsquare : ∀ q ∈ b.source, a (pointMap F q) = (b q).val.1 := by
    intro q hq
    exact (congrArg a (himage q hq)).trans
      ((inverseImageChart_apply P Dj w.val.1 (Dj (b q).val.1)).trans (Dj.symm_apply_apply _))
  have hproj : ContMDiff 𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel d) ∞ (fun v : W => v.val.1) :=
    (ProductComplexManifold.contMDiff_fst (n := d) (m := r) (X := A) (Y := ComplexModel r)).comp
      contMDiff_subtype_val
  have hlocal := isSubmersionAtOfComplement_local_square
    (X := CMfd.of (n := d) A) (X' := CMfd.of (n := d) N)
    (Y := CMfd.of (n := d+r) W) (Y' := CMfd.of (n := d+r) M)
    a b (inverseImageChart_holomorphic P Dj w.val.1) (inverseImageChart_holomorphic R Di w)
    hproj.continuous (windowProjection_fixedComplement W (b (pointMap i w)))
    (pointMap_holomorphic F).continuous.continuousAt hp hsource hsquare
  have hdim : d+r-d = r := by omega
  change Manifold.IsSubmersionAtOfComplement (ComplexModel (d+r-d))
    𝓘(ℂ,ComplexModel (d+r)) 𝓘(ℂ,ComplexModel d) ∞ (pointMap F) (pointMap i w)
  rw [hdim]
  exact hlocal

end ProductSquares

section SmoothMaps
variable {m n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- Ordinary native smoothness internally gives a GLOBAL genuine submersion on the SAME original points. -/
theorem pointMap_isSubmersion (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : IsSmoothMorphism F) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (pointMap F) := by
  refine ⟨ComplexModel (m-n),inferInstance,inferInstance,?_⟩
  intro x
  let sx : (wholeModel (n := m) M).obj.left := ⟨x,mem_univ x⟩
  have hreg : F.hom.left.base sx ∈ intrinsicRegularLocus (wholeModel (n := n) N).obj :=
    isSmooth_wholeModel (M := N) (F.hom.left.base sx)
  obtain ⟨w⟩ := exists_whole_window F sx (hF sx) hreg
  have hsub := native_product_square_submersionAt w.window F w.sourceMap w.targetMap
    w.source_open w.target_open w.square w.sourcePoint
  have hbase : pointMap w.sourceMap w.sourcePoint = x := congrArg Subtype.val w.point
  exact Eq.mp (congrArg (fun z => Manifold.IsSubmersionAtOfComplement (ComplexModel (m-n))
    𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ (pointMap F) z) hbase) hsub

/-- The recovered submersion induces the ENTIRE SAME original native morphism. -/
theorem exists_global_submersion (F : wholeModel (n := m) M ⟶ wholeModel (n := n) N)
    (hF : IsSmoothMorphism F) :
    ∃ (b : M → N) (hb : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ b),
      nativeMorphism hb.contMDiff = F ∧ ∀ x, b x = pointMap F x := by
  exact ⟨pointMap F,pointMap_isSubmersion F hF,nativeMorphism_pointMap F,fun _ => rfl⟩

end SmoothMaps

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothManifoldReflection
