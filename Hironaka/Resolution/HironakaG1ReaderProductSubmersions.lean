import Hironaka.Resolution.HironakaG1RelativeReaderWindow
import Hironaka.Resolution.HironakaG1RelativeBoundaryProjections
import Hironaka.Resolution.HironakaG1SNCReaderNormalization
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
import Hironaka.Resolution.HironakaSmoothSubmersionMonomialChartPullback

/-! Exact product charts for the two projections of the relative reader window. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG1ReaderProductSubmersions
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates
  HironakaG1RelativeBoundaryProjections HironakaG1SNCReaderNormalization
  HironakaSmoothSubmersionComposition HironakaSmoothSubmersionMonomialChartPullback

/-- Identifies the coordinate function block with its genuine Euclidean model. -/
def euclideanBlock (d : ℕ) : Block d ≃L[ℂ] ComplexModel d :=
  ({ toFun := WithLp.toLp 2
     invFun := WithLp.ofLp
     left_inv := WithLp.ofLp_toLp 2
     right_inv := WithLp.toLp_ofLp 2
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Block d ≃ₗ[ℂ] ComplexModel d).toContinuousLinearEquiv

/-- Two function blocks joined in literal first/complement order. -/
def joinBlock (r d : ℕ) : (Block r × Block d) ≃L[ℂ] ComplexModel (r+d) :=
  ((euclideanBlock r).prodCongr (euclideanBlock d)).trans (splitCoordinates r d).symm

/-- Source product coordinates, with the right inactive and ratio block
in the Euclidean complement. -/
def sourceProduct (r a b : ℕ) :
    Ambient r a b ≃L[ℂ] (ComplexModel (r+a) × ComplexModel (r+b)) :=
  (({
    toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
    invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop } :
    Ambient r a b ≃L[ℂ] ((Block r × Block a) × (Block r × Block b)))).trans
    ((joinBlock r a).prodCongr (joinBlock r b))

/-- Target product coordinates, used after scaling the active block. -/
def targetProduct (r a b : ℕ) :
    Ambient r a b ≃L[ℂ] (ComplexModel (r+b) × ComplexModel (r+a)) :=
  (({
    toFun p := ((p.1.1,p.2.2),(p.1.2,p.2.1))
    invFun p := ((p.1.1,p.2.1),(p.2.2,p.1.2))
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop } :
    Ambient r a b ≃L[ℂ] ((Block r × Block b) × (Block r × Block a)))).trans
    ((joinBlock r b).prodCongr (joinBlock r a))

/-- Explicit Euclidean model for the common ambient dimension. -/
def ambientEuclidean (r a b : ℕ) :
    Ambient r a b ≃L[ℂ] ComplexModel ((r+a)+(r+b)) :=
  (sourceProduct r a b).trans (splitCoordinates (r+a) (r+b)).symm

/-- The first literal projection is the standard product projection
in the source product coordinates. -/
theorem source_product_fst (r a b : ℕ) (x : Ambient r a b) :
    (sourceProduct r a b x).1 = joinBlock r a (leftProjection r a b x) := rfl

/-- The second literal projection is the standard product projection
after the genuine scaling chart and the target index reordering. -/
theorem target_product_fst (r a b : ℕ) (x : Ambient r a b) :
    (targetProduct r a b (scalingChart r a b x)).1 = joinBlock r b (rightProjection r a b x) := rfl

section Generic
variable {P K : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

private theorem opens_inverse_holo (U : Opens P) (hU : Nonempty U) :
    ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,P) ∞
      (U.openPartialHomeomorphSubtypeCoe hU).symm (U.openPartialHomeomorphSubtypeCoe hU).target := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  have hval : ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,P) ∞
      ((Subtype.val : U → P) ∘ e.symm) e.target :=
    contMDiffOn_id.congr (fun _ hx => e.right_inv hx)
  intro x hx
  exact (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp (hval x hx)

private theorem window_chart_maximal (U : Opens P) (hU : Nonempty U) (e : OpenPartialHomeomorph P P)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,P) ∞ P) :
    (U.openPartialHomeomorphSubtypeCoe hU).trans e ∈
      IsManifold.maximalAtlas 𝓘(ℂ,P) ∞ U := by
  let v := U.openPartialHomeomorphSubtypeCoe hU
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,P) ∞
      (e ∘ (Subtype.val : U → P)) (v.source ∩ v ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      contMDiff_subtype_val.contMDiffOn (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,P) ∞
      (v.symm ∘ e.symm) (e.target ∩ e.symm ⁻¹' v.target)
    exact (opens_inverse_holo U hU).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ hz => hz.2)

/-- A product formula on a genuine model chart proves submersion for the
original map from any open restriction of that chart. -/
theorem window_product_isSubmersion {n : ℕ} {M : CMfd.{0} n}
    (U : Opens P) (d : OpenPartialHomeomorph P P)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,P) ∞ P)
    (hU : (U : Set P) ⊆ d.source)
    (c : OpenPartialHomeomorph M (ComplexModel n))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ,ComplexModel n) ∞ M)
    (E : P ≃L[ℂ] (ComplexModel n × K)) (f : U → M)
    (hf : ∀ x, f x ∈ c.source) (hcoord : ∀ x, c (f x) = (E (d x.val)).1) :
    Manifold.IsSubmersionOfComplement K 𝓘(ℂ,P) 𝓘(ℂ,ComplexModel n) ∞ f := by
  intro x
  let dom := (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).trans d
  have hx (y : U) : y ∈ dom.source := ⟨mem_univ _, hU y.property⟩
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts E dom c (hx x) (hf x)
    (window_chart_maximal U ⟨x⟩ d hd) hc (fun y _ => hf y)
  intro w hw
  have hw' : w ∈ dom.target := by simpa [mfld_simps] using hw
  have he := dom.right_inv hw'
  change d (dom.symm w).val = w at he
  change c (f (dom.symm w)) = _
  rw [hcoord, he]
  rfl

end Generic

section Reader
variable {r a b n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
  {p : M} {q : N}
  (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p))
  (Ψ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) q q))
  (hΦ : Φ.source ⊆ (chartAt (ComplexModel n) p).target)
  (hΨ : Ψ.source ⊆ (chartAt (ComplexModel m) q).target)
  (σ : Fin (r+a) ≃ Fin n) (τ : Fin (r+b) ≃ Fin m)
  (U : Opens (Ambient r a b))

/-- Original left reader applied to the concrete joined projection. -/
def leftReader (h : ∀ x : U, joinBlock r a (leftProjection r a b x.val) ∈ readerTarget Φ σ)
    (x : U) : M :=
  (readerDiffeomorph Φ hΦ σ).symm ⟨_, h x⟩ |>.val

/-- Original right reader applied after scaling in the concrete ratio chart. -/
def rightReader (h : ∀ x : U, joinBlock r b (rightProjection r a b x.val) ∈ readerTarget Ψ τ)
    (x : U) : N :=
  (readerDiffeomorph Ψ hΨ τ).symm ⟨_, h x⟩ |>.val

/-- The literal left reader map has Euclidean complementary dimension r+b. -/
theorem leftReader_isSubmersion
    (h : ∀ x : U, joinBlock r a (leftProjection r a b x.val) ∈ readerTarget Φ σ) :
    Manifold.IsSubmersionOfComplement (ComplexModel (r+b))
      𝓘(ℂ,Ambient r a b) 𝓘(ℂ,ComplexModel n) ∞ (leftReader Φ hΦ σ U h) := by
  let c := holomorphicChart p Φ
  let E := (sourceProduct r a b).trans
    ((coordinateReindex σ).symm.prodCongr (ContinuousLinearEquiv.refl ℂ (ComplexModel (r+b))))
  have hd : OpenPartialHomeomorph.refl (Ambient r a b) ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Ambient r a b) ∞ (Ambient r a b) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  apply window_product_isSubmersion U (OpenPartialHomeomorph.refl _) hd (subset_univ _)
    c (holomorphicChart_mem_maximalAtlas p Φ hΦ) E
  · intro x
    exact ((readerDiffeomorph Φ hΦ σ).symm ⟨_, h x⟩).property
  · intro x
    let y : readerTarget Φ σ := ⟨_, h x⟩
    let z := (readerDiffeomorph Φ hΦ σ).symm y
    have hz := congrArg Subtype.val ((readerDiffeomorph Φ hΦ σ).apply_symm_apply y)
    change coordinateReindex σ (c z.val) = joinBlock r a (leftProjection r a b x.val) at hz
    change c z.val = (coordinateReindex σ).symm (joinBlock r a (leftProjection r a b x.val))
    rw [← hz, ContinuousLinearEquiv.symm_apply_apply]

/-- The literal right reader map has Euclidean complementary dimension r+a. -/
theorem rightReader_isSubmersion (hU : (U : Set (Ambient r a b)) ⊆ unitLocus r a b)
    (h : ∀ x : U, joinBlock r b (rightProjection r a b x.val) ∈ readerTarget Ψ τ) :
    Manifold.IsSubmersionOfComplement (ComplexModel (r+a))
      𝓘(ℂ,Ambient r a b) 𝓘(ℂ,ComplexModel m) ∞ (rightReader Ψ hΨ τ U h) := by
  let c := holomorphicChart q Ψ
  let E := (targetProduct r a b).trans
    ((coordinateReindex τ).symm.prodCongr (ContinuousLinearEquiv.refl ℂ (ComplexModel (r+a))))
  apply window_product_isSubmersion U (scalingChart r a b) (scalingChart_mem_maximalAtlas r a b) hU
    c (holomorphicChart_mem_maximalAtlas q Ψ hΨ) E
  · intro x
    exact ((readerDiffeomorph Ψ hΨ τ).symm ⟨_, h x⟩).property
  · intro x
    let y : readerTarget Ψ τ := ⟨_, h x⟩
    let z := (readerDiffeomorph Ψ hΨ τ).symm y
    have hz := congrArg Subtype.val ((readerDiffeomorph Ψ hΨ τ).apply_symm_apply y)
    change coordinateReindex τ (c z.val) = joinBlock r b (rightProjection r a b x.val) at hz
    change c z.val = (coordinateReindex τ).symm (joinBlock r b (rightProjection r a b x.val))
    rw [← hz, ContinuousLinearEquiv.symm_apply_apply]

end Reader
section EuclideanTransport
variable {P Q K : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q] [NormedAddCommGroup K] [NormedSpace ℂ K]

private theorem linear_domChart_maximal {U : Opens P} {V : Opens Q}
    (a : V ≃ₘ⟮𝓘(ℂ,Q), 𝓘(ℂ,P)⟯ U) (L : Q ≃L[ℂ] P)
    (d : OpenPartialHomeomorph U P) (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,P) ∞ U) :
    (a.toHomeomorph.toOpenPartialHomeomorph.trans d).trans
       L.symm.toHomeomorph.toOpenPartialHomeomorph ∈
         IsManifold.maximalAtlas 𝓘(ℂ,Q) ∞ V := by
  let v := a.toHomeomorph.toOpenPartialHomeomorph.trans d
  have hv : ContMDiffOn 𝓘(ℂ,Q) 𝓘(ℂ,P) ∞ v v.source := by
    change ContMDiffOn 𝓘(ℂ,Q) 𝓘(ℂ,P) ∞ (d ∘ a) (univ ∩ a ⁻¹' d.source)
    exact (contMDiffOn_of_mem_maximalAtlas hd).comp
      a.contMDiff.contMDiffOn (fun _ hz => hz.2)
  have hvi : ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,Q) ∞ v.symm v.target := by
    change ContMDiffOn 𝓘(ℂ,P) 𝓘(ℂ,Q) ∞ (a.symm ∘ d.symm) (d.target ∩ d.symm ⁻¹' univ)
    exact a.symm.contMDiff.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas hd).mono inter_subset_left)
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ,Q) 𝓘(ℂ,Q) ∞ (L.symm ∘ v) (v.source ∩ v ⁻¹' univ)
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn (hv.mono inter_subset_left)
  · change ContMDiffOn 𝓘(ℂ,Q) 𝓘(ℂ,Q) ∞ (v.symm ∘ L) (univ ∩ L ⁻¹' v.target)
    exact hvi.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)

/-- Reparameterizing the source by a genuine open-model diffeomorphism
and linear model equivalence preserves the explicit Euclidean complement. -/
theorem product_submersion_reparameterize {n : ℕ} {M : CMfd.{0} n}
    {U : Opens P} {V : Opens Q} {f : U → M}
    (a : V ≃ₘ⟮𝓘(ℂ,Q), 𝓘(ℂ,P)⟯ U) (L : Q ≃L[ℂ] P)
    (hf : Manifold.IsSubmersionOfComplement K 𝓘(ℂ,P) 𝓘(ℂ,ComplexModel n) ∞ f) :
    Manifold.IsSubmersionOfComplement K 𝓘(ℂ,Q) 𝓘(ℂ,ComplexModel n) ∞ (f ∘ a) := by
  intro x
  let h := hf (a x)
  let d := (a.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart).trans
    L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hx : x ∈ d.source := ⟨⟨mem_univ _, h.mem_domChart_source⟩, mem_univ _⟩
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (L.trans h.equiv) d h.codChart
    hx h.mem_codChart_source (linear_domChart_maximal a L h.domChart h.domChart_mem_maximalAtlas)
    h.codChart_mem_maximalAtlas
  · intro y hy
    exact h.source_subset_preimage_source hy.1.2
  · intro w hw
    have hw' : w ∈ d.target := by simpa [mfld_simps] using hw
    have hwD : L w ∈ h.domChart.target := hw'.2.1
    have hTarget : L w ∈ (h.domChart.extend 𝓘(ℂ,P)).target := by
      simpa [mfld_simps] using hwD
    have hEq := h.writtenInCharts hTarget
    change h.codChart (f (h.domChart.symm (L w))) = (h.equiv (L w)).1 at hEq
    change h.codChart (f (a (a.symm (h.domChart.symm (L w))))) = (h.equiv (L w)).1
    rwa [a.apply_symm_apply]

/-- Transport an actual open through an explicit linear equivalence. -/
def linearImageOpen (L : P ≃L[ℂ] Q) (U : Opens P) : Opens Q :=
  ⟨L.symm ⁻¹' (U : Set P), U.isOpen.preimage L.symm.continuous⟩

/-- The exact linear reparameterization between the source window and its
genuine image open, in both original manifold structures. -/
def linearImageWindow (L : P ≃L[ℂ] Q) (U : Opens P) :
    linearImageOpen L U ≃ₘ⟮𝓘(ℂ,Q), 𝓘(ℂ,P)⟯ U where
  toFun x := ⟨L.symm x.val, x.property⟩
  invFun x := ⟨L x.val, by change L.symm (L x.val) ∈ U; rw [L.symm_apply_apply]; exact x.property⟩
  left_inv x := Subtype.ext (L.apply_symm_apply x.val)
  right_inv x := Subtype.ext (L.symm_apply_apply x.val)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff U _).mp
    (L.symm.contDiff.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (linearImageOpen L U) _).mp
    (L.contDiff.contMDiff.comp contMDiff_subtype_val)

end EuclideanTransport

open HironakaG1RelativeReaderWindow

section ExactReader
variable {n m : ℕ} {M : CMfd.{0} n} {N : CMfd.{0} m}
  {p : M} {q : N} {E : List (Set M)} {F : List (Set N)}
  {τ : Fin E.length ≃ Fin F.length}
  (R : RelativeReaders p q E F τ)

/-- The actual reader window's first map is a submersion with the stated
Euclidean complementary dimension. -/
theorem firstReaderMap_isSubmersionOfComplement :
    Manifold.IsSubmersionOfComplement (ComplexModel (R.r+R.b))
      𝓘(ℂ,Ambient R.r R.a R.b) 𝓘(ℂ,ComplexModel n) ∞ (firstReaderMap R) := by
  have h (x : readerUnitWindow R) :
      joinBlock R.r R.a (leftProjection R.r R.a R.b x.val) ∈ R.sourceCoordinateOpen := x.property.1.2
  exact leftReader_isSubmersion R.Φ₁ R.hsrc₁ R.σ₁ (readerUnitWindow R) h

/-- The actual reader window's second map is a submersion in the
nonzero-ratio scaling chart, with the stated Euclidean complement. -/
theorem secondReaderMap_isSubmersionOfComplement :
    Manifold.IsSubmersionOfComplement (ComplexModel (R.r+R.a))
      𝓘(ℂ,Ambient R.r R.a R.b) 𝓘(ℂ,ComplexModel m) ∞ (secondReaderMap R) := by
  have hU : (readerUnitWindow R : Set (Ambient R.r R.a R.b)) ⊆ unitLocus R.r R.a R.b :=
    fun _ hx => hx.1.1
  have h (x : readerUnitWindow R) :
      joinBlock R.r R.b (rightProjection R.r R.a R.b x.val) ∈ R.targetCoordinateOpen := x.property.2
  exact rightReader_isSubmersion R.Φ₂ R.hsrc₂ R.σ₂ (readerUnitWindow R) hU h

/-- The same reader window, in a single finite Euclidean complex model. -/
def euclideanReaderWindow : Opens (ComplexModel ((R.r+R.a)+(R.r+R.b))) :=
  linearImageOpen (ambientEuclidean R.r R.a R.b) (readerUnitWindow R)

/-- The original ratio-window points and their Euclidean coordinates are
identified by an actual biholomorphism. -/
def euclideanReaderChange :
    euclideanReaderWindow R ≃ₘ⟮𝓘(ℂ, ComplexModel ((R.r+R.a)+(R.r+R.b))),
      𝓘(ℂ, Ambient R.r R.a R.b)⟯ readerUnitWindow R :=
  linearImageWindow (ambientEuclidean R.r R.a R.b) (readerUnitWindow R)

/-- Both original reader maps are simultaneous submersions from the same
genuine Euclidean model open. -/
theorem euclidean_reader_maps_submersions :
    Manifold.IsSubmersionOfComplement (ComplexModel (R.r+R.b))
      𝓘(ℂ,ComplexModel ((R.r+R.a)+(R.r+R.b))) 𝓘(ℂ,ComplexModel n) ∞
        (firstReaderMap R ∘ euclideanReaderChange R) ∧
    Manifold.IsSubmersionOfComplement (ComplexModel (R.r+R.a))
      𝓘(ℂ,ComplexModel ((R.r+R.a)+(R.r+R.b))) 𝓘(ℂ,ComplexModel m) ∞
        (secondReaderMap R ∘ euclideanReaderChange R) :=
  ⟨product_submersion_reparameterize (euclideanReaderChange R) (ambientEuclidean R.r R.a R.b).symm
      (firstReaderMap_isSubmersionOfComplement R),
    product_submersion_reparameterize (euclideanReaderChange R) (ambientEuclidean R.r R.a R.b).symm
      (secondReaderMap_isSubmersionOfComplement R)⟩

/-- The common Euclidean reader maps preserve the exact paired whole
boundary slots, including the absent slots. -/
theorem euclidean_reader_maps_slot_preimage_eq (i : Fin E.length) :
    (firstReaderMap R ∘ euclideanReaderChange R) ⁻¹' E.get i =
      (secondReaderMap R ∘ euclideanReaderChange R) ⁻¹' F.get (τ i) := by
  rw [preimage_comp, preimage_comp]
  exact congrArg ((euclideanReaderChange R) ⁻¹' ·) (reader_maps_slot_preimage_eq R i)

end ExactReader

end
end Hironaka.HironakaG1ReaderProductSubmersions
