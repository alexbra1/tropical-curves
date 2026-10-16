import TropicalCurves.UnitBoxPerturbation

/-!
# The unit cube, its corners, and its coordinate faces

The cube reuses `UnitBoxPerturbation.unitCube`. Its vertices are mathlib's
actual extreme points, characterized using `extremePoints_pi`. No finiteness
assumption on the coordinate index type is needed.

An optional Boolean in each coordinate specifies an endpoint condition:
`none` leaves the coordinate free; `some false` fixes zero; `some true`
fixes one. These subsets are convex extreme subsets of the cube, and their
extreme points are exactly the cube corners they contain.
-/

namespace TropicalCurves
namespace UnitCube

open Set UnitBoxPerturbation

variable {I : Type*}

/-- The left endpoint is an extreme point of a closed real interval. -/
private theorem left_mem_extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    a ∈ (Icc a b).extremePoints ℝ := by
  refine ⟨⟨le_rfl, hab⟩, ?_⟩
  intro x hx y hy hseg
  by_cases hxy : x = y
  · subst y
    rw [openSegment_same] at hseg
    have hax : a = x := hseg
    exact ⟨hax.symm, hax.symm⟩
  · rw [openSegment_eq_Ioo' hxy] at hseg
    have hmin : a ≤ min x y := le_min hx.1 hy.1
    exact (not_lt_of_ge hmin hseg.1).elim

/-- The right endpoint is an extreme point of a closed real interval. -/
private theorem right_mem_extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    b ∈ (Icc a b).extremePoints ℝ := by
  refine ⟨⟨hab, le_rfl⟩, ?_⟩
  intro x hx y hy hseg
  by_cases hxy : x = y
  · subst y
    rw [openSegment_same] at hseg
    have hbx : b = x := hseg
    exact ⟨hbx.symm, hbx.symm⟩
  · rw [openSegment_eq_Ioo' hxy] at hseg
    have hmax : max x y ≤ b := max_le hx.2 hy.2
    exact (not_lt_of_ge hmax hseg.2).elim

/-- Only the endpoints of a nonempty closed real interval are extreme. -/
private theorem extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    (Icc a b).extremePoints ℝ = {a, b} := by
  ext x
  constructor
  · intro hx
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    have hi : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hxa), lt_of_le_of_ne hx.1.2 hxb⟩
    have hab' : a < b := hi.1.trans hi.2
    have hs : x ∈ openSegment ℝ a b := by
      rwa [openSegment_eq_Ioo hab']
    have hax := (hx.2 ⟨le_rfl, hab'.le⟩ ⟨hab'.le, le_rfl⟩ hs).1
    exact (hi.1.ne hax).elim
  · intro hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact left_mem_extremePoints_Icc hab
    · exact right_mem_extremePoints_Icc hab

/-- The closed unit cube, using the existing coordinate-box definition. -/
abbrev Cube (I : Type*) : Set (I → ℝ) := unitCube I

/-- Binary coordinate vectors. -/
def corners (I : Type*) : Set (I → ℝ) := {x | ∀ i, x i = 0 ∨ x i = 1}

@[simp] theorem mem_cube {x : I → ℝ} : x ∈ Cube I ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := Iff.rfl

@[simp] theorem mem_corners {x : I → ℝ} :
    x ∈ corners I ↔ ∀ i, x i = 0 ∨ x i = 1 := Iff.rfl

/-- Product-set presentation of the unit cube. -/
theorem cube_eq_pi (I : Type*) :
    Cube I = Set.univ.pi (fun _ : I => Set.Icc (0 : ℝ) 1) := by
  ext x
  simp [unitCube, Set.mem_pi]

/-- The genuine extreme points of the unit cube are its binary corners. -/
theorem extremePoints_cube (I : Type*) : (Cube I).extremePoints ℝ = corners I := by
  rw [cube_eq_pi, extremePoints_pi]
  ext x
  simp [corners, Set.mem_pi, extremePoints_Icc (show (0 : ℝ) ≤ 1 by norm_num)]

/-- The binary-coordinate conclusion of an integrality argument gives an
actual extreme point of the source cube. -/
theorem binary_mem_extremePoints_cube {x : I → ℝ}
    (hx : ∀ i, x i = 0 ∨ x i = 1) : x ∈ (Cube I).extremePoints ℝ := by
  rw [extremePoints_cube]
  exact hx

/-- Conversely every cube vertex has binary coordinates. -/
theorem extremePoints_cube_binary {x : I → ℝ}
    (hx : x ∈ (Cube I).extremePoints ℝ) : ∀ i, x i = 0 ∨ x i = 1 := by
  rwa [extremePoints_cube] at hx

/-- The unit cube is convex. -/
theorem cube_convex (I : Type*) : Convex ℝ (Cube I) := by
  rw [cube_eq_pi]
  exact convex_pi fun _ _ => convex_Icc 0 1

/-- A source face specified by optional coordinate endpoints. The endpoint
condition is definitionally the same as `UnitFlowPolytope.OnSourceFace`,
without creating a dependency on that module. -/
def sourceFace (face : I → Option Bool) : Set (I → ℝ) :=
  Cube I ∩ {x | ∀ i b, face i = some b → x i = if b then 1 else 0}

@[simp] theorem mem_sourceFace {face : I → Option Bool} {x : I → ℝ} :
    x ∈ sourceFace face ↔ x ∈ Cube I ∧
      ∀ i b, face i = some b → x i = if b then 1 else 0 := Iff.rfl

/-- The unrestricted face is the whole cube. -/
@[simp] theorem sourceFace_none :
    sourceFace (fun _ : I => none) = Cube I := by
  ext x
  simp [sourceFace]

/-- Every coordinate face lies in the source cube. -/
theorem sourceFace_subset_cube (face : I → Option Bool) : sourceFace face ⊆ Cube I :=
  fun _ hx => hx.1

/-- The specified source faces are convex. -/
theorem sourceFace_convex (face : I → Option Bool) : Convex ℝ (sourceFace face) := by
  intro x hx y hy a b ha hb hab
  refine ⟨cube_convex I hx.1 hy.1 ha hb hab, ?_⟩
  intro i bit hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.2 i bit hi, hy.2 i bit hi]
  rw [← add_mul, hab, one_mul]

/-- Every specified source face is an extreme subset of the cube. -/
theorem sourceFace_isExtreme (face : I → Option Bool) :
    IsExtreme ℝ (Cube I) (sourceFace face) := by
  refine ⟨sourceFace_subset_cube face, ?_⟩
  intro y hy z hz x hx hsegment
  have hcoordinate (i : I) : x i ∈ openSegment ℝ (y i) (z i) := by
    rcases hsegment with ⟨a, b, ha, hb, hab, hcombine⟩
    exact ⟨a, b, ha, hb, hab, congrFun hcombine i⟩
  have hfixed : ∀ i bit, face i = some bit →
      y i = (if bit then 1 else 0) ∧ z i = (if bit then 1 else 0) := by
    intro i bit hi
    have hext : (if bit then 1 else 0 : ℝ) ∈ (Set.Icc 0 1).extremePoints ℝ := by
      cases bit
      · exact left_mem_extremePoints_Icc (by norm_num)
      · exact right_mem_extremePoints_Icc (by norm_num)
    have hxi := hx.2 i bit hi
    exact hext.2 (hy i) (hz i) (hxi ▸ hcoordinate i)
  exact ⟨⟨hy, fun i bit hi => (hfixed i bit hi).1⟩,
    ⟨hz, fun i bit hi => (hfixed i bit hi).2⟩⟩

/-- The vertices of a coordinate face are precisely the cube corners in it. -/
theorem extremePoints_sourceFace (face : I → Option Bool) :
    (sourceFace face).extremePoints ℝ = sourceFace face ∩ corners I := by
  rw [(sourceFace_isExtreme face).extremePoints_eq, extremePoints_cube]

/-- In particular, passing to a source face never creates cube vertices. -/
theorem sourceFace_vertices_subset_cube_vertices (face : I → Option Bool) :
    (sourceFace face).extremePoints ℝ ⊆ (Cube I).extremePoints ℝ :=
  (sourceFace_isExtreme face).extremePoints_subset_extremePoints

/-- Filling free coordinates by zero gives a canonical corner of each face. -/
def faceCorner (face : I → Option Bool) : I → ℝ := fun i =>
  match face i with
  | some true => 1
  | _ => 0

/-- Each specified source face is nonempty, including in dimension zero. -/
theorem faceCorner_mem_sourceFace (face : I → Option Bool) :
    faceCorner face ∈ sourceFace face := by
  constructor
  · intro i
    cases h : face i with
    | none => simp [faceCorner, h]
    | some bit => cases bit <;> simp [faceCorner, h]
  · intro i bit hi
    cases bit <;> simp [faceCorner, hi]

theorem sourceFace_nonempty (face : I → Option Bool) : (sourceFace face).Nonempty :=
  ⟨faceCorner face, faceCorner_mem_sourceFace face⟩

/-- Fixing every coordinate gives exactly one corner. -/
theorem sourceFace_all_fixed (bits : I → Bool) :
    sourceFace (fun i => some (bits i)) = {fun i => if bits i then 1 else 0} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    funext i
    exact hx.2 i (bits i) rfl
  · intro hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    constructor
    · intro i
      dsimp only
      cases hb : bits i <;> norm_num [hb]
    · intro i bit hi
      have hb : bits i = bit := Option.some.inj hi
      dsimp only
      rw [hb]

end UnitCube
end TropicalCurves
