import TropicalCurves.UnitLiftedCells
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Data.Set.Finite.Powerset

/-!
# Convexity of unit-length Jacobian pullback cells

The flow description of a pulled-back cell consists of linear equations,
unit-coordinate bounds, and optional source-face equations. A convex
combination of witnesses remains a witness, including its vertex potential.
This proves convexity of the actual quotient-cell pullback through the exact
identification established in `UnitLiftedCells`.

Convexity here does not assume integrality, extremality, quasistability, or a
specific period shift. The result therefore applies in particular to every
quasistable target chart and every integral-cycle translate.
-/

noncomputable section

namespace TropicalCurves
namespace UnitCellConvexity

open UnitBoxPerturbation UnitFlowPolytope UnitLiftedCells

/-- Coordinate bounds between zero and one are preserved by convex combination. -/
theorem unitCube_convex (J : Type*) : Convex ℝ (unitCube J) := by
  intro u hu v hv a b ha hb hab j
  change 0 ≤ a * u j + b * v j ∧ a * u j + b * v j ≤ 1
  constructor
  · exact add_nonneg (mul_nonneg ha (hu j).1) (mul_nonneg hb (hv j).1)
  · calc
      a * u j + b * v j ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left (hu j).2 ha)
          (mul_le_mul_of_nonneg_left (hv j).2 hb)
      _ = 1 := by simpa only [mul_one] using hab

/-- An arbitrary collection of prescribed source endpoint coordinates is
an affine, hence convex, set. -/
theorem onSourceFace_convex {I : Type*} (face : I → Option Bool) :
    Convex ℝ {x : I → ℝ | OnSourceFace face x} := by
  intro x hx y hy a b ha hb hab i value hface
  change a * x i + b * y i = if value then 1 else 0
  rw [hx i value hface, hy i value hface, ← add_mul, hab, one_mul]

/-- The source cube together with any of its coordinate-face conditions is convex. -/
theorem sourceFace_convex {I : Type*} (face : I → Option Bool) :
    Convex ℝ {x : I → ℝ | x ∈ unitCube I ∧ OnSourceFace face x} :=
  (unitCube_convex I).inter (onSourceFace_convex face)

variable {J E V I : Type*} [Fintype J] [DecidableEq E]

/-- Projecting signed bounded slots subject to affine potential equations
gives a convex set. The signs may be arbitrary integers for this lemma. -/
theorem projectedSlots_convex (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    Convex ℝ (projectedSlots source target edge sign z selected face) := by
  classical
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨u, hu, ⟨p, hp⟩, hux, hfaceX⟩
  rcases hy with ⟨v, hv, ⟨q, hq⟩, hvy, hfaceY⟩
  refine ⟨a • u + b • v, (unitCube_convex J) hu hv ha hb hab, ?_, ?_, ?_⟩
  · refine ⟨a • p + b • q, fun e => ?_⟩
    have hrow : slotRow edge sign (a • u + b • v) e =
        a * slotRow edge sign u e + b * slotRow edge sign v e := by
      change rowMap edge sign (a • u + b • v) e = _
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hrow, hp e, hq e]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * ((z e : ℝ) + p (target e) - p (source e)) +
          b * ((z e : ℝ) + q (target e) - q (source e)) =
          (a + b) * (z e : ℝ) + (a * p (target e) + b * q (target e)) -
            (a * p (source e) + b * q (source e)) := by ring
      _ = _ := by rw [hab, one_mul]
  · simp only [map_add, map_smul, hux, hvy]
  · exact onSourceFace_convex face hfaceX hfaceY ha hb hab

section Compactness

variable [Fintype E]

omit [Fintype J] in
/-- The coordinate unit cube is compact in the product topology. -/
theorem unitCube_isCompact : IsCompact (unitCube J) := by
  have heq : unitCube J = Set.Icc (0 : J → ℝ) 1 := by
    ext u
    simp only [unitCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def,
      Pi.zero_apply, Pi.one_apply, forall_and]
  rw [heq]
  exact isCompact_Icc

/-- All optional source endpoint equations define a closed set. -/
theorem onSourceFace_isClosed (face : I → Option Bool) :
    IsClosed {x : I → ℝ | OnSourceFace face x} := by
  simp only [OnSourceFace, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun value =>
    isClosed_iInter fun hface => ?_
  exact isClosed_eq (continuous_apply i) continuous_const

/-- An existential potential is still a closed constraint: the allowed row
differences form a finite-dimensional linear subspace of the edge coordinates. -/
theorem potentialConstraint_isClosed (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) :
    IsClosed {u : J → ℝ | ∃ p : V → ℝ, ∀ e,
      slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e)} := by
  let G : FiniteStability.EndpointGraph V E := ⟨source, target⟩
  have heq : {u : J → ℝ | ∃ p : V → ℝ, ∀ e,
      slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e)} =
      (fun u => rowMap edge sign u - fun e => (z e : ℝ)) ⁻¹'
        (LinearMap.range (UnitJacobian.gradient G) : Set (E → ℝ)) := by
    ext u
    change (∃ p : V → ℝ, ∀ e, slotRow edge sign u e =
      (z e : ℝ) + p (target e) - p (source e)) ↔
      ∃ p : V → ℝ, UnitJacobian.gradient G p = rowMap edge sign u - fun e => (z e : ℝ)
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      ext e
      change p (target e) - p (source e) = slotRow edge sign u e - (z e : ℝ)
      linarith [hp e]
    · rintro ⟨p, hp⟩
      refine ⟨p, fun e => ?_⟩
      have he := congrFun hp e
      change p (target e) - p (source e) = slotRow edge sign u e - (z e : ℝ) at he
      linarith
  rw [heq]
  exact (Submodule.closed_of_finiteDimensional (LinearMap.range (UnitJacobian.gradient G))).preimage
    ((rowMap edge sign).continuous_of_finiteDimensional.sub continuous_const)

/-- Every projected flow cell is compact, even though its auxiliary potentials
need not be bounded. The bounded slot witness and closed gradient range suffice. -/
theorem projectedSlots_isCompact (source target : E → V) (edge : J → E)
    (sign : J → ℤ) (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    IsCompact (projectedSlots source target edge sign z selected face) := by
  let feasible : Set (J → ℝ) := unitCube J ∩ {u | ∃ p : V → ℝ, ∀ e,
    slotRow edge sign u e = (z e : ℝ) + p (target e) - p (source e)}
  have hcompact : IsCompact feasible := unitCube_isCompact.inter_right
    (potentialConstraint_isClosed source target edge sign z)
  have hprojection : Continuous (projection selected : (J → ℝ) → (I → ℝ)) :=
    continuous_pi fun i => continuous_apply (selected i)
  have heq : projectedSlots source target edge sign z selected face =
      (projection selected '' feasible) ∩ {x | OnSourceFace face x} := by
    ext x
    constructor
    · rintro ⟨u, hu, hp, hux, hface⟩
      exact ⟨⟨u, ⟨hu, hp⟩, hux⟩, hface⟩
    · rintro ⟨⟨u, ⟨hu, hp⟩, hux⟩, hface⟩
      exact ⟨u, hu, hp, hux, hface⟩
  rw [heq]
  exact (hcompact.image hprojection).inter_right (onSourceFace_isClosed face)

end Compactness

section Polytopes

/-- There are finitely many binary vectors when the source coordinate set is finite. -/
theorem corners_finite (I : Type*) [Fintype I] : (UnitCube.corners I).Finite := by
  classical
  let corner : (I → Bool) → I → ℝ := fun bits i => if bits i then 1 else 0
  have hsubset : UnitCube.corners I ⊆ Set.range corner := by
    intro x hx
    refine ⟨fun i => decide (x i = 1), ?_⟩
    funext i
    rcases hx i with hzero | hone
    · simp [corner, hzero]
    · simp [corner, hone]
  exact (Set.finite_range corner).subset hsubset

/-- The exact vertex set of a flow cell is the set of source-cube corners it
contains. The reverse inclusion uses extremality in the ambient cube. -/
theorem projectedSlots_extremePoints_eq_corners (source target : E → V)
    (edge : J → E) (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    (projectedSlots source target edge sign z selected face).extremePoints ℝ =
      projectedSlots source target edge sign z selected face ∩ UnitCube.corners I := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hx.1, extreme_source_coordinate_binary source target edge sign hsign z selected face hx⟩
  · intro x hx
    apply inter_extremePoints_subset_extremePoints_of_subset
      ((projectedSlots_subset_sourceFace source target edge sign z selected face).trans
        (UnitCube.sourceFace_subset_cube face))
    exact ⟨hx.1, UnitCube.binary_mem_extremePoints_cube hx.2⟩

variable [Fintype E] [Fintype I]

/-- A flow cell is the convex hull of the finitely many source-cube corners
that it contains. Thus these are genuine compact polytopes, including empty cells. -/
theorem projectedSlots_eq_convexHull_corners (source target : E → V)
    (edge : J → E) (sign : J → ℤ) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (z : E → ℤ) (selected : I → J) (face : I → Option Bool) :
    projectedSlots source target edge sign z selected face =
      convexHull ℝ (projectedSlots source target edge sign z selected face ∩ UnitCube.corners I) := by
  have hkm := closure_convexHull_extremePoints
    (projectedSlots_isCompact source target edge sign z selected face)
    (projectedSlots_convex source target edge sign z selected face)
  rw [projectedSlots_extremePoints_eq_corners source target edge sign hsign z selected face] at hkm
  have hfinite : (projectedSlots source target edge sign z selected face ∩
      UnitCube.corners I).Finite := (corners_finite I).subset Set.inter_subset_right
  rw [hfinite.isClosed_convexHull.closure_eq] at hkm
  exact hkm.symm

/-- A family of cells generated by source-cube corners has only finitely many
distinct cells, even if its chart and period labels form an infinite type. -/
theorem finite_family_of_corner_hulls (cells : Set (Set (I → ℝ)))
    (h : ∀ P ∈ cells, P = convexHull ℝ (P ∩ UnitCube.corners I)) : cells.Finite := by
  have hfinite : (convexHull ℝ '' Set.powerset (UnitCube.corners I)).Finite :=
    (corners_finite I).powerset.image _
  apply hfinite.subset
  intro P hP
  exact ⟨P ∩ UnitCube.corners I, Set.inter_subset_right, (h P hP).symm⟩

end Polytopes

section Pullback

variable [Fintype E] [DecidableEq V] [Fintype I]

omit [Fintype E] [DecidableEq V] in
/-- Every actual lifted Jacobian-cell pullback, including every source face
and every integral period translate, is convex. -/
theorem pullbackCell_convex (G : FiniteStability.EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ) (sourceEdges : I → E) (targetEdges : J → E)
    (period : E → ℤ) (face : I → Option Bool) :
    Convex ℝ (pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face) := by
  classical
  rw [pullbackCell_eq_projectedSlots]
  exact projectedSlots_convex _ _ _ _ _ _ _

omit [DecidableEq V] in
/-- The actual lifted-cell pullbacks are compact, including all boundary faces. -/
theorem pullbackCell_isCompact (G : FiniteStability.EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ) (sourceEdges : I → E) (targetEdges : J → E)
    (period : E → ℤ) (face : I → Option Bool) :
    IsCompact (pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face) := by
  classical
  rw [pullbackCell_eq_projectedSlots]
  exact projectedSlots_isCompact _ _ _ _ _ _ _

omit [DecidableEq V] in
/-- Every actual pulled-back cell is a polytope generated by the source-cube
corners it contains. No new vertices are needed to generate the whole cell. -/
theorem pullbackCell_eq_convexHull_corners (G : FiniteStability.EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ) (sourceEdges : I → E) (targetEdges : J → E)
    (period : E → ℤ) (face : I → Option Bool) :
    pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face =
      convexHull ℝ
        (pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face ∩
          UnitCube.corners I) := by
  classical
  rw [pullbackCell_eq_projectedSlots]
  exact projectedSlots_eq_convexHull_corners _ _ _ _
    (by intro j; cases j <;> simp) _ _ _

omit [Fintype E] [DecidableEq V] in
/-- In particular the entire set of vertices of each pullback cell is finite. -/
theorem pullbackCell_extremePoints_finite (G : FiniteStability.EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ) (sourceEdges : I → E) (targetEdges : J → E)
    (period : E → ℤ) (face : I → Option Bool) :
    ((pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face).extremePoints ℝ).Finite := by
  apply (corners_finite I).subset
  intro x hx
  exact pullbackCell_vertex_binary G sourceCorner targetCorner sourceEdges targetEdges period face hx

end Pullback

end UnitCellConvexity
end TropicalCurves
