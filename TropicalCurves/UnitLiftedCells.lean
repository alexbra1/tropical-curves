import TropicalCurves.UnitJacobian
import TropicalCurves.UnitFlowPolytope
import TropicalCurves.UnitCube

/-!
# Pullbacks of unit-length Jacobian cell charts

An edge-product Abel lift has an integral corner chain and subtracts a sum
of moving unit-edge coordinates. A target pseudo-divisor chart has the same
form, with one parameter for each exceptional edge. This file defines their
pullback in the actual gradient quotient, for every integral period shift,
and identifies it with a signed-slot flow polytope. The period is allowed to
be any integral chain here; actual Jacobian deck shifts are its cycle subset.
-/

noncomputable section

namespace TropicalCurves
namespace UnitLiftedCells

open FiniteStability UnitJacobian UnitBoxPerturbation UnitFlowPolytope

variable {V E I J : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
  [Fintype I] [Fintype J]

/-- Sum all moving coordinates assigned to a given edge, with repetitions. -/
def parameterChain (edges : I → E) (x : I → ℝ) : E → ℝ :=
  fun e => ∑ i, if edges i = e then x i else 0

/-- The affine lift of an edge-product divisor chart. -/
def affineLift (G : EndpointGraph V E) (corner : E → ℤ)
    (edges : I → E) (x : I → ℝ) : Cover G :=
  coverClass G (castChain corner - parameterChain edges x)

/-- A target chart, translated by an integral edge chain in the cover. -/
def liftedCell (G : EndpointGraph V E) (corner : E → ℤ)
    (edges : J → E) (period : E → ℤ) : Set (Cover G) :=
  {w | ∃ y ∈ unitCube J,
    coverClass G (castChain corner - parameterChain edges y + castChain period) = w}

/-- One pulled-back cell, including an arbitrary face of the source cube. -/
def pullbackCell (G : EndpointGraph V E) (sourceCorner targetCorner : E → ℤ)
    (sourceEdges : I → E) (targetEdges : J → E) (period : E → ℤ)
    (face : I → Option Bool) : Set (I → ℝ) :=
  {x | x ∈ unitCube I ∧ OnSourceFace face x ∧
    affineLift G sourceCorner sourceEdges x ∈
      liftedCell G targetCorner targetEdges period}

omit [Fintype E] in
/-- Each row has the source parameters with sign `+1` and target parameters
with sign `-1`, even when the same original edge occurs several times. -/
theorem slotRow_sum (sourceEdges : I → E) (targetEdges : J → E)
    (x : I → ℝ) (y : J → ℝ) (e : E) :
    slotRow (Sum.elim sourceEdges targetEdges)
      (Sum.elim (fun _ : I => (1 : ℤ)) (fun _ : J => (-1 : ℤ)))
      (Sum.elim x y) e = parameterChain sourceEdges x e -
        parameterChain targetEdges y e := by
  classical
  simp only [slotRow, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, parameterChain]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

omit [Fintype E] [DecidableEq V] in
/-- Equality in the gradient quotient is exactly the signed-slot row system. -/
theorem cover_equality_iff (G : EndpointGraph V E)
    (sourceCorner targetCorner period : E → ℤ)
    (sourceEdges : I → E) (targetEdges : J → E) (x : I → ℝ) (y : J → ℝ) :
    coverClass G (castChain sourceCorner - parameterChain sourceEdges x) =
      coverClass G (castChain targetCorner - parameterChain targetEdges y + castChain period) ↔
    ∃ p : V → ℝ, ∀ e,
      slotRow (Sum.elim sourceEdges targetEdges)
        (Sum.elim (fun _ : I => (1 : ℤ)) (fun _ : J => (-1 : ℤ)))
        (Sum.elim x y) e =
        ((sourceCorner - targetCorner - period) e : ℝ) +
          p (G.target e) - p (G.source e) := by
  rw [cover_eq_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨-p, fun e => ?_⟩
    have he := congrFun hp e
    rw [slotRow_sum]
    simp only [Pi.sub_apply, Pi.add_apply, castChain_apply, gradient_apply] at he
    simp only [Pi.sub_apply, Int.cast_sub, Pi.neg_apply]
    linarith
  · rintro ⟨p, hp⟩
    refine ⟨-p, ?_⟩
    ext e
    have he := hp e
    rw [slotRow_sum] at he
    simp only [Pi.sub_apply, Int.cast_sub] at he
    simp only [Pi.sub_apply, Pi.add_apply, castChain_apply, gradient_apply, Pi.neg_apply]
    linarith

omit [Fintype E] [DecidableEq V] in
/-- Exact identification with the independently defined flow polytope.
This is a theorem about the actual quotient-cell pullback, not an assumption
that its vertices are integral. -/
theorem pullbackCell_eq_projectedSlots (G : EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ)
    (sourceEdges : I → E) (targetEdges : J → E) (period : E → ℤ)
    (face : I → Option Bool) :
    pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face =
      projectedSlots G.source G.target (Sum.elim sourceEdges targetEdges)
        (Sum.elim (fun _ : I => (1 : ℤ)) (fun _ : J => (-1 : ℤ)))
        (sourceCorner - targetCorner - period) Sum.inl face := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hface, y, hy, heq⟩
    refine ⟨Sum.elim x y, ?_, ?_, rfl, hface⟩
    · intro j
      cases j with
      | inl i => exact hx i
      | inr j => exact hy j
    · exact (cover_equality_iff G sourceCorner targetCorner period
        sourceEdges targetEdges x y).mp heq.symm
  · rintro ⟨u, hu, hp, hux, hface⟩
    refine ⟨?_, hface, (fun j => u (Sum.inr j)), ?_, ?_⟩
    · intro i
      have hi := congrFun hux i
      exact hi ▸ hu (Sum.inl i)
    · intro j
      exact hu (Sum.inr j)
    · apply Eq.symm
      apply (cover_equality_iff G sourceCorner targetCorner period
        sourceEdges targetEdges x (fun j => u (Sum.inr j))).mpr
      have hsplit : Sum.elim x (fun j => u (Sum.inr j)) = u := by
        funext j
        cases j with
        | inl i => exact (congrFun hux i).symm
        | inr j => rfl
      rw [hsplit]
      exact hp

omit [Fintype E] [DecidableEq V] in
/-- Every vertex of every lifted-chart pullback has binary coordinates.
No injectivity assumptions on the edge lists are needed. -/
theorem pullbackCell_vertex_binary (G : EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ)
    (sourceEdges : I → E) (targetEdges : J → E) (period : E → ℤ)
    (face : I → Option Bool) {x : I → ℝ}
    (hx : x ∈ (pullbackCell G sourceCorner targetCorner sourceEdges targetEdges
      period face).extremePoints ℝ) : ∀ i, x i = 0 ∨ x i = 1 := by
  classical
  rw [pullbackCell_eq_projectedSlots] at hx
  exact extreme_source_coordinate_binary G.source G.target
    (Sum.elim sourceEdges targetEdges)
    (Sum.elim (fun _ : I => (1 : ℤ)) (fun _ : J => (-1 : ℤ)))
    (by intro j; cases j <;> simp)
    (sourceCorner - targetCorner - period) Sum.inl face hx

omit [Fintype E] [DecidableEq V] in
/-- The no-new-vertices theorem for arbitrary integral unit-edge chart
offsets, stated with actual extreme points on both sides. -/
theorem pullbackCell_no_new_vertices (G : EndpointGraph V E)
    (sourceCorner targetCorner : E → ℤ)
    (sourceEdges : I → E) (targetEdges : J → E) (period : E → ℤ)
    (face : I → Option Bool) :
    (pullbackCell G sourceCorner targetCorner sourceEdges targetEdges period face).extremePoints ℝ
      ⊆ (unitCube I).extremePoints ℝ := by
  intro x hx
  exact UnitCube.binary_mem_extremePoints_cube
    (pullbackCell_vertex_binary G sourceCorner targetCorner sourceEdges targetEdges period face hx)

end UnitLiftedCells
end TropicalCurves
