import TropicalCurves.UnitAbelMap
import TropicalCurves.UnitLiftedCells
import TropicalCurves.UnitCellConvexity

/-!
# No new vertices for tropical Abel maps with unit edge lengths

The source is a product of closed unit edges, with repetitions allowed.
The target charts are the actual divisor-integration images of quasistable
pseudo-divisors on the graph's edge subdivisions. Their covering charts are
translated by all integral cycles. Intersecting their inverse images with
all source cube faces defines the induced cell family.

Every cell's genuine extreme points are corners of the source cube. The
proof uses neither a hypothesis asserting integrality nor a restriction on
the selected edges. Genericity is included in the final user-facing theorem;
the cellwise argument in fact works for every rooted-quasistable selection.
-/

noncomputable section

namespace TropicalCurves
namespace UnitNoNewVertices

open FiniteStability UnitJacobian UnitRoutes UnitAbelMap UnitPseudoDivisor
  UnitLiftedCells UnitBoxPerturbation

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]
  [DecidableEq V] [DecidableEq E]

omit [Fintype E] in
/-- The row-sum and basis-vector presentations of edge integration agree. -/
theorem parameterChain_eq_edgeChain (edges : I → E) (x : I → ℝ) :
    parameterChain edges x = edgeChain edges x := by
  classical
  ext e
  simp [parameterChain, edgeChain, Pi.single_apply, eq_comm]

variable (G : EndpointGraph V E) {q : V} (R : VertexRoutes G q)

/-- Turn cube coordinates into the actual closed-edge product. -/
def edgeParameters (edges : I → E) (x : I → ℝ) (hx : x ∈ unitCube I) :
    (unitGraph G).EdgeProduct edges := fun i => ⟨x i, hx i⟩

/-- The affine source lift projects to the actual divisor Abel map, including
all endpoint coordinates. -/
theorem source_lift_projects (F : V → ℤ) (edges : I → E)
    (x : I → ℝ) (hx : x ∈ unitCube I) :
    coverProjection G (affineLift G (cornerChain G R F edges) edges x) =
      divisorClass G R ((unitGraph G).edgeAbelDivisor (fixedVertexDivisor G F)
        edges (edgeParameters G edges x hx)) := by
  rw [divisorClass_edgeAbelDivisor]
  simp only [affineLift, coverProjection_coverClass, edgeParameters]
  rw [parameterChain_eq_edgeChain]

/-- The nonempty closed chart indexed by a pseudo-divisor label, defined
using the actual moving divisor on the original curve point set. -/
def targetCell (T : PseudoDivisorType V E) : Set (Jacobian G) :=
  {w | ∃ y : (unitGraph G).EdgeProduct
      (fun e : {e : E // e ∈ T.exceptional} => e.val),
    divisorClass G R (pseudoDivisor G T y) = w}

/-- Integer cycle translates of a target covering chart project to the
actual pseudo-divisor class for the same edge parameters. -/
theorem target_lift_projects (T : PseudoDivisorType V E) (c : E → ℤ)
    (hc : integerBoundary G c = 0)
    (y : {e : E // e ∈ T.exceptional} → ℝ) (hy : y ∈ unitCube _) :
    coverProjection G (coverClass G
      (castChain (cornerChain G R T.coefficients (fun e : {e // e ∈ T.exceptional} => e.val)) -
        parameterChain (fun e : {e // e ∈ T.exceptional} => e.val) y + castChain c)) =
      divisorClass G R (pseudoDivisor G T
        (edgeParameters G (fun e : {e // e ∈ T.exceptional} => e.val) y hy)) := by
  rw [coverProjection_coverClass, map_add, classMap_integerCycle G c hc, add_zero,
    divisorClass_pseudoDivisor]
  simp only [edgeParameters]
  rw [parameterChain_eq_edgeChain]

/-- All periodic lifts of one target chart project onto exactly that chart. -/
theorem liftedCell_projects (T : PseudoDivisorType V E) (c : E → ℤ)
    (hc : integerBoundary G c = 0) :
    coverProjection G '' liftedCell G
      (cornerChain G R T.coefficients (fun e : {e // e ∈ T.exceptional} => e.val))
      (fun e : {e // e ∈ T.exceptional} => e.val) c = targetCell G R T := by
  ext w
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨edgeParameters G _ y hy, (target_lift_projects G R T c hc y hy).symm⟩
  · rintro ⟨y, rfl⟩
    let yr : {e : E // e ∈ T.exceptional} → ℝ := fun e => y e
    have hy : yr ∈ unitCube _ := fun e => (y e).property
    refine ⟨_, ⟨yr, hy, rfl⟩, ?_⟩
    exact target_lift_projects G R T c hc yr hy

/-- The actual target-cell inverse image is exhausted by the cycle-shifted
covering pullbacks. Thus the lifted construction omits no inverse-image
piece, even when the full inverse image in the quotient is disconnected. -/
theorem target_preimage_iff (F : V → ℤ) (edges : I → E)
    (T : PseudoDivisorType V E) (x : (unitGraph G).EdgeProduct edges) :
    divisorClass G R ((unitGraph G).edgeAbelDivisor (fixedVertexDivisor G F) edges x)
      ∈ targetCell G R T ↔
    ∃ c : E → ℤ, integerBoundary G c = 0 ∧
      (fun i => (x i : ℝ)) ∈ pullbackCell G (cornerChain G R F edges)
        (cornerChain G R T.coefficients (fun e : {e // e ∈ T.exceptional} => e.val))
        edges (fun e : {e // e ∈ T.exceptional} => e.val) c (fun _ => none) := by
  constructor
  · rintro ⟨y, hy⟩
    have heq := hy.symm
    rw [divisorClass_edgeAbelDivisor, divisorClass_pseudoDivisor,
      ← parameterChain_eq_edgeChain, ← parameterChain_eq_edgeChain] at heq
    obtain ⟨c, hc, heq⟩ := (class_eq_iff_cover_shift G _ _).mp heq
    refine ⟨c, hc, (fun i => (x i).property), ?_, (fun e => (y e : ℝ)),
      (fun e => (y e).property), heq.symm⟩
    intro i bit hi
    cases hi
  · rintro ⟨c, hc, _hx, _hface, y, hy, heq⟩
    let yp := edgeParameters G (fun e : {e // e ∈ T.exceptional} => e.val) y hy
    refine ⟨yp, ?_⟩
    have hsource := source_lift_projects G R F edges (fun i => (x i : ℝ))
      (fun i => (x i).property)
    have htarget := target_lift_projects G R T c hc y hy
    have hproj := congrArg (coverProjection G) heq
    exact htarget.symm.trans (hproj.trans hsource)

/-- The induced cell family: every quasistable type, every integral-cycle
translate, and every coordinate face of the source cube is included. -/
def inducedCells (μ : V → ℝ) (F : V → ℤ) (edges : I → E) : Set (Set (I → ℝ)) :=
  {P | ∃ T : QuasistableType G μ q, ∃ c : E → ℤ,
    integerBoundary G c = 0 ∧ ∃ face : I → Option Bool,
      P = pullbackCell G (cornerChain G R F edges)
        (cornerChain G R T.val.coefficients
          (fun e : {e // e ∈ T.val.exceptional} => e.val))
        edges (fun e : {e // e ∈ T.val.exceptional} => e.val) c face}

/-- Vertices of a cell family are the actual extreme points of its cells. -/
def vertices (cells : Set (Set (I → ℝ))) : Set (I → ℝ) :=
  {x | ∃ P ∈ cells, x ∈ P.extremePoints ℝ}

/-- Every vertex of every induced cell is an original cube vertex. -/
theorem no_new_vertices (μ : V → ℝ) (F : V → ℤ) (edges : I → E) :
    vertices (inducedCells G R μ F edges) ⊆ (unitCube I).extremePoints ℝ := by
  rintro x ⟨P, ⟨T, c, _hc, face, rfl⟩, hx⟩
  exact pullbackCell_no_new_vertices G _ _ _ _ _ _ hx

/-- Equivalently, every induced vertex has each coordinate equal to zero or one. -/
theorem induced_vertex_binary (μ : V → ℝ) (F : V → ℤ) (edges : I → E)
    {x : I → ℝ} (hx : x ∈ vertices (inducedCells G R μ F edges)) :
    ∀ i, x i = 0 ∨ x i = 1 :=
  UnitCube.extremePoints_cube_binary (no_new_vertices G R μ F edges hx)

/-- Stronger geometric form: each induced cell is the convex hull of the
source cube corners that it contains. -/
theorem induced_cell_eq_convexHull_corners (μ : V → ℝ) (F : V → ℤ) (edges : I → E)
    {P : Set (I → ℝ)} (hP : P ∈ inducedCells G R μ F edges) :
    P = convexHull ℝ (P ∩ UnitCube.corners I) := by
  obtain ⟨T, c, _hc, face, rfl⟩ := hP
  exact UnitCellConvexity.pullbackCell_eq_convexHull_corners G _ _ _ _ _ _

/-- Despite the infinite set of integral-cycle labels, the induced family
has only finitely many distinct cells. -/
theorem inducedCells_finite (μ : V → ℝ) (F : V → ℤ) (edges : I → E) :
    (inducedCells G R μ F edges).Finite :=
  UnitCellConvexity.finite_family_of_corner_hulls _
    (fun _ hP => induced_cell_eq_convexHull_corners G R μ F edges hP)

/-- Connected finite unit-length tropical curves satisfy the requested
no-new-vertices property. The hypotheses include the standard source/target
degree compatibility and original-graph genericity. The stronger cellwise
result above explains why these two hypotheses are not needed in its proof. -/
theorem unit_length_abel_no_new_vertices (q : V) (hG : (skeleton G).Connected)
    (μ : V → ℝ) (_hgeneral : IsGeneral G μ)
    (D : (unitGraph G).Divisor) (_hD : (unitGraph G).VertexSupported D)
    (edges : I → E)
    (_hdegree : polarizationDegree μ =
      (((unitGraph G).degree D - (Fintype.card I : ℤ) : ℤ) : ℝ)) :
    vertices (inducedCells G (routes_of_connected G q hG) μ
      (fun v => D ((unitGraph G).vertex v)) edges) ⊆ (unitCube I).extremePoints ℝ :=
  no_new_vertices G (routes_of_connected G q hG) μ _ edges

end UnitNoNewVertices
end TropicalCurves
