import MPC.Chess.CheckingCrossing

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- The same construction exercises the solver in every nonparallel pair of
-- directions, with known parameters 1 and 2 and an arbitrary rational point.
example (d e : RayDirection) (hd : rayDet d e ≠ 0) (p : PlanePoint) :
    nonparallelIntersection (rayPoint p d (-1)) (rayPoint p e (-2)) d e = some p := by
  apply (nonparallelIntersection_eq_some_iff _ _ p d e).mpr
  refine ⟨hd, ?_, ?_⟩
  · simpa using (onRationalRay_shift_same p d (-1) 0).mpr (by norm_num)
  · simpa using (onRationalRay_shift_same p e (-2) 0).mpr (by norm_num)

-- Diagonal intersections need not be lattice points. Swapping the rays gives
-- exactly the same result and swaps the two positive parameters.
example : nonparallelIntersection (0, 0) (1, 0) .northEast .northWest = some (1/2, 1/2) ∧
    nonparallelIntersection (1, 0) (0, 0) .northWest .northEast = some (1/2, 1/2) := by
  norm_num [nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector]

example : ¬ ∃ p : Pos, p.toPlane = (1/2, 1/2) := by
  rintro ⟨p, hp⟩
  have hx : (p.toInt.1 : ℚ) = 1/2 := congrArg Prod.fst hp
  have hi : 2 * p.toInt.1 = 1 := by
    exact_mod_cast (show (2 : ℚ) * (p.toInt.1 : ℚ) = 1 by linarith)
  omega

-- Board origins can have an intersection outside the board.
example : nonparallelIntersection (0, 7) (7, 0) .northEast .north = some (7, 14) := by
  norm_num [nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector]

example : ¬ ∃ p : Pos, p.toPlane = (7, 14) := by
  rintro ⟨p, hp⟩
  have hy := congrArg Prod.snd hp
  simp only [Pos.toPlane, Pos.toInt, Int.cast_natCast] at hy
  have hv : p.2.val = 14 := by exact_mod_cast hy
  have hb := p.2.isLt
  omega

-- The full ray includes its origin. Negative parameters are still excluded.
example : nonparallelIntersection (0, 0) (0, 1) .east .south = some (0, 0) ∧
    nonparallelIntersection (0, 0) (-1, -1) .east .north = none := by
  norm_num [nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector]

example (d : RayDirection) : OnRationalRay (3, 3) d (3, 3) := onRationalRay_origin _ _

example (k p : Pos) (d : RayDirection) (hp : OnRay k d p) : OnRationalRay k.toPlane d p.toPlane :=
  (onRationalRay_toPlane_iff k p d).mpr (Or.inr hp)

-- The ray parameter is injective, and the two shifted bounds include their
-- endpoints. These facts do not choose A1 or A2 among checking crossings.
example : OnRationalRay (3/2, 0) .east (2, 0) ∧
    OnRationalRay (3/2, 0) .west (3/2, 0) ∧ ¬ OnRationalRay (3/2, 0) .east (1, 0) := by
  norm_num [OnRationalRay, rayParameter, rayPoint, RayDirection.vector]

example (o : PlanePoint) (d : RayDirection) (s t : ℚ) (h : rayPoint o d s = rayPoint o d t) : s = t :=
  rayPoint_injective o d h

-- Distinct parallel supporting lines are disjoint.
example : ¬ ∃ p, OnRationalRay (0, 0) .east p ∧ OnRationalRay (0, 1) .east p := by
  rw [parallel_rays_intersect_iff (0, 0) (0, 1) .east .east (by norm_num [rayDet, RayDirection.vector])]
  norm_num [rayOffset, RayDirection.vector]

-- A `none` solver result does not mean disjointness when the rays overlap.
example : nonparallelIntersection (0, 0) (1, 0) .east .east = none ∧
    OnRationalRay (0, 0) .east (2, 0) ∧ OnRationalRay (1, 0) .east (2, 0) ∧
    OnRationalRay (0, 0) .east (3, 0) ∧ OnRationalRay (1, 0) .east (3, 0) := by
  norm_num [nonparallelIntersection, rayDet, OnRationalRay, rayParameter, rayPoint, RayDirection.vector]

-- Facing opposite rays meet on the closed interval; outward-facing rays do
-- not meet. Coincident origins remain a one-point intersection.
example : OnRationalRay (0, 0) .east (1/2, 0) ∧ OnRationalRay (2, 0) .west (1/2, 0) ∧
    OnRationalRay (0, 0) .east (2, 0) ∧ OnRationalRay (2, 0) .west (2, 0) := by
  norm_num [OnRationalRay, rayParameter, rayPoint, RayDirection.vector]

example : ¬ ∃ p, OnRationalRay (0, 0) .east p ∧ OnRationalRay (-2, 0) .west p := by
  rw [parallel_rays_intersect_iff (0, 0) (-2, 0) .east .west (by norm_num [rayDet, RayDirection.vector])]
  norm_num [rayOffset, rayParameter, RayDirection.vector, RayDirection.opposite]

example (p : PlanePoint) (h : OnRationalRay (0, 0) .east p ∧ OnRationalRay (0, 0) .west p) :
    p = (0, 0) := by
  obtain ⟨t, ht, rfl⟩ := (onRationalRay_iff_nonneg_parameter _ _ _).mp h.1
  have hh := h.2
  have hs : t ≤ 0 := (onRationalRay_shift_opposite (0, 0) .east 0 t).mp (by simpa [RayDirection.opposite] using hh)
  have he : t = 0 := by linarith
  simp [he]

example (p : PlanePoint) (hp : OnRationalRay (0, 0) .northEast p ∧ OnRationalRay (1, 0) .northWest p) :
    p = (1/2, 1/2) := by
  apply rationalRay_intersection_unique (d := .northEast) (e := .northWest)
    (a := (0, 0)) (b := (1, 0)) (by norm_num [rayDet, RayDirection.vector]) hp
  norm_num [OnRationalRay, rayParameter, rayPoint, RayDirection.vector]

private def crossingBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (2, 0) then some ⟨c.opponent, .king⟩
  else if q = (2, 2) then some ⟨c.opponent, .bishop⟩
  else if q = (0, 2) then some ⟨c, .bishop⟩ else none

private def crossingKings (c : Color) : Color → Pos := fun owner => if owner = c then (0, 0) else (2, 0)
private def crossingTrace (c : Color) : MoveTrace := .empty ⟨crossingBoard c, c, {}, none⟩

-- Both colors and the state-based crossing definition are checked without
-- claiming a positive-length legal mutual-check trace.
example (c : Color) : (crossingTrace c).KingsWellPlaced (fun _ => crossingKings c) := by
  unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
  cases c <;> decide

example (c : Color) : (crossingTrace c).CheckingCrossing (crossingKings c) (Pos.toPlane (1, 1)) := by
  rw [MoveTrace.checkingCrossing_toPlane_iff]
  cases c <;> decide

example (c : Color) : ¬ (crossingTrace c).CheckingCrossing (crossingKings c) (Pos.toPlane (3, 3)) := by
  rw [MoveTrace.checkingCrossing_toPlane_iff]
  cases c <;> decide

-- Even actual checking rays with board origins can cross at a half-integer.
private def halfBoard : Board := fun q =>
  if q = (0, 0) then some ⟨.white, .king⟩
  else if q = (3, 0) then some ⟨.black, .king⟩
  else if q = (4, 4) then some ⟨.black, .bishop⟩
  else if q = (0, 3) then some ⟨.white, .bishop⟩ else none
private def halfKings : Color → Pos | .white => (0, 0) | .black => (3, 0)

example : (MoveTrace.empty ⟨halfBoard, .white, {}, none⟩).CheckingCrossing halfKings (3/2, 3/2) := by
  apply MoveTrace.checkingCrossing_of_nonparallelIntersection _ halfKings _ .northEast .northWest
  · decide
  · decide
  · norm_num [halfKings, Pos.toPlane, Pos.toInt, nonparallelIntersection, rayIntersectionParameters,
      rayOffset, rayDet, rayPoint, RayDirection.vector, Fin.coe_ofNat_eq_mod]

end MPC.Chess.Tests
