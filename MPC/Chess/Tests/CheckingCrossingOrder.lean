import MPC.Chess.SecondCrossingMoves

namespace MPC.Chess.Tests

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- Parameter order is distance order for all eight directions, including
-- rational non-lattice points. The origin is allowed in this geometric test.
example (o : PlanePoint) (d : RayDirection) (s t : ℚ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s < t ↔ planeTaxicabDistance o (rayPoint o d s) < planeTaxicabDistance o (rayPoint o d t) := by
  simpa using ((onRationalRay_rayPoint o d s).mpr hs).parameter_lt_iff_distance_lt
    ((onRationalRay_rayPoint o d t).mpr ht)

private def twoKings (c : Color) : Color → Pos := fun owner => if owner = c then (0, 0) else (4, 2)
private def twoBoard (c : Color) : Board := fun q =>
  if q = (0, 0) then some ⟨c, .king⟩
  else if q = (4, 2) then some ⟨c.opponent, .king⟩
  else if q = (0, 7) then some ⟨c.opponent, .rook⟩
  else if q = (2, 2) then some ⟨c, .rook⟩
  else if q = (3, 3) then some ⟨c, .bishop⟩ else none
private def twoTrace (c : Color) : MoveTrace := .empty ⟨twoBoard c, c, {}, none⟩

-- These are state-only examples, not positive-length legal checking periods.
-- Both owner assignments yield A1=(0,2), A2=(0,6) on the north ray.
private theorem two_rays (c : Color) (owner : Color) (d : RayDirection) :
    (twoTrace c).CheckingRay (twoKings c owner) owner d ↔
      (owner = c ∧ d = .north) ∨ (owner = c.opponent ∧ (d = .west ∨ d = .northWest)) := by
  cases c <;> cases owner <;> cases d <;> decide

private theorem two_crossings (c : Color) :
    (twoTrace c).checkingCrossings (twoKings c) = {(0, 2), (0, 6)} := by
  ext p
  rw [MoveTrace.mem_checkingCrossings_iff]
  simp only [two_rays]
  cases c <;> simp [Color.opponent, and_or_left, or_and_right, exists_or, twoKings] <;>
    norm_num [nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet, rayPoint,
    RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod] <;> simp only [eq_comm]

private theorem two_parameters (c : Color) :
    (twoTrace c).rayCrossingParameters (twoKings c) c .north = {2, 6} := by
  rw [MoveTrace.rayCrossingParameters, two_crossings]
  cases c <;> norm_num [twoKings, Pos.toPlane, Pos.toInt, OnRationalRay, rayParameter, rayPoint,
    RayDirection.vector, Finset.filter_insert, Finset.filter_singleton]

example (c : Color) : (twoTrace c).KingsWellPlaced (fun _ => twoKings c) := by
  unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
  cases c <;> decide

example (c : Color) :
    (twoTrace c).firstCheckingCrossing (twoKings c) c .north (by rw [two_parameters]; decide) = (0, 2) ∧
    (twoTrace c).secondCheckingCrossing (twoKings c) c .north (by rw [two_parameters]; decide) = (0, 6) := by
  simp only [MoveTrace.firstCheckingCrossing, MoveTrace.secondCheckingCrossing,
    MoveTrace.checkingCrossingAt, Finset.orderEmbOfFin_apply]
  simp only [two_parameters]
  have hs : ({2, 6} : Finset ℚ).sort (· ≤ ·) = [2, 6] := by
    rw [Finset.sort_insert (· ≤ ·) (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; norm_num) (by norm_num)]
    simp
  simp only [hs, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
  cases c <;> norm_num [twoKings, rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt]

-- A ray with no crossings cannot supply a finite index for either A1 or A2.
example (c : Color) : (twoTrace c).rayCrossingParameters (twoKings c) c .south = ∅ := by
  rw [MoveTrace.rayCrossingParameters, two_crossings]
  cases c <;> norm_num [twoKings, Pos.toPlane, Pos.toInt, OnRationalRay, rayParameter, rayPoint,
    RayDirection.vector, Finset.filter_insert, Finset.filter_singleton]

private def halfKings : Color → Pos | .white => (0, 0) | .black => (3, 0)
private def halfBoard : Board := fun q =>
  if q = (0, 0) then some ⟨.white, .king⟩
  else if q = (3, 0) then some ⟨.black, .king⟩
  else if q = (4, 4) then some ⟨.black, .bishop⟩
  else if q = (0, 3) then some ⟨.white, .bishop⟩ else none
private def halfTrace : MoveTrace := .empty ⟨halfBoard, .white, {}, none⟩

private theorem half_rays (c : Color) (d : RayDirection) :
    halfTrace.CheckingRay (halfKings c) c d ↔
      (c = .white ∧ d = .northEast) ∨ (c = .black ∧ d = .northWest) := by
  cases c <;> cases d <;> decide

private theorem half_crossings : halfTrace.checkingCrossings halfKings = {(3/2, 3/2)} := by
  ext p
  rw [MoveTrace.mem_checkingCrossings_iff]
  simp only [half_rays]
  simp
  norm_num [halfKings, nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod]
  exact eq_comm

-- A half-integer crossing stays rational: it is not rounded onto the board.
-- A singleton supports A1 but does not meet the precondition for A2.
example : halfTrace.rayCrossingParameters halfKings .white .northEast = {3/2} := by
  rw [MoveTrace.rayCrossingParameters, half_crossings]
  norm_num [halfKings, Pos.toPlane, Pos.toInt, OnRationalRay, rayParameter, rayPoint,
    RayDirection.vector, Finset.filter_singleton]

private def overlapKings : Color → Pos | .white => (0, 0) | .black => (6, 0)
private def overlapBoard : Board := fun q =>
  if q = (2, 0) then some ⟨.black, .rook⟩
  else if q = (4, 0) then some ⟨.white, .rook⟩ else none
private def overlapTrace : MoveTrace := .empty ⟨overlapBoard, .white, {}, none⟩
private theorem overlap_rays (c : Color) (d : RayDirection) :
    overlapTrace.CheckingRay (overlapKings c) c d ↔
      (c = .white ∧ d = .east) ∨ (c = .black ∧ d = .west) := by
  cases c <;> cases d <;> decide

-- Without the positive periodic hypotheses the complete crossing relation
-- can contain a whole segment, while the nonparallel enumeration is empty.
example : overlapTrace.checkingCrossings overlapKings = ∅ := by
  ext p
  rw [MoveTrace.mem_checkingCrossings_iff]
  simp only [overlap_rays]
  simp [nonparallelIntersection, rayDet, RayDirection.vector]

example (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 6) :
    overlapTrace.CheckingCrossing overlapKings (t, 0) := by
  intro owner
  cases owner
  · refine ⟨.east, (overlap_rays _ _).mpr (by simp), ?_⟩
    simpa [overlapKings, OnRationalRay, rayParameter, rayPoint,
      RayDirection.vector, Pos.toPlane, Pos.toInt] using ht
  · refine ⟨.west, (overlap_rays _ _).mpr (by simp), ?_⟩
    norm_num [overlapKings, OnRationalRay, rayParameter, rayPoint,
      RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod]
    exact ht'

private def originKings : Color → Pos := fun _ => (3, 3)
private def originBoard : Board := fun q =>
  if q = (3, 4) ∨ q = (4, 3) then some ⟨.black, .rook⟩
  else if q = (2, 4) then some ⟨.white, .bishop⟩ else none
private def originTrace : MoveTrace := .empty ⟨originBoard, .white, {}, none⟩
private theorem origin_rays (c : Color) (d : RayDirection) :
    originTrace.CheckingRay (originKings c) c d ↔
      (c = .white ∧ (d = .north ∨ d = .east)) ∨ (c = .black ∧ d = .northWest) := by
  cases c <;> cases d <;> decide

-- Coincident origins intentionally do not satisfy KingsWellPlaced. Two
-- direction pairs produce one point, and the finite set removes the duplicate.
example : originTrace.checkingCrossings originKings = {(3, 3)} := by
  ext p
  rw [MoveTrace.mem_checkingCrossings_iff]
  simp only [origin_rays]
  simp [and_or_left, or_and_right, exists_or]
  norm_num [originKings, nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod]
  exact eq_comm

private def outsideKings : Color → Pos | .white => (0, 6) | .black => (7, 0)
private def outsideBoard : Board := fun q =>
  if q = (1, 7) then some ⟨.black, .bishop⟩
  else if q = (7, 1) then some ⟨.white, .rook⟩ else none
private def outsideTrace : MoveTrace := .empty ⟨outsideBoard, .white, {}, none⟩

-- Actual board checkers can define rays meeting beyond the board edge. The
-- enumeration is in the rational plane and must not clip that intersection.
example : (7, 13) ∈ outsideTrace.checkingCrossings outsideKings := by
  apply (MoveTrace.mem_checkingCrossings_iff _ _ _).mpr
  refine ⟨.northEast, .north, by decide, by decide, ?_⟩
  norm_num [outsideKings, nonparallelIntersection, rayIntersectionParameters, rayOffset, rayDet,
    rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt, Fin.coe_ofNat_eq_mod]

-- Conditional A1/A2 statements apply to the complete predicate on a genuine
-- positive periodic trace, with no separate nonparallel or origin assumption.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len)
    (c : Color) (d : RayDirection) (h : 1 < (tr.rayCrossingParameters (kp 0) c d).card) :
    tr.CheckingCrossing (kp 0) (tr.secondCheckingCrossing (kp 0) c d h) ∧
    planeTaxicabDistance (kp 0 c).toPlane (tr.firstCheckingCrossing (kp 0) c d (by omega)) <
      planeTaxicabDistance (kp 0 c).toPlane (tr.secondCheckingCrossing (kp 0) c d h) := by
  refine ⟨(tr.mem_checkingCrossings_iff_of_periodic_checks kp hl hk hc hp hn _).mp
    (tr.secondCheckingCrossing_spec (kp 0) c d h).1, ?_⟩
  exact tr.checkingCrossingAt_distance_strictMono (kp 0) c d (show (⟨0, by omega⟩ : Fin _) < ⟨1, h⟩ from Nat.zero_lt_one)

-- The two witnesses may arrive in reverse order. The cardinality used for
-- A2 is derived from their distinctness, not supplied as an extra premise.
private theorem two_card (c : Color) :
    2 ≤ ((twoTrace c).rayCrossingParameters (twoKings c) c .north).card := by
  apply (twoTrace c).rayCrossingParameters_card_two_le_of_distinct (twoKings c) c .north
    (0, 6) (0, 2) (by decide)
  · rw [two_crossings]; simp
  · rw [two_crossings]; simp
  · cases c <;> norm_num [twoKings, OnRationalRay, rayParameter, rayPoint,
      RayDirection.vector, Pos.toPlane, Pos.toInt]
  · cases c <;> norm_num [twoKings, OnRationalRay, rayParameter, rayPoint,
      RayDirection.vector, Pos.toPlane, Pos.toInt]

example (c : Color) :
    rayParameter (twoKings c c).toPlane .north
      ((twoTrace c).secondCheckingCrossing (twoKings c) c .north (two_card c)) ≤ 6 := by
  apply (twoTrace c).secondCheckingCrossing_parameter_le_of_two (twoKings c) c .north
    (two_card c) (0, 6) (0, 2) 6 (by decide)
  · rw [two_crossings]; simp
  · rw [two_crossings]; simp
  all_goals cases c <;> norm_num [twoKings, OnRationalRay, rayParameter, rayPoint,
    RayDirection.vector, Pos.toPlane, Pos.toInt]

-- Equality at A2 and strict distance beyond it are both allowed by the
-- order statement. This static board is not a positive checking period.
example (c : Color) :
    let A₂ := (twoTrace c).secondCheckingCrossing (twoKings c) c .north (two_card c)
    A₂ = (0, 6) ∧ planeTaxicabDistance (twoKings c c).toPlane A₂ <
      planeTaxicabDistance (twoKings c c).toPlane (0, 7) := by
  dsimp only
  have he : (twoTrace c).secondCheckingCrossing (twoKings c) c .north (two_card c) = (0, 6) := by
    simp only [MoveTrace.secondCheckingCrossing, MoveTrace.checkingCrossingAt,
      Finset.orderEmbOfFin_apply, two_parameters]
    have hs : ({2, 6} : Finset ℚ).sort (· ≤ ·) = [2, 6] := by
      rw [Finset.sort_insert (· ≤ ·) (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; norm_num)
        (by norm_num)]
      simp
    simp only [hs, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
    cases c <;> norm_num [twoKings, rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt]
  refine ⟨he, ?_⟩
  rw [he]
  cases c <;> norm_num [twoKings, planeTaxicabDistance, Pos.toPlane, Pos.toInt]

-- All directions and rational parameters, including half-integer crossings:
-- witness points need not be board squares or the first two in the ordering.
example (tr : MoveTrace) (kp : Color → Pos) (c : Color) (d : RayDirection)
    (s t : ℚ) (hs : 0 ≤ s) (hst : s < t)
    (hA : rayPoint (kp c).toPlane d s ∈ tr.checkingCrossings kp)
    (hB : rayPoint (kp c).toPlane d t ∈ tr.checkingCrossings kp) :
    ∃ h : 1 < (tr.rayCrossingParameters kp c d).card,
      rayParameter (kp c).toPlane d (tr.secondCheckingCrossing kp c d h) ≤ t := by
  have hne : rayPoint (kp c).toPlane d s ≠ rayPoint (kp c).toPlane d t :=
    fun he => (ne_of_lt hst) (rayPoint_injective _ _ he)
  have hrA := (onRationalRay_rayPoint (kp c).toPlane d s).mpr hs
  have hrB := (onRationalRay_rayPoint (kp c).toPlane d t).mpr (le_trans hs (le_of_lt hst))
  have hcard := tr.rayCrossingParameters_card_two_le_of_distinct kp c d _ _ hne hA hB hrA hrB
  exact ⟨hcard, tr.secondCheckingCrossing_parameter_le_of_two kp c d hcard _ _ t hne hA hB
    hrA hrB (by simpa using le_of_lt hst) (by simp)⟩

-- For any state (including first/last), an actual checker supplies the ray
-- premise itself. No crossing-count or immobility assumption is added.
example (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len)
    (k : Fin (tr.len + 1)) (c : Color) (C : Pos) (X : Piece)
    (hX : (tr.states k).board C = some X) (ho : X.owner = c.opponent)
    (ha : attacks (tr.states k).board X C (kp k c)) (d : RayDirection)
    (hdir : OnRay (kp 0 c) d C) :
    ∃ h : 1 < (tr.rayCrossingParameters (kp 0) c d).card,
      C.toPlane = tr.secondCheckingCrossing (kp 0) c d h ∨
      planeTaxicabDistance (kp 0 c).toPlane (tr.secondCheckingCrossing (kp 0) c d h) <
        planeTaxicabDistance (kp 0 c).toPlane C.toPlane := by
  have hr : tr.CheckingRay (kp 0 c) c d := by
    refine ⟨k, C, X, hX, ho, ?_, hdir⟩
    rwa [tr.kingPositions_eq_of_periodic_checks kp hl hk hc hp k 0] at ha
  exact ⟨_, tr.checker_eq_or_beyond_second_of_periodic_checks kp hl hk hc hp hn c d hr k C X hX ho ha hdir⟩

private def atSecondTrace (c : Color) : MoveTrace :=
  .empty ⟨(twoBoard c).relocate (0, 7) (0, 6) none, c, {}, none⟩

private theorem atSecond_parameters (c : Color) :
    (atSecondTrace c).rayCrossingParameters (twoKings c) c .north = {2, 6} := by
  have hr (owner : Color) (d : RayDirection) :
      (atSecondTrace c).CheckingRay (twoKings c owner) owner d ↔
        (twoTrace c).CheckingRay (twoKings c owner) owner d := by
    cases c <;> cases owner <;> cases d <;> decide
  have he : (atSecondTrace c).checkingCrossings (twoKings c) = (twoTrace c).checkingCrossings (twoKings c) := by
    ext p
    simp only [MoveTrace.mem_checkingCrossings_iff, hr]
  simpa only [MoveTrace.rayCrossingParameters, he] using two_parameters c

private theorem atSecond_position (c : Color) :
    (atSecondTrace c).secondCheckingCrossing (twoKings c) c .north
      (by rw [atSecond_parameters]; decide) = (0, 6) := by
  simp only [MoveTrace.secondCheckingCrossing, MoveTrace.checkingCrossingAt,
    Finset.orderEmbOfFin_apply, atSecond_parameters]
  have hs : ({2, 6} : Finset ℚ).sort (· ≤ ·) = [2, 6] := by
    rw [Finset.sort_insert (· ≤ ·) (by intro b hb; simp only [Finset.mem_singleton] at hb; subst b; norm_num)
      (by norm_num)]
    simp
  simp only [hs, Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ]
  cases c <;> norm_num [twoKings, rayPoint, RayDirection.vector, Pos.toPlane, Pos.toInt]

-- A genuine checker at A2 can be immovable in a zero-length trace, even
-- with well-placed kings and all remaining trace conditions. Length matters.
example (c : Color) :
    (atSecondTrace c).FollowsLegalMoves ∧
    (atSecondTrace c).KingsWellPlaced (fun _ => twoKings c) ∧
    (atSecondTrace c).EveryMoveChecksOpponent (fun _ => twoKings c) ∧
    (atSecondTrace c).BoardTurnPeriodic ∧ (atSecondTrace c).len = 0 ∧
    ((atSecondTrace c).states 0).board (0, 6) = some ⟨c.opponent, .rook⟩ ∧
    attacks ((atSecondTrace c).states 0).board ⟨c.opponent, .rook⟩ (0, 6) (twoKings c c) ∧
    (atSecondTrace c).ImmovableAt (0, 6) ∧
    (atSecondTrace c).secondCheckingCrossing (twoKings c) c .north
      (by rw [atSecond_parameters]; decide) = (0, 6) := by
  refine ⟨(fun i => Fin.elim0 i), ?_, (fun i => Fin.elim0 i), ⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, atSecond_position c⟩
  · unfold MoveTrace.KingsWellPlaced MPC.Chess.KingsWellPlaced
    cases c <;> decide
  all_goals cases c <;> decide

-- The general rational-order API identifies the only earlier crossing;
-- the example does not assume that candidate points are board squares.
example (c : Color) (q : PlanePoint) (hm : q ∈ (atSecondTrace c).checkingCrossings (twoKings c))
    (hr : OnRationalRay (twoKings c c).toPlane .north q)
    (hlt : rayParameter (twoKings c c).toPlane .north q < 6) :
    q = (atSecondTrace c).firstCheckingCrossing (twoKings c) c .north
      (by rw [atSecond_parameters]; decide) := by
  apply (atSecondTrace c).crossing_before_second_eq_first (twoKings c) c .north
    (by rw [atSecond_parameters]; decide) q hm hr
  rw [atSecond_position]
  simpa [rayParameter, twoKings, Pos.toPlane, Pos.toInt] using hlt

end MPC.Chess.Tests
