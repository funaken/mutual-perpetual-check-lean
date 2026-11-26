import MPC.Chess.CheckingCrossingSet
import Mathlib.Data.Finset.Sort

/-! Distinct crossings on a fixed ray, ordered by its nonnegative rational
parameter. First and second crossings require explicit cardinality bounds. -/

namespace MPC.Chess

/-- The rational taxicab distance; on a fixed ray it induces the same order
as distance along that ray. No square roots or real angles are needed. -/
def planeTaxicabDistance (o p : PlanePoint) : ℚ := |p.1 - o.1| + |p.2 - o.2|

theorem planeTaxicabDistance_rayPoint (o : PlanePoint) (d : RayDirection) (t : ℚ)
    (ht : 0 ≤ t) : planeTaxicabDistance o (rayPoint o d t) =
      t * ((|d.vector.1| : ℤ) + |d.vector.2| : ℤ) := by
  have h_one : |(1 : ℚ)| = 1 := abs_of_nonneg (by norm_num)
  cases d <;> norm_num [planeTaxicabDistance, rayPoint, RayDirection.vector, abs_of_nonneg ht, h_one] <;> ring

theorem OnRationalRay.parameter_lt_iff_distance_lt {o p q : PlanePoint} {d : RayDirection}
    (hp : OnRationalRay o d p) (hq : OnRationalRay o d q) :
    rayParameter o d p < rayParameter o d q ↔ planeTaxicabDistance o p < planeTaxicabDistance o q := by
  conv_rhs => rw [hp.2, hq.2, planeTaxicabDistance_rayPoint _ _ _ hp.1,
    planeTaxicabDistance_rayPoint _ _ _ hq.1]
  cases d <;> norm_num [RayDirection.vector]

namespace MoveTrace

/-- Distinct parameters of enumerated crossings on one closed rational ray. -/
def rayCrossingParameters (tr : MoveTrace) (kp : Color → Pos) (c : Color) (d : RayDirection) : Finset ℚ :=
  ((tr.checkingCrossings kp).filter (OnRationalRay (kp c).toPlane d)).image
    (rayParameter (kp c).toPlane d)

theorem mem_rayCrossingParameters_iff (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (t : ℚ) : t ∈ tr.rayCrossingParameters kp c d ↔
      0 ≤ t ∧ rayPoint (kp c).toPlane d t ∈ tr.checkingCrossings kp := by
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hmem, hr⟩ := Finset.mem_filter.mp hp
    subst t
    exact ⟨hr.1, hr.2 ▸ hmem⟩
  · rintro ⟨ht, hm⟩
    apply Finset.mem_image.mpr
    exact ⟨_, Finset.mem_filter.mpr ⟨hm, (onRationalRay_rayPoint _ _ _).mpr ht⟩,
      rayParameter_rayPoint _ _ _⟩

theorem mem_rayCrossingParameters_iff_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection) (t : ℚ) :
    t ∈ tr.rayCrossingParameters (kp 0) c d ↔
      0 < t ∧ tr.CheckingCrossing (kp 0) (rayPoint (kp 0 c).toPlane d t) := by
  rw [tr.mem_rayCrossingParameters_iff,
    tr.mem_checkingCrossings_iff_of_periodic_checks kp hl hk hc hp hn]
  constructor
  · rintro ⟨ht, hx⟩
    refine ⟨lt_of_le_of_ne ht ?_, hx⟩
    intro he
    apply tr.checkingCrossing_ne_king_of_periodic_checks kp hl hk hc hp hn _ hx c
    simp [← he]
  · rintro ⟨ht, hx⟩
    exact ⟨le_of_lt ht, hx⟩

/-- The index is zero based: index 0 is the paper's A₁ and index 1 is A₂.
The finite index prevents selecting a nonexistent crossing. -/
def checkingCrossingAt (tr : MoveTrace) (kp : Color → Pos) (c : Color) (d : RayDirection)
    (i : Fin (tr.rayCrossingParameters kp c d).card) : PlanePoint :=
  rayPoint (kp c).toPlane d ((tr.rayCrossingParameters kp c d).orderEmbOfFin rfl i)

@[simp]
theorem checkingCrossingAt_parameter (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (i : Fin (tr.rayCrossingParameters kp c d).card) :
    rayParameter (kp c).toPlane d (tr.checkingCrossingAt kp c d i) =
      (tr.rayCrossingParameters kp c d).orderEmbOfFin rfl i := by
  exact rayParameter_rayPoint _ _ _

theorem checkingCrossingAt_mem (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (i : Fin (tr.rayCrossingParameters kp c d).card) :
    tr.checkingCrossingAt kp c d i ∈ tr.checkingCrossings kp ∧
      OnRationalRay (kp c).toPlane d (tr.checkingCrossingAt kp c d i) := by
  have h := (tr.mem_rayCrossingParameters_iff kp c d _).mp
    ((tr.rayCrossingParameters kp c d).orderEmbOfFin_mem rfl i)
  exact ⟨h.2, (onRationalRay_rayPoint _ _ _).mpr h.1⟩

/-- Enumeration is surjective on the crossings of this ray, not just sound. -/
theorem exists_checkingCrossingAt_iff (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (p : PlanePoint) :
    (∃ i, tr.checkingCrossingAt kp c d i = p) ↔
      p ∈ tr.checkingCrossings kp ∧ OnRationalRay (kp c).toPlane d p := by
  constructor
  · rintro ⟨i, rfl⟩
    exact tr.checkingCrossingAt_mem kp c d i
  · rintro ⟨hm, hr⟩
    have ht : rayParameter (kp c).toPlane d p ∈ tr.rayCrossingParameters kp c d :=
      (tr.mem_rayCrossingParameters_iff kp c d _).mpr ⟨hr.1, hr.2 ▸ hm⟩
    obtain ⟨i, hi⟩ := Set.ext_iff.mp ((tr.rayCrossingParameters kp c d).range_orderEmbOfFin rfl)
      (rayParameter (kp c).toPlane d p) |>.mpr ht
    exact ⟨i, by unfold checkingCrossingAt; rw [hi]; exact hr.2.symm⟩

theorem checkingCrossingAt_parameter_strictMono (tr : MoveTrace) (kp : Color → Pos)
    (c : Color) (d : RayDirection) :
    StrictMono (fun i => rayParameter (kp c).toPlane d (tr.checkingCrossingAt kp c d i)) := by
  simpa only [checkingCrossingAt_parameter] using
    (tr.rayCrossingParameters kp c d).orderEmbOfFin rfl |>.strictMono

theorem checkingCrossingAt_distance_strictMono (tr : MoveTrace) (kp : Color → Pos)
    (c : Color) (d : RayDirection) :
    StrictMono (fun i => planeTaxicabDistance (kp c).toPlane (tr.checkingCrossingAt kp c d i)) := by
  intro i j hij
  exact ((tr.checkingCrossingAt_mem kp c d i).2.parameter_lt_iff_distance_lt
    (tr.checkingCrossingAt_mem kp c d j).2).mp
      (tr.checkingCrossingAt_parameter_strictMono kp c d hij)

/-- A₁ is only defined when this ray has at least one enumerated crossing. -/
def firstCheckingCrossing (tr : MoveTrace) (kp : Color → Pos) (c : Color) (d : RayDirection)
    (h : 0 < (tr.rayCrossingParameters kp c d).card) : PlanePoint :=
  tr.checkingCrossingAt kp c d ⟨0, h⟩

/-- A₂ requires two distinct crossings; their existence is not assumed in
`CheckingRay` and is not proved by this definition. -/
def secondCheckingCrossing (tr : MoveTrace) (kp : Color → Pos) (c : Color) (d : RayDirection)
    (h : 1 < (tr.rayCrossingParameters kp c d).card) : PlanePoint :=
  tr.checkingCrossingAt kp c d ⟨1, h⟩

/-- A₁ is a crossing on the ray and has the least parameter among all such
crossings. This applies even when the arbitrary trace has just one crossing. -/
theorem firstCheckingCrossing_spec (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (h : 0 < (tr.rayCrossingParameters kp c d).card) :
    tr.firstCheckingCrossing kp c d h ∈ tr.checkingCrossings kp ∧
    OnRationalRay (kp c).toPlane d (tr.firstCheckingCrossing kp c d h) ∧
    ∀ p ∈ tr.checkingCrossings kp, OnRationalRay (kp c).toPlane d p →
      rayParameter (kp c).toPlane d (tr.firstCheckingCrossing kp c d h) ≤
        rayParameter (kp c).toPlane d p := by
  refine ⟨(tr.checkingCrossingAt_mem kp c d ⟨0, h⟩).1,
    (tr.checkingCrossingAt_mem kp c d ⟨0, h⟩).2, ?_⟩
  intro p hm hr
  obtain ⟨i, rfl⟩ := (tr.exists_checkingCrossingAt_iff kp c d p).mpr ⟨hm, hr⟩
  exact (tr.checkingCrossingAt_parameter_strictMono kp c d).monotone (show (⟨0, h⟩ : Fin _) ≤ i from Nat.zero_le _)

/-- A₂ is strictly after A₁ and is the least crossing other than A₁. In
particular there can be no enumerated crossing strictly between them. -/
theorem secondCheckingCrossing_spec (tr : MoveTrace) (kp : Color → Pos) (c : Color)
    (d : RayDirection) (h : 1 < (tr.rayCrossingParameters kp c d).card) :
    tr.secondCheckingCrossing kp c d h ∈ tr.checkingCrossings kp ∧
    OnRationalRay (kp c).toPlane d (tr.secondCheckingCrossing kp c d h) ∧
    rayParameter (kp c).toPlane d (tr.firstCheckingCrossing kp c d (by omega)) <
      rayParameter (kp c).toPlane d (tr.secondCheckingCrossing kp c d h) ∧
    ∀ p ∈ tr.checkingCrossings kp, OnRationalRay (kp c).toPlane d p →
      p ≠ tr.firstCheckingCrossing kp c d (by omega) →
      rayParameter (kp c).toPlane d (tr.secondCheckingCrossing kp c d h) ≤
        rayParameter (kp c).toPlane d p := by
  refine ⟨(tr.checkingCrossingAt_mem kp c d ⟨1, h⟩).1,
    (tr.checkingCrossingAt_mem kp c d ⟨1, h⟩).2,
    tr.checkingCrossingAt_parameter_strictMono kp c d (show (⟨0, by omega⟩ : Fin _) < ⟨1, h⟩ from Nat.zero_lt_one), ?_⟩
  intro p hm hr hn
  obtain ⟨i, rfl⟩ := (tr.exists_checkingCrossingAt_iff kp c d p).mpr ⟨hm, hr⟩
  have hi : 1 ≤ i.val := by
    by_contra! hz
    have he : i = ⟨0, by omega⟩ := Fin.ext (show i.val = 0 by omega)
    exact hn (by simp only [he, firstCheckingCrossing])
  exact (tr.checkingCrossingAt_parameter_strictMono kp c d).monotone hi

end MoveTrace
end MPC.Chess
