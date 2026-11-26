import MPC.Chess.CheckingCrossingOrder
import MPC.Chess.CheckingCrossingWitness

/-! Lemma 6.4(1): every actual checking ray has at least two crossings,
and each checker lies at or beyond its second crossing. -/

namespace MPC.Chess

private theorem parameter_lt_of_between {k C A : Pos} {d : RayDirection}
    (hC : OnRay k d C) (hA : Between C k A) :
    rayParameter k.toPlane d A.toPlane < rayParameter k.toPlane d C.toPlane := by
  have hrA := (onRationalRay_toPlane_iff k A d).mpr (Or.inr (hC.of_between hA))
  have hrC := (onRationalRay_toPlane_iff k C d).mpr (Or.inr hC)
  apply (hrA.parameter_lt_iff_distance_lt hrC).mpr
  have hdist := (hC.between_iff_distance (hC.of_between hA)).mp hA
  unfold rayDistance at hdist
  unfold planeTaxicabDistance Pos.toPlane
  simp only
  exact_mod_cast hdist

namespace MoveTrace

/-- Distinct points on one ray have distinct parameters, even for non-lattice
crossings. No periodicity or checking-ray hypothesis is needed here. -/
theorem rayCrossingParameters_card_two_le_of_distinct (tr : MoveTrace)
    (kp : Color → Pos) (c : Color) (d : RayDirection) (A B : PlanePoint)
    (hne : A ≠ B) (hA : A ∈ tr.checkingCrossings kp) (hB : B ∈ tr.checkingCrossings kp)
    (hrA : OnRationalRay (kp c).toPlane d A) (hrB : OnRationalRay (kp c).toPlane d B) :
    2 ≤ (tr.rayCrossingParameters kp c d).card := by
  apply Finset.one_lt_card.mpr
  refine ⟨_, (tr.mem_rayCrossingParameters_iff kp c d _).mpr ⟨hrA.1, hrA.2 ▸ hA⟩,
    _, (tr.mem_rayCrossingParameters_iff kp c d _).mpr ⟨hrB.1, hrB.2 ▸ hB⟩, ?_⟩
  intro he
  exact hne (hrA.2.trans (by rw [he]; exact hrB.2.symm))

/-- Two distinct crossings below a parameter bound force A₂ below that bound.
The witnesses need not themselves be A₁ and A₂, nor be given in sorted order. -/
theorem secondCheckingCrossing_parameter_le_of_two (tr : MoveTrace)
    (kp : Color → Pos) (c : Color) (d : RayDirection)
    (h : 1 < (tr.rayCrossingParameters kp c d).card) (A B : PlanePoint) (t : ℚ)
    (hne : A ≠ B) (hA : A ∈ tr.checkingCrossings kp) (hB : B ∈ tr.checkingCrossings kp)
    (hrA : OnRationalRay (kp c).toPlane d A) (hrB : OnRationalRay (kp c).toPlane d B)
    (hAt : rayParameter (kp c).toPlane d A ≤ t) (hBt : rayParameter (kp c).toPlane d B ≤ t) :
    rayParameter (kp c).toPlane d (tr.secondCheckingCrossing kp c d h) ≤ t := by
  have hs := (tr.secondCheckingCrossing_spec kp c d h).2.2.2
  by_cases he : A = tr.firstCheckingCrossing kp c d (by omega)
  · exact (hs B hB hrB (by intro hb; exact hne (he.trans hb.symm))).trans hBt
  · exact (hs A hA hrA he).trans hAt

/-- The cardinality needed to define A₂ follows from the periodic trace
conditions and an actual checking ray; it is not a new model assumption. -/
theorem rayCrossingParameters_card_two_le_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) :
    2 ≤ (tr.rayCrossingParameters (kp 0) c d).card := by
  obtain ⟨A, B, hne, hA, hB, hrA, hrB⟩ :=
    tr.checkingRay_two_crossings_of_periodic_checks kp hl hk hc hp hn c d hr
  exact tr.rayCrossingParameters_card_two_le_of_distinct (kp 0) c d A.toPlane B.toPlane
    (fun he => hne (Pos.toPlane_injective he)) hA hB
    ((onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hrA))
    ((onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hrB))

/-- The checker parameter is at least A₂'s. `hr` and the actual checker are
separate inputs so one selected A₂ can be reused at every state on this ray. -/
theorem checker_parameter_ge_second_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (k : Fin (tr.len + 1)) (C : Pos) (X : Piece)
    (hX : (tr.states k).board C = some X) (ho : X.owner = c.opponent)
    (ha : attacks (tr.states k).board X C (kp k c)) (hdir : OnRay (kp 0 c) d C) :
    rayParameter (kp 0 c).toPlane d (tr.secondCheckingCrossing (kp 0) c d
      (tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn c d hr)) ≤
      rayParameter (kp 0 c).toPlane d C.toPlane := by
  obtain ⟨A, B, hne, hA, hB, hbA, hbB⟩ :=
    tr.checker_two_crossings_of_periodic_checks kp hl hk hc hp hn k c C X hX ho ha
  have hrA := hdir.of_between hbA
  have hrB : OnRay (kp 0 c) d B := by
    rcases hbB with rfl | hbB
    · exact hdir
    · exact hdir.of_between hbB
  apply tr.secondCheckingCrossing_parameter_le_of_two (kp 0) c d _ A.toPlane B.toPlane _
    (fun he => hne (Pos.toPlane_injective he)) hA hB
    ((onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hrA))
    ((onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hrB))
  · exact le_of_lt (parameter_lt_of_between hdir hbA)
  · rcases hbB with rfl | hbB
    · exact le_refl _
    · exact le_of_lt (parameter_lt_of_between hdir hbB)

/-- Paper Lemma 6.4(1): the checker is A₂ itself or strictly farther from the
king on the same ray. A₂ remains a rational point, with no board rounding. -/
theorem checker_eq_or_beyond_second_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len) (c : Color) (d : RayDirection)
    (hr : tr.CheckingRay (kp 0 c) c d) (k : Fin (tr.len + 1)) (C : Pos) (X : Piece)
    (hX : (tr.states k).board C = some X) (ho : X.owner = c.opponent)
    (ha : attacks (tr.states k).board X C (kp k c)) (hdir : OnRay (kp 0 c) d C) :
    let A₂ := tr.secondCheckingCrossing (kp 0) c d
      (tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn c d hr)
    C.toPlane = A₂ ∨
      planeTaxicabDistance (kp 0 c).toPlane A₂ < planeTaxicabDistance (kp 0 c).toPlane C.toPlane := by
  dsimp only
  have hrA := (tr.secondCheckingCrossing_spec (kp 0) c d
    (tr.rayCrossingParameters_card_two_le_of_periodic_checks kp hl hk hc hp hn c d hr)).2.1
  have hrC := (onRationalRay_toPlane_iff _ _ _).mpr (Or.inr hdir)
  have hle := tr.checker_parameter_ge_second_of_periodic_checks kp hl hk hc hp hn c d hr k C X hX ho ha hdir
  rcases lt_or_eq_of_le hle with hlt | he
  · exact Or.inr ((hrA.parameter_lt_iff_distance_lt hrC).mp hlt)
  · exact Or.inl (hrC.2.trans (by rw [← he]; exact hrA.2.symm))

end MoveTrace
end MPC.Chess
