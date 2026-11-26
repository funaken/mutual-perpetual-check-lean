import MPC.Basic.Lemmas
import MPC.Geometry.KingMoveGeometry
/-!
# MPC.Geometry.KingImmobility

The paper's Proposition 2.2 (kings are immovable) on independent traces. A trace
is periodic when its last state equals its first. In a mutual-check trace the
kings' alignment can only be lost: a king move needs aligned kings beforehand, and any other move leaves both kings in place. With the
owner-oriented movement condition a king move also ends the alignment, so in a
periodic trace no king ever moves and both initial king squares are immovable in
the sense of Definition 2.1. Drops on a king's square are excluded by deriving a
contradiction, not by an extra premise. -/

namespace MPC

/-- Both kings stand on a common file, rank, or diagonal. Independent of the turn. -/
def KingsAligned (kp : Player → Pos) : Prop :=
  Pos.isAligned (kp .sente) (kp .gote)

/-- Alignment is symmetric. -/
theorem Pos.isAligned_comm (a b : Pos) : Pos.isAligned a b ↔ Pos.isAligned b a := by
  simp only [Pos.isAligned, Pos.dirTo, Prod.mk.injEq, Int.natAbs_eq_natAbs_iff]
  constructor <;> intro h <;> omega

private theorem kingsAligned_iff (kp : Player → Pos) (p : Player) :
    KingsAligned kp ↔ Pos.isAligned (kp p) (kp p.opponent) := by
  cases p
  · exact Iff.rfl
  · exact Pos.isAligned_comm _ _

namespace MoveTrace

/-- The trace returns to its initial state: board, hands, and turn all agree. -/
def IsPeriodic (tr : MoveTrace) : Prop :=
  tr.states (Fin.last tr.len) = tr.states 0

/-- Move `i` moves the mover's own king. -/
def KingMoveAt (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos) (i : Fin tr.len) :
    Prop :=
  ∃ (dst : Pos) (promote : Bool),
    tr.moves i = .boardMove (kp i.castSucc (tr.before i).turn) dst promote

/-- The source of a board move that is not a king move holds neither king. -/
private theorem kingPos_ne_src (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (hm : tr.moves i = .boardMove src dst promote)
    (h : ¬ tr.KingMoveAt kp i) (o : Player) : kp i.castSucc o ≠ src := by
  intro he
  rcases Player.eq_or_eq_opponent o (tr.before i).turn with rfl | rfl
  · exact h ⟨dst, promote, by rw [hm, he]⟩
  · obtain ⟨piece, hp, ho⟩ := hs i src dst promote hm
    rw [← he] at hp
    have hking := (hk i.castSucc).king_present (tr.before i).turn.opponent
    have hpiece := Option.some.inj (hp.symm.trans hking)
    rw [hpiece] at ho
    exact Player.opponent_ne_self _ ho

/-- A move that is not a king move leaves both king positions unchanged. -/
theorem kingPos_succ_of_not_kingMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (i : Fin tr.len) (h : ¬ tr.KingMoveAt kp i) : kp i.succ = kp i.castSucc := by
  rcases hm : tr.moves i with ⟨src, dst, promote⟩ | ⟨pt, dst⟩
  · funext o
    rw [tr.kingPos_succ_of_boardMove kp ht hk i src dst promote hm o]
    simp only [kingPosAfterBoardMove, ite_eq_right (kingPos_ne_src tr kp hs hk i src dst promote hm h o)]
  · exact tr.kingPos_succ_of_dropMove kp ht hk i pt dst hm

/-- A board move never lands on a king that does not move: a king on the
    destination afterwards must have come from the source. -/
theorem boardMove_dst_ne_kingPos (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (hm : tr.moves i = .boardMove src dst promote)
    (o : Player) (h : kp i.castSucc o ≠ src) : kp i.castSucc o ≠ dst := by
  intro hd
  have hpos : kp i.succ o = dst := by
    rw [tr.kingPos_succ_of_boardMove kp ht hk i src dst promote hm o]
    simp only [kingPosAfterBoardMove, ite_eq_right h]
    exact hd
  have hking : (tr.after i).board.grid dst = some ⟨o, .king⟩ := by
    rw [← hpos]
    exact (hk i.succ).king_present o
  rw [tr.boardMove_grid_dst ht i src dst promote hm] at hking
  cases hsrc : (tr.before i).board.grid src with
  | none =>
    rw [hsrc] at hking
    cases hking
  | some piece =>
    obtain ⟨p, pt⟩ := piece
    rw [hsrc] at hking
    have hpk : p = o ∧ pt = .king := by
      cases promote <;> simpa [PieceType.promote_eq_king_iff] using hking
    obtain ⟨rfl, rfl⟩ := hpk
    exact h ((hk i.castSucc p src).mp hsrc).symm

/-- In a mutual-check trace satisfying the stated transition and safety premises, no drop lands on a
    king's square. Placement allows only re-dropping the mover's own king there;
    that drop must check, so the kings would stand adjacent. -/
theorem dropMove_dst_ne_kingPos (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (pt : PieceType) (dst : Pos)
    (hm : tr.moves i = .dropMove pt dst) (o : Player) : kp i.castSucc o ≠ dst := by
  intro hd
  have hpos : kp i.succ o = dst := by
    rw [tr.kingPos_succ_of_dropMove kp ht hk i pt dst hm]
    exact hd
  have hking : (tr.after i).board.grid dst = some ⟨o, .king⟩ := by
    rw [← hpos]
    exact (hk i.succ).king_present o
  rw [tr.dropMove_grid_dst ht i pt dst hm] at hking
  simp only [Option.some.injEq, Piece.mk.injEq] at hking
  obtain ⟨ho, hpt⟩ := hking
  subst ho hpt
  rcases (tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe
    h0).mp hc i with ⟨piece, hp, _, ha⟩ | hu
  · rw [hm] at hp ha
    change (tr.after i).board.grid dst = some piece at hp
    rw [tr.dropMove_grid_dst ht i .king dst hm] at hp
    cases hp
    apply tr.kings_not_adjacent kp hk hsafe h0 i.succ (tr.before i).turn
    rw [hpos]
    exact ha
  · rw [hm] at hu
    exact hu

/-- Alignment can only be lost: if the kings are aligned after a move, they were
    aligned before it. No movement condition is needed. -/
theorem kingsAligned_castSucc_of_succ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len)
    (h : KingsAligned (kp i.succ)) : KingsAligned (kp i.castSucc) := by
  by_cases hkm : tr.KingMoveAt kp i
  · obtain ⟨dst, promote, hm⟩ := hkm
    exact (kingsAligned_iff _ (tr.before i).turn).mpr
      (tr.kingMove_aligned_before kp ht hs hk hsafe h0 hc i dst promote hm)
  · rwa [← tr.kingPos_succ_of_not_kingMove kp ht hs hk i hkm]

/-- Alignment at a later state implies alignment at every earlier state. -/
theorem kingsAligned_of_le (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) {j k : Fin (tr.len + 1)} (hjk : j ≤ k)
    (h : KingsAligned (kp k)) : KingsAligned (kp j) := by
  revert hjk h
  induction k using Fin.induction with
  | zero =>
    intro hjk h
    rw [Fin.le_zero_iff.mp hjk]
    exact h
  | succ i ih =>
    intro hjk h
    by_cases he : j = i.succ
    · rw [he]
      exact h
    · have hlt : j < i.succ := Nat.lt_of_le_of_ne hjk fun hv => he (Fin.ext hv)
      exact ih (Fin.le_castSucc_iff.mpr hlt)
        (tr.kingsAligned_castSucc_of_succ kp ht hs hk hsafe h0 hc i h)

/-- In a periodic trace with consistent placement, the last king positions are the
    first ones. -/
theorem IsPeriodic.kingPos_last {tr : MoveTrace} (hp : tr.IsPeriodic)
    {kp : Fin (tr.len + 1) → Player → Pos} (hk : tr.KingsWellPlaced kp) :
    kp (Fin.last tr.len) = kp 0 := by
  have h := hk (Fin.last tr.len)
  rw [show tr.states (Fin.last tr.len) = tr.states 0 from hp] at h
  exact h.positions_unique (hk 0)

/-- Proposition 2.2: in a periodic mutual-check trace satisfying the stated transition and safety
    premises and the owner-oriented movement condition, no move is a king move. -/
theorem not_kingMoveAt_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) : ¬ tr.KingMoveAt kp i := by
  rintro ⟨dst, promote, hm⟩
  have hbefore : KingsAligned (kp i.castSucc) := (kingsAligned_iff _ (tr.before i).turn).mpr
    (tr.kingMove_aligned_before kp ht hs hk hsafe h0 hc i dst promote hm)
  have hfirst : KingsAligned (kp 0) :=
    tr.kingsAligned_of_le kp ht hs hk hsafe h0 hc (Fin.zero_le _) hbefore
  apply tr.kingMove_not_aligned_after kp ht hs hk hsafe h0 hc hr i dst promote hm
  apply (kingsAligned_iff _ (tr.before i).turn).mp
  apply tr.kingsAligned_of_le kp ht hs hk hsafe h0 hc (Fin.le_last i.succ)
  rw [hp.kingPos_last hk]
  exact hfirst

/-- Under the same premises both king positions are constant. -/
theorem kingPos_eq_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (k : Fin (tr.len + 1)) : kp k = kp 0 := by
  induction k using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [tr.kingPos_succ_of_not_kingMove kp ht hs hk i
      (tr.not_kingMoveAt_of_periodic kp ht hs hk hsafe h0 hc hr hp i), ih]

/-- Proposition 2.2 in the form of Definition 2.1: both initial king squares are
    immovable, since no move uses them as a source, destination, or drop square. -/
theorem immovableAt_kingPos_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (o : Player) : tr.ImmovableAt (kp 0 o) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [(hk 0).king_present o]
    exact Option.some_ne_none _
  · rw [← tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc]
    have hnk := tr.not_kingMoveAt_of_periodic kp ht hs hk hsafe h0 hc hr hp i
    have key : ∀ m : Move, tr.moves i = m → ¬ m.Touches (kp i.castSucc o) := by
      intro m hm
      cases m with
      | boardMove src dst promote =>
        have hsrc := kingPos_ne_src tr kp hs hk i src dst promote hm hnk o
        have hdst := tr.boardMove_dst_ne_kingPos kp ht hk i src dst promote hm o hsrc
        simp only [Move.Touches]
        rintro (he | he)
        exacts [hsrc he, hdst he]
      | dropMove pt dst =>
        exact tr.dropMove_dst_ne_kingPos kp ht hs hk hsafe h0 hc i pt dst hm o
    exact key _ rfl

end MoveTrace
end MPC
