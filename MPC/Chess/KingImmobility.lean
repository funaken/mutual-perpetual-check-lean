import MPC.Chess.KingGeometry
import MPC.Chess.PeriodicReduction

/-! Kings are fixed in a periodic mutual-check trace. Initial non-mover safety
is obtained from the last legal move, not supplied as a new premise. -/

namespace MPC.Chess

def KingsAligned (kp : Color → Pos) : Prop := (kp .white).aligned (kp .black)

private theorem kingsAligned_iff (kp : Color → Pos) (c : Color) :
    KingsAligned kp ↔ (kp c).aligned (kp c.opponent) := by
  cases c
  · rfl
  · exact Pos.aligned_comm _ _

namespace MoveTrace

theorem kingPositions_after_of_legal (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len) :
    kp i.succ = kingPositionsAfter (kp i.castSucc) (tr.before i).turn (tr.moves i) := by
  obtain ⟨q, hm, he⟩ := hl i
  have hq := hm.placement.positions_unique (hk i.castSucc)
  subst q
  have ha := hm.kingsWellPlaced_after
  rw [← he] at ha
  exact (hk i.succ).positions_unique ha

theorem ownKing_safe_after_of_legal (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len) :
    ¬ inCheck (tr.after i).board (tr.before i).turn (kp i.succ (tr.before i).turn) := by
  obtain ⟨q, hm, he⟩ := hl i
  have hq := hm.placement.positions_unique (hk i.castSucc)
  subst q
  rw [tr.kingPositions_after_of_legal kp hl hk i, he]
  exact hm.ownKingSafe

theorem opponent_safe_of_periodic (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp) (hp : tr.BoardTurnPeriodic)
    (hn : 0 < tr.len) (k : Fin (tr.len + 1)) :
    ¬ inCheck (tr.states k).board (tr.states k).turn.opponent
      (kp k (tr.states k).turn.opponent) := by
  have step (i : Fin tr.len) :
      ¬ inCheck (tr.states i.succ).board (tr.states i.succ).turn.opponent
        (kp i.succ (tr.states i.succ).turn.opponent) := by
    have hs := tr.ownKing_safe_after_of_legal kp hl hk i
    have ht := (hl i).turn
    change (tr.states i.succ).turn = _ at ht
    simpa only [ht, Color.opponent_opponent, MoveTrace.after] using hs
  refine Fin.cases ?_ step k
  let lastMove : Fin tr.len := ⟨tr.len - 1, by omega⟩
  have he : lastMove.succ = Fin.last tr.len := by apply Fin.ext; simp [lastMove]; omega
  have hkLast : MPC.Chess.KingsWellPlaced (tr.states 0).board (kp (Fin.last tr.len)) := by
    rw [← hp.1]; exact hk _
  have hkp := hkLast.positions_unique (hk 0)
  have hs := step lastMove
  rwa [he, hp.1, hp.2, hkp] at hs

theorem kings_not_adjacent_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hp : tr.BoardTurnPeriodic) (hn : 0 < tr.len)
    (k : Fin (tr.len + 1)) (c : Color) :
    ¬ attacks Board.empty ⟨c, .king⟩ (kp k c) (kp k c.opponent) := by
  intro ha
  have hs := tr.opponent_safe_of_periodic kp hl hk hp hn k
  by_cases he : c = (tr.states k).turn
  · subst c
    exact hs ⟨kp k (tr.states k).turn, ⟨(tr.states k).turn, .king⟩,
      (hk k).king_present _, (Color.opponent_opponent _).symm, ha⟩
  · have he' : c = (tr.states k).turn.opponent := by
      cases c <;> cases ht : (tr.states k).turn <;> simp_all [Color.opponent]
    subst c
    exact hs ⟨kp k (tr.states k).turn, ⟨(tr.states k).turn, .king⟩,
      (hk k).king_present _, (Color.opponent_opponent _).symm,
      king_attack_symm _ _ _ _ _ _ (by simpa using ha)⟩

private theorem opponent_king_ne_source (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hk : tr.KingsWellPlaced kp)
    (i : Fin tr.len) (src : Pos) (p : Piece) (hs : (tr.before i).board src = some p)
    (ho : p.owner = (tr.before i).turn) : kp i.castSucc (tr.before i).turn.opponent ≠ src := by
  intro he
  have hp := (hk i.castSucc).king_present (tr.before i).turn.opponent
  change (tr.before i).board _ = _ at hp
  rw [he, hs] at hp
  have hc := congrArg Piece.owner (Option.some.inj hp)
  simp only at hc
  rw [ho] at hc
  exact (tr.before i).turn.opponent_ne hc.symm

/-- The two local conclusions of Proposition 2.2, after Part 3's reduction. -/
theorem kingMove_alignment (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic)
    (i : Fin tr.len) (src dst : Pos) (hm : tr.moves i = .boardMove src dst none)
    (hs : (tr.before i).board src = some ⟨(tr.before i).turn, .king⟩) :
    KingsAligned (kp i.castSucc) ∧ ¬ KingsAligned (kp i.succ) := by
  have hn : 0 < tr.len := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsrc : src = kp i.castSucc (tr.before i).turn := (hk i.castSucc _ src).mp hs
  have hopp := opponent_king_ne_source tr kp hk i src _ hs rfl
  have hkp := tr.kingPositions_after_of_legal kp hl hk i
  rw [hm] at hkp
  have hown : kp i.succ (tr.before i).turn = dst := by
    rw [hkp]; simp [kingPositionsAfter, relocateKingPositions, hsrc]
  have henemy : kp i.succ (tr.before i).turn.opponent =
      kp i.castSucc (tr.before i).turn.opponent := by
    rw [hkp]; simp [kingPositionsAfter, relocateKingPositions, hopp]
  have hbefore := tr.opponent_safe_of_periodic kp hl hk hp hn i.castSucc
  have hafter := hc i
  rw [henemy] at hafter
  obtain ⟨q, p, hq, ho, ha⟩ := hafter
  obtain ⟨_, hlm, he⟩ := hl i
  rw [hm] at he
  have hmove : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hlm.movement
  obtain ⟨m, hms, _, hne, _, _, hmovement⟩ := hmove
  have hme : m = ⟨(tr.before i).turn, .king⟩ := Option.some.inj (hms.symm.trans hs)
  subst m
  have hdst : (tr.after i).board dst = some ⟨(tr.before i).turn, .king⟩ := by
    rw [he]; simp [applyMove, applyBoard, hs, Piece.promote]
  have hqd : q ≠ dst := by
    intro h
    subst q
    rw [hdst] at hq
    cases hq
    apply tr.kings_not_adjacent_of_periodic kp hl hk hp hn i.succ (tr.before i).turn
    simpa only [hown, henemy, attacks] using ha
  have hqs : q ≠ src := by
    intro h
    subst q
    rw [he] at hq
    change (tr.before i).board.relocate src dst none src = some p at hq
    rw [Board.relocate_source _ _ _ _ hne] at hq
    contradiction
  have hq0 : (tr.before i).board q = some p := by
    rw [he] at hq
    change (tr.before i).board.relocate src dst none q = some p at hq
    rwa [Board.relocate_other _ _ _ _ _ hqs hqd] at hq
  have hnot : ¬ attacks (tr.before i).board p q (kp i.castSucc (tr.before i).turn.opponent) :=
    fun h => hbefore ⟨q, p, hq0, ho, h⟩
  rw [he] at ha
  obtain ⟨hkind, hbetween, hnotbetween⟩ := new_attack_source_between _ src dst _ p q _ hs hnot ha
  have hal := attacks_aligned_of_slider hkind ha
  have hdempty := tr.boardMove_destination_empty_of_periodic hl hp i src dst none hm
  have hdt := (hk i.castSucc).ne_of_empty hdempty (tr.before i).turn.opponent
  have hstep : attacks Board.empty ⟨.white, .king⟩ src dst := by
    simpa [OrdinaryMovement, attacks] using hmovement
  have hsapart : ¬ attacks Board.empty ⟨.white, .king⟩ src (kp i.castSucc (tr.before i).turn.opponent) := by
    simpa only [hsrc, attacks] using
      tr.kings_not_adjacent_of_periodic kp hl hk hp hn i.castSucc (tr.before i).turn
  have hdapart : ¬ attacks Board.empty ⟨.white, .king⟩ dst (kp i.castSucc (tr.before i).turn.opponent) := by
    simpa only [hown, henemy, attacks] using
      tr.kings_not_adjacent_of_periodic kp hl hk hp hn i.succ (tr.before i).turn
  constructor
  · apply (kingsAligned_iff _ (tr.before i).turn).mpr
    rw [← hsrc]
    exact aligned_of_between hal hbetween
  · intro h
    have hd := (kingsAligned_iff _ (tr.before i).turn).mp h
    rw [hown, henemy] at hd
    exact not_aligned_of_king_step hal hbetween hnotbetween hqd.symm hdt hstep hsapart hdapart hd

private theorem kingPositions_step_of_nonking (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (i : Fin tr.len) (src dst : Pos) (p : Piece)
    (hm : tr.moves i = .boardMove src dst none) (hs : (tr.before i).board src = some p)
    (hnk : p.kind ≠ .king) : kp i.succ = kp i.castSucc := by
  rw [tr.kingPositions_after_of_legal kp hl hk i, hm]
  funext c
  have hne : kp i.castSucc c ≠ src := by
    intro he
    have hking := (hk i.castSucc).king_present c
    change (tr.before i).board _ = _ at hking
    rw [he, hs] at hking
    exact hnk (congrArg Piece.kind (Option.some.inj hking))
  simp [kingPositionsAfter, relocateKingPositions, hne]

private theorem kingsAligned_step (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic)
    (i : Fin tr.len) : KingsAligned (kp i.succ) → KingsAligned (kp i.castSucc) := by
  obtain ⟨src, dst, p, hm, hs, ho, _⟩ := tr.ordinary_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  by_cases hkind : p.kind = .king
  · have he : p = ⟨(tr.before i).turn, .king⟩ := by cases p; simp_all
    subst p
    exact fun _ => (tr.kingMove_alignment kp hl hk hc hp i src dst hm hs).1
  · rw [tr.kingPositions_step_of_nonking kp hl hk i src dst p hm hs hkind]
    exact id

private theorem kingsAligned_of_le (tr : MoveTrace) (kp : Fin (tr.len + 1) → Color → Pos)
    (hl : tr.FollowsLegalMoves) (hk : tr.KingsWellPlaced kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hp : tr.BoardTurnPeriodic)
    {i j : Fin (tr.len + 1)} (hij : i ≤ j) : KingsAligned (kp j) → KingsAligned (kp i) := by
  revert hij
  induction j using Fin.induction with
  | zero => intro hij h; rwa [Fin.le_zero_iff.mp hij]
  | succ j ih =>
    intro hij h
    by_cases he : i = j.succ
    · rwa [he]
    · have hlt : i < j.succ := Nat.lt_of_le_of_ne hij (fun h => he (Fin.ext h))
      exact ih (Fin.le_castSucc_iff.mpr hlt) (tr.kingsAligned_step kp hl hk hc hp j h)

theorem boardMove_piece_ne_king_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) (src dst : Pos) (p : Piece)
    (hm : tr.moves i = .boardMove src dst none) (hs : (tr.before i).board src = some p) :
    p.kind ≠ .king := by
  intro hkind
  obtain ⟨_, hv, _⟩ := hl i
  have hm' : PseudoLegal (tr.before i) (.boardMove src dst none) := by simpa only [hm] using hv.movement
  obtain ⟨q, hq, ho, _⟩ := hm'
  have he : q = p := Option.some.inj (hq.symm.trans hs)
  subst q
  have he : p = ⟨(tr.before i).turn, .king⟩ := by cases p; simp_all
  subst p
  obtain ⟨hb, ha⟩ := tr.kingMove_alignment kp hl hk hc hp i src dst hm hs
  have hfirst := tr.kingsAligned_of_le kp hl hk hc hp (Fin.zero_le _) hb
  have hkLast : MPC.Chess.KingsWellPlaced (tr.states 0).board (kp (Fin.last tr.len)) := by
    rw [← hp.1]; exact hk _
  have hkp := hkLast.positions_unique (hk 0)
  apply ha
  apply tr.kingsAligned_of_le kp hl hk hc hp (Fin.le_last i.succ)
  rwa [hkp]

/-- Both king-position functions agree at any two states, including an empty
trace. This is a consequence of periodic checks, not a model field. -/
theorem kingPositions_eq_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i j : Fin (tr.len + 1)) : kp i = kp j := by
  have hzero (k : Fin (tr.len + 1)) : kp k = kp 0 := by
    induction k using Fin.induction with
    | zero => rfl
    | succ k ih =>
      obtain ⟨src, dst, p, hm, hs, _⟩ := tr.ordinary_nonPawn_move_of_periodic_checks kp hl hk hc hp k
      rw [tr.kingPositions_step_of_nonking kp hl hk k src dst p hm hs
        (tr.boardMove_piece_ne_king_of_periodic_checks kp hl hk hc hp k src dst p hm hs), ih]
  exact (hzero i).trans (hzero j).symm

theorem ordinary_nonKing_nonPawn_move_of_periodic_checks (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Color → Pos) (hl : tr.FollowsLegalMoves)
    (hk : tr.KingsWellPlaced kp) (hc : tr.EveryMoveChecksOpponent kp)
    (hp : tr.BoardTurnPeriodic) (i : Fin tr.len) :
    ∃ src dst p, tr.moves i = .boardMove src dst none ∧
      (tr.before i).board src = some p ∧ p.owner = (tr.before i).turn ∧
      p.kind ≠ .king ∧ p.kind ≠ .pawn ∧ src ≠ dst ∧ (tr.before i).board dst = none ∧
      attacks (tr.before i).board p src dst := by
  obtain ⟨src, dst, p, hm, hs, ho, hnp, hne, hd, ha⟩ :=
    tr.ordinary_nonPawn_move_of_periodic_checks kp hl hk hc hp i
  exact ⟨src, dst, p, hm, hs, ho,
    tr.boardMove_piece_ne_king_of_periodic_checks kp hl hk hc hp i src dst p hm hs,
    hnp, hne, hd, ha⟩

end MoveTrace
end MPC.Chess
