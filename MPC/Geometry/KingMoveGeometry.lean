import MPC.Basic.Lemmas
import MPC.Glare.GlaringMove
/-!
# MPC.Geometry.KingMoveGeometry

The per-move steps of the paper's Proposition 2.2 (kings are immovable) on
independent traces. With consistent placement the kings never stand adjacent,
so a king move cannot check directly; in a mutual-check trace it is a discovered
check. Its unblocked checker's line runs through the king's source to the enemy
king, so the kings were aligned before the move. A one-step king move then
leaves every line through the enemy king, so they are not aligned afterwards.
The last step needs the owner-oriented movement condition; periodicity is not
used here. No GameSeq or global immovability premise is used.
-/

namespace MPC

private theorem pos_ext_of_int {a b : Pos} (h1 : (a.1.val : ℤ) = b.1.val)
    (h2 : (a.2.val : ℤ) = b.2.val) : a = b :=
  Prod.ext (Fin.ext (by exact_mod_cast h1)) (Fin.ext (by exact_mod_cast h2))

/-- Orienting the king's directions for either owner yields the same set. -/
private theorem king_step_forPlayer_iff (d : Dir) (o : Player) :
    d ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o) ↔ d ∈ PieceType.king.stepDirs := by
  have h1 : ∀ x ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o),
      x ∈ PieceType.king.stepDirs := by
    cases o <;> decide
  have h2 : ∀ x ∈ PieceType.king.stepDirs,
      x ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o) := by
    cases o <;> decide
  exact ⟨h1 d, h2 d⟩

/-- Every oriented slide direction is a unit step. -/
private theorem slide_mem_king (pt : PieceType) (o : Player) (d : Dir)
    (h : d ∈ pt.slideDirs.map (Dir.forPlayer · o)) : d ∈ PieceType.king.stepDirs := by
  have key : ∀ x ∈ pt.slideDirs.map (Dir.forPlayer · o), x ∈ PieceType.king.stepDirs := by
    cases o <;> cases pt <;> decide
  exact key d h

/-- King attacks are symmetric and board-independent. -/
private theorem king_attack_symm (b1 b2 : Board) (o1 o2 : Player) (a c : Pos)
    (h : attacksOriented b1 o1 .king a c) : attacksOriented b2 o2 .king c a := by
  rcases h with hs | ⟨_, hsd, _⟩
  · have hs' : Pos.dirTo a c ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o1) := hs
    rw [king_step_forPlayer_iff, PieceType.mem_king_stepDirs_iff] at hs'
    refine Or.inl ?_
    show Pos.dirTo c a ∈ PieceType.king.stepDirs.map (Dir.forPlayer · o2)
    rw [king_step_forPlayer_iff, PieceType.mem_king_stepDirs_iff]
    simp only [Pos.dirTo] at hs' ⊢
    omega
  · simp [PieceType.slideDirs] at hsd

/-- A king step from the target is a king attack in either direction. -/
private theorem king_attack_of_step (board : Board) (o : Player) (a c : Pos)
    (h : Pos.dirTo a c ∈ PieceType.king.stepDirs) : attacksOriented board o .king a c :=
  Or.inl ((king_step_forPlayer_iff _ o).mpr h)

/-- With consistent placement, a player not in check has no adjacent enemy king. -/
private theorem not_adjacent_of_safe (board : Board) (kp : Player → Pos)
    (hk : KingsWellPlaced board kp) (p : Player) (hsafe : ¬ inCheckOriented board p (kp p))
    (o : Player) : ¬ attacksOriented board o .king (kp o) (kp o.opponent) := by
  intro ha
  apply hsafe
  cases o <;> cases p
  · exact ⟨kp .gote, ⟨.gote, .king⟩, hk.king_present _, rfl,
      king_attack_symm board board _ _ _ _ ha⟩
  · exact ⟨kp .sente, ⟨.sente, .king⟩, hk.king_present _, rfl, ha⟩
  · exact ⟨kp .gote, ⟨.gote, .king⟩, hk.king_present _, rfl, ha⟩
  · exact ⟨kp .sente, ⟨.sente, .king⟩, hk.king_present _, rfl,
      king_attack_symm board board _ _ _ _ ha⟩

private theorem boardMove_dst_king_iff (bs : BoardState) (src dst : Pos)
    (promote : Bool) (owner : Player) :
    (applyMove bs (.boardMove src dst promote)).board.grid dst = some ⟨owner, .king⟩ ↔
      bs.board.grid src = some ⟨owner, .king⟩ := by
  rw [applyMove_boardMove_grid_dst]
  cases hs : bs.board.grid src with
  | none => simp
  | some piece =>
    cases piece with
    | mk p pt => cases promote <;> simp [Piece.mk.injEq, PieceType.promote_eq_king_iff]

/-- Unblocked-checker geometry from an unchecked target: the checker slides along
    a unit direction, the source is a strict intermediate step, the checker is not
    at the destination, and no intermediate step is the destination. -/
private theorem unblocked_geometry (bs : BoardState) (src dst target : Pos) (promote : Bool)
    (kingOwner : Player) (hbefore : ¬ inCheckOriented bs.board kingOwner target)
    (h : hasUnblockedCheckerOriented bs.board (applyMove bs (.boardMove src dst promote)).board
      (.boardMove src dst promote) kingOwner target) :
    ∃ (pos : Pos) (d : Dir) (n j : ℕ), d ∈ PieceType.king.stepDirs ∧ 1 ≤ j ∧ j < n ∧
      pos ≠ dst ∧
      target.toInt = (pos.toInt.1 + ↑n * d.1, pos.toInt.2 + ↑n * d.2) ∧
      src.toInt = (pos.toInt.1 + ↑j * d.1, pos.toInt.2 + ↑j * d.2) ∧
      ∀ l : ℕ, 1 ≤ l → l < n →
        dst.toInt ≠ (pos.toInt.1 + ↑l * d.1, pos.toInt.2 + ↑l * d.2) := by
  obtain ⟨pos, piece, _, hpd, hp0, _, ho, ha, hmem, hdst, _, _⟩ := h
  rcases ha with hstep | ⟨d, hdm, hnorm, n, hn, hx, hy, _⟩
  · exact False.elim (hbefore ⟨pos, piece, hp0, ho, Or.inl hstep⟩)
  have hdk := slide_mem_king _ _ d hdm
  have hd : d ≠ (0, 0) := by
    intro he
    rw [he] at hdk
    exact absurd hdk (by decide)
  have hx' : target.toInt.1 = pos.toInt.1 + ↑n * d.1 := by
    dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
    omega
  have hy' : target.toInt.2 = pos.toInt.2 + ↑n * d.2 := by
    dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
    omega
  have hm := mem_slidePath_iff_of_exact_steps pos target d n hd hn hnorm hx' hy'
  obtain ⟨j, hj, hjn, hsrc⟩ := (hm src.toInt).mp hmem
  exact ⟨pos, d, n, j, hdk, hj, hjn, hpd, Prod.ext hx' hy', hsrc,
    fun l hl hln he => hdst ((hm _).mpr ⟨l, hl, hln, he⟩)⟩

/-- Positions differing by a multiple of a unit step are aligned. -/
private theorem isAligned_of_ray (a b : Pos) (d : Dir) (m : ℤ)
    (hd : d ∈ PieceType.king.stepDirs)
    (h1 : (b.1.val : ℤ) - a.1.val = m * d.1) (h2 : (b.2.val : ℤ) - a.2.val = m * d.2) :
    Pos.isAligned a b := by
  rw [PieceType.mem_king_stepDirs_iff] at hd
  obtain ⟨hd1, hd1', hd2, hd2', _⟩ := hd
  show Pos.dirTo a b = (0, 0) ∨ (Pos.dirTo a b).1 = 0 ∨ (Pos.dirTo a b).2 = 0 ∨
    (Pos.dirTo a b).1.natAbs = (Pos.dirTo a b).2.natAbs
  right
  simp only [Pos.dirTo, Int.natAbs_eq_natAbs_iff]
  have e1 : d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1 := by omega
  have e2 : d.2 = -1 ∨ d.2 = 0 ∨ d.2 = 1 := by omega
  rcases e1 with e1 | e1 | e1 <;> rcases e2 with e2 | e2 | e2 <;>
    rw [e1] at h1 <;> rw [e2] at h2 <;> omega

/-- Finite geometry behind Proposition 2.2: a unit step `e` off the direction `d`
    (neither `d` nor `-d`) from a point `m ≥ 2` steps before the target, ending
    non-adjacent to the target, is not aligned with the target. -/
theorem not_isAligned_of_step_off_line (src dst target : Pos) (d : Dir) (m : ℕ)
    (hd : d ∈ PieceType.king.stepDirs) (hm : 2 ≤ m)
    (ht : target.toInt = (src.toInt.1 + ↑m * d.1, src.toInt.2 + ↑m * d.2))
    (he : Pos.dirTo src dst ∈ PieceType.king.stepDirs)
    (hne : Pos.dirTo src dst ≠ d) (hne' : Pos.dirTo src dst ≠ (-d.1, -d.2))
    (hapart : Pos.dirTo dst target ∉ PieceType.king.stepDirs) :
    ¬ Pos.isAligned dst target := by
  intro hal
  apply hapart
  have ht1 : (target.1.val : ℤ) = src.1.val + ↑m * d.1 := congrArg Prod.fst ht
  have ht2 : (target.2.val : ℤ) = src.2.val + ↑m * d.2 := congrArg Prod.snd ht
  have hn1 : ¬ ((dst.1.val : ℤ) - src.1.val = d.1 ∧ (dst.2.val : ℤ) - src.2.val = d.2) :=
    fun h => hne (Prod.ext h.1 h.2)
  have hn2 : ¬ ((dst.1.val : ℤ) - src.1.val = -d.1 ∧ (dst.2.val : ℤ) - src.2.val = -d.2) :=
    fun h => hne' (Prod.ext h.1 h.2)
  have hal' : ((target.1.val : ℤ) - dst.1.val = 0 ∧ (target.2.val : ℤ) - dst.2.val = 0) ∨
      (target.1.val : ℤ) - dst.1.val = 0 ∨ (target.2.val : ℤ) - dst.2.val = 0 ∨
      ((target.1.val : ℤ) - dst.1.val = (target.2.val : ℤ) - dst.2.val ∨
        (target.1.val : ℤ) - dst.1.val = -((target.2.val : ℤ) - dst.2.val)) := by
    have h := hal
    simp only [Pos.isAligned, Pos.dirTo, Prod.mk.injEq, Int.natAbs_eq_natAbs_iff] at h
    exact h
  rw [PieceType.mem_king_stepDirs_iff] at hd he ⊢
  simp only [Pos.dirTo] at he ⊢
  obtain ⟨hd1, hd1', hd2, hd2', hd0⟩ := hd
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have e1 : d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1 := by omega
  have e2 : d.2 = -1 ∨ d.2 = 0 ∨ d.2 = 1 := by omega
  rcases e1 with e1 | e1 | e1 <;> rcases e2 with e2 | e2 | e2 <;>
    rw [e1] at ht1 hn1 hn2 <;> rw [e2] at ht2 hn1 hn2 <;> omega

namespace MoveTrace

/-- A board move relocates exactly the king standing on its source. -/
theorem kingPos_succ_of_boardMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (hm : tr.moves i = .boardMove src dst promote)
    (o : Player) :
    kp i.succ o = kingPosAfterBoardMove (kp i.castSucc) src dst o := by
  have hb : MPC.KingsWellPlaced (tr.before i).board (kp i.castSucc) := hk i.castSucc
  have ha : MPC.KingsWellPlaced (tr.after i).board (kp i.succ) := hk i.succ
  have hdst : ∀ owner, (tr.after i).board.grid dst = some ⟨owner, .king⟩ ↔
      (tr.before i).board.grid src = some ⟨owner, .king⟩ := by
    intro owner
    rw [ht i, hm]
    exact boardMove_dst_king_iff (tr.before i) src dst promote owner
  unfold kingPosAfterBoardMove
  by_cases hs : kp i.castSucc o = src
  · rw [ite_eq_left hs]
    refine ((ha o dst).mp ?_).symm
    rw [hdst o, ← hs]
    exact hb.king_present o
  · rw [ite_eq_right hs]
    by_cases hd : kp i.castSucc o = dst
    · exfalso
      have hp := ha.king_present o
      by_cases h1 : kp i.succ o = dst
      · rw [h1, hdst o] at hp
        exact hs ((hb o src).mp hp).symm
      · by_cases h2 : kp i.succ o = src
        · have hsd : src ≠ dst := fun he => h1 (h2.trans he)
          rw [h2, tr.boardMove_grid_src ht i src dst promote hm hsd] at hp
          cases hp
        · rw [tr.boardMove_grid_other ht i src dst promote _ hm h2 h1] at hp
          exact h1 (((hb o _).mp hp).trans hd)
    · refine ((ha o _).mp ?_).symm
      rw [tr.boardMove_grid_other ht i src dst promote _ hm hs hd]
      exact hb.king_present o

/-- A drop never relocates a king; dropping on a king's square breaks placement
    unless it reproduces that king. -/
theorem kingPos_succ_of_dropMove (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hk : tr.KingsWellPlaced kp) (i : Fin tr.len)
    (pt : PieceType) (dst : Pos) (hm : tr.moves i = .dropMove pt dst) :
    kp i.succ = kp i.castSucc := by
  funext o
  have hb : MPC.KingsWellPlaced (tr.before i).board (kp i.castSucc) := hk i.castSucc
  have ha : MPC.KingsWellPlaced (tr.after i).board (kp i.succ) := hk i.succ
  by_cases hd : kp i.castSucc o = dst
  · by_cases h1 : kp i.succ o = dst
    · rw [h1, hd]
    · exfalso
      have hp := ha.king_present o
      rw [tr.dropMove_grid_other ht i pt dst _ hm h1] at hp
      exact h1 (((hb o _).mp hp).trans hd)
  · refine ((ha o _).mp ?_).symm
    rw [tr.dropMove_grid_other ht i pt dst _ hm hd]
    exact hb.king_present o

/-- With consistent placement, initial non-mover safety, and self-safety, the
    kings are never adjacent in any state. -/
theorem kings_not_adjacent (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (hk : tr.KingsWellPlaced kp) (hsafe : tr.EveryMoveLeavesOwnKingSafe kp)
    (h0 : tr.InitialOpponentKingSafe kp) (k : Fin (tr.len + 1)) (o : Player) :
    ¬ attacksOriented (tr.states k).board o .king (kp k o) (kp k o.opponent) := by
  refine Fin.cases ?_ (fun i => ?_) k
  · exact not_adjacent_of_safe _ (kp 0) (hk 0) _ h0 o
  · exact not_adjacent_of_safe (tr.after i).board (kp i.succ) (hk i.succ) _ (hsafe i) o

/-- In a mutual-check trace satisfying the stated transition and safety premises, a king move is a
    discovered check: a direct check by the king would make the kings adjacent. -/
theorem kingMove_unblockedChecker (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove (kp i.castSucc (tr.before i).turn) dst promote) :
    hasUnblockedCheckerOriented (tr.before i).board (tr.after i).board (tr.moves i)
      (tr.before i).turn.opponent (kp i.succ (tr.before i).turn.opponent) := by
  refine ((tr.everyMoveChecksOpponent_iff_destination_or_unblocked_of_safe kp ht hs hk hsafe
    h0).mp hc i).resolve_left ?_
  rintro ⟨piece, hp, _, ha⟩
  rw [hm] at hp ha
  have hpos : kp i.succ (tr.before i).turn = dst := by
    rw [tr.kingPos_succ_of_boardMove kp ht hk i _ dst promote hm]
    simp [kingPosAfterBoardMove]
  have hking : (tr.after i).board.grid dst = some ⟨(tr.before i).turn, .king⟩ := by
    rw [← hpos]
    exact (hk i.succ).king_present _
  change (tr.after i).board.grid dst = some piece at hp
  rw [hking] at hp
  cases hp
  apply hsafe i
  refine ⟨kp i.succ (tr.before i).turn.opponent, ⟨(tr.before i).turn.opponent, .king⟩,
    (hk i.succ).king_present _, rfl, ?_⟩
  rw [hpos]
  exact king_attack_symm _ _ _ _ _ _ ha

/-- Proposition 2.2, first step: before a king move in such a trace, the two
    kings stand on a common file, rank, or diagonal. -/
theorem kingMove_aligned_before (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (i : Fin tr.len) (dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove (kp i.castSucc (tr.before i).turn) dst promote) :
    Pos.isAligned (kp i.castSucc (tr.before i).turn) (kp i.castSucc (tr.before i).turn.opponent) := by
  have hu := tr.kingMove_unblockedChecker kp ht hs hk hsafe h0 hc i dst promote hm
  rw [ht i, hm, tr.opponentKingPos_succ_eq kp ht hs hk i] at hu
  obtain ⟨pos, d, n, j, hd, _, hjn, _, htgt, hsrc, _⟩ :=
    unblocked_geometry (tr.before i) _ dst _ promote _
      (tr.before_opponent_not_inCheck kp ht hsafe h0 i) hu
  have a1 := congrArg Prod.fst htgt
  have a2 := congrArg Prod.snd htgt
  have b1 := congrArg Prod.fst hsrc
  have b2 := congrArg Prod.snd hsrc
  simp only [Pos.toInt] at a1 a2 b1 b2
  exact isAligned_of_ray _ _ d (↑n - ↑j) hd (by rw [a1, b1]; ring) (by rw [a2, b2]; ring)

/-- Proposition 2.2, second step: with owner-oriented movement, a king move
    leaves every line through the enemy king. -/
theorem kingMove_not_aligned_after (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (i : Fin tr.len) (dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove (kp i.castSucc (tr.before i).turn) dst promote) :
    ¬ Pos.isAligned (kp i.succ (tr.before i).turn) (kp i.succ (tr.before i).turn.opponent) := by
  have hpos : kp i.succ (tr.before i).turn = dst := by
    rw [tr.kingPos_succ_of_boardMove kp ht hk i _ dst promote hm]
    simp [kingPosAfterBoardMove]
  have hopp := tr.opponentKingPos_succ_eq kp ht hs hk i
  have hadj0 := tr.kings_not_adjacent kp hk hsafe h0 i.castSucc (tr.before i).turn
  have hadj1 := tr.kings_not_adjacent kp hk hsafe h0 i.succ (tr.before i).turn
  rw [hpos, hopp] at hadj1
  rw [hpos, hopp]
  have hu := tr.kingMove_unblockedChecker kp ht hs hk hsafe h0 hc i dst promote hm
  rw [ht i, hm, hopp] at hu
  obtain ⟨pos, d, n, j, hd, hj, hjn, hpd, htgt, hsrc, hnot⟩ :=
    unblocked_geometry (tr.before i) _ dst _ promote _
      (tr.before_opponent_not_inCheck kp ht hsafe h0 i) hu
  set src := kp i.castSucc (tr.before i).turn with hsrc_def
  set target := kp i.castSucc (tr.before i).turn.opponent with htarget_def
  have a1 : (target.1.val : ℤ) = pos.1.val + ↑n * d.1 := congrArg Prod.fst htgt
  have a2 : (target.2.val : ℤ) = pos.2.val + ↑n * d.2 := congrArg Prod.snd htgt
  have b1 : (src.1.val : ℤ) = pos.1.val + ↑j * d.1 := congrArg Prod.fst hsrc
  have b2 : (src.2.val : ℤ) = pos.2.val + ↑j * d.2 := congrArg Prod.snd hsrc
  -- The king moves one step.
  have he : Pos.dirTo src dst ∈ PieceType.king.stepDirs := by
    rcases hr i src dst promote ⟨(tr.before i).turn, .king⟩ hm ((hk i.castSucc).king_present _)
      with hst | ⟨_, hsd, _⟩
    · exact (king_step_forPlayer_iff _ _).mp hst
    · simp [PieceType.slideDirs] at hsd
  -- The kings were not adjacent before, so the source is at least two steps away.
  have hm2 : 2 ≤ n - j := by
    by_contra hlt
    have hnj : n = j + 1 := by omega
    subst hnj
    apply hadj0
    apply king_attack_of_step
    have hdir : Pos.dirTo src target = d := by
      refine Prod.ext ?_ ?_
      · change (target.1.val : ℤ) - src.1.val = d.1
        rw [a1, b1]; push_cast; ring
      · change (target.2.val : ℤ) - src.2.val = d.2
        rw [a2, b2]; push_cast; ring
    rw [hdir]
    exact hd
  have hcast : ((n - j : ℕ) : ℤ) = ↑n - ↑j := Nat.cast_sub hjn.le
  refine not_isAligned_of_step_off_line src dst target d (n - j) hd hm2 ?_ he ?_ ?_ ?_
  · refine Prod.ext ?_ ?_
    · change (target.1.val : ℤ) = src.1.val + ↑(n - j) * d.1
      rw [a1, b1, hcast]; ring
    · change (target.2.val : ℤ) = src.2.val + ↑(n - j) * d.2
      rw [a2, b2, hcast]; ring
  · -- Stepping toward the target lands on the checker's path.
    intro hed
    have c1 : (dst.1.val : ℤ) - src.1.val = d.1 := congrArg Prod.fst hed
    have c2 : (dst.2.val : ℤ) - src.2.val = d.2 := congrArg Prod.snd hed
    refine hnot (j + 1) (by omega) (by omega) (Prod.ext ?_ ?_)
    · change (dst.1.val : ℤ) = pos.1.val + ↑(j + 1) * d.1
      push_cast; linarith
    · change (dst.2.val : ℤ) = pos.2.val + ↑(j + 1) * d.2
      push_cast; linarith
  · -- Stepping back lands on the checker's path or on the checker itself.
    intro hed
    have c1 : (dst.1.val : ℤ) - src.1.val = -d.1 := congrArg Prod.fst hed
    have c2 : (dst.2.val : ℤ) - src.2.val = -d.2 := congrArg Prod.snd hed
    by_cases hj1 : j = 1
    · subst hj1
      exact hpd (pos_ext_of_int (by push_cast at b1; linarith) (by push_cast at b2; linarith)).symm
    · have hc1 : ((j - 1 : ℕ) : ℤ) = ↑j - 1 := Nat.cast_sub (by omega)
      refine hnot (j - 1) (by omega) (by omega) (Prod.ext ?_ ?_)
      · change (dst.1.val : ℤ) = pos.1.val + ↑(j - 1) * d.1
        rw [hc1]; linarith
      · change (dst.2.val : ℤ) = pos.2.val + ↑(j - 1) * d.2
        rw [hc1]; linarith
  · -- The kings are not adjacent afterwards.
    intro hmem
    exact hadj1 (king_attack_of_step _ _ _ _ hmem)

end MoveTrace
end MPC
