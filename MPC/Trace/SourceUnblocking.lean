import MPC.Trace.CheckerLocation
import MPC.Basic.SlidePath
/-!
# MPC.Trace.SourceUnblocking

With a present moving piece, a newly enabled attack at fixed attack/target
coordinates comes from clearing its source. Non-destination checkers retain their piece
contents by this one update; no global immovability or GameSeq is used.
-/

namespace MPC

private theorem pos_onBoard (p : Pos) : onBoard p.toInt := by
  change 0 ≤ (p.1.val : ℤ) ∧ (p.1.val : ℤ) < 9 ∧
    0 ≤ (p.2.val : ℤ) ∧ (p.2.val : ℤ) < 9
  exact ⟨by omega, by exact_mod_cast p.1.isLt,
    by omega, by exact_mod_cast p.2.isLt⟩

private theorem toPos_int (p : Pos) (h : onBoard p.toInt) : toPos p.toInt h = p := by
  ext <;> simp [toPos, Pos.toInt, Int.toNat_natCast]

private theorem toPos_eq_int (q : ℤ × ℤ) (h : onBoard q) (p : Pos)
    (he : toPos q h = p) : q = p.toInt := by
  subst p
  have h1 := h.1
  have h2 := h.2.2.1
  ext <;> simp [toPos, Pos.toInt] <;> omega

/-- Every post-move piece away from the destination was already present with
    identical contents. No source-presence or movement-rule premise is needed. -/
theorem applyMove_boardMove_other_piece_before (bs : BoardState) (src dst pos : Pos) (promote : Bool)
    (pc : Piece) (hd : pos ≠ dst)
    (hp : (applyMove bs (.boardMove src dst promote)).board.grid pos = some pc) :
    pos ≠ src ∧ bs.board.grid pos = some pc := by
  have hs : pos ≠ src := by
    intro he
    subst pos
    rw [applyMove_boardMove_grid_src bs src dst promote hd] at hp
    contradiction
  exact ⟨hs, (applyMove_boardMove_grid_other bs src dst promote pos hs hd).symm.trans hp⟩

/-- A fixed piece/position/target gains an attack only through source unblocking.
    Source presence makes the destination occupied afterwards. Attack-source
    presence/ownership and move legality are not part of this geometric lemma. -/
theorem applyMove_boardMove_new_attack_path (bs : BoardState) (src dst pos target : Pos) (promote : Bool)
    (moving pc : Piece) (hsrc : bs.board.grid src = some moving)
    (hbefore : ¬ attacksOriented bs.board pc.owner pc.pieceType pos target)
    (hafter : attacksOriented (applyMove bs (.boardMove src dst promote)).board
      pc.owner pc.pieceType pos target) :
    src.toInt ∈ slidePath pos target ∧
    dst.toInt ∉ slidePath pos target ∧
    ¬ pathClear bs.board pos target ∧
    pathClear (applyMove bs (.boardMove src dst promote)).board pos target := by
  rcases hafter with hstep | ⟨d, hdir, hn, k, hk, hx, hy, hc⟩
  · exact False.elim (hbefore (Or.inl hstep))
  have hblocked : ¬ pathClear bs.board pos target := by
    intro hclear
    exact hbefore (Or.inr ⟨d, hdir, hn, k, hk, hx, hy, hclear⟩)
  have hdst : dst.toInt ∉ slidePath pos target := by
    intro hmem
    have he := hc dst.toInt hmem (pos_onBoard dst) (pos_onBoard dst)
    rw [toPos_int, applyMove_boardMove_grid_dst, hsrc] at he
    contradiction
  refine ⟨?_, hdst, hblocked, hc⟩
  by_contra hsm
  apply hblocked
  intro q hq hob hproof
  have hne_src : toPos q hproof ≠ src := by
    intro he
    exact hsm (toPos_eq_int q hproof src he ▸ hq)
  have hne_dst : toPos q hproof ≠ dst := by
    intro he
    exact hdst (toPos_eq_int q hproof dst he ▸ hq)
  rw [← applyMove_boardMove_grid_other bs src dst promote _ hne_src hne_dst]
  exact hc q hq hob hproof

/-- The unblocked source is a strict intermediate point on an owner-oriented
    slide ray of at most eight steps, using the exact slide-path membership theorem. -/
theorem applyMove_boardMove_new_attack_exact_slide (bs : BoardState) (src dst pos target : Pos) (promote : Bool)
    (moving pc : Piece) (hsrc : bs.board.grid src = some moving)
    (hbefore : ¬ attacksOriented bs.board pc.owner pc.pieceType pos target)
    (hafter : attacksOriented (applyMove bs (.boardMove src dst promote)).board
      pc.owner pc.pieceType pos target) :
    ∃ d ∈ pc.pieceType.slideDirs.map (Dir.forPlayer · pc.owner),
      (Pos.dirTo pos target).normalize = d ∧
      ∃ n j : ℕ, 1 ≤ n ∧ n ≤ 8 ∧ 1 ≤ j ∧ j < n ∧
        target.toInt = (pos.toInt.1 + ↑n * d.1, pos.toInt.2 + ↑n * d.2) ∧
        src.toInt = (pos.toInt.1 + ↑j * d.1, pos.toInt.2 + ↑j * d.2) := by
  have hmem := (applyMove_boardMove_new_attack_path bs src dst pos target promote moving pc hsrc hbefore hafter).1
  rcases hafter with hstep | ⟨d, hdir, hn, n, hk, hx, hy, _⟩
  · exact False.elim (hbefore (Or.inl hstep))
  have hd : d ≠ (0, 0) := by
    intro he
    rw [he] at hdir
    rcases pc with ⟨owner, pt⟩
    cases owner <;> cases pt <;>
      simp [PieceType.slideDirs, Dir.forPlayer, Dir.flip, Prod.ext_iff] at hdir
  have hx' : target.toInt.1 = pos.toInt.1 + ↑n * d.1 := by
    dsimp [Pos.dirTo, Pos.toInt] at hx ⊢
    omega
  have hy' : target.toInt.2 = pos.toInt.2 + ↑n * d.2 := by
    dsimp [Pos.dirTo, Pos.toInt] at hy ⊢
    omega
  obtain ⟨j, hj, hjn, he⟩ :=
    (mem_slidePath_iff_of_exact_steps pos target d n hd hk hn hx' hy' src.toInt).mp hmem
  exact ⟨d, hdir, hn, n, j, hk,
    slideSteps_le_eight_of_endpoints pos target d n hd hx' hy', hj, hjn,
    Prod.ext hx' hy', he⟩

/-- A post-move other-position checker of a previously unchecked fixed target
    is retained and newly enabled through source unblocking. A destination
    checker may coexist; no absence of destination checkers is required. -/
theorem applyMove_boardMove_otherChecker_source_unblocking (bs : BoardState) (src dst target : Pos) (promote : Bool)
    (moving : Piece) (kingOwner : Player) (hsrc : bs.board.grid src = some moving)
    (hbefore : ¬ inCheckOriented bs.board kingOwner target)
    (hother : hasOtherCheckerOriented (applyMove bs (.boardMove src dst promote)).board
      (.boardMove src dst promote) kingOwner target) :
    ∃ pos piece, pos ≠ src ∧ pos ≠ dst ∧ bs.board.grid pos = some piece ∧
      (applyMove bs (.boardMove src dst promote)).board.grid pos = some piece ∧
      piece.owner = kingOwner.opponent ∧
      attacksOriented (applyMove bs (.boardMove src dst promote)).board
        piece.owner piece.pieceType pos target ∧
      src.toInt ∈ slidePath pos target ∧ dst.toInt ∉ slidePath pos target ∧
      ¬ pathClear bs.board pos target ∧
      pathClear (applyMove bs (.boardMove src dst promote)).board pos target := by
  obtain ⟨pos, hd, pc, hp, ho, ha⟩ := hother
  obtain ⟨hs, hp0⟩ := applyMove_boardMove_other_piece_before bs src dst pos promote pc hd hp
  have hn : ¬ attacksOriented bs.board pc.owner pc.pieceType pos target := by
    intro hb
    exact hbefore ⟨pos, pc, hp0, ho, hb⟩
  exact ⟨pos, pc, hs, hd, hp0, hp, ho, ha,
    applyMove_boardMove_new_attack_path bs src dst pos target promote moving pc hsrc hn ha⟩

/-- Apply the one-step result at any trace index. Target equality is explicit;
    interpreting the targets as actual kings additionally requires placement
    consistency, not assumed here or derived from this theorem. -/
theorem MoveTrace.boardMove_otherChecker_source_unblocking (tr : MoveTrace) (ht : tr.FollowsTransitions)
    (kp : Fin (tr.len + 1) → Player → Pos) (i : Fin tr.len)
    (src dst : Pos) (promote : Bool) (moving : Piece) (owner : Player)
    (hm : tr.moves i = .boardMove src dst promote)
    (hs : (tr.before i).board.grid src = some moving)
    (hk : kp i.succ owner = kp i.castSucc owner)
    (hb : ¬ inCheckOriented (tr.before i).board owner (kp i.castSucc owner))
    (ha : hasOtherCheckerOriented (tr.after i).board (tr.moves i) owner (kp i.succ owner)) :
    ∃ pos piece, pos ≠ src ∧ pos ≠ dst ∧ (tr.before i).board.grid pos = some piece ∧
      (tr.after i).board.grid pos = some piece ∧ piece.owner = owner.opponent ∧
      attacksOriented (tr.after i).board piece.owner piece.pieceType pos (kp i.succ owner) ∧
      src.toInt ∈ slidePath pos (kp i.succ owner) ∧
      dst.toInt ∉ slidePath pos (kp i.succ owner) ∧
      ¬ pathClear (tr.before i).board pos (kp i.succ owner) ∧
      pathClear (tr.after i).board pos (kp i.succ owner) := by
  have hb' : ¬ inCheckOriented (tr.before i).board owner (kp i.succ owner) := by
    simpa only [hk] using hb
  rw [ht i, hm] at ha ⊢
  exact applyMove_boardMove_otherChecker_source_unblocking (tr.before i) src dst (kp i.succ owner) promote moving owner hs hb' ha

end MPC
