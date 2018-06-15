---- MODULE watches ----
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS NumLiterals
ASSUME NumLiterals > 3
NL == NumLiterals

(* --algorithm transfer
variables watches = [x \in 1..2 |-> x], blockers = [x \in 1..2 |-> 3-x],
          literals = [x \in 1..NL |-> 0], prop = 0,
          backtrack = 0, trail = <<>>, limit = 0;

define
  \*MyWatch(l) == if { x \in 1..2: watches[x] = l } = {} then 0 else CHOOSE x \in 1..2: watches[x] = l end
  NotFalseLiterals == { x \in 1..NL: literals[x] /= 1 }
  BlockersNotFalse == { x \in 1..2: literals[blockers[x]] /= 1 } /= {}
  
  Watched == { watches[x]: x \in 1..2 }
  UnsetLiterals == { x \in 1..NL: literals[x] = 0 }
  NonFalse == { x \in 1..NL: literals[x] /= 1 }
  NonFalseWatched == { x \in NonFalse: x /= watches[1] /\ x /= watches[2] }
  PassChecks == { x \in 1..NL:
                             \/ literals[x] = 2                         \* Accept true literals
                             \/ ( literals[x] = 0 /\ x \notin Watched ) \* Accept unwatched unset literals
                             }
  NextFrom(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S: \A y \in S: x <= y
  
  NextLiteral == NextFrom(PassChecks)
  NextUnwatchedLiteral == NextFrom(NonFalseWatched)
  
  ValidWatches == /\ watches[1] /= watches[2]
                  /\ ( literals[watches[1]] /= 1 \/ literals[blockers[1]] = 2 )
                  /\ ( literals[watches[2]] /= 1 \/ literals[blockers[2]] = 2 )
  UnitClause == Cardinality(NonFalse) <= 1
  
  MyWatch(self) == IF watches[1] = self THEN 1 ELSE IF watches[2] = self THEN 2 ELSE 0


  (*NextLiteral == IF { x \in 1..NL: literals[x] /= 1 } = {}
                 THEN 0 ELSE CHOOSE x \in 1..NL:
                             /\ literals[x] /= 1
                             /\ \A y \in 1..NL: literals[y] /= 1 => x <= y
  NextUnwatchedLiteral == IF { x \in 1..NL: literals[x] /= 1 /\ watches[1] /= x /\ watches[2] /= x } = {}
                          THEN 0 ELSE CHOOSE x \in 1..NL:
                             /\ literals[x] /= 1
                             /\ \A y \in 1..NL: literals[y] /= 1 => x <= y*)
end define;

macro update_watches_bothknown(watch)
begin
    if NextLiteral = 0 then \* cardinality must be low
      assert Cardinality(UnsetLiterals) = 2; \* There should be 2 unset literal (the watched one)
      prop := CHOOSE x \in UnsetLiterals: x /= self; \* Set that literal true
    elsif literals[NextLiteral] = 2 then \* if found a true literal then keep watch and update blocker
      blockers[watch] := NextLiteral;
    else \* next must be unassigned - update watch
      watches[watch] := NextLiteral;
      blockers[watch] := IF NextLiteral = 1 THEN 2 ELSE 1;
    end if;
end macro;

process literal \in 1..NL
begin L:
  while limit < NL + NL do
    await prop = 0 /\ backtrack = 0;
    limit := limit + 1;
    if literals[self] = 0 then
      trail := Append(trail, self);
      \* set var x to true or false
       either
        literals[self] := 1;
        if MyWatch(self) /= 0 then \* Only care if there is a watch on this literal
          if literals[blockers[MyWatch(self)]] = 2 then \* If our blocking literal is true then skip
            skip;
          else
            update_watches_bothknown(MyWatch(self));
            if prop > 0 then
              PROP: literals[prop] := 2 || trail := Append(trail, prop) || prop := 0;
            else
              skip;
            end if;
          end if;
        else
          skip;
        end if;
      or
        literals[self] := 2;
        \* nothing to do when set to true
      end either;
    elsif Len(trail) < NL \/ trail[NL] /= self then \* Backtrack to self when we aren't propogated
      backtrack := CHOOSE x \in 1..Len(trail): trail[x] = self;
      BACKTRACK:
        literals := [x \in { trail[y] : y \in backtrack..Len(trail) } |-> 0] @@ literals;
        trail := IF backtrack = 1 THEN <<>> ELSE [x \in 1..backtrack-1 |-> trail[x]];
        backtrack := 0;
    else
      skip;  
    end if;
  end while;
end process;

end algorithm *)
\* BEGIN TRANSLATION
VARIABLES watches, blockers, literals, prop, backtrack, trail, limit, pc

(* define statement *)
NotFalseLiterals == { x \in 1..NL: literals[x] /= 1 }
BlockersNotFalse == { x \in 1..2: literals[blockers[x]] /= 1 } /= {}

Watched == { watches[x]: x \in 1..2 }
UnsetLiterals == { x \in 1..NL: literals[x] = 0 }
NonFalse == { x \in 1..NL: literals[x] /= 1 }
NonFalseWatched == { x \in NonFalse: x /= watches[1] /\ x /= watches[2] }
PassChecks == { x \in 1..NL:
                           \/ literals[x] = 2
                           \/ ( literals[x] = 0 /\ x \notin Watched )
                           }
NextFrom(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S: \A y \in S: x <= y

NextLiteral == NextFrom(PassChecks)
NextUnwatchedLiteral == NextFrom(NonFalseWatched)

ValidWatches == /\ watches[1] /= watches[2]
                /\ ( literals[watches[1]] /= 1 \/ literals[blockers[1]] = 2 )
                /\ ( literals[watches[2]] /= 1 \/ literals[blockers[2]] = 2 )
UnitClause == Cardinality(NonFalse) <= 1

MyWatch(self) == IF watches[1] = self THEN 1 ELSE IF watches[2] = self THEN 2 ELSE 0


vars == << watches, blockers, literals, prop, backtrack, trail, limit, pc >>

ProcSet == (1..NL)

Init == (* Global variables *)
        /\ watches = [x \in 1..2 |-> x]
        /\ blockers = [x \in 1..2 |-> 3-x]
        /\ literals = [x \in 1..NL |-> 0]
        /\ prop = 0
        /\ backtrack = 0
        /\ trail = <<>>
        /\ limit = 0
        /\ pc = [self \in ProcSet |-> "L"]

L(self) == /\ pc[self] = "L"
           /\ IF limit < NL + NL
                 THEN /\ prop = 0 /\ backtrack = 0
                      /\ limit' = limit + 1
                      /\ IF literals[self] = 0
                            THEN /\ trail' = Append(trail, self)
                                 /\ \/ /\ literals' = [literals EXCEPT ![self] = 1]
                                       /\ IF MyWatch(self) /= 0
                                             THEN /\ IF literals'[blockers[MyWatch(self)]] = 2
                                                        THEN /\ TRUE
                                                             /\ pc' = [pc EXCEPT ![self] = "L"]
                                                             /\ UNCHANGED << watches, 
                                                                             blockers, 
                                                                             prop >>
                                                        ELSE /\ IF NextLiteral = 0
                                                                   THEN /\ Assert(Cardinality(UnsetLiterals) = 2, 
                                                                                  "Failure of assertion at line 52, column 7 of macro called at line 76, column 13.")
                                                                        /\ prop' = (CHOOSE x \in UnsetLiterals: x /= self)
                                                                        /\ UNCHANGED << watches, 
                                                                                        blockers >>
                                                                   ELSE /\ IF literals'[NextLiteral] = 2
                                                                              THEN /\ blockers' = [blockers EXCEPT ![(MyWatch(self))] = NextLiteral]
                                                                                   /\ UNCHANGED watches
                                                                              ELSE /\ watches' = [watches EXCEPT ![(MyWatch(self))] = NextLiteral]
                                                                                   /\ blockers' = [blockers EXCEPT ![(MyWatch(self))] = IF NextLiteral = 1 THEN 2 ELSE 1]
                                                                        /\ prop' = prop
                                                             /\ IF prop' > 0
                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "PROP"]
                                                                   ELSE /\ TRUE
                                                                        /\ pc' = [pc EXCEPT ![self] = "L"]
                                             ELSE /\ TRUE
                                                  /\ pc' = [pc EXCEPT ![self] = "L"]
                                                  /\ UNCHANGED << watches, 
                                                                  blockers, 
                                                                  prop >>
                                    \/ /\ literals' = [literals EXCEPT ![self] = 2]
                                       /\ pc' = [pc EXCEPT ![self] = "L"]
                                       /\ UNCHANGED <<watches, blockers, prop>>
                                 /\ UNCHANGED backtrack
                            ELSE /\ IF Len(trail) < NL \/ trail[NL] /= self
                                       THEN /\ backtrack' = (CHOOSE x \in 1..Len(trail): trail[x] = self)
                                            /\ pc' = [pc EXCEPT ![self] = "BACKTRACK"]
                                       ELSE /\ TRUE
                                            /\ pc' = [pc EXCEPT ![self] = "L"]
                                            /\ UNCHANGED backtrack
                                 /\ UNCHANGED << watches, blockers, literals, 
                                                 prop, trail >>
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << watches, blockers, literals, prop, 
                                      backtrack, trail, limit >>

PROP(self) == /\ pc[self] = "PROP"
              /\ /\ literals' = [literals EXCEPT ![prop] = 2]
                 /\ prop' = 0
                 /\ trail' = Append(trail, prop)
              /\ pc' = [pc EXCEPT ![self] = "L"]
              /\ UNCHANGED << watches, blockers, backtrack, limit >>

BACKTRACK(self) == /\ pc[self] = "BACKTRACK"
                   /\ literals' = [x \in { trail[y] : y \in backtrack..Len(trail) } |-> 0] @@ literals
                   /\ trail' = (IF backtrack = 1 THEN <<>> ELSE [x \in 1..backtrack-1 |-> trail[x]])
                   /\ backtrack' = 0
                   /\ pc' = [pc EXCEPT ![self] = "L"]
                   /\ UNCHANGED << watches, blockers, prop, limit >>

literal(self) == L(self) \/ PROP(self) \/ BACKTRACK(self)

Next == (\E self \in 1..NL: literal(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


====
