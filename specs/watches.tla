---- MODULE watches ----
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS NumLiterals
ASSUME NumLiterals > 3
NL == NumLiterals

(* --algorithm transfer
variables watches = [x \in 1..2 |-> x], blockers = [x \in 1..2 |-> 3-x],
          literals = [x \in 1..NL |-> 0], prop = 0,
          backtrack = 0, trail = <<>>;

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
  
  (*NextLiteral == IF { x \in 1..NL: literals[x] /= 1 } = {}
                 THEN 0 ELSE CHOOSE x \in 1..NL:
                             /\ literals[x] /= 1
                             /\ \A y \in 1..NL: literals[y] /= 1 => x <= y
  NextUnwatchedLiteral == IF { x \in 1..NL: literals[x] /= 1 /\ watches[1] /= x /\ watches[2] /= x } = {}
                          THEN 0 ELSE CHOOSE x \in 1..NL:
                             /\ literals[x] /= 1
                             /\ \A y \in 1..NL: literals[y] /= 1 => x <= y*)
end define;

macro update_watches(watch)
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
variables watch = 0, called = 0;
begin L:
  while called < 5 do
    await prop = 0 /\ backtrack = 0;
    called := called + 1;
    if literals[self] = 0 then
      trail := Append(trail, self);
      \* set var x to true or false
       either
        literals[self] := 1;
        watch := IF watches[1] = self THEN 1 ELSE IF watches[2] = self THEN 2 ELSE 0;
        if watch /= 0 then \* Only care if there is a watch on this literal
          if literals[blockers[watch]] = 2 then \* If our blocking literal is true then skip
            skip;
          else
            update_watches(watch);
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
VARIABLES watches, blockers, literals, prop, backtrack, trail, pc

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

VARIABLES watch, called

vars == << watches, blockers, literals, prop, backtrack, trail, pc, watch, 
           called >>

ProcSet == (1..NL)

Init == (* Global variables *)
        /\ watches = [x \in 1..2 |-> x]
        /\ blockers = [x \in 1..2 |-> 3-x]
        /\ literals = [x \in 1..NL |-> 0]
        /\ prop = 0
        /\ backtrack = 0
        /\ trail = <<>>
        (* Process literal *)
        /\ watch = [self \in 1..NL |-> 0]
        /\ called = [self \in 1..NL |-> 0]
        /\ pc = [self \in ProcSet |-> "L"]

L(self) == /\ pc[self] = "L"
           /\ IF called[self] < 5
                 THEN /\ prop = 0 /\ backtrack = 0
                      /\ called' = [called EXCEPT ![self] = called[self] + 1]
                      /\ IF literals[self] = 0
                            THEN /\ trail' = Append(trail, self)
                                 /\ \/ /\ literals' = [literals EXCEPT ![self] = 1]
                                       /\ watch' = [watch EXCEPT ![self] = IF watches[1] = self THEN 1 ELSE IF watches[2] = self THEN 2 ELSE 0]
                                       /\ IF watch'[self] /= 0
                                             THEN /\ IF literals'[blockers[watch'[self]]] = 2
                                                        THEN /\ TRUE
                                                             /\ pc' = [pc EXCEPT ![self] = "L"]
                                                             /\ UNCHANGED << watches, 
                                                                             blockers, 
                                                                             prop >>
                                                        ELSE /\ IF NextLiteral = 0
                                                                   THEN /\ Assert(Cardinality(UnsetLiterals) = 2, 
                                                                                  "Failure of assertion at line 49, column 7 of macro called at line 75, column 13.")
                                                                        /\ prop' = (CHOOSE x \in UnsetLiterals: x /= self)
                                                                        /\ UNCHANGED << watches, 
                                                                                        blockers >>
                                                                   ELSE /\ IF literals'[NextLiteral] = 2
                                                                              THEN /\ blockers' = [blockers EXCEPT ![watch'[self]] = NextLiteral]
                                                                                   /\ UNCHANGED watches
                                                                              ELSE /\ watches' = [watches EXCEPT ![watch'[self]] = NextLiteral]
                                                                                   /\ blockers' = [blockers EXCEPT ![watch'[self]] = IF NextLiteral = 1 THEN 2 ELSE 1]
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
                                       /\ UNCHANGED <<watches, blockers, prop, watch>>
                                 /\ UNCHANGED backtrack
                            ELSE /\ IF Len(trail) < NL \/ trail[NL] /= self
                                       THEN /\ backtrack' = (CHOOSE x \in 1..Len(trail): trail[x] = self)
                                            /\ pc' = [pc EXCEPT ![self] = "BACKTRACK"]
                                       ELSE /\ TRUE
                                            /\ pc' = [pc EXCEPT ![self] = "L"]
                                            /\ UNCHANGED backtrack
                                 /\ UNCHANGED << watches, blockers, literals, 
                                                 prop, trail, watch >>
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << watches, blockers, literals, prop, 
                                      backtrack, trail, watch, called >>

PROP(self) == /\ pc[self] = "PROP"
              /\ /\ literals' = [literals EXCEPT ![prop] = 2]
                 /\ prop' = 0
                 /\ trail' = Append(trail, prop)
              /\ pc' = [pc EXCEPT ![self] = "L"]
              /\ UNCHANGED << watches, blockers, backtrack, watch, called >>

BACKTRACK(self) == /\ pc[self] = "BACKTRACK"
                   /\ literals' = [x \in { trail[y] : y \in backtrack..Len(trail) } |-> 0] @@ literals
                   /\ trail' = (IF backtrack = 1 THEN <<>> ELSE [x \in 1..backtrack-1 |-> trail[x]])
                   /\ backtrack' = 0
                   /\ pc' = [pc EXCEPT ![self] = "L"]
                   /\ UNCHANGED << watches, blockers, prop, watch, called >>

literal(self) == L(self) \/ PROP(self) \/ BACKTRACK(self)

Next == (\E self \in 1..NL: literal(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


====
