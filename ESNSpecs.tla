------------------------------ MODULE ESNSpecs ---------------------------

EXTENDS  Sequences,Naturals,TLC,FiniteSets

CONSTANTS any

VARIABLES depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack, _pc

vars == << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack, _pc >>

upperbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : n >= m

lowerbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : m >= n

Enterprise1 == 
               LET Enterprise1_start == 1 IN 
                LET Enterprise1_end == 1 IN
                    Enterprise1_start .. Enterprise1_end

Enterprise2 == 
               LET Enterprise2_start == upperbound(Enterprise1) + 1 IN 
                LET Enterprise2_end == upperbound(Enterprise1) + 1 IN
                    Enterprise2_start .. Enterprise2_end

ProcSet == Enterprise1 \cup Enterprise2

Init == 
    /\ depth = 0
    /\ cp = any
    /\ EP1Users = {"Alice", "Tim"}
    /\ EP2Users = {"Bob", "Genny"}
    /\ AllUsers = (EP1Users \cup EP2Users)
    /\ EP1Res = {"R1", "R2"}
    /\ EP2Res = {"R3", "R4"}
    /\ AllRes = (EP1Res \cup EP2Res)
    /\ ReqPool = [u \in AllUsers, r \in AllRes |-> [status |-> {}]]
    /\ h = {}
    /\ a = 0
    /\ _Enterprise1_data = [self \in Enterprise1 |-> [ self |-> self, parentID |-> 0, Name|->"Enterprise1", Policies|->[u \in AllUsers |-> CASE (u = "Alice") -> {[res |-> "R2", act |-> "deny"], [res |-> "R3", act |-> "allow"]} [] (u = "Bob") -> {[res |-> "R4", act |-> "deny"], [res |-> "R3", act |-> "allow"]} [] (u = "Tim") -> {[res |-> "R3", act |-> "allow"], [res |-> "R2", act |-> "deny"]} [] (u = "Genny") -> {[res |-> "R4", act |-> "deny"], [res |-> "R4", act |-> "deny"]}], rules|->0, status|->0, statusRecord|->0, u|->0, idS_u|->{}, r|->0, idS_r|->{}, rule|->0, idS_rule|->{}]]

    /\ _Enterprise2_data = [self \in Enterprise2 |-> [ self |-> self, parentID |-> 0, Name|->"Enterprise2", Policies|->[u \in AllUsers |-> CASE (u = "Alice") -> {[res |-> "R2", act |-> "deny"], [res |-> "R1", act |-> "allow"]} [] (u = "Bob") -> {[res |-> "R1", act |-> "deny"], [res |-> "R2", act |-> "allow"]} [] (u = "Tim") -> {[res |-> "R1", act |-> "deny"], [res |-> "R4", act |-> "deny"]} [] (u = "Genny") -> {[res |-> "R1", act |-> "deny"], [res |-> "R4", act |-> "allow"]}], rules|->0, status|->0, statusRecord|->0, u|->0, idS_u|->{}, r|->0, idS_r|->{}, rule|->0, idS_rule|->{}]]

    /\ _stack = [self \in ProcSet |-> << >>]
    /\ _pc = [self \in ProcSet |-> CASE self \in Enterprise1 -> "Lbl_1"
                         []self \in Enterprise2 -> "Lbl_5"]

Push(s,e) == e \circ s 

Lbl_1(self) == 
               /\ _pc[self] = "Lbl_1"
               /\ cp = any
                  /\ cp' = self
                  /\ depth' = depth + 1
                  /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                  /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack >>
Lbl_2(self) == 
               /\ _pc[self] = "Lbl_2"
               /\ cp = self
               /\ IF AllUsers # {} /\ _Enterprise1_data[self].idS_u = {}
                        THEN /\ LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].idS_u = AllUsers] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                /\ _Enterprise1_data' = __Enterprise1_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                        ELSE
                             /\ IF _Enterprise1_data[self].idS_u # {}
                                      THEN /\ LET u == CHOOSE fech \in _Enterprise1_data[self].idS_u : TRUE IN
                                              LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].u = u] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                              /\ _Enterprise1_data' = __Enterprise1_data
                                              /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                              /\ depth' = depth - 1
                                              /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack >>
Lbl_3(self) == 
               /\ _pc[self] = "Lbl_3"
               /\ cp = self
               /\ IF AllRes # {} /\ _Enterprise1_data[self].idS_r = {}
                        THEN /\ LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].idS_r = AllRes] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                /\ _Enterprise1_data' = __Enterprise1_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                        ELSE
                             /\ IF _Enterprise1_data[self].idS_r # {}
                                      THEN /\ LET r == CHOOSE fech \in _Enterprise1_data[self].idS_r : TRUE IN
                                              LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].r = r] IN
                                              LET ___Enterprise1_data == [__Enterprise1_data EXCEPT ![self].rules = __Enterprise1_data[self].Policies[__Enterprise1_data[self].u]] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                              /\ _Enterprise1_data' = ___Enterprise1_data
                                              /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                      ELSE
                                           /\ LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].idS_u = _Enterprise1_data[self].idS_u \ {_Enterprise1_data[self].u }] IN
                                              /\ IF __Enterprise1_data[self].idS_u # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                            /\ _Enterprise1_data' = __Enterprise1_data
                                                            /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                    ELSE
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                            /\ _Enterprise1_data' = __Enterprise1_data
                                                            /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                            /\ depth' = depth - 1
                                                            /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
Lbl_4(self) == 
               /\ _pc[self] = "Lbl_4"
               /\ cp = self
               /\ IF _Enterprise1_data[self].rules # {} /\ _Enterprise1_data[self].idS_rule = {}
                        THEN /\ LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].idS_rule = _Enterprise1_data[self].rules] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                /\ _Enterprise1_data' = __Enterprise1_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                        ELSE
                             /\ IF _Enterprise1_data[self].idS_rule # {}
                                      THEN /\ LET rule == CHOOSE fech \in _Enterprise1_data[self].idS_rule : TRUE IN
                                              LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].rule = rule] IN
                                              /\ \/ /\ (__Enterprise1_data[self].rule.res = __Enterprise1_data[self].r)
                                                    /\ LET ___Enterprise1_data == [__Enterprise1_data EXCEPT ![self].statusRecord = ReqPool[__Enterprise1_data[self].u, __Enterprise1_data[self].r]] IN
                                                       LET ____Enterprise1_data == [___Enterprise1_data EXCEPT ![self].statusRecord.status = (___Enterprise1_data[self].statusRecord.status \cup {___Enterprise1_data[self].rule.act})] IN
                                                       LET _ReqPool == [ReqPool EXCEPT ![____Enterprise1_data[self].u, ____Enterprise1_data[self].r] = ____Enterprise1_data[self].statusRecord] IN
                                                       LET _____Enterprise1_data == [____Enterprise1_data EXCEPT ![self].idS_rule = ____Enterprise1_data[self].idS_rule \ {____Enterprise1_data[self].rule }] IN
                                                       /\ IF _____Enterprise1_data[self].idS_rule # {}
                                                             THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                                                     /\ _Enterprise1_data' = _____Enterprise1_data
                                                                     /\ ReqPool' = _ReqPool
                                                                     /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise2_data, _stack >>
                                                             ELSE
                                                                  /\ LET ______Enterprise1_data == [_____Enterprise1_data EXCEPT ![self].idS_r = _____Enterprise1_data[self].idS_r \ {_____Enterprise1_data[self].r }] IN
                                                                     /\ IF ______Enterprise1_data[self].idS_r # {}
                                                                           THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                                                                   /\ _Enterprise1_data' = ______Enterprise1_data
                                                                                   /\ ReqPool' = _ReqPool
                                                                                   /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise2_data, _stack >>
                                                                           ELSE
                                                                                /\ LET _______Enterprise1_data == [______Enterprise1_data EXCEPT ![self].idS_u = ______Enterprise1_data[self].idS_u \ {______Enterprise1_data[self].u }] IN
                                                                                   /\ IF _______Enterprise1_data[self].idS_u # {}
                                                                                         THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                                                 /\ _Enterprise1_data' = _______Enterprise1_data
                                                                                                 /\ ReqPool' = _ReqPool
                                                                                                 /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise2_data, _stack >>
                                                                                         ELSE
                                                                                                 /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                                                 /\ _Enterprise1_data' = _______Enterprise1_data
                                                                                                 /\ ReqPool' = _ReqPool
                                                                                                 /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                                                 /\ depth' = depth - 1
                                                                                                 /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise2_data, _stack >>
                                                 \/ /\ ~((__Enterprise1_data[self].rule.res = __Enterprise1_data[self].r))
                                                       /\ LET ___Enterprise1_data == [__Enterprise1_data EXCEPT ![self].idS_rule = __Enterprise1_data[self].idS_rule \ {__Enterprise1_data[self].rule }] IN
                                                          /\ IF ___Enterprise1_data[self].idS_rule # {}
                                                                THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                                                        /\ _Enterprise1_data' = ___Enterprise1_data
                                                                        /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                                ELSE
                                                                     /\ LET ____Enterprise1_data == [___Enterprise1_data EXCEPT ![self].idS_r = ___Enterprise1_data[self].idS_r \ {___Enterprise1_data[self].r }] IN
                                                                        /\ IF ____Enterprise1_data[self].idS_r # {}
                                                                              THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                                                                      /\ _Enterprise1_data' = ____Enterprise1_data
                                                                                      /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                                              ELSE
                                                                                   /\ LET _____Enterprise1_data == [____Enterprise1_data EXCEPT ![self].idS_u = ____Enterprise1_data[self].idS_u \ {____Enterprise1_data[self].u }] IN
                                                                                      /\ IF _____Enterprise1_data[self].idS_u # {}
                                                                                            THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                                                    /\ _Enterprise1_data' = _____Enterprise1_data
                                                                                                    /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                                                            ELSE
                                                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                                                    /\ _Enterprise1_data' = _____Enterprise1_data
                                                                                                    /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                                                    /\ depth' = depth - 1
                                                                                                    /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                      ELSE
                                           /\ LET __Enterprise1_data == [_Enterprise1_data EXCEPT ![self].idS_r = _Enterprise1_data[self].idS_r \ {_Enterprise1_data[self].r }] IN
                                              /\ IF __Enterprise1_data[self].idS_r # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                                            /\ _Enterprise1_data' = __Enterprise1_data
                                                            /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                    ELSE
                                                         /\ LET ___Enterprise1_data == [__Enterprise1_data EXCEPT ![self].idS_u = __Enterprise1_data[self].idS_u \ {__Enterprise1_data[self].u }] IN
                                                            /\ IF ___Enterprise1_data[self].idS_u # {}
                                                                  THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_2"]
                                                                          /\ _Enterprise1_data' = ___Enterprise1_data
                                                                          /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
                                                                  ELSE
                                                                          /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                          /\ _Enterprise1_data' = ___Enterprise1_data
                                                                          /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                          /\ depth' = depth - 1
                                                                          /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise2_data, _stack >>
_Enterprise1(self) == 
                          Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ Lbl_4(self)  
Lbl_5(self) == 
               /\ _pc[self] = "Lbl_5"
               /\ cp = any
                  /\ cp' = self
                  /\ depth' = depth + 1
                  /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                  /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack >>
Lbl_6(self) == 
               /\ _pc[self] = "Lbl_6"
               /\ cp = self
               /\ IF AllUsers # {} /\ _Enterprise2_data[self].idS_u = {}
                        THEN /\ LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].idS_u = AllUsers] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                /\ _Enterprise2_data' = __Enterprise2_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                        ELSE
                             /\ IF _Enterprise2_data[self].idS_u # {}
                                      THEN /\ LET u == CHOOSE fech \in _Enterprise2_data[self].idS_u : TRUE IN
                                              LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].u = u] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                              /\ _Enterprise2_data' = __Enterprise2_data
                                              /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                              /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                              /\ depth' = depth - 1
                                              /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _Enterprise2_data, _stack >>
Lbl_7(self) == 
               /\ _pc[self] = "Lbl_7"
               /\ cp = self
               /\ IF AllRes # {} /\ _Enterprise2_data[self].idS_r = {}
                        THEN /\ LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].idS_r = AllRes] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                /\ _Enterprise2_data' = __Enterprise2_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                        ELSE
                             /\ IF _Enterprise2_data[self].idS_r # {}
                                      THEN /\ LET r == CHOOSE fech \in _Enterprise2_data[self].idS_r : TRUE IN
                                              LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].r = r] IN
                                              LET ___Enterprise2_data == [__Enterprise2_data EXCEPT ![self].rules = __Enterprise2_data[self].Policies[__Enterprise2_data[self].u]] IN
                                              /\ _pc' = [_pc EXCEPT ![self] = "Lbl_8"]
                                              /\ _Enterprise2_data' = ___Enterprise2_data
                                              /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                      ELSE
                                           /\ LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].idS_u = _Enterprise2_data[self].idS_u \ {_Enterprise2_data[self].u }] IN
                                              /\ IF __Enterprise2_data[self].idS_u # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                                            /\ _Enterprise2_data' = __Enterprise2_data
                                                            /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                    ELSE
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                            /\ _Enterprise2_data' = __Enterprise2_data
                                                            /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                            /\ depth' = depth - 1
                                                            /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
Lbl_8(self) == 
               /\ _pc[self] = "Lbl_8"
               /\ cp = self
               /\ IF _Enterprise2_data[self].rules # {} /\ _Enterprise2_data[self].idS_rule = {}
                        THEN /\ LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].idS_rule = _Enterprise2_data[self].rules] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_8"]
                                /\ _Enterprise2_data' = __Enterprise2_data
                                /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                        ELSE
                             /\ IF _Enterprise2_data[self].idS_rule # {}
                                      THEN /\ LET rule == CHOOSE fech \in _Enterprise2_data[self].idS_rule : TRUE IN
                                              LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].rule = rule] IN
                                              /\ \/ /\ (__Enterprise2_data[self].rule.res = __Enterprise2_data[self].r)
                                                    /\ LET ___Enterprise2_data == [__Enterprise2_data EXCEPT ![self].statusRecord = ReqPool[__Enterprise2_data[self].u, __Enterprise2_data[self].r]] IN
                                                       LET ____Enterprise2_data == [___Enterprise2_data EXCEPT ![self].statusRecord.status = (___Enterprise2_data[self].statusRecord.status \cup {___Enterprise2_data[self].rule.act})] IN
                                                       LET _ReqPool == [ReqPool EXCEPT ![____Enterprise2_data[self].u, ____Enterprise2_data[self].r] = ____Enterprise2_data[self].statusRecord] IN
                                                       LET _____Enterprise2_data == [____Enterprise2_data EXCEPT ![self].idS_rule = ____Enterprise2_data[self].idS_rule \ {____Enterprise2_data[self].rule }] IN
                                                       /\ IF _____Enterprise2_data[self].idS_rule # {}
                                                             THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_8"]
                                                                     /\ _Enterprise2_data' = _____Enterprise2_data
                                                                     /\ ReqPool' = _ReqPool
                                                                     /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise1_data, _stack >>
                                                             ELSE
                                                                  /\ LET ______Enterprise2_data == [_____Enterprise2_data EXCEPT ![self].idS_r = _____Enterprise2_data[self].idS_r \ {_____Enterprise2_data[self].r }] IN
                                                                     /\ IF ______Enterprise2_data[self].idS_r # {}
                                                                           THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                                                                   /\ _Enterprise2_data' = ______Enterprise2_data
                                                                                   /\ ReqPool' = _ReqPool
                                                                                   /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise1_data, _stack >>
                                                                           ELSE
                                                                                /\ LET _______Enterprise2_data == [______Enterprise2_data EXCEPT ![self].idS_u = ______Enterprise2_data[self].idS_u \ {______Enterprise2_data[self].u }] IN
                                                                                   /\ IF _______Enterprise2_data[self].idS_u # {}
                                                                                         THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                                                                                 /\ _Enterprise2_data' = _______Enterprise2_data
                                                                                                 /\ ReqPool' = _ReqPool
                                                                                                 /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise1_data, _stack >>
                                                                                         ELSE
                                                                                                 /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                                                 /\ _Enterprise2_data' = _______Enterprise2_data
                                                                                                 /\ ReqPool' = _ReqPool
                                                                                                 /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                                                 /\ depth' = depth - 1
                                                                                                 /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, h, a, _Enterprise1_data, _stack >>
                                                 \/ /\ ~((__Enterprise2_data[self].rule.res = __Enterprise2_data[self].r))
                                                       /\ LET ___Enterprise2_data == [__Enterprise2_data EXCEPT ![self].idS_rule = __Enterprise2_data[self].idS_rule \ {__Enterprise2_data[self].rule }] IN
                                                          /\ IF ___Enterprise2_data[self].idS_rule # {}
                                                                THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_8"]
                                                                        /\ _Enterprise2_data' = ___Enterprise2_data
                                                                        /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                                ELSE
                                                                     /\ LET ____Enterprise2_data == [___Enterprise2_data EXCEPT ![self].idS_r = ___Enterprise2_data[self].idS_r \ {___Enterprise2_data[self].r }] IN
                                                                        /\ IF ____Enterprise2_data[self].idS_r # {}
                                                                              THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                                                                      /\ _Enterprise2_data' = ____Enterprise2_data
                                                                                      /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                                              ELSE
                                                                                   /\ LET _____Enterprise2_data == [____Enterprise2_data EXCEPT ![self].idS_u = ____Enterprise2_data[self].idS_u \ {____Enterprise2_data[self].u }] IN
                                                                                      /\ IF _____Enterprise2_data[self].idS_u # {}
                                                                                            THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                                                                                    /\ _Enterprise2_data' = _____Enterprise2_data
                                                                                                    /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                                                            ELSE
                                                                                                    /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                                                    /\ _Enterprise2_data' = _____Enterprise2_data
                                                                                                    /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                                                    /\ depth' = depth - 1
                                                                                                    /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                      ELSE
                                           /\ LET __Enterprise2_data == [_Enterprise2_data EXCEPT ![self].idS_r = _Enterprise2_data[self].idS_r \ {_Enterprise2_data[self].r }] IN
                                              /\ IF __Enterprise2_data[self].idS_r # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_7"]
                                                            /\ _Enterprise2_data' = __Enterprise2_data
                                                            /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                    ELSE
                                                         /\ LET ___Enterprise2_data == [__Enterprise2_data EXCEPT ![self].idS_u = __Enterprise2_data[self].idS_u \ {__Enterprise2_data[self].u }] IN
                                                            /\ IF ___Enterprise2_data[self].idS_u # {}
                                                                  THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_6"]
                                                                          /\ _Enterprise2_data' = ___Enterprise2_data
                                                                          /\ UNCHANGED << depth, cp, EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
                                                                  ELSE
                                                                          /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                                          /\ _Enterprise2_data' = ___Enterprise2_data
                                                                          /\ cp' = IF depth - 1 = 0 THEN any ELSE self
                                                                          /\ depth' = depth - 1
                                                                          /\ UNCHANGED << EP1Users, EP2Users, AllUsers, EP1Res, EP2Res, AllRes, ReqPool, h, a, _Enterprise1_data, _stack >>
_Enterprise2(self) == 
                          Lbl_5(self) \/ Lbl_6(self) \/ Lbl_7(self) \/ Lbl_8(self)  

Next == (\E self \in Enterprise1 : _Enterprise1(self))
                          \/ (\E self \in Enterprise2 : _Enterprise2(self))
                          \/ ((\A self \in ProcSet : _pc[self] = "Done")
                              /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Inv0 == \A u \in AllUsers, r \in AllRes : ((ReqPool[u, r].status \cap {"allow", "deny"}) # {"allow", "deny"})

=================================================================================
