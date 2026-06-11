


push(K, [S|Ss], R, Formula) :-
	stack_atom(K, Stack),
	head_atom(K, Head),
	push(Ss, S, R, Stack, Head, Formula).

stack(K, X, S, Y,  at(Stack,[X,S,Y])) :-
	stack_atom(K, Stack).
head(K, Y,  at(Head,[Y])) :-
	head_atom(K, Head).
word(L, W, R, at(word, [L,  W, R])).

push([], S, R, Stack, Head, exists(X,p(at(Stack,[R,S,X]),at(Head,[X])))).
push([S|Ss], S0, R, Stack, Head, exists(X,p(at(Stack,[R,S0,X]),Form))) :-
	push(Ss, S, X, Stack, Head, Form).

% =
% formula for popping symbol T from stack K
pop(K,  S, [Y,Z|Qs], Qs, [at(Head,[Z]),at(Stack,[Y,S,Z])|As], As, [at(Head,[Y])|Bs],Bs) :-
	head_atom(K,  Head),
	stack_atom(K, Stack).
push(K, Ss, [Y|Qs], Qs, [at(Head,[Y])|As], As, [Push|Bs], Bs) :-
	head_atom(K, Head),
	push(K, Ss, Y, Push).
repl(K, S, Ss, [Y,Z|Qs], Qs, [at(Head,[Z]),at(Stack,[Y,S,Z])|As], As, [Push|Bs], Bs) :-
	head_atom(K, Head),
	stack_atom(K, Stack),
	push(K, Ss, Y, Push).
scan(S, [X, Y|Qs], Qs,  [at(head,[X]),at(word,[X,S,Y])|As], As, [at(head,[Y])|Bs], Bs).
state(Q1, Q2, Qs, Qs, [at(Q1,[])|As], As, [at(Q2,[])|Bs], Bs).


actions_to_formulas(Actions, F) :-
	actions_to_formula(Actions, Qs, [], Bs, [], Cs, []),
	create_formula(Qs, Bs, Cs, F).

create_formula([], Bs,  Cs, F) :-
	create_formula(Bs, Cs, F).
create_formula([Q|Qs], Bs,  Cs, forall(Q, F)) :-
	create_formula(Qs, Bs, Cs, F).

create_formula([], [C|Cs], F) :-
	create_formula1(Cs, C, F).
create_formula([B|Bs], Cs, impl(B,F)) :-
	create_formula(Bs, Cs, F).

create_formula1([], C, C).
create_formula1([C|Cs], C0, p(C0,F)) :-
	create_formula1(Cs, C, F).

actions_to_formula([], Qs, Qs, Bs, Bs, Cs, Cs).
actions_to_formula([A|As], Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	action_to_formula(A, Qs0, Qs1, Bs0, Bs1, Cs0, Cs1),
	actions_to_formula(As, Qs1, Qs, Bs1, Bs, Cs1, Cs).

action_to_formula(pop(K,S), Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	pop(K, S, Qs0, Qs, Bs0, Bs, Cs0, Cs).
action_to_formula(push(K,Ss), Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	push(K, Ss, Qs0, Qs, Bs0, Bs, Cs0, Cs).
action_to_formula(repl(K,S,Ss), Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	repl(K, S, Ss, Qs0, Qs, Bs0, Bs, Cs0, Cs).
action_to_formula(scan(S), Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	scan(S, Qs0, Qs, Bs0, Bs, Cs0, Cs).
action_to_formula(state(Q1,Q2), Qs0, Qs, Bs0, Bs, Cs0, Cs) :-
	state(Q1, Q2, Qs0, Qs, Bs0, Bs, Cs0, Cs).

test(Q0,  A0, B0) :-
	state(q1, q1, Q0, Q1,  A0, A1, B0, B1),
	scan(b, Q1, Q2, A1, A2, B1, B2),
	pop(1, d, Q2, [], A2, [], B2, []).

pop(K,  S, forall(Y, forall(Z, impl(at(Head,[Z]),impl(at(Stack,[Y,S,Z]),at(Head,[Y])))))) :-
	head_atom(K,  Head),
	stack_atom(K, Stack).
push(K, Ss, forall(Y,impl(at(Head,[Y]),Push))) :-
	head_atom(K, Head),
	push(K, Ss, Y, Push).
repl(K, S, Ss, forall(Y, forall(Z, impl(at(Head,[Z]),impl(at(Stack,[Y,S,Z]),Push))))) :-
	head_atom(K, Head),
	stack_atom(K, Stack),
	push(K, Ss, Y, Push).
scan(S, forall(X, forall(Y, impl(at(head,[X]),impl(at(word,[X,S,Y]),at(head,[Y])))))).



state_change(X, Y,  impl(at(X,[]),at(Y,[]))).

stack_init(K, p(Stack,Head)) :-
	stack(K, 0, e, 0, Stack),
	head(K, 0, Head).


stack_atom(1, stack1).
stack_atom(2, stack2).
stack_atom(3, stack3).

head_atom(1, head1).
head_atom(2, head2).
head_atom(3, head3).

test :-
        /* this should fail ! */
	prove([forall(X,exists(Y,at(f,[X,Y])))], exists(V,forall(W,at(f,[W,V])))).
test0 :-
	prove([exists(X,forall(Y,at(f,[X,Y])))], forall(V,exists(W,at(f,[W,V])))).
