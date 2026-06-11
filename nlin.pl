

stack(K, X, S, Y,  at(Stack,[X,S,Y])) :-
	stack_atom(K, Stack).
head(K, Y,  at(Head,[Y])) :-
	head_atom(K, Head).
word(L, W, R, at(word, [L,  W, R])).


push(K, [S|Ss], R, Formula) :-
	stack_atom(K, Stack),
	head_atom(K, Head),
	push(Ss, S, R, Stack, Head, Formula).

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


goal_formula(N, Q0, QF, F) :-
	create_formula([], [at(state, [Q0]), at(head,[0]),at(word, [N,e,N]),
			    at(head1, [0]), at(stack1, [0,e,0]),
			    at(head2, [0]), at(stack2, [0,e,0]),
			    at(head3, [0]), at(stack3, [0,e,0])],
			   [at(state, [QF]), at(head,[N]),at(word, [N,e,N]),
			    at(head1, [0]), at(stack1, [0,e,0]),
			    at(head2, [0]), at(stack2, [0,e,0]),
			    at(head3, [0]), at(stack3, [0,e,0])],  F).  

word_formula(N0, Word, N, Actions, p(at(word, [N0, Word,  N]), F)) :-
	actions_to_formula(Actions, F).


test_ab :-
	parse([a-[[scan(a),push(1,[a])]],
	       b-[[scan(b),pop(1,a)]]], q0, q0).

test_mix :-
	parse([a-[[scan(a),push(1,[a])]],
	       b-[[scan(b),push(2,[b])]],
	       c-[[scan(c),push(3,[c])],
	          [pop(1,a),pop(2,b),pop(3,c)]]
	      ],  q0, q0).
test_mix1 :-
	parse([a-[[scan(a),push(1,[a])],[pop(1,a)]]
	      ],  q0, q0).
test_mix2 :-
	parse([a-[scan(a),push(1,[a])],
	       b-[scan(b),push(2,[b]),
	          pop(1,a),pop(2,b)]
	      ],  q0, q0).

parse(WordsActions, Q0, QF) :-
	words_actions_antecedent(WordsActions, 0, N, Antecedent),
	goal_formula(N, Q0, QF, Goal),
	prove(Antecedent, Goal).

words_actions_antecedent([],  N, N, []).
words_actions_antecedent([W-As|Ws], N0, N, [F|Fs]) :-
	N1 is N0 + 1,
	word_formula(N0, W, N1, As, F),
	words_actions_antecedent(Ws, N1, N, Fs).

actions_to_formula([A|As], F) :-
	actions_to_formula(As, A, F).

actions_to_formula([], Actions, F) :-
	actions_to_formula(Actions, Qs, [], Bs, [], Cs, []),
	create_formula(Qs, Bs, Cs, F).
actions_to_formula([A|As], Actions, p(F,Formula)) :-
	actions_to_formula(Actions, Qs, [], Bs, [], Cs, []),
	create_formula(Qs, Bs, Cs, F),
	actions_to_formula(As, A, Formula).
	

%actions_to_formula([Actions|ActionList], [F|Fs]) :-
%	actions_to_formula(Actions, Qs, [], Bs, [], Cs, []),%
%	create_formula(Qs, Bs, Cs, F).

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



pop(K,  S, forall(Y, forall(Z, impl(at(Head,[Z]),impl(at(Stack,[Y,S,Z]),at(Head,[Y])))))) :-
	head_atom(K,  Head),
	stack_atom(K, Stack).
push(K, Ss, forall(Y,impl(at(Head,[Y]),Push))) :-
	% hack to allow atoms to be treated as singleton lists
	( is_list(Ss) -> Stack = Ss ; Stack = [Ss] ),
	head_atom(K, Head),
	push(K, Stack, Y, Push).
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
