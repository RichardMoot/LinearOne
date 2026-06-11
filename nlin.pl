


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
pop(K,  S, forall(Y, forall(Z, impl(at(Head,[Z]),impl(at(Stack,[Y,S,Z]),at(Head,[Y])))))) :-
	head_atom(K,  Head),
	stack_atom(K, Stack).
push(K, Ss, forall(Y,impl(at(Head,[Y]),Push) :-
	head_atom(K, Head),
	stack_atom(K, Stack),
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
