


peek1(K, L, W, M, p(at(Stack,[L,W,M]), at(Head,[L,W,M]))) :-
	stack_atom(K, Stack),
	head_atom(K, Head).
peek2(K, L, V, M, W, R, p(p(at(Stack,[L,V,M]),at(Stack,[M,W,R])), at(Head,[M,W,R]))) :-
	stack_atom(K, Stack),
	head_atom(K, Head).
push(K, [S|Ss], R, Formula) :-
	stack_atom(K, Stack),
	head_atom(K, Head),
	push(Ss, S, R, Stack, Head, Formula).

stack(K, X, S, Y,  at(Stack,[X,S,Y])) :-
	stack_atom(K, Stack).
head(K, X, S, Y,  at(Head,[X,S,Y])) :-
	head_atom(K, Head).
word(L, W, R, at(word, [L,  W, R])).

push([], S, R, Stack, Head, exists(X,p(at(Stack,[R,S,X]),at(Head,[R,S,X])))).
push([S|Ss], S0, R, Stack, Head, exists(X,p(at(Stack,[R,S0,X]),Form))) :-
	push(Ss, S, X, Stack, Head, Form).

% =
% formula for popping symbol T from stack K
pop(K,  T, forall(X, forall(Y, forall(Z, forall(S, impl(Peek2, Peek1)))))) :-
	peek1(K, X, S, Y, Peek1),
	peek2(K, X, S, Y, T, Z, Peek2).
push(K, Ss, forall(X,forall(T,forall(Y,impl(Peek,p(Stack,Push)))))) :-
	peek1(K, X, T, Y, Peek),
	stack(K, X, T, Y, Stack),
	push(K, Ss, Y, Push).
repl(K, S, Ss, forall(X, forall(Y, forall(Z, forall(T, impl(Peek,p(Stack,Push))))))) :-
	peek2(K, X, S, Y, T, Z, Peek),
	stack(K, X, T, Y, Stack),
	push(K, Ss, Y, Push).

state_change(X, Y,  impl(at(X,[]),at(Y,[]))).

stack_init(K, p(Stack,Head)) :-
	stack(K, 0, e, 0, Stack),
	head(K, 0, e, 0, Head).


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
