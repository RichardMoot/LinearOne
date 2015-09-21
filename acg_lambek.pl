
% This translation is a direct adaptation from the translation function from Appendix A of the following paper

% Makoto Kanazawa (2015) Syntactic Features for Regular Constraints and an Approximation of Directional
% Slashes in Abstract Categorial Grammars, in Yusuke Kubota and Robert Levine (eds) Proceedings of
% Empirical Advances in Categorial Grammars, pp. 34-70.

:- use_module(lexicon, [macro_expand/2]).
:- use_module(ordset, [ord_key_insert/4,ord_key_member/3]).

l2a(F0, W) :-
	lambek_to_acg(F0, F, W, Term),
	portray_clause(lex(W, F, Term, W)),
	fail.
l2a(_, _).

lambek_to_acg_count(F, Number) :-
	findall(.,lambek_to_acg(F,_,w,_), L),
	length(L, Number).

lambek_to_acg(F0, F, T0, T) :-
	macro_expand(F0, F1),
	acg(F1, F2, T0, T1),
	numbervars(T1, 0, _),
	term_to_formula(F2, T1, F),
	filter_term(T1, T).

lambek_to_e_acg(F0, F, T0, T) :-
	macro_expand(F0, F1),
	acg(F1, F, T0, T),
	numbervars(T, 0, _).


acg(at(A), at(A), X, X) :-
	!.
acg(dl(A0,B0), (A->B), X, lambda(Y, Term)) :-
	!,
	lambek(A0, A, 1, 1, Y, Term0),
	acg(B0, B, Term0+X, Term).
acg(dr(B0,A0), (A->B), X, lambda(Z, Term)) :-
	!,
	lambek(A0, A, 1, 1, Z, Term0),
	acg(B0, B, X+Term0, Term).

lambek(at(A), at(A), _, _, X, X).
lambek(dl(A0,B0), (A->B), N0, M, X, appl('O_L'(N0),Term)) :-
	N is N0 + 1,
	acg(A0, A, epsilon('L',N0), Term0),
	lambek(B0, B, N, M, appl(X, Term0), Term).
lambek(dr(B0,A0), (A->B), N, M0, X, appl('O_R'(M0),Term)) :-
	M is M0 + 1,
	acg(A0, A, epsilon('R',M0), Term0),
	lambek(B0, B, N, M, appl(X, Term0), Term).

filter_term(appl('O_L'(_), A0), A) :-
	!,
	filter_term(A0, A).
filter_term(appl('O_R'(_), A0), A) :-
	!,
	filter_term(A0, A).
filter_term(epsilon(_,_), epsilon) :-
	!.
filter_term('$VAR'(N), '$VAR'(N)) :-
	!.
filter_term(appl(A0,B0), appl(A,B)) :-
	!,
	filter_term(A0, A),
	filter_term(B0, B).
filter_term(lambda(A,B0), lambda(A, B)) :-
	!,
	filter_term(B0, B).
filter_term(A0+B0, A+B) :-
	!,
	filter_term(A0, A),
	filter_term(B0, B).
filter_term(A, A) :-
	atomic(A).

type_skeleton(at(_), _).
type_skeleton((A0->B0), (A->B)) :-
	!,
	type_skeleton(A0, A),
	type_skeleton(B0, B).

term_to_formula(F0, Term, F) :-
	type_skeleton(F0, Type),
	term_to_states(Term, Type, []),
	merge_formula(F0, Type, F).


merge_formula(at(N), p(X,Y), At) :-
	At =.. [N,X,Y].
merge_formula((A1->B1), (A2->B2), (A->B)) :-
	merge_formula(A1, A2, A),
	merge_formula(B1, B2, B).


term_to_states(lambda('$VAR'(N),B), (T->U), Set0) :-
	!,
	ord_key_insert(Set0, N, T, Set),
	term_to_states(B, U, Set).
term_to_states(appl('O_L'(N0),B), p(N, R), Set) :-
	!,
	term_to_states(B, p(N1, R), Set),
	prev_state_left(N0, N1, N).
term_to_states(appl('O_R'(N0),B), p(L, N), Set) :-
	!,
	term_to_states(B, p(L, N1), Set),
	prev_state_right(N0, N1, N).
term_to_states(appl(A,B), U, Set) :-
	!,
	term_to_states(A, (T->U), Set),
	term_to_states(B, T, Set).
term_to_states('$VAR'(N), T, Set) :-
	!,
	ord_key_member(N, Set, T).
term_to_states(epsilon('R',N), p(0, N), _) :-
	!.
term_to_states(epsilon('L',N), p(N, 0), _) :-
	!.
term_to_states(Term0+Term1, p(L, R), Set) :-
	!,
	term_to_states(Term0, p(L0, R0), Set),
	term_to_states(Term1, p(L1, R1), Set),
	combine_left(L0, L1, L),
	combine_right(R0, R1, R).
term_to_states(A, p(0, 0), _) :-
	atomic(A),
	!.


prev_state_left(1, 1, 0).
% second left argument
prev_state_left(2, 21, 1).

combine_left(0, 0, 0).
combine_left(1, 0, 1).
% second left argument
combine_left(21, 0, 21).
combine_left(2, 1, 21).

prev_state_right(1, 1, 0).
% second right argument
prev_state_right(2, 12, 1).

combine_right(0, 0, 0).
combine_right(0, 1, 1).
% second right argument
combine_right(0, 12, 12).
combine_right(1, 2, 12).

% = ord_key_union(+Map1, +Map2, ?Map3)
%
% as ord_union/3, but for ordered sets of Key-Value pairs. If Map1 and Map2 contain the
% same Key, Map3 will unfiy the two values.                RM

ord_key_union([], Set2, Set2).
ord_key_union([H1-V1|T1], Set2, Union) :-
	ord_key_union_2(Set2, H1, V1, T1, Union).

ord_key_union_2([], H1, V1, T1, [H1-V1|T1]).
ord_key_union_2([H2-V2|T2], H1, V1, T1, Union) :-
	compare(Order, H1, H2),
	ord_key_union_3(Order, H1, V1, T1, H2, V2, T2, Union).

ord_key_union_3(<, H1, V1, T1, H2, V2, T2, [H1-V1|Union]) :-
	ord_key_union_2(T1, H2, V2, T2, Union).
ord_key_union_3(=, H1, V, T1, _, V, T2, [H1-V|Union]) :-
	ord_key_union(T1, T2, Union).
ord_key_union_3(>, H1, V1, T1, H2, V2, T2, [H2-V2|Union]) :-
	ord_key_union_2(T2, H1, V1, T1, Union).


test(and_rnr, F, S) :-
	lambek_to_acg(dr(dl(dl(dr(dr(s,np),np),s),dl(dr(dr(s,np),np),s)),dl(dr(dr(s,np),np),s)), F, and, S).

test(very, F, S) :-
	lambek_to_acg(dr(dl(dl(np,s),dl(np,s)),dl(dl(np,s),dl(np,s))), F, very, S).

count(tv, Count) :-
	lambek_to_acg_count(tv, Count).
count(and_rnr, Count) :-
	lambek_to_acg_count(dr(dl(dl(dr(dr(s,np),np),s),dl(dr(dr(s,np),np),s)),dl(dr(dr(s,np),np),s)), Count).
count(very, Count) :-
	lambek_to_acg_count(dr(dl(dl(np,s),dl(np,s)),dl(dl(np,s),dl(np,s))), Count).



formula(and_rnr, dr(dl(dl(dr(dr(s,np),np),s),dl(dr(dr(s,np),np),s)),dl(dr(dr(s,np),np),s))).
formula(very, dr(dl(dl(np,s),dl(np,s)),dl(dl(np,s),dl(np,s)))).