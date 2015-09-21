
% This translation is a direct adaptation from the translation function from Appendix A of the following paper

% Makoto Kanazawa (2015) Syntactic Features for Regular Constraints and an Approximation of Directional
% Slashes in Abstract Categorial Grammars, in Yusuke Kubota and Robert Levine (eds) Proceedings of
% Empirical Advances in Categorial Grammars, pp. 34-70.

:- use_module(lexicon, [macro_expand/2]).

lambek_to_acg(F0, T0, F, T) :-
	macro_expand(F0, F1),
	acg(F1, F, T0, T1),
	numbervars(T1, 0, _),
	filter_term(T1, T).

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
lambek(dl(A0,B0), (A->B), N0, M, X, appl('O'('L',N0),Term)) :-
	N is N0 + 1,
	acg(A0, A, epsilon('L',N0), Term0),
	lambek(B0, B, N, M, appl(X, Term0), Term).
lambek(dr(B0,A0), (A->B), N0, M, X, appl('O'('R',N0),Term)) :-
	N is N0 + 1,
	acg(A0, A, epsilon('R',N0), Term0),
	lambek(B0, B, N, M, appl(X, Term0), Term).

filter_term(appl('O'(_, _), A0), A) :-
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

term_to_state('$VAR'(_), 0, 0).
term_to_state(A, 0, 0) :-
	atomic(A),
	!.
term_to_state(epsilon('R',N), 0, N).
term_to_state(epsilon('L',N), N, 0).
term_to_state(Term0+Term1, L, R) :-
	term_to_state(Term0, L0, R0),
	term_to_state(Term1, L1, R1),
	combine_left(L0, L1, L),
	combine_right(R0, R1, R).
