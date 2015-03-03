

lookup(Words, Formulas, Goal, ExpandedGoal) :-
	lexical_lookup(Words, Formulas, Semantics, 0, N),
	translate(Goal, [0, N]).

lexical_lookup([], [], [], N, N).
lexical_lookup([W|Ws], [F|Fs], [S|Ss], N0, N) :-
    (
	lex(W, _, _)
    ->	     
        /* Lambek/Displacement entry */
	lex(W, F0, S),
	N1 is N0 + 1,
	translate(F0, [N0,N1], F),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
        lex(W, _, _, _)
    ->
        /* hybrid entry */
        lex(W, F0, L, S),
	N1 is N0 + 1,
	translate_hybrid(F0, L, W, N0, N1, F),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
        /* first-order linear logic entry */
        lex(W, _, _, _, _)
    ->
        N1 is N0 + 1,
	lex(W, F, N0, N1, S),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
        format(user_error, '~N{Error: No lexical entry for "~w"}~n', [W])
    ).

macro_expand(dr(A0,B0), dr(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(A0, A) :-
	atom(A0),
	!,
	A = at(A0).
macro_expand(A0|B0, h(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

in_lexicon(W) :-
	lex(W, _, _).
in_lexicon(W) :-
	lex(W, _, _, _).
