:- module(lexicon, [parse/2, lookup/4, lookup/5, macro_expand/2, parse_all/0]).

:- use_module(translations, [translate/3, translate_hybrid/6]).

% define operators to allow for easier specification of
% hybrid and displacement lexical entries.
%
% WARNING: in case of doubt, use parentheses to disambiguate!
% I have deliberately not changed the definitions of standard
% mathematical and logical operations of Prolog, notably |
% (alternative of ; for use in DCG), \ and *.
%
% This means for example that:
% c/d*b/c = ((c/d)*b)/c
% which corresponds to a left-to-right evaluation of the
% mathematical functions of division and multiplication.
% However, we do have the familiar a/b/c = (a/b)/c and
% c\b\a = (c\(b\a) and even a\b/c = (a\b)/c.

:- op(400, xfy, \).
:- op(400, xfy, \>).  % = \downarrow_>
:- op(400, yfx, />).  % = \uparrow_>
:- op(400, xfy, \<).  % = \downarrow_<
:- op(400, yfx, /<).  % = \uparrow_>
:- op(400, yfx, *<).  % = \odot_<
:- op(400, yfx, *>).  % = \odot_>
:- op(400, fx, ^).



parse_all :-
	findall(N, clause(test(N),_), List),
	parse_all(List, Solutions),
	print_solutions(List, Solutions).

print_solutions(L, NS) :-
	format(user_error, 'SentNo Solutions~n', []),
	print_solutions(L, 0, 0, NS).
print_solutions([], S, F, []) :-
	Total is S + F,
	format(user_error, '~nTotal sentences :~|~t~d~4+~nSucceeded       :~|~t~d~4+~nFailed          :~|~t~d~4+~n', [Total, S, F]).
print_solutions([N|Ns], S0, F0, [P|Ps]) :-
	format(user_error, '~|~t~d~6+ ~|~t~d~9+', [N,P]),
    (
	P =:= 0
    ->
        format(user_error, ' *~n', []),
	F is F0 + 1,
	S = S0
    ;
        nl(user_error), 
        S is S0 + 1,
        F = F0
    ),
	print_solutions(Ns, S, F, Ps).

parse_all([], []).
parse_all([N|Ns], [P|Ps]) :-
        test(N),
        user:'$PROOFS'(P),
	parse_all(Ns, Ps).

parse(ListOfWords, Goal0) :-
	initialisation,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(0)),
	lookup(ListOfWords, Formulas, LexSem, Goal0, Goal),
	/* update lookup statistics */
	'$LOOKUP'(N0),
	N is N0 + 1,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(N)),
        format(user_error, '~N= Lookup ~w~n', [N]),	
	multi_prove(Formulas, Goal, LexSem),
	fail.
parse(_, _) :-
        format(user_error, '~N= Done!~2n================~n=  statistics  =~n================~n', []),	
	'$LOOKUP'(L),
	write_lookups(L),
        final_statistics,
	/* succeed only if at least one proof was found */
        user:'$PROOFS'(N),
        N > 0.

write_lookups(P) :-
   (
       P =:= 0
   ->
       format(user_output, 'No lexical lookups!~n', [])
   ;
       P =:= 1
   ->
       format(user_output, '1 lexical lookup.~n', [])
   ;
       format(user_output, '~p lexical lookups.~n', [P])
   ).


lookup(Words, Formulas, Goal, ExpandedGoal) :-
	lookup(Words, Formulas, _, Goal, ExpandedGoal).

lookup(Words, Formulas, Semantics, Goal0, ExpandedGoal) :-
	lexical_lookup(Words, Formulas, Semantics, 0, N),
	macro_expand(Goal0, Goal),
	translate(Goal, [0, N], ExpandedGoal).

lexical_lookup([], [], [], N, N).
lexical_lookup([W|Ws], [F|Fs], [N0-S|Ss], N0, N) :-
    (
	current_predicate(lex/3),	
	lex(W, _, _)
    ->	     
        /* Lambek/Displacement entry */
	lex(W, F0, S),
	N1 is N0 + 1,
	macro_expand(F0, F1),
	translate(F1, [N0,N1], F),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
	current_predicate(lex/4),	
        lex(W, _, _, _)
    ->
        /* hybrid entry */
        lex(W, F0, L, S),
	N1 is N0 + 1,
	macro_expand(F0, F1),
	translate_hybrid(F1, L, W, N0, N1, F),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
        /* first-order linear logic entry */
	current_predicate(lex/5),	
        lex(W, _, _, _, _)
    ->
        N1 is N0 + 1,
	lex(W, F, N0, N1, S),
	lexical_lookup(Ws, Fs, Ss, N1, N)
    ;
        format(user_error, '~N{Error: No lexical entry for "~w"}~n', [W]),
        fail
    ).

macro_expand(d_q, F) :-
	!,
	macro_expand(((s/<n)\<s)/cn, F).
macro_expand(d_tv, F) :-
	!,
	macro_expand((n\s)/n, F).
macro_expand(d_vp, F) :-
	!,
	macro_expand(n\s, F).
macro_expand(h_det, F) :-
	!,
	macro_expand(((s|(s|np))|n), F).
macro_expand(tv, dr(dl(at(np),at(s)),at(np))) :-
	!.
macro_expand(vp, dl(at(np),at(s))) :-
	!.
macro_expand(A0, A) :-
	atom(A0),
	!,
	A = at(A0).
macro_expand(at(A), at(A)).
macro_expand(at(A,B), at(A,B)).


macro_expand(forall(X,A0), forall(X,A)) :-
	macro_expand(A0, A).
macro_expand(exists(X,A0), exists(X,A)) :-
	macro_expand(A0, A).
macro_expand(impl(A0,B0), impl(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand(p(K,A0,B0), p(K,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dl(K,A0,B0), dl(K,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dr(K,A0,B0), dr(K,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0*B0), p(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(p(A0,B0), p(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0\B0), dl(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dl(A0,B0), dl(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0/B0), dr(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dr(A0,B0), dr(A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).


macro_expand((A0\<B0), dl(<,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0\>B0), dl(>,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0/<B0), dr(<,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0/>B0), dr(>,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0*<B0), p(<,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0*>B0), p(>,A,B)) :-
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(^A0, bridge(A)) :-
	macro_expand(A0, A).
macro_expand(bridge(A0), bridge(A)) :-
	macro_expand(A0, A).
macro_expand(lproj(A0), lproj(A)) :-
	macro_expand(A0, A).
macro_expand(rproj(A0), rproj(A)) :-
	macro_expand(A0, A).

macro_expand((B0->A0), h(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0|B0), h(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

in_lexicon(W) :-
	lex(W, _, _).
in_lexicon(W) :-
	lex(W, _, _, _).
