:- module(lexicon, [lookup/4, lookup/5, macro_expand/2, lexical_lookup/5, lex_to_displacement/2, lex_to_hybrid/3]).

:- use_module(translations, [translate/3, translate_hybrid/6,linear_to_hybrid/3,linear_to_displacement/3]).
:- use_module(auxiliaries, [universal_closure/2,universal_disclosure/2]).

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

:- dynamic hybrid_lookup/3, memo_lookup/2.

lookup(Words, Formulas, Goal, ExpandedGoal) :-
	lookup(Words, Formulas, _, Goal, ExpandedGoal).

lookup(Words, Formulas, Semantics, Goal0, ExpandedGoal) :-
	retractall(hybrid_lookup(_, _, _)),
	sentence_lookup(Words, Formulas, Semantics, 0, N),
	macro_expand(Goal0, Goal),
	translate(Goal, [0, N], ExpandedGoal).

sentence_lookup([], [], [], N, N).
sentence_lookup([W|Ws], [F|Fs], [N0-S|Ss], N0, N) :-
        N1 is N0 + 1,
	lexical_lookup(W, F, S, N0, N1),
	sentence_lookup(Ws, Fs, Ss, N1, N).

lexical_lookup(Word, Formula, Semantics, N0, N1) :-
    (
	current_predicate(lex/3),	
	lex(Word, _, _)
    ->	     
        /* Lambek/Displacement entry */
	lex(Word, Formula0, Semantics0),
	copy_term(Semantics0, Semantics),    
	macro_expand(Formula0, Formula1),
        translate(Formula1, [N0,N1], Formula),
        retractall(memo_lookup(N0, _)),
        assert(memo_lookup(N0, Word))
    ;
	current_predicate(lex/4),	
        lex(Word, _, _, _)
    ->
        /* hybrid entry */
        lex(Word, Formula0, ProsTerm0, Semantics0),
	/* prevent potential errors caused by accidental sharing of variables between ProsTerm and Semantics0 */
	copy_term(ProsTerm0, ProsTerm),
	copy_term(Semantics0, Semantics),    
	macro_expand(Formula0, Formula1),
        translate_hybrid(Formula1, ProsTerm, Word, N0, N1, Formula),
	retractall(hybrid_lookup(N0, _, _)),
	assert(hybrid_lookup(N0, Formula1, ProsTerm))
    ;
        /* first-order linear logic entry */
	current_predicate(lex/5),	
        lex(Word, _, _, _, _)
    ->
	lex(Word, Formula, N0, N1, Semantics0),
	/* prevent potential errors caused by accidental sharing of variables between ProsTerm and Semantics0 */
	copy_term(Semantics0, Semantics)
    ;
        format(user_error, '~N{Error: No lexical entry for "~w"}~n', [Word]),
        fail
    ).

lex_to_displacement(Word, Formula) :-
	lexical_lookup(Word, MFormula, _, 1, 2),
	universal_closure(MFormula, CFormula),
	linear_to_displacement(CFormula, [1,2], Formula).
lex_to_hybrid(Word, Formula, Term) :-
	lexical_lookup(Word, MFormula, _, 1, 2),
	universal_disclosure(MFormula, FFormula),
%	MFormula = FFormula,
	linear_to_hybrid(FFormula, Formula, Term).

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
macro_expand(h_det_c, F) :-
	!,
	macro_expand(((s|(s|np(_)))|n), F).
macro_expand(tv, dr(dl(at(np),at(s)),at(np))) :-
	!.
macro_expand(vp, dl(at(np),at(s))) :-
	!.
macro_expand(tv_c, dr(dl(at(np, [nom]),at(s)),at(np, [acc]))) :-
	!.
macro_expand(vp_c, dl(at(np, [nom]),at(s))) :-
	!.
macro_expand(F, Formula) :-
	current_predicate(atomic_formula/3),
	atomic_formula(F, At, Vars),
	!,
   (
	is_list(Vars)
   ->	
        Formula = at(At, Vars)
   ;
        Formula = at(At, [Vars])
   ).
macro_expand(A0, A) :-
	atom(A0),
	!,
   (
	current_predicate(atomic_formula/3),
        atomic_formula(F, A0, _Vars)
   ->
        format(user_error, '~N{Warning: atomic formula used as "~w" but declared as "~w"}~n', [A0,F])
   ;
        true
   ),
	A = at(A0).
macro_expand(at(A), at(A)).
macro_expand(at(A,B), at(A,B)).


macro_expand(forall(X,A0), forall(X,A)) :-
	!,
	macro_expand(A0, A).
macro_expand(exists(X,A0), exists(X,A)) :-
	!,
	macro_expand(A0, A).
macro_expand(impl(A0,B0), impl(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand(p(K,A0,B0), p(K,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dl(K,A0,B0), dl(K,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dr(K,A0,B0), dr(K,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0*B0), p(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(p(A0,B0), p(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0\B0), dl(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dl(A0,B0), dl(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).

macro_expand((A0/B0), dr(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(dr(A0,B0), dr(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).


macro_expand((A0\<B0), dl(<,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0\>B0), dl(>,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0/<B0), dr(<,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0/>B0), dr(>,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0*<B0), p(<,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0*>B0), p(>,A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(^A0, bridge(A)) :-
	!,
	macro_expand(A0, A).
macro_expand(bridge(A0), bridge(A)) :-
	!,
	macro_expand(A0, A).
macro_expand(lproj(A0), lproj(A)) :-
	!,
	macro_expand(A0, A).
macro_expand(rproj(A0), rproj(A)) :-
	!,
	macro_expand(A0, A).

macro_expand((B0->A0), h(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand((A0|B0), h(A,B)) :-
	!,
	macro_expand(A0, A),
	macro_expand(B0, B).
macro_expand(Formula, Formula) :-
	!,
	functor(Formula, F, A),
	functor(Term, F, A),
	format('~N{Warning: unknown formula ~w with functor ~w/~d}~n', [Formula, F, A]),
    (
	atomic_formula(Atomic, F, _),
        functor(Atomic, F, A0)
    ->
	format('~N{Warning: did you mean ~w/~d?}~n', [F, A0])
    ;		  
        format('{Warning: you have to declare atomic formulas explicitly with: atomic_formula(~p).}~n', [Term])
    ).

in_lexicon(W) :-
	lex(W, _, _).
in_lexicon(W) :-
	lex(W, _, _, _).
