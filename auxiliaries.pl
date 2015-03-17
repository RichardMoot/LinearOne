:- module(auxiliaries, [select_formula/4, count_check/4, subproofs/2, rulename/2, is_axiom/1, merge_fvs/3, free_vars_n/2, free_vars_p/2, free_vars/2, antecedent/2]).

:- use_module(ordset, [ord_union/3, ord_delete/3]).

% = select_formula(+Formula, +Index, +List, -Rest)
%
% selects Index-Formula pair from list, using forced-choice
% determinism

select_formula(F, N, L0, L) :-
        select(N-F, L0, L),
        !.


count_check(LN, LP, AtName, Rest) :-
	Count is LP - LN,
   (
	Count =:= 0
   ->				  
        true
   ;		   
        format(user_error, '~NCount check failure: count(~w)= ~w', [AtName, Count]),
        print_count_offenders(Rest),
        fail
   ).

print_count_offenders([]) :-
	nl(user_error).
print_count_offenders([AtName-atoms(Pos, Neg)|Rest]) :-
	length(Pos, LP),
	length(Neg, LN),
	Count is LP - LN,
   (
	Count =:= 0
   ->				  
        true
   ;		   
        format(user_error, ', count(~w)= ~w', [AtName, Count])
   ),
 	print_count_offenders(Rest).

% = print_diff_lists(+List1, +List2)
%
% supposing List1 and List2 have the same length, we print the members of the two lists
% side-by-side, marking by * the elements which differ between the two lists

print_diff_lists([], []).
print_diff_lists([A|As], [B|Bs]) :-
	copy_term(A, AA),
	copy_term(B, BB),
	numbervars(AA, 0, _),
	numbervars(BB, 0, _),
	( A == B -> C = ' '	; C = '*' ),
	format(user_error, '~w~t~w~50|~t~w~100|~w~n', [C,AA,BB,C]),
	print_diff_lists(As, Bs).

% = sub_proofs(+Proof, ?SubProofList)
%
% true if SubProofList is the list of premisses of the current rule

subproofs(_-R, S) :-
        subproofs(R, S).
subproofs(rule(_,_,_,S), S).

% = rule(+Proof, ?RuleName)
%
% true if RuleName is the name of the current rule

rulename(_-R, N) :-
        rulename(R, N).
rulename(rule(N,_,_,_), N).

% = antecedent(+Proof, ?Antecedent)
%
% true if Antecedent is the antecedent of the conclusion of the
% given Proof.

antecedent(_-R, Ant) :-
	antecedent(R, Ant).
antecedent(rule(_,Ant,_,_), Ant).

% = is_axiom(+Proof)
%
% true if Proof is an axiom rule

is_axiom(_-R) :-
        is_axiom(R).
is_axiom(rule(ax,_,_,_)).


% merge two sets of free variables
% remove variables already instantiated (these have an integer value)
% we need to sort again (since variable instantiations/unifications may
% have changed term order)

merge_fvs(Vs0, Ws0, Zs) :-
    reduce_fvs(Vs0, Vs1),
    sort(Vs1, Vs),
    reduce_fvs(Ws0, Ws1),
    sort(Ws1, Ws),
    ord_union(Vs, Ws, Zs).

reduce_fvs([], []).
reduce_fvs([V|Vs], Ws) :-
    (
        integer(V)
    ->
        reduce_fvs(Vs, Ws)
    ;
        Ws = [V|Ws0],
        reduce_fvs(Vs, Ws0)
    ).



% = free_vars_n(+Formula, -SetOfFreeVars)
%
% true if Formula (of negative polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free. For example, a prefix of
% universal quantifiers is removed (and, in
% general, any negative forall/impl and
% postive exists/prod); this is the implicit
% tensor contraction rule).

free_vars_n(_-A, Vars) :-
        free_vars_n(A, Vars).
free_vars_n(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_n(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_n(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(impl(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_n(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(forall(_,A), Vars) :-
        free_vars_n(A, Vars).
free_vars_n(exists(X,A), Vars) :-
       free_vars(A, Vars0),
       ord_delete(Vars0, X, Vars).

% = free_vars_p(+Formula, -SetOfFreeVars)
%
% true if Formula (of positive polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free (this is the implicit tensor
% contraction rule).

free_vars_p(_-A, Vars) :-
        free_vars_p(A, Vars).
free_vars_p(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_p(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_p(p(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_p(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(exists(_,A), Vars) :-
        free_vars_p(A, Vars).
free_vars_p(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = free_vars(+Formula, -SetOfFreeVars)
%
% true if Formula has SetOfFreeVars under the
% standard interpretation of free/bound.

free_vars(_-A, Vars) :-
        free_vars(A, Vars).
free_vars(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(exists(X,A), Vars) :-
        free_vars(A, Vars0),
	ord_delete(Vars0, X, Vars).
free_vars(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = non_member(+Element, +List)
%
% true if Element is not a member of List (that is if it is not strictly
% equal to one of the members of List; member_chk(Element, List) must fail).

non_member(_, []).
non_member(X, [Y|Ys]) :-
	X \== Y,
	non_member(X, Ys).
