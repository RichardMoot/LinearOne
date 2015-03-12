% -*- Mode: Prolog -*-

:- module(sem_utils,  [reduce_sem/2,
		       substitute_sem/3,
		       replace_sem/4,
		       get_variable_types/3,
		       check_lexicon_typing/0,
		       free_var_indices/2,
		       freeze/2,
		       melt/2,
		       replace_sem/4,
		       melt_bound_variables/2]).

% =

:- use_module(ordset,     [ord_intersect/3,
			   ord_insert/3,
			   ord_delete/3,
			   ord_subset/2,
			   ord_subtract/3]).
:- use_module(tree234, [btree_get/3,
	                btree_insert/4,
			btree_put/4]).
:- use_module(lexicon, [macro_expand/2]).


reduce_quine(active).

reduce_eta(active).

% reduce_sem(+LambdaTerm, -BetaEtaReducedLambdaTerm)
%
% true if BetaEtaReducedLambdaTerm is the beta-eta normal form of
% Lambda Term. Works using a simply repeat loop reducing one redex
% at each step.

reduce_sem(Term0, Term) :-
	get_max_variable_number(Term0, Max),
	reduce_sem(Term0, Term1, Max, _),
	relabel_sem_vars(Term1, Term).

reduce_sem(Term0, Term, Max0, Max) :-
	reduce_sem1(Term0, Term1, Max0, Max1),
	!,
	reduce_sem(Term1, Term, Max1, Max).

reduce_sem(Term, Term, Max, Max).


% reduce_sem1(+Redex, -Contractum).
%
% true if Redex reduces to Contractum in a single beta or eta
% reduction.

reduce_sem1(appl(lambda(X0,T0),Y), T, Max0, Max) :-
	alpha_conversion(lambda(X0,T0),lambda(X,T1), Max0, Max),
	replace_sem(T1, X, Y, T).
reduce_sem1(lambda(X,appl(F,X)), F, Max, Max) :-
	reduce_eta(active),
	\+ subterm(F, X).
reduce_sem1(pi1(pair(T,_)), T, Max, Max).
reduce_sem1(pi2(pair(_,T)), T, Max, Max).
reduce_sem1(pair(pi1(T),pi2(T)), T, Max, Max) :-
	reduce_eta(active).

% = Quine's reductions

reduce_sem1(bool(true,&,X), X, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(X,&,true), X, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(false,&,_), false, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(_,&,false), false, Max, Max) :-
	reduce_quine(active).

reduce_sem1(bool(true,\/,_), true, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(_,\/,true), true, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(false,\/,X), X, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(X,\/,false), X, Max, Max) :-
	reduce_quine(active).

reduce_sem1(bool(true,->,X), X, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(_,->,true), true, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(false,->,_), true, Max, Max) :-
	reduce_quine(active).
reduce_sem1(bool(X,->,false), not(X), Max, Max) :-
	reduce_quine(active).

% = recursive case

reduce_sem1(T, U, Max0, Max) :-
	T =.. [F|Ts],
	reduce_list(Ts, Us, Max0, Max),
	U =.. [F|Us].

reduce_list([T|Ts], [U|Ts], Max0, Max) :-
	reduce_sem1(T, U, Max0, Max).
reduce_list([T|Ts], [T|Us], Max0, Max) :-
	reduce_list(Ts, Us, Max0, Max).

% subterm(Term, SubTerm)
%
% true if Term contains SubTerm as a subterm.

subterm(X, X) :- 
	!.
subterm(X, Y) :-
	functor(X, _, N),
	subterm(N, X, Y).

subterm(N0, X, Y) :-
	N0 > 0,
	arg(N0, X, A),
	subterm(A, Y).

subterm(N0, X, Y) :-
	N0 > 0,
	N is N0-1,
	subterm(N, X, Y).

% = alpha_conversion(+InTerm, -OutTerm)

alpha_conversion(Term0, Term, Max0, Max) :-
	melt_bound_variables(Term0, Term),
	Max1 is Max0 + 1,
	numbervars(Term, Max1, Max).

% = replace_sem(InTerm, Term1, Term2, OutTerm, Max)
%
% true if OutTerm is InTerm with all occurrences of Term1 replaced
% by occurrences of Term2.

replace_sem(X0, X, Y0, Y) :-
	X0 == X,
	!,
	Y = Y0.
replace_sem(X, _, _, X) :-
	var(X),
	!.
replace_sem(U, X, Y, V) :-
	functor(U, F, N),
	functor(V, F, N),
	replace_sem(N, U, X, Y, V).

replace_sem(0, _, _, _, _) :- 
	!.
replace_sem(N0, U, X, Y, V) :-
	N0 > 0,
	N is N0-1,
	arg(N0, U, A),
	replace_sem(A, X, Y, B),
	arg(N0, V, B),
	replace_sem(N, U, X, Y, V).

% = substitute_sem(+ListOfSubstitutions, +InTerm, -OutTerm).

substitute_sem(L, T0, T) :-
	max_key_list(L, 0, Max0),
	get_max_variable_number(T0, Max1),
	Max2 is max(Max0+1,Max1+1),
	numbervars(T0, Max2, Max),
	substitute_sem(L, T0, T, Max, _).

substitute_sem([], T, T, N, N).
substitute_sem([X-U|Rest], T0, T, N0, N) :-
	numbervars(U, N0, N1),
	replace_sem(T0, '$VAR'(X), U, T1),
	substitute_sem(Rest, T1, T, N1, N).

max_key_list([], M, M).
max_key_list([K-_|Ss], M0, M) :-
    (
       K > M0
    ->
       max_key_list(Ss, K, M)
    ;
       max_key_list(Ss, M0, M)
    ).

% = free_var_indices(+Term, -ListOfVariableIndices)
%
% given a Term representing a lambda term return all
% indices of variables occurring freely in this lambda term.

free_var_indices('$VAR'(N), [N]) :-
	!.
free_var_indices(A, []) :-
	atomic(A),
	!.
free_var_indices(lambda('$VAR'(X),Y), F) :-
	!,
	free_var_indices(Y, F0),
	ord_delete(F0, X, F).
free_var_indices(quant(_,'$VAR'(X),Y), F) :-
	!,
	free_var_indices(Y, F0),
	ord_delete(F0, X, F).
free_var_indices(T, F) :-
	T =.. [Fun|Args],
	free_var_indices_list([Fun|Args], [], F).

free_var_indices_list([], F, F).
free_var_indices_list([A|As], F0, F) :-
	free_var_indices(A, V),
	ord_union(F0, V, F1),
	free_var_indices_list(As, F1, F).

bound_variables(Var, []) :-
	var(Var),
	!.
bound_variables(lambda(X, Y), BVs) :-
	 !,
    (
	var(X)
    ->
        /* already molten */
        bound_variables(Y, BVs)
    ;
	X = '$VAR'(N),
	bound_variables(Y, BVs0),
	ord_insert(BVs0, N, BVs)
    ).
bound_variables('$VAR'(_), []) :-
	!.
bound_variables(X, []) :-
	atomic(X),
	!.
bound_variables(Term, BVs) :-
	Term =.. List,
	bound_variables_list(List, BVs).

bound_variables_list([], []).
bound_variables_list([V|Vs], Bs) :-
	bound_variables(V, Bs0),
	bound_variables_list(Vs, Bs1),
	ord_union(Bs0, Bs1, Bs).

% = relabel_sem_vars(T0, T)
%
% rename the variables in term T0 in such a way that all variables are in
% the range '$VAR'(0) to '$VAR'(N) for the smallest N possible.

relabel_sem_vars(T0, T) :-
	relabel_sem_vars(T0, T, 0, _, empty, _).

% relabel_sem(T0, T, M0, M)

relabel_sem_vars('$VAR'(I), '$VAR'(J), N0, N, M0, M) :-
	!,
    (
        btree_get(M0, I, J)
    ->
        M = M0,
        N = N0
    ;
        J = N0,
        N is N0 +1,
        btree_insert(M0, I, J, M)
    ).
relabel_sem_vars(Term0, Term, N0, N, M0, M) :-
	functor(Term0, F, A),
	functor(Term, F, A),
	relabel_sem_vars_args(1, A, Term0, Term, N0, N, M0, M).

relabel_sem_vars_args(A0, A, Term0, Term, N0, N, M0, M) :-
    (
	A0 > A
    ->
        N = N0,
        M = M0
    ;
        arg(A0, Term0, Arg0),
        arg(A0, Term, Arg),
        relabel_sem_vars(Arg0, Arg, N0, N1, M0, M1),
        A1 is A0 + 1,
        relabel_sem_vars_args(A1, A, Term0, Term, N1, N, M1, M)
    ).

create_tree([], Tree, Tree).
create_tree([I|Vs], Tree0, Tree) :-
	btree_put(Tree0, I, _, Tree1),
	create_tree(Vs, Tree1, Tree).

% = melt_bound_variables(+Term0, -Term)
%
% true if Term is identical to Term0 but with all occurrences of
% bound variables (because of numbervars, all variables are of the form
% '$VAR'(N)') replaced by Prolog variables.

melt_bound_variables(Term0, Term) :-
	bound_variables(Term0, List),
	create_tree(List, empty, Tree),
	melt_bound_variables(Term0, Term, Tree).

melt_bound_variables(X, X, _Tree) :-
	var(X),
	!.
melt_bound_variables('$VAR'(I), Var, Tree) :-
	!,
    (
         btree_get(Tree, I, Var)
    ->
         true
    ;
         Var = '$VAR'(I)
    ).
melt_bound_variables(Term0, Term, Tree) :-
	functor(Term0, F, A),
	functor(Term, F, A),
	melt_bound_variables_args(1, A, Term0, Term, Tree).

melt_bound_variables_args(A0, A, Term0, Term, Tree) :-
    (
	A0 > A
    ->
        true
    ;
        arg(A0, Term0, Arg0),
        arg(A0, Term, Arg),
        melt_bound_variables(Arg0, Arg, Tree),
        A1 is A0 + 1,
        melt_bound_variables_args(A1, A, Term0, Term, Tree)
    ).

% = get_variable_numbers(+LambdaTerm, -SetOfIntegers)
%
% true if SetOfIntegers contains all variable number which
% are the result of a call to numbervars/3 (that is to say,
% the set of all N which occur as a subterm '$VAR'(N))

get_variable_numbers(Term, Set) :-
	get_variable_numbers(Term, List, []),
	sort(List, Set).

get_variable_numbers(Var, L, L) :-
	var(Var),
	!.
get_variable_numbers('$VAR'(N), [N|L], L) :-
	!.
get_variable_numbers(Term, L0, L) :-
	functor(Term, _, A),
	get_variable_numbers_args(1, A, Term, L0, L).

get_variable_numbers_args(A0, A, Term, L0, L) :-
    (
        A0 > A
    ->
        L = L0
    ;
        arg(A0, Term, Arg),
        get_variable_numbers(Arg, L0, L1),
        A1 is A0 +1,
        get_variable_numbers_args(A1, A, Term, L1, L)
    ).

% = get_max_variable_number(+LambdaTerm, ?MaxVar)
%
% true if MaxVar is the largest number N which
% occurs as a subterm '$VAR'(N)) of LambdaTerm
% That is to say, if LambdaTerm contains variables
% and MaxVar1 is MaxVar + 1, then the call
%
%   numbervars(LambdaTerm, MaxVar1, NewMaxVar)
%
% is guaranteed to be sound (in the sense that
% it does not accidentally unifies distinct
% variables.
%
% If LambdaTerm contains no occurrences of a
% subterm '$VAR'(N) then MaxVar is defined as
% -1.

get_max_variable_number(Term, Max) :-
	get_max_variable_number(Term, -1, Max).

get_max_variable_number(Var, Max, Max) :-
	var(Var),
	!.
get_max_variable_number('$VAR'(N), Max0, Max) :-
	!,
	Max is max(N,Max0).
get_max_variable_number(Term, Max0, Max) :-
	functor(Term, _, A),
	get_max_variable_number_args(1, A, Term, Max0, Max).

get_max_variable_number_args(A0, A, Term, Max0, Max) :-
    (
        A0 > A
    ->
        Max = Max0
    ;
        arg(A0, Term, Arg),
        get_max_variable_number(Arg, Max0, Max1),
        A1 is A0 +1,
        get_max_variable_number_args(A1, A, Term, Max1, Max)
    ).


get_variable_types(Sem, Formula, Tree) :-
    (
	/* skip typing checking if no atomic_type/2 declarations */
        /* are found in the grammar file */
	user:atomic_type(_, _)
    ->
        get_variable_types1(Sem, Formula, Tree)
    ;
        Tree = empty
    ).

% = skip variable typing in case the term is not well-typed

get_variable_types1(Sem, Formula, Tree) :-
	get_atomic_types(Tr),
	syntactic_to_semantic_type(Formula, goal, Type, Tr),
        check_type(Sem, Type, goal, empty, Tree),
	!.
get_variable_types1(_, _, empty).


% check_lexicon_typing.
%
% check if the lambda term semantics in the lexicon is well-typed.

check_lexicon_typing :-
    (
	/* skip typing checking if no atomic_type/2 declarations */
        /* are found in the grammar file */
	user:atomic_type(_, _)
    ->
	get_atomic_types(Tree),
	findall(lex(A,B,C), lexicon_triple(A,B,C), Lexicon),
	check_lexicon_typing(Lexicon, Tree)
    ;
	format('{Warning: no atomic_type/2 declarations found in grammar}~n{Warning: semantic type verification disabled}~n', []),
	format(log, '{Warning: no atomic_type/2 declarations found in grammar}~n{Warning: semantic type verification disabled}~n', [])
    ).

check_lexicon_typing([], _).
check_lexicon_typing([lex(Word,SynType,Term)|Ls], Tree) :-
	numbervars(Term, 0, _),
	format(log, 'lex( ~w ,~n     ~w ,~n     ~w )~n', [Word, SynType, Term]),
    (
	syntactic_to_semantic_type(SynType, Word, Type, Tree)
    ->
	format(log, 'Type: ~w~nTerm: ~w~n', [Type, Term]),
	check_lexicon_typing(Term, Type, Word)
    ;
	true
    ),
	check_lexicon_typing(Ls, Tree).

check_lexicon_typing(Term, Type, Word) :-
	check_type(Term, Type, Word, empty, _),
	!.
check_lexicon_typing(Term, Type, Word) :-
	format(log, '{Warning: typing check failed for:}~n{Word: ~w}~n{Term: ~w}~n{Type: ~w}~n', [Word,Term,Type]),
	format('{Warning: typing check failed for:}~n{Word: ~w}~n{Term: ~w}~n{Type: ~w}~n', [Word,Term,Type]).


lexicon_triple(A, B, C) :-
	user:lex(A, B0, C),
	macro_expand(B0, B).

lexicon_triple(A, B, C) :-
	user:default_semantics(A, B0, C),
	macro_expand(B0, B),
	instantiate(A, B).

lexicon_triple(A, B, C) :-
	user:default_semantics(A, _, B0, C),
	macro_expand(B0, B),
	instantiate(A, B).

instantiate('WORD'(B), B) :-
	!.
instantiate(_, _).

check_type(At, Type, Word, Tr0, Tr) :-
	atomic(At),
	!,
    (
	btree_get(Tr0, At, TA)
    ->
	Tr0 = Tr,
	verify_expected_type(At, Word, Type, TA)
    ;
	btree_insert(Tr0, At, Type, Tr)
    ).	
check_type('WORD'(_), _Type, _Word, Tr, Tr) :-
	!.
check_type('$VAR'(N), Type, Word, Tr0, Tr) :-
	!,
    (
	btree_get(Tr0, N, TN)
    ->
	Tr = Tr0,
	verify_expected_type('$VAR'(N), Word, Type, TN)
    ;
	btree_insert(Tr0, N, Type, Tr)
    ).
check_type(lambda('$VAR'(N),T), Type, Word, Tr0, Tr) :-
	!,
    (
	Type = (V->W)
    ->
	btree_insert(Tr0, N, V, Tr1),
	check_type(T, W, Word, Tr1, Tr)
    ;
	Tr = Tr0,
	format('{Typing Error (~w): expected type(~p)->type(~W) found ~W}~n', [Word,'$VAR'(N),T,[numbervars(true)],Type,[numbervars(true)]]),
	format(log, '{Typing Error (~w): expected type(~w)->type(~W) found ~W}~n', [Word,'$VAR'(N),T,[numbervars(true)],Type,[numbervars(true)]])
    ).
check_type(sub(X,_), Type, W, Tr0, Tr) :-
	!,
	check_type(X, Type, W, Tr0, Tr).
check_type(sup(X,_), Type, W, Tr0, Tr) :-
	!,
	check_type(X, Type, W, Tr0, Tr).
check_type(num(X), E, W, Tr0, Tr) :-
	!,
	e_type(E),
	check_type(X, E, W, Tr0, Tr).
check_type(complement(X), E, W, Tr0, Tr) :-
	!,
	e_type(E),
	check_type(X, E, W, Tr0, Tr).
check_type(time(X), E, W, Tr0, Tr) :-
	!,
	verify_e_type(time(X), W, E),
	s_type(S),
	check_type(X, S, W, Tr0, Tr).
check_type(count(X), E, W, Tr0, Tr) :-
	!,
	e_type(E),
	t_type(T),
	check_type(X, E->T, W, Tr0, Tr).
check_type(not(X), T, W, Tr0, Tr) :-
	!,
	check_type(X, T, W, Tr0, Tr).
check_type(appl(X,Y), W, Word, Tr0, Tr) :-
	!,
	check_type(X, (V->W), Word, Tr0, Tr1),
	check_type(Y, V, Word, Tr1, Tr).
check_type(quant(Q,X), T, Word, Tr0, Tr) :-
	e_type(E),
	t_type(U),
    (
        Q = iota
    ->
        verify_e_type(quant(Q,X), Word, T),
        V = (T -> U)
    ;
        V = (E -> U)
    ),
	!,
        check_type(X, V, Word, Tr0, Tr).
check_type(quant(Q,V,X), T, Word, Tr0, Tr) :-
	!,
	e_type(E),
	check_type(V, E, Word, Tr0, Tr1),  
    (
	Q = iota
    ->
	verify_e_type(quant(Q,V,X), Word, T)
    ;
        t_type(U),
        verify_expected_type(quant(Q,V,X), Word, T, U)
    ),
	check_type(X, t, Word, Tr1, Tr).
% allow polymorphic booleans
check_type(bool(X,B,Y), T, Word, Tr0, Tr) :-
	!,
	e_type(E),
	t_type(T),
	operator_type(B, E, T, U, V),
	check_type(X, U, Word, Tr0, Tr1),
	check_type(Y, V, Word, Tr1, Tr).
check_type(pair(X,Y), Type, Word, Tr0, Tr) :-
	!,
    (
	Type = U-V
    ->
	check_type(X, U, Word, Tr0, Tr1),
	check_type(Y, V, Word, Tr1, Tr)
    ;
	Tr = Tr0,
	format('{Typing Error (~w): expected type(~p)->type(~w) found ~w}~n', [Word,pair(X,Y),U-V,Type]),
	format(log, '{Typing Error (~w): expected type(~w)->type(~w) found ~w}~n', [Word,pair(X,Y),U-V,Type])
    ).
check_type(fst(X), Type, Word, Tr0, Tr) :-
	!,
	check_type(X, Type-_, Word, Tr0, Tr).
check_type(snd(X), Type, Word, Tr0, Tr) :-
	!,
	check_type(X, _-Type, Word, Tr0, Tr).
check_type(pi1(X), Type, Word, Tr0, Tr) :-
	!,
	check_type(X, Type-_, Word, Tr0, Tr).
check_type(pi2(X), Type, Word, Tr0, Tr) :-
	!,
	check_type(X, _-Type, Word, Tr0, Tr).

% unknown term
check_type(Term, Type, Word, Tr, Tr) :-
	format('{Typing Error (~w): unknown term ~k of type ~p}~n', [Word,Term,Type]),
	format(log, '{Typing Error (~w): unknown term ~k of type ~p}~n', [Word,Term,Type]).	

% = polymorphic
operator_type((=) , _, _, X, X).
operator_type((:=) , _, _, X, X).
operator_type(< , _, _, X, X).
operator_type(> , _, _, X, X).
operator_type(neq , _, _, X, X).
% = DRS
operator_type(overlaps , _, _, X, X).
operator_type(abuts , _, _, X, X).
% = entity and set
operator_type(in, E, T, E, Set) :-
	semantic_set_type(E, T, Set).
operator_type(not_in, E, T, E, Set) :-
	semantic_set_type(E, T, Set).
% = set and set
operator_type(intersect, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(intersection, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(setminus, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(union, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(subset, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(subseteq, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(nsubseteq, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
operator_type(subsetneq, E, T, Set, Set) :-
	semantic_set_type(E, T, Set).
% = default to boolean
operator_type(_, _, T, T, T).

verify_expected_type(Term, Word, ExpectedType, Type) :-
    (
	Type = ExpectedType
    ->
	true
    ;
	format('{Typing Error (~w): expected type(~p) = ~w, found ~w}~n', [Word,Term,ExpectedType,Type]),
	format(log, '{Typing Error (~w): expected type(~w) = ~w, found ~w}~n', [Word,Term,ExpectedType,Type])
    ).

verify_e_or_s_type(Term, Word, Type) :-
	findall(ES, (e_type(ES) ; s_type(ES)), ESs),
    (
        memberchk(Type, ESs)
    ->
        true
    ;
	format('{Typing Error (~w): expected either an entity or a state/event type for type(~p) in ~w, found ~w}~n', [Word,Term,Es,Type]),
	format('{Typing Error (~w): expected either an entity or a state/event type for type(~p) in ~w, found ~w}~n', [Word,Term,Es,Type])
    ).
	

verify_e_type(Term, Word, Type) :-
	findall(E, e_type(E), Es),
    (
	memberchk(Type, Es)
    ->
        true
    ;
	format('{Typing Error (~w): expected entity for type(~p) in ~w, found ~w}~n', [Word,Term,Es,Type]),
	format('{Typing Error (~w): expected entity for type(~p) in ~w, found ~w}~n', [Word,Term,Es,Type])
    ).

verify_s_type(Term, Word, Type) :-
	findall(S, s_type(S), Ss),
    (
	memberchk(Type, Ss)
    ->
        true
    ;
	format('{Typing Error (~w): expected state type for type(~p) in ~w, found ~w}~n', [Word,Term,Ss,Type]),
	format('{Typing Error (~w): expected state type for type(~p) in ~w, found ~w}~n', [Word,Term,Ss,Type])
    ).

verify_t_type(Term, Word, Type) :-
	findall(T, t_type(T), Ts),
    (
	memberchk(Type, Ts)
    ->
        true
    ;
	format('{Typing Error (~w): expected boolean type for type(~p) in ~w, found ~w}~n', [Word,Term,Ts,Type]),
	format('{Typing Error (~w): expected boolean type for type(~p) in ~w, found ~w}~n', [Word,Term,Ts,Type])
    ).



check_var_list([], _, Tr, Tr).
check_var_list([V|Vs], Word, Tr0, Tr) :-
	check_var(V, Word, Tr0, Tr1),
	check_var_list(Vs, Word, Tr1, Tr).

check_var(event(V), Word, Tr0, Tr) :-
	!,
	check_type(V, S, Word, Tr0, Tr),
	verify_s_type(V, Word, S).
check_var(variable(V), Word, Tr0, Tr) :-
	!,
	check_type(V, E, Word, Tr0, Tr),
	verify_e_type(V, Word, E).
check_var(set_variable(V), Word, Tr0, Tr) :-
	!,
	check_type(V, E->T, Word, Tr0, Tr),
	verify_e_type(V, Word, E),
	verify_t_type(V, Word, T).
check_var(constant(V), Word, Tr0, Tr) :-
	!,
	check_type(V, E, Word, Tr0, Tr),
	verify_e_type(V, Word, E).
check_var(V, Word, Tr0, Tr) :-
	check_type(V, E, Word, Tr0, Tr),
	verify_e_type(V, Word, E).


check_cond_list([], _, Tr, Tr).
check_cond_list([C|Cs], Word, Tr0, Tr) :-
	t_type(T),
	check_type(C, T, Word, Tr0, Tr1),
	check_cond_list(Cs, Word, Tr1, Tr).

syntactic_to_semantic_type(lit(A), _W, T, Tree) :-
	!,
	btree_get(Tree, A, T).
syntactic_to_semantic_type(dia(_,A), W, TA, Tree) :-
	!,
	syntactic_to_semantic_type(A, W, TA, Tree).
syntactic_to_semantic_type(box(_,A), W, TA, Tree) :-
	!,
	syntactic_to_semantic_type(A, W, TA, Tree).
syntactic_to_semantic_type(dr(_,B,A), W, (TA->TB), Tree) :-
	!,
	syntactic_to_semantic_type(A, W, TA, Tree),
	syntactic_to_semantic_type(B, W, TB, Tree).
syntactic_to_semantic_type(dl(_,A,B), W, (TA->TB), Tree) :-
	!,
	syntactic_to_semantic_type(A, W, TA, Tree),
	syntactic_to_semantic_type(B, W, TB, Tree).
syntactic_to_semantic_type(p(_,A,B), W, TA-TB, Tree) :-
	!,
	syntactic_to_semantic_type(A, W, TA, Tree),
	syntactic_to_semantic_type(B, W, TB, Tree).
syntactic_to_semantic_type(Syn, W, _, _) :-
	format('{Formula Error(~w): unknown syntactic formula ~w}~n', [W,Syn]),
	format(log, '{Formula Error(~w): unknown syntactic formula ~w}~n', [W,Syn]),
	fail.
	
e_type(E) :-
    (
	user:entity_type(_)
    ->
	user:entity_type(E)
    ;
        E = e
    ).

drs_type(Drs) :-
    (
        user:drs_type(_)
    ->
        user:drs_type(Drs)
    ;
        t_type(Drs)
    ).

t_type(Bool) :-
    (
	user:boolean_type(_)
    ->
	user:boolean_type(Bool)
	
    ;
        Bool = t
    ).

s_type(State) :-
    (
	user:state_type(_)
    ->
	user:state_type(State)
    ;
        State = s
    ).


get_atomic_types(Tree) :-
	findall(D, user:atomic_formula(D), Atoms0),
	sort(Atoms0, Atoms),
	get_atomic_types(Atoms, empty, Tree).

get_atomic_types([], T, T).
get_atomic_types([A|As], T0, T) :-
    (
	user:atomic_type(A, Type)
    ->
	btree_insert(T0, A, Type, T1)
    ;
	format('{Error: unknown semantic type for atomic type ~w}~n', [A]),
	format(log, '{Error: unknown semantic type for atomic type ~w}~n', [A]),
	T1 = T0
    ),
	get_atomic_types(As, T1, T).

% = freeze(+Term, -FrozenTerm)

freeze(Term0, Term) :-
	copy_term(Term0, Term),
	numbervars(Term, 1, _).

% = melt(+Frozen, -Term)

melt(Term, Molten) :-
	melt(Term, Molten, empty, _).

melt('$VAR'(N), Var, T0, T) :-
	integer(N),
	!,
     (
         btree_get(T0, N, Var)
     ->
         T = T0
     ;
         btree_insert(T0, N, Var, T)
     ).
melt(A0, A, T0, T) :-
	atomic(A0),
	!,
	A = A0,
	T = T0.
melt(Term0, Term, T0, T) :-
	Term0 =.. [F|List0],
	melt_list(List0, List, T0, T),	
	Term =.. [F|List].

melt_list([], [], T, T).
melt_list([A|As], [B|Bs], T0, T) :-
	melt(A, B, T0, T1),
	melt(As, Bs, T1, T).
