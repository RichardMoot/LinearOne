
:- module(translations, [translate_lambek/3,
			 linear_to_lambek/3,
			 translate_displacement/3,
			 linear_to_displacement/3,
			 displacement_sort/2,
		 	 translate_hybrid/6,
			 linear_to_hybrid/2,
			 linear_to_hybrid/3,
			 linear_to_hybrid/4,
			 translate/3,
			 principal_type/2,
			 compute_pros_term/3,
			 compute_pros_term/5,
			 compute_type/2,
			 compute_types/3,
			 pure_to_simple/3,
			 simple_to_pure/2,
			 simple_to_pure/4,
			 formula_type/2,
			 inhabitants/2,
			 inhabitants/3,
			 exhaustive_test/6]).


:- use_module(lexicon, [macro_expand/2]).
:- use_module(auxiliaries, [non_member/2,
			    identical_prefix/3,
			    identical_postfix/3,
			    identical_lists/2]).
:- use_module(ordset, [ord_key_union_u/3, ord_key_insert/4, ord_key_member/3]).

:- op(190, yfx, @).

% = hybrid_pros
%
% This flag controls how the prosodic lambda term of hybrid type-logical grammars are output to LaTeX.
%
% When set of "pure", lambda terms are converted to pure lambda terms (without either the empty string
% "epsilon" or the explicit concatenation operation "+".
%
% When set to "simple", pure lambda terms are converted, whenever possible, to simple lambda terms
% using concatenation "+" and the empty string "epsilon".

%hybrid_pros(pure).
hybrid_pros(simple).


translate(F0, [X,Y], F) :-
	translate_lambek(F0, [X,Y], F),
	!.
translate(F0, [X,Y], F) :-
	translate_displacement(F0, [X,Y], F),
	!.

% =======================
% =   Lambek calculus   =
% =======================

% = translate_lambek(+LambekFormula, -LinearLogicFormula)
%
% true if LinearLogicFormula is the first-order linear logic formula
% which corresponds to the Lambek calculus formula

translate_lambek(at(A), [X,Y], at(A,[X,Y])).
translate_lambek(at(A,Vs0), [X,Y], at(A, Vs)) :-
	append(Vs0, [X,Y], Vs).
translate_lambek(dr(A0,B0), [X,Y], forall(Z,impl(B,A))) :-
	translate_lambek(B0, [Y,Z], B),
	translate_lambek(A0, [X,Z], A).
translate_lambek(dl(B0,A0), [Y,Z], forall(X,impl(B,A))) :-
	translate_lambek(B0, [X,Y], B),
	translate_lambek(A0, [X,Z], A).
translate_lambek(p(A0,B0), [X,Z], exists(Y,p(A,B))) :-
	translate_lambek(A0, [X,Y], A),
	translate_lambek(B0, [Y,Z], B).

% = linear_to_lambek(-LinearLogicFormula, Positions, LambekFormula)
%
% the inverse of translate_lambek, works correctly even when LinearLogicFormula
% is not a ground term (for example when it contains first-order quantifiers).
% We can obtain the same result by
%
% copy_term(F0, F), translate_lambek(Lambek, Pos, F)

linear_to_lambek(forall(Z,impl(A,B)), [X,Y], F) :-
	linear_to_lambek(A, [VA,WA], FA),
	linear_to_lambek(B, [VB,WB], FB),
   (
        /* it is important to use strict identity rather than unification here */
	/* and elsewhere to avoid accidentally unifying positions (which would */
	/* give an incorrect Lambek connective) */   
	VA == VB,
	VB == Z
   ->
	WA = X,
	Y = WB,
	F = dl(FA,FB)
    ;
        WA == WB,
        WB == Z
   ->
	VA = Y,
	VB = X,
	F = dr(FB,FA)
   ).
linear_to_lambek(exists(Y, p(A,B)), [X,Z], F) :-
	linear_to_lambek(A, [VA,WA], FA),
	linear_to_lambek(B, [VB,WB], FB),
   (
        WA == Y,
	VB == Y
   ->
        VA = X,
	WB = Z,
	F = p(FA,FB)
   ).
linear_to_lambek(at(A, Vs0), [X,Y], at(A, Prefix)) :-
	atomic_formula_prefix(A, Prefix),
	!,
	append(Prefix, [X,Y], Vs0).
linear_to_lambek(at(A,[X,Y]), [X,Y], at(A)).

% =============================
% =   Displacement calculus   =
% =============================

% = displacement_sort(+DFormula, ?Sort).
%
% true if Sort is the sort of Displacement calculus formula DFormula
% (according to the definition of sort on p. 11, Figure 2 of
% Morril, Valentin & Fadda, 2011).
% requires the sorts of atomic formulas to be defined by the
% predicate d_atom_sort/2 (which defaults to 0).

displacement_sort(at(A), S) :-
	d_atom_sort(A, S).
displacement_sort(at(A,_), S) :-
	d_atom_sort(A, S).
displacement_sort(p(A,B), S) :-
	displacement_sort(A, SA),
	displacement_sort(B, SB),
	S is SA + SB.
displacement_sort(dl(A,C), S) :-
	displacement_sort(A, SA),
	displacement_sort(C, SC),
	S is SC - SA.
displacement_sort(dr(C,B), S) :-
	displacement_sort(C, SC),
	displacement_sort(B, SB),
	S is SC - SB.
displacement_sort(p(_K,A,B), S) :-
	displacement_sort(A, SA),
	displacement_sort(B, SB),
	S is SA + SB - 1.
displacement_sort(dl(_K,A,C), S) :-
	displacement_sort(A, SA),
	displacement_sort(C, SC),
	S is SC + 1 - SA.
displacement_sort(dr(_K,C,B), S) :-
	displacement_sort(C, SC),
	displacement_sort(B, SB),
	S is SC + 1 - SB.
displacement_sort(bridge(A), S) :-
	displacement_sort(A, SA),
	S is SA - 1.
displacement_sort(rproj(A), S) :-
	displacement_sort(A, SA),
	S is SA - 1.
displacement_sort(lproj(A), S) :-
	displacement_sort(A, SA),
	S is SA - 1.

% = d_atom_sort(?AtomName, ?Sort)
%
% true if Sort is the sort of atom AtomName.

% Dutch infinitives (inf or si) are of sort 1
d_atom_sort(inf, 1) :-
	!.
d_atom_sort(si, 1) :-
	!.
d_atom_sort(vpi, 1) :-
	!.
% Atom sort defaults to zero
d_atom_sort(_, 0).

% = translate_displacement(+DFormula, +ListOfVars, -LinearFormula)
%
% true if LinearFormula is the first-order linear logic translation of
% Displacement calculus formula DFormula, using the translation of
% Moot (2013), Table 5.

translate_displacement(at(A), Vars, at(A, Vars)).

translate_displacement(at(A, Vars0), Vars1, at(A, Vars)) :-
	append(Vars0, Vars1, Vars).

% Lambek calculus connectives

translate_displacement(p(A0,B0), Vars, exists(X,p(A,B))) :-
	displacement_sort(A0, SA),
	N is 2*SA+1,
	split(Vars, N, Left, [X], Right),
	translate_displacement(A0, Left, A),
	translate_displacement(B0, [X|Right], B).
translate_displacement(dr(C0,B0), Vars, F0) :-
	displacement_sort(B0, SB),
	last(Vars, Last, VarsPrefix),
	M is 2*SB + 1,
	length(Vs, M),
	append(VarsPrefix, Vs, VarsC),
	forall_prefix(Vs, F0, impl(B,C)),	
	translate_displacement(C0, VarsC, C),
	translate_displacement(B0, [Last|Vs], B).
translate_displacement(dl(A0,C0), [V|Vars], F0) :-
	displacement_sort(A0, SA),
	N is 2*SA+1,
	length(Vs, N),
	forall_prefix(Vs, F0, impl(A,C)),
	append(Vs, [V], VarsA),
	append(Vs, Vars, VarsC),
	translate_displacement(A0, VarsA, A),
	translate_displacement(C0, VarsC, C).

% allow "up" and "down" as aliases for "dr" and "dl" respectively  
% eg. dr(>,A,B) = \uparrow_<
%     dl(>,A,B) = \downarrow_<

translate_displacement(up(K,A,B), Vs, F) :-
        !,
        translate_displacement(dr(K,A,B), Vs, F).
translate_displacement(down(K,A,B), Vs, F) :-
        !,
        translate_displacement(dl(K,A,B), Vs, F).

% initial wrap

translate_displacement(p(>,A0,B0), [X0|Vars], exists(X1,exists(XN,p(A,B)))) :-
	!,
	displacement_sort(B0, SB),
	N is 2*SB + 2,
	/* Left = X2,...,X_n-1
	   Right = X_n+1,...,X_n+m
	   L2 = X2,...,X_n */
	split(Vars, N, Left, LE, Right),
	copy_term(Left-LE,L2-H2),
	LE = [],
	H2 = [XN],
	/* VarsA = X_0,X_1,X_n,...,X_n+m */
	/* VarsB = X_1,...,X_n */
        translate_displacement(A0, [X0,X1,XN|Right], A),
	translate_displacement(B0, [X1|L2], B).
translate_displacement(dr(>,C0,B0), [X0,X1,XN|Vars], F0) :-
	!,
	/* Vars = X_n+1,...,X_n+m */
	displacement_sort(B0, SB),
	N is 2*SB + 2,
	L is N - 2,
	/* Vs = X_2,...,X_n-1 */
	length(Vs, L),
	forall_prefix(Vs, F0, impl(B,C)),
	/* VarsB = X_1,...,X_n */
	append([X1|Vs], [XN], VarsB),
	/* VarsC = X_0,X_2,...,X_n-1,X_n+1,...,X_n+m */
	append([X0|Vs], Vars, VarsC),
	translate_displacement(B0, VarsB, B),
	translate_displacement(C0, VarsC, C).
translate_displacement(dl(>,A0,C0), [X1|Vars], F0) :-
	!,
	/* Vars = X_2,...,X_n */
	displacement_sort(A0, SA),
	M is 2*SA - 1,
	/* Vs = X_n+1,...,X_n+m */
	length(Vs, M),
	/* XN1 = X_2,...,X_n-1 */
	last(Vars, XN, XN1),
	/* VarsA = X_0,X_1,X_n,...,X_n+m */
	/* VarsC = X_0,X_2,...,X_n-1,X_n+1,...,X_n+m */
	append([X0|XN1], Vs, VarsC),
	forall_prefix([X0|Vs], F0, impl(A,C)),
	translate_displacement(A0, [X0,X1,XN|Vs], A),
	translate_displacement(C0, VarsC, C).

% final wrap

translate_displacement(p(<,A0,B0), Vars, exists(XN,exists(XNM1,p(A,B)))) :-
	displacement_sort(B0, SB),
	N is 2*SB + 2,
	/* Left = X_0,...,X_n-1
	   Right0 = X_n+1,...,X_n+m-2,X_n+m
	   Right  = X_n+1,...,X_n+m-2
	   L2 = X2,...,X_n */
	split(Vars, N, Left, [], Right0),
	last(Right0, XNM, Right),
	append(Left, [XN,XNM1,XNM], VarsA),
	append([XN|Right], [XNM1], VarsB),
	/* VarsA = X_0,...,X_n,X_n+m-1,X_n+m */
	/* VarsB = X_n,...,X_n+m-1 */
        translate_displacement(A0, VarsA, A),
	translate_displacement(B0, VarsB, B).
translate_displacement(dr(<,C0,B0), [X0|Vars], F0) :-
	/* Vars = X_1,...,X_n,X_n+m-1,X_n+m */
	displacement_sort(B0, SB),
	M is 2*SB + 2,
	L is M - 2,
	/* Left = X_1,...,X_n-1 */
	append(Left, [XN,XNM1,XNM], Vars),
	/* Vs = X_n+1,...,X_n+m-2 */
	length(Vs, L),
	forall_prefix(Vs, F0, impl(B,C)),
	/* VarsB = X_n,...,X_n+m-1 */
	append([XN|Vs], [XNM1], VarsB),
	/* Aux = X_n+1,...,X_n+m-2,X_n+m */
	append(Vs, [XNM], Aux),
	/* VarsC = X_0,...,X_n-1,X_n+1,...,X_n+m-2,X_n+m */
	append([X0|Left], Aux, VarsC),
	translate_displacement(B0, VarsB, B),
	translate_displacement(C0, VarsC, C).
translate_displacement(dl(<,A0,C0), [XN|Vars], F0) :-
	/* Vars = X_n+1,...,X_n+m-1 */
	/* Right = X_n+1,...,X_n+m-2 */
	last(Vars, XNM1, Right),
	displacement_sort(A0, SA),
	N is 2*SA - 1,
	L is N + 1,
	/* Vs = X_0,....,X_n-1,X_n+m */
	length(Vs, L),
	/* Left = X_0,...,X_n-1 */
	append(Left, [XNM], Vs),
	/* VarsA = X_0,...,X_n,X_n+m-1,X_n+m */
	/* VarsC = X_0,...,X_n-1,X_n+1,...,X_n+m-2,X_n+m */
	append(Left, [XN,XNM1,XNM], VarsA),
	/* Tmp = X_n+1,...,X_n+m-2,X_n+m */
	append(Right, [XNM], Tmp),
	append(Left, Tmp, VarsC),
	forall_prefix(Vs, F0, impl(A,C)),
	translate_displacement(A0, VarsA, A),
	translate_displacement(C0, VarsC, C).

% bridge, right projection and left projection
% NOTE: only leftmost bridge is provided (though it would be
% simple to add rightmost bridge if desired. Translations of
% split and the injections are not provided at the moment.
 
translate_displacement(bridge(A0), [V|Vars], exists(X,F0)) :-
	translate_displacement(A0, [V,X,X|Vars], F0).
translate_displacement(rproj(A0), Vars, forall(X,F0)) :-
	translate_displacement(A0, [X,X|Vars], F0).
translate_displacement(lproj(A0), Vars0, forall(X,F0)) :-
	append(Vars0, [X,X], Vars),
	translate_displacement(A0, Vars, F0).

forall_prefix([], F, F).
forall_prefix([X|Xs], forall(X,F0), F) :-
	forall_prefix(Xs, F0, F).

last([A|As], L, Rest) :-
	last(As, A, L, Rest).
last([], A, A, []).
last([A|As], B, L, [B|Rs]) :-
	last(As, A, L, Rs).

split([V|Vs], N0, [V|Ls0], Ls, Rs) :-
    (
        N0 =< 1
    ->
        Vs = Rs,
        Ls = Ls0
    ;
        N is N0 - 1,
        split(Vs, N, Ls0, Ls, Rs)
    ).

% = linear_to_displacement
%
% translate a first-order linear logic formula into a Displacement calculus formula

linear_to_displacement(at(A, Vs0), Vs, at(A, Prefix)) :-
	atomic_formula_prefix(A, Prefix),
	append(Prefix, Vs, Vs0),
	!.
linear_to_displacement(at(A, Vs), Vs, at(A)) :-
	!.
% = Lambek product
linear_to_displacement(exists(XN,p(A0,B0)), VList, p(A,B)) :-
	linear_to_displacement(A0, VarsA, A),
	linear_to_displacement(B0, [V|VarsB], B),
	append(X0XN1, [W], VarsA),
	V == XN,
	W == XN,
	!,
	append(X0XN1, VarsB, VList).
% = \odot
linear_to_displacement(exists(X1,exists(XN,p(A0,B0))), VList, p(I,A,B)) :-
	linear_to_displacement(A0, VarsA, A),
	linear_to_displacement(B0, VarsB, B),
	displacement_product(VarsA, VarsB, X1, XN, VList, I),
	!.
% = any Displacement calculus implication	
linear_to_displacement(F0, VarList, F) :-
	d_implication(F0, A0, B0, QVars, []),
	linear_to_displacement(A0, VarsA, A),
	linear_to_displacement(B0, VarsB, B),
	displacement_connective(VarsA, VarsB, QVars, VarList, A, B, F),
	!.
% ^
linear_to_displacement(exists(X,F0), [Z|Rest], bridge(F)) :-
	linear_to_displacement(F0, [Z,V,W|Rest], F),
	V == X,
	W == X,
	!.
% right projection
linear_to_displacement(forall(X,F0), Rest, rproj(F)) :-
	linear_to_displacement(F0, [V,W|Rest], F),
	V == X,
	W == X,
	!.
% left projection
linear_to_displacement(forall(X,F0), VList, lproj(F)) :-
	!,
	linear_to_displacement(F0, FList, F),
	append(VList, [V,W], FList),
	V == X,
	W == X,
	!.
	
displacement_product([X0,V,W|VarsA], [V1|VarsB], X1, XN, VarList, Dir) :-
	V == X1,
	W == XN,
	V1 == X1,
	append(X2XN1, [W1], VarsB),
	W1 == XN,
	!,
	Dir = >,
	append([X0|X2XN1], VarsA, VarList).
displacement_product(VarsA, [V|VarsB], XN, XNM1, VarList, Dir) :-
	V == XN,
	append(XN1XNM2, [W], VarsB),
	W == XNM1,
	append(X0XN1, [V1,W1,XNM], VarsA),
	V1 == XN,
	W1 == XNM1,
	!,
	Dir = <,
	append(XN1XNM2, [XNM], Tail),
	append(X0XN1, Tail, VarList).

		
% displacement_connective
%
% We distinguish the different Displacement calculus connectives based on the first-order
% variables. Like for the Lambek calculus, we have to be careful to require strict identity
% here.

% \
displacement_connective(VarsA, VarsB, QVars, VarList, A, B, dl(A,B)) :-
	identical_prefix(QVars, [XN], VarsA),
	identical_prefix(QVars, XN1XNM, VarsB),
	!,
	VarList = [XN|XN1XNM].
% /
displacement_connective([XN|VarsA], VarsB, QVars, VarList, A, B, dr(B,A)) :-
	identical_lists(VarsA, QVars),
	identical_postfix(X0XN1, QVars, VarsB),
	!,
	append(X0XN1, [XN], VarList).
% A = X1...XN
% B = X0,X2,...,XN-1,XN+1,XN+M
% Q = X2,...,XN-1
% \uparrow_>
displacement_connective([X1|VarsA], [X0|VarsB], QVars, VarList, A, B, dr(>,B,A)) :-
	identical_prefix(QVars, XN1XNM, VarsB),
	append(Mid, [XN], VarsA),
	identical_lists(Mid, QVars),
	!,
	VarList = [X0,X1,XN|XN1XNM].
% \downarrow_>
displacement_connective([X0,X1,XN|VarsA], [V|VarsB], [Q|QVars], VarList, A, B, dl(>,A,B)) :-
	Q == X0,
	V == X0,
	identical_lists(VarsA, QVars),
	identical_postfix(X2XN1, QVars, VarsB),
	!,
	append([X1|X2XN1], [XN], VarList).
% \uparrow_<
displacement_connective([XN|VarsA], VarsB, QVars, VarList, A, B, dr(<,B,A)) :-
	append(Mid, [XNM1], VarsA),
	identical_lists(Mid, QVars),
	append(X0XNM2, [XNM], VarsB),
	identical_postfix(X0XN1, QVars, X0XNM2),
	!,
	append(X0XN1,[XN,XNM1,XNM], VarList).
% \downarrow_<
displacement_connective(VarsA, VarsB, QVars, VarList, A, B, dl(<,A,B)) :-
	append(Mid, [Q], QVars),
	identical_prefix(Mid, XN1XNM ,VarsB),
	append(XN1XNM1, [XNM], XN1XNM),
	Q == XNM,
	identical_prefix(Mid, [XN,XNM1,R], VarsA),
	R == XNM,
	!,
	append([XN|XN1XNM1], [XNM1], VarList).
	

% =

d_implication(forall(X,F), A, B) -->
	[X],
	d_implication(F, A, B).
d_implication(impl(A,B), A,B) -->
	[].

% ====================================
% =   Hybrid type-logical grammars   =
% ====================================

linear_to_hybrid(at(A, _), at(A)).
linear_to_hybrid(forall(Z,impl(A,B)), F) :-
	linear_to_lambek(forall(Z,impl(A,B)), [_,_], F).
linear_to_hybrid(exists(Y, p(A,B)), F) :-
	linear_to_lambek(exists(Y, p(A,B)), [_,_], F).
linear_to_hybrid(impl(A,B), h(FB,FA)) :-
	linear_to_hybrid(A, FA),
	linear_to_hybrid(B, FB).


linear_to_hybrid(Formula, HybridFormula, LambdaTerm) :-
	linear_to_hybrid(Formula, VarList, PrincipalFormula, HybridFormula),
	numbervars(VarList, 0, _),
	find_positions(VarList, Ps0),
	sort(Ps0, Ps),
	Ps = [L, R],
	first_proof([impl(at(R,[]),at(L,[]))], PrincipalFormula, LambdaTerm).

find_positions([], []).
find_positions([V|Vs], Ps0) :-
    (
	integer(V)
     ->
        Ps0 = [V|Ps]
     ;
        Ps0 = Ps
     ),		   
        find_positions(Vs, Ps).


atomic_formula_prefix(A, List) :-
	current_predicate(atomic_formula/3), 
        atomic_formula(_, A, Prefix),
  (
	is_list(Prefix)
  ->
        List = Prefix
  ;
        List = [_]
  ).
  
% = linear_to_hybrid(+LinearLogicFormula, -PositionsList, -PrincipalFormula, -HybridFormula)
%
% PrincipalFormula is of the correct "shape" to combine with LinearLogicFormula

% Lambek atoms
linear_to_hybrid(at(A, Vs0), Vs, Impl, Result) :-
    (
        /* take care of features */		
        atomic_formula_prefix(A, Prefix)
    ->
        append(Prefix, Vs, Vs0),
	Result = at(A, Prefix)    
    ;
        Vs = Vs0,
        Result = at(A)
    ),
	list_to_impl(Vs, Impl).
% Lambek implications
linear_to_hybrid(forall(Z,impl(A,B)), [X,Y], impl(at(Y,[]),at(X,[])), F) :-
	linear_to_lambek(forall(Z,impl(A,B)), [X,Y], F).
% Lambek product; not sure if this is needed, if it is, we need to add some more code elsewhere
linear_to_hybrid(exists(Y, p(A,B)), [X,Z], p(at(Z,[]),at(X,[])), F) :-
	linear_to_lambek(exists(Y, p(A,B)), [X,Z], F).
% Hybrid implication
linear_to_hybrid(impl(A,B), Vars, impl(TA,TB), h(FB,FA)) :-
	linear_to_hybrid(A, Vars0, TA, FA),
	linear_to_hybrid(B, Vars1, TB, FB),
	append(Vars0, Vars1, Vars).

list_to_impl([V1,V2], impl(at(V2,[]),at(V1,[]))) :-
	!.
list_to_impl([V3,V1,V2,V4], impl(impl(at(V1,[]),at(V2,[])),impl(at(V3,[]),at(V4,[])))).


% = translate_hybrid(+HybridFormula, +ProsodicTerm, +Word, +LeftPos, +RightPos, -LinearFormula)
%
% translate HybridFormula with ProsodicTerm (of Word with LeftPos/RightPos) to LinearFormula.
% We use ProsodicTerm to compute the principal type, then use the principal type to compute the
% first-order arguments of the atomic subformulas.

translate_hybrid(Formula, Term, Word, L, R, LinearFormula) :-
	formula_type(Formula, Type),
	type_skeleton(Type, TypeS),
	principal_type(lambda(Word,Term), impl(WT,TypeS)),
	format_debug('~N= after principal type computation=~n Term: ~p~n Type: ~p~n', [lambda(Word,Term), impl(WT,TypeS)]), 
    (
	WT = impl(R,L)
    ->
	true
    ;
	format(user_error, '~N{Error: type mismatch ~w should be typable as ~p but is typed as ~p}~n', [Word,impl(R,L),WT]),
	fail
    ),
        match(Formula, TypeS, LinearFormula).

match(at(sneg), impl(impl(TA,TB),impl(TC,TD)), at(sneg, [TC,TA,TB,TD])) :-
	!,
	check_variables([TC,TA,TB,TD], sneg, impl(impl(TA,TB),impl(TC,TD))).
match(at(A, Vs0), impl(TB,TA), at(A, Vs)) :-
	append(Vs0, [TA,TB], Vs).
match(at(A), impl(TB,TA), at(A, [TA,TB])) :-
	check_variables([TA,TB], A, impl(TB,TA)).
match(h(B,A), impl(TA,TB), impl(FA,FB)) :-
	match(A, TA, FA),
	match(B, TB, FB).
match(dr(A,B), impl(TB, TA), F) :-
	translate_lambek(dr(A,B), [TA,TB], F).
match(dl(A,B), impl(TB, TA), F) :-
	translate_lambek(dl(A,B), [TA,TB], F).
match(p(A,B), impl(TB, TA), F) :-
	translate_lambek(p(A,B), [TA,TB], F).

check_variables([], _, _).
check_variables([V|Vs], F, T) :-
   (
	var(V)
   ->
        true
   ;		   
        functor(V,impl,2)
   ->
	format(user_error, '~N{Error: type mismatch ~w, ~w, ~w}~n', [V,F,T]),
        fail
   ;
        true
   ),
        check_variables(Vs, F, T).	

% = type_skeleton(+InType, -OutType)
%
% true if OutType is the same as InType, but with all occurrences
% of the atomic type s replaced by a distinct free variable.

type_skeleton(s, _).
type_skeleton(impl(A0,B0), impl(A,B)) :-
	type_skeleton(A0, A),
	type_skeleton(B0, B).

% = formula_type(+HybridFormula, -ProsodicType)
%
% computed the prosodic type of a hybrid formula

formula_type(h(B,A), impl(TA,TB)) :-
	formula_type(A, TA),
	formula_type(B, TB).
formula_type(dr(_,_), impl(s,s)).
formula_type(dl(_,_), impl(s,s)).
formula_type(p(_,_), impl(s,s)).
formula_type(at(At, _), Type) :-
	atom_type(At, Type).
formula_type(at(At), Type) :-
	atom_type(At, Type).

% = atom_type(+AtomName, -Type)
%
% gives the Type corresponding to each AtomName; impl(s,s)
% corresponds to the basic string type.
%
% NOTE: defaults to basic string impl(s,s) when not
% otherwise specified.

atom_type(inf, impl(impl(s,s),impl(s,s))) :-
	!.
atom_type(sneg, impl(impl(s,s),impl(s,s))) :-
	!.
atom_type(_, impl(s,s)).

% = 

compute_pros_term(Lambda0, Formula, Lambda) :-
	compute_pros_term(Lambda0, Formula, Lambda, 0, _).

compute_pros_term(Lambda0, Formula, Lambda, Max0, Max) :-
	numbervars(Lambda0, Max0, Max1),
	formula_type(Formula, Type),
	simple_to_pure(Lambda0, Max1, Max2, Lambda1),
	normalize_pros_pure(Lambda1, Lambda2),
  (
	hybrid_pros(pure)
  ->
	Lambda = Lambda2,
	Max = Max2  
  ;
        pure_to_simple(Lambda2, Type, Lambda),
        numbervars(Lambda, Max2, Max)
  ).

% = normalization of prosodic term

normalize_pros_pure(Term0, Term) :-
	normalize_pros_pure(Term0, Term, []).

normalize_pros_pure(appl(X,Y), Term, As) :-
	/* WARNING: there is no alpha conversion here! */
	normalize_pros_pure(X, Term, [Y|As]),
	/* cut must be at the end to allow backtracking */
	!.
normalize_pros_pure(lambda(X, appl(Term0, X)), Term, []) :-
        /* subterm check shouldn't be necessary if all lambda terms are linear */
	\+ subterm(Term0, X),
	!,
	normalize_pros_pure(Term0, Term).
normalize_pros_pure(lambda(X,Term0), Term, [A|As]) :-
	!,
	replace(Term0, X, A, Term1),
	normalize_pros_pure(Term1, Term, As).
normalize_pros_pure(lambda(X, Term0), lambda(X, Term), []) :-
	!,
	normalize_pros_pure(Term0, Term).
normalize_pros_pure(Term, appl(Term,B), [A]) :-
	normalize_pros_pure(A, B, []).
normalize_pros_pure(Term, Term, []).



subterm(X, X).
subterm(appl(X,_), Z) :-
	subterm(X, Z).
subterm(appl(_,Y), Z) :-
	subterm(Y, Z).
subterm(X+_, Z) :-
	subterm(X, Z).
subterm(_+Y, Z) :-
	subterm(Y, Z).
subterm(lambda(_,X), Z) :-
	subterm(X, Z).


replace(X, X, Y, Y) :-
	!.
replace(appl(X0,Y0), V, W, appl(X,Y)) :-
	!,
	replace(X0, V, W, X),
	replace(Y0, V, W, Y).
replace(X0+Y0, V, W, X+Y) :-
	!,
	replace(X0, V, W, X),
	replace(Y0, V, W, Y).
replace(lambda(X, Y0), V, W, lambda(X, Y)) :-
	!,
   ( X = V -> Y = Y0 ; replace(Y0, V, W, Y)).
replace(A, _, _, A).


% = translate pure lambda term to simplified lambda term (requires types)
%

pure_to_simple_formula(PureTerm, Formula0, SimpleTerm) :-
	macro_expand(Formula0, Formula),
	formula_type(Formula, Type),
	pure_to_simple(PureTerm, Type, SimpleTerm).

pure_to_simple(PureTerm, Type, SimpleTerm) :-
	compute_types(PureTerm, Type, Tree),
	pure_to_simple(PureTerm, Tree, Type, SimpleTerm).

pure_to_simple(Atom, Tree, impl(s,s), Atom) :-
	atomic(Atom),
	!,
	ord_key_member(Atom, Tree, impl(s,s)).
pure_to_simple('$VAR'(N), Tree, Type, '$VAR'(N)) :-
	!,
	ord_key_member('$VAR'(N), Tree, Type).
pure_to_simple(lambda(Z,Term0), Tree, impl(s,s), Term) :-
	translate_string_concat(Term0, Z, Tree, Term),
	!.
pure_to_simple(appl(X0,Y0), Tree, TXY, appl(X,Y)) :-
	pure_to_simple(X0, Tree, impl(TY,TXY), X),
	pure_to_simple(Y0, Tree, TY, Y).
pure_to_simple(lambda(X,Y0), Tree, impl(TX,TY), lambda(X,Term)) :-
	ord_key_member(X, Tree, TX),
	pure_to_simple(Y0, Tree, TY, Term).

translate_string_concat(Z, Z, _, epsilon) :-
	!.
translate_string_concat(appl(X0,Y), Z, Tree, Term) :-
	get_type(Tree, X0, impl(s,s)),
	pure_to_simple(X0, Tree, impl(s,s), X),
	translate_string_concat(Y, X, Z, Tree, Term).

translate_string_concat(Z, X, Z, _, X) :-
	!.
translate_string_concat(appl(X1,Y), X0, Z, Tree, X0+Term) :-
	get_type(Tree, X1, impl(s,s)),
	pure_to_simple(X1, Tree, impl(s,s), X),
	translate_string_concat(Y, X, Z, Tree, Term).

simple_to_pure(X0@Y0, appl(X,Y)) :-
	!,
	simple_to_pure(X0, X),
	simple_to_pure(Y0, Y).
simple_to_pure(X^Y0, lambda(X,Y)) :-
	!,
	simple_to_pure(Y0, Y).
simple_to_pure(X0+Y0, lambda(Z,appl(X,appl(Y,Z)))) :-
	!,
	simple_to_pure(X0, X),
	simple_to_pure(Y0, Y).
simple_to_pure(epsilon, lambda(Z,Z)) :-
	!.
simple_to_pure(appl(X0,Y0), appl(X,Y)) :-
	!,
	simple_to_pure(X0, X),
	simple_to_pure(Y0, Y).
simple_to_pure(lambda(X,Y0), lambda(X,Y)) :-
	!,
	simple_to_pure(Y0, Y).
simple_to_pure(X, X).

simple_to_pure(X0@Y0, N0, N, appl(X,Y)) :-
	!,
	simple_to_pure(X0, N0, N1, X),
	simple_to_pure(Y0, N1, N, Y).
simple_to_pure(X^Y0, N0, N, lambda(X,Y)) :-
	!,
	simple_to_pure(Y0, N0, N, Y).
simple_to_pure(X0+Y0, N0, N, lambda('$VAR'(N0),appl(X,appl(Y,'$VAR'(N0))))) :-
	!,
	N1 is N0 + 1, 
	simple_to_pure(X0, N1, N2, X),
	simple_to_pure(Y0, N2, N, Y).
simple_to_pure(epsilon, N0, N, lambda('$VAR'(N0),'$VAR'(N0))) :-
	N is N0 + 1, 
	!.
simple_to_pure(appl(X0,Y0), N0, N, appl(X,Y)) :-
	!,
	simple_to_pure(X0, N0, N1, X),
	simple_to_pure(Y0, N1, N, Y).
simple_to_pure(lambda(X,Y0), N0, N, lambda(X,Y)) :-
	!,
	simple_to_pure(Y0, N0, N, Y).
simple_to_pure(X, N, N, X).



% = principal_type(+Term, -PrincipalType)
%
% compute the PrincipalType of linear lambda term Term.

principal_type(Term, Type) :-
	format_debug('~N= before principal type computation=~n Term: ~p~n Type: ~p~n===~n', [Term, Type]), 
	principal_type(Term, Type, _List).

principal_type(V, Type, [V-Type]) :-
	var(V),
	!.	
principal_type(epsilon, impl(TypeZ,TypeZ), []) :-
	!,
	/* epsilon must be of type sigma->sigma (ie. a string) */
	verify_non_compound(TypeZ,TypeZ, epsilon, 'epsilon of').
principal_type(At, impl(TypeZ,TypeS), [At-impl(TypeZ,TypeS)]) :-
	atom(At),
	!,
	/* atoms must be of type sigma->sigma (ie. strings) */
	verify_non_compound(TypeZ, TypeS, At, 'atom of').
principal_type(A+B, impl(TypeZ,TypeS), List) :-
	!,
        /* allow explicit concatenation using +, though only of terms typed sigma->sigma */
	verify_non_compound(TypeZ, TypeS, A+B, 'concatenation producing'),
	principal_type(lambda(Z,appl(A,appl(B,Z))), impl(TypeZ,TypeS), List).
principal_type(appl(A,B), TypeA, ABlist) :-
        !,
	principal_type(A, impl(TypeB,TypeA), Alist),
	principal_type(B, TypeB, Blist),
	/* might be doable with difference lists, though the abstraction */
        /* case below requires us to select from the constructed list */
	append(Alist, Blist, ABlist).
principal_type(lambda(A,B), impl(TypeA,TypeB), AList) :-
        !,
	principal_type(B, TypeB, BList),
	get_type(BList, A, TypeA, AList),
	format_debug(' ~p = ~p~n', [A,TypeA]).
principal_type(Term, Type, _) :-
        /* unknown term, print error message (helps correct typos, such as subterms of the form lambda/3 or appl/1) */
        functor(Term, F, A),
        format(user_error, '~N{Error: unknown subterm ~w (~w/~w) of type ~p}~n', [Term, F, A, Type]),
	fail.



get_type(List, Term, Type) :-
	get_type(List, Term, Type, _).

get_type([], B, _, []) :-
	/* error message if a free variable appears */
	format(user_error, '{Warning: free occurrences of ~w}~n', [B]). 
get_type([A-TypeA|Rest], B, TypeB, New) :-
     (
         A == B
     ->
         TypeA = TypeB,
         New = Rest
     ;
         New = [A-TypeA|New0],
         get_type(Rest, B, TypeB, New0)
     ).


get_type_premisses(_, '$VAR'(N), Type) :-
	current_predicate(proof_generation:free_var/2),
	proof_generation:free_var(N, Type),
	!.
get_type_premisses(OrdSet, Term, Type) :-
	ord_key_member(Term, OrdSet, Type).

% = compute_type(+Term, -PrincipalType)
%
% compute the PrincipalType of linear lambda term Term.

compute_type(Term, Type) :-
	format_debug('~N= before principal type computation=~n Term: ~p~n Type: ~p~n===~n', [Term, Type]), 
	compute_types(Term, Type, _List).

compute_types('$VAR'(N), Type, ['$VAR'(N)-Type]) :-
	!,
   (
	current_predicate(proof_generation:free_var/2),
	proof_generation:free_var(N, Type0)
   ->
        Type = Type0
    ;
        true
    ).	    
compute_types(epsilon, impl(s,s), []) :-
	!.
compute_types(At, impl(s,s), [At-impl(s,s)]) :-
	atom(At),
	!.
compute_types(A+B, impl(s,s), List) :-
	!,
	compute_types(lambda(Z,appl(A,appl(B,Z))), impl(s,s), List).
compute_types(appl(A,B), TypeA, ABlist) :-
        !,
	compute_types(A, impl(TypeB,TypeA), Alist),
	compute_types(B, TypeB, Blist),
	/* might be doable with difference lists, though the abstraction */
        /* case below requires us to select from the constructed list */
	ord_key_union_u(Alist, Blist, ABlist0),
	ord_key_insert(ABlist0, appl(A,B), TypeA, ABlist).
compute_types(lambda(A,B), impl(TypeA,TypeB), BList) :-
        !,
	compute_types(B, TypeB, BList0),
	ord_key_member(A, BList0, TypeA),
	ord_key_insert(BList0, lambda(A,B), impl(TypeA,TypeB), BList),
	format_debug(' ~p = ~p~n', [A,TypeA]).
compute_types(Term, Type, _) :-
        /* unknown term, print error message (helps correct typos, such as subterms of the form lambda/3 or appl/1) */
        functor(Term, F, A),
        format(user_error, '~N{Error: unknown subterm ~w (~w/~w) of type ~p}~n', [Term, F, A, Type]),
	fail.

% = inhabitants(+Type, ?Term)
%
% true if Term is a (long normal form) inhabitatant of Type; can be used to
% enumerate inhabitants

inhabitants(Type, Term) :-
	inhabitants(Type, Term, [], []).
inhabitants(Type, Term, Word) :-
	inhabitants(Type, Term, [Word-impl(s,s)], []).

inhabitants(s, Term, Set0, Set) :-
	select(X-A, Set0, Set1),
	argument_list(A, X, Term, List, []),
	inhabitants_list(List, Set1, Set).
inhabitants(impl(A,B), lambda(X, Term), Set0, Set) :-
	inhabitants(B, Term, [X-A|Set0], Set),
	non_member(X-A, Set).


inhabitants_list([], Set, Set).
inhabitants_list([X-A|Rest], Set0, Set) :-
	inhabitants(A, X, Set0, Set1),
	inhabitants_list(Rest, Set1, Set).

argument_list(s, Term, Term) -->
	[].
argument_list(impl(A,B), X, Term) -->
	[Y-A],
	argument_list(B, appl(X,Y), Term).

% = exhaustive_test(Word, Formula, Semantics, Sentence, Goal)

exhaustive_test(File, Word, Formula0, Semantics, Sentence, Goal) :-
	open(File, write, Stream, []),
	macro_expand(Formula0, Formula),
	formula_type(Formula, Type),
	setof(Term, inhabitants(impl(impl(s,s),Type), Term), List),
	selectchk(Word, Sentence, OtherWords),
	format(Stream, ':- op(400, xfy, \\).~2n:- abolish(lex/3), abolish(lex/4), abolish(test/1).~2n', []),
	format(Stream, '% = lexicon~2n', []), 
	export_lexicon(OtherWords, Stream),
	export_lexicon(List, Stream, Formula0, Word, 1, Semantics),
	format(Stream, '~2n% = sentences~2n', []), 
	export_sentences(List, Stream, Word, 1, Sentence, Goal),
	close(Stream).

export_lexicon([], _).
export_lexicon([W|Ws], Stream) :-
   (	
	current_predicate(lex/4),	
	lex(W, A, B, C)
   ->
	portray_clause(Stream, (lex(W,A,B,C) :- true))
   ;
	format(user_error, '~N{Warning: no lexical entry found for "~w"}~n', [W]) 
   ),  
        export_lexicon(Ws, Stream).

export_lexicon([], _, _, _, _, _).
export_lexicon([lambda(W,Term)|Rest], Stream, Formula, Word, N0, Semantics) :-
	atom_concat(Word, N0, W),
	N is N0 + 1,
	portray_clause(Stream, (lex(W, Formula, Term, Semantics) :- true)),
	export_lexicon(Rest, Stream, Formula, Word, N, Semantics).


export_sentences([], _, _, _, _, _).
export_sentences([_|Ls], Stream, Word0, N0, Sentence, Goal) :-
	atom_concat(Word0, N0, Word),
	N is N0 + 1,
	selectchk(Word0, Sentence, Word, Sentence1),
	portray_clause(Stream, (test(N0) :- parse(Sentence1, Goal))),
	export_sentences(Ls, Stream, Word0, N, Sentence, Goal).
	
% = debugging tools

verify_non_compound(TypeA, TypeB, Term, Diag) :-
     (
        compound(TypeA)		
     ->
	format(user_error, '{Error: ~w non-string term ~w of type ~w->~w}~n', [Diag, Term, TypeA, TypeB]) 
     ;
        compound(TypeB)		
     ->
	format(user_error, '{Error: ~w non-string term ~w of type ~w->~w}~n', [Diag, Term, TypeA, TypeB]) 
     ;
        true
     ).

debug(0).

format_debug(_, _) :-
	debug(0),
	!.
format_debug(X, Y) :-
	format(user_error, X, Y).
