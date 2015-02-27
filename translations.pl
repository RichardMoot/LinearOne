:- module(translations, [translate_lambek/3,translate_displacement/3,translate_hybrid/6]).

% =======================
% =   Lambek calculus   =
% =======================

% = translate_lambek(+LambekFormula, -LinearLogicFormula)
%
% true if LinearLogicFormula is the first-order linear logic formula
% which corresponds to the Lambek calculus formula

translate_lambek(at(A), [X,Y], at(A,[X,Y])).
translate_lambek(dr(A0,B0), [X,Y], forall(Z,impl(B,A))) :-
	translate_lambek(B0, [Y,Z], B),
	translate_lambek(A0, [X,Z], A).
translate_lambek(dl(B0,A0), [Y,Z], forall(X,impl(B,A))) :-
	translate_lambek(B0, [X,Y], B),
	translate_lambek(A0, [X,Z], A).
translate_lambek(p(A0,B0), [X,Z], exists(Y,p(A,B))) :-
	translate_lambek(A0, [X,Y], A),
	translate_lambek(B0, [Y,Z], B).

% =============================
% =   Displacement calculus   =
% =============================

% = displacement_sort(+DFormula, ?Sort).
%
% true if Sort is the sort of Displacement calculus formula DFormula
% (according to the definition of sort on p. 11, Figure 2 of
% Morril, Valentin & Fadda (2011).
% requires the sorts of atomic formulas to be defined by the
% predicate d_atom_sort/2.

displacement_sort(at(A), S) :-
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

% = d_atom_sort(?AtomName, ?Sort)
%
% true if Sort is the sort of atom AtomName.

d_atom_sort(inf, 1).
d_atom_sort(np, 0).
d_atom_sort(n, 0).
d_atom_sort(s, 0).
d_atom_sort(pp, 0).
d_atom_sort(vp, 0).


% = translate_displacement(+DFormula, +ListOfVars, -LinearFormula)
%
% true if LinearFormula is the first-order linear logic translation of
% Displacement calculus formula DFormula, using the translation of
% Moot (2013), Table 5.

translate_displacement(at(A), Vars, at(A, Vars)).

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


forall_prefix([], F, F).
forall_prefix([X|Xs], forall(X,F0), F) :-
	forall_prefix(Xs, F0, F).

%last([A|As], L) :-
%	last0(As, A, L).
%last0([], L, L).
%last0([A|As], _, L) :-
%	last0(As, A, L).

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


% dr(>,A,B) = uparrow_<
% dl(>,A,B) = downarrow_<

% ====================================
% =   Hybrid type-logical grammars   =
% ====================================

translate_hybrid(Formula, Term, Word, L, R, LinearFormula) :-
	formula_type(Formula, Type),
	type_skeleton(Type, TypeS),
	principal_type(lambda(Word,Term), impl(impl(R,L),TypeS)),
	match(Formula, TypeS, LinearFormula).

match(at(A), impl(TB,TA), at(A, [TA,TB])).
match(h(B,A), impl(TA,TB), impl(FA,FB)) :-
	match(A, TA, FA),
	match(B, TB, FB).
match(dr(A,B), impl(TB, TA), F) :-
	translate_lambek(dr(A,B), [TA,TB], F).
match(dl(A,B), impl(TB, TA), F) :-
	translate_lambek(dl(A,B), [TA,TB], F).
match(p(A,B), impl(TB, TA), F) :-
	translate_lambek(p(A,B), [TA,TB], F).

% = type_skeleton(+InType, -OutType)
%
% true if OutType is the same as InType, but with all occurrences
% of the atomic type s replaced by a distinct free variable.

type_skeleton(s, _).
type_skeleton(impl(A0,B0), impl(A,B)) :-
	type_skeleton(A0, A),
	type_skeleton(B0, B).

formula_type(h(B,A), impl(TA,TB)) :-
	formula_type(A, TA),
	formula_type(B, TB).
formula_type(dr(_,_), impl(s,s)).
formula_type(dl(_,_), impl(s,s)).
formula_type(p(_,_), impl(s,s)).
formula_type(at(At), Type) :-
	atom_type(At, Type).

% = atom_type(+AtomName, -Type)
%
% gives the Type corresponding to each AtomName; impl(s,s)
% corresponds to the basic string type.
%
% NOTE: you MUST extend this list if you add atomic formulas

atom_type(s, impl(s,s)).
atom_type(n, impl(s,s)).
atom_type(np, impl(s,s)).
atom_type(pp, impl(s,s)).
atom_type(inf, impl(impl(s,s),impl(s,s))).


principal_type(Term, Type) :-
	principal_type(Term, Type, _List).

principal_type(V, Type, [V-Type]) :-
	var(V),
	!.
principal_type(At, Type, [At-Type]) :-
	atom(At),
	!.
principal_type(appl(A,B), TypeA, ABlist) :-
	principal_type(A, impl(TypeB,TypeA), Alist),
	principal_type(B, TypeB, Blist),
	/* might be doable with difference lists, though the abstraction */
        /* case below requires us to select from the constructed list */
	append(Alist, Blist, ABlist).
principal_type(lambda(A,B), impl(TypeA,TypeB), AList) :-
	principal_type(B, TypeB, BList),
	get_type(BList, A, TypeA, AList).

get_type([], B, _, []) :-
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
