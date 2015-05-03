% ====================================
% = First-order linear logic grammar =
% ====================================

% This grammar provides some examples of how to use the first-order variables for some things which cannot directly be implemented
% either in hybrid type-logical grammars or in displacement grammars (even when case is added). The treatment of non-associativity
% and blocking empty antecedent derivations given here is briefly mentioned in Section 6 of the following article
%
% Richard Moot (2014), Extended Lambek calculi and first-order linear logic, in Claudia Casadio, Bob Coecke, Michael Moortgat and
% Philip Scott, eds `Categories and Types in Logic, Language, and Physics: Essays Dedicated to Jim Lambek on the Occasion of His
% 90th Birthday', Springer LNCS 8222, 297-330

:- op(190, yfx, @).

:- abolish(lex/3), abolish(lex/4), abolish(test/1), abolish(atomic_formula/3), abolish(atomic_formula/1), abolish(macro/2).

% For lambda terms, X^M is short for lambda(X,M) and M@N
% is short for appl(M,N). As expected, X^Y^Z^X@Y@Z is
% short for lambda(X,lambda(Y,lambda(Z,appl(appl(X,Y),Z))))
% though be warned that X@Y+V@Z corresponds to (X@Y)+(V@Z)

atomic_formula(n(_)).
atomic_formula(np(_)).
atomic_formula(s(_)).
atomic_formula(pp(_)).

% = specify some abbreviations to make the lexical entries slightly more compact

macro(adj(L,R), forall(X,forall(Y,impl(at(n, [X,R,Y]), at(n, [s(X),L,Y]))))).
macro(pp(X,Y,Z), at(pp, [X,Y,Z])).
macro(np(X,Y,Z), at(np, [X,Y,Z])).
macro(n(X,Y,Z), at(n, [X,Y,Z])).
macro(s(X,Y,Z), at(s, [X,Y,Z])).


lex(the, forall(X,forall(Y,forall(Z,impl(n(Y,R,X), np(Z,L,X))))), L, R, iota).
lex(hulk, forall(X,n(X,L,R)), L, R, hulk).
lex(is, forall(Y,impl(adj(R,Y),forall(X,impl(np(nom,X,L), s(main,X,Y))))), L, R, Pred^Subj^Pred@Subj).
lex(red, adj(L,R), L, R, red).
lex(green, adj(L,R), L, R, green).
lex(very, forall(X,impl(adj(R,X),adj(L,X))), L, R, Adj^N^(very@Adj)@N).
% extraction and CSC
lex(book, forall(X,n(X,L,R)), L, R, book).
lex(and, forall(Z,forall(Y,impl(np(t(Z),R,Y),forall(X,impl(np(s(Z),X,L),np(Z,X,Y)))))), L, R, and).
lex(read, forall(Z,forall(Y,impl(np(Z,R,Y),forall(X,impl(np(Z,X,L),s(Z,X,Y)))))), L, R, read).
lex(mary, forall(Z,np(Z,L,R)), L, R, mary).
lex(ak, forall(Z,np(Z,L,R)), L, R, ak).
lex(wp, forall(Z,np(Z,L,R)), L, R, wp).
lex(which, forall(Z,forall(X,impl(exists(Y,impl(np(Z,Y,Y),s(Z,R,X))),forall(V,impl(n(Z,V,L),n(Z,V,X)))))), L, R, Q^P^X^bool(P@X,&,Q@X)).
   
test(1) :-
	parse([the,hulk,is,green], s(main)).
test(2) :-
	/* should fail because of non-associativity */
	parse([the,hulk,is,green,red], s(main)).
test(3) :-
	/* NOTE: the semantics looks odd due to the notation convention for binary predicates, which displays */
        /*     (very green) (iota hulk)  */
        /* as   very(iota(hulk), green)  */
	/* (change "option(prolog_like)." to "option(lambda_like)." in latex.pl to switch this off) */
	parse([the,hulk,is,very,green], s(main)).
test(4) :-
	/* should fail because empy antecedent derivations have been excluded for "very" */
	parse([the,hulk,is,very], s(main)).

% extraction and CSC
test(5) :-
	parse([book,which,mary,read], forall(X,n(X))).
test(6) :-
	parse([mary,read,ak,and,wp], forall(X,s(X))).
test(7) :-
	parse([book,which,mary,read,ak,and], forall(X,n(X))).
test(8) :-
	parse([book,which,mary,read,and,wp], forall(X,n(X))).