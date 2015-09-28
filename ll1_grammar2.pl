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

atomic_formula(up).
atomic_formula(home).

% = specify some abbreviations to make the lexical entries slightly more compact

macro(pp(X,Y), at(pp, [X,Y])).
macro(np(X,Y), at(np, [X,Y])).
macro(n(X,Y), at(n, [X,Y])).
macro(s(X,Y), at(s, [X,Y])).
macro(tv(X,Y), forall(R,impl(at(np, [Y,R]),forall(L,impl(at(np, [L,X]), at(s, [L,R])))))).
macro(tv(A,B,C,D), impl(at(np, [B,C]),forall(X,impl(at(np, [X,A]), at(s, [X,D]))))).

lex(peter, np(L,R), L, R, peter).
lex(suzy, np(L,R), L, R, suzy).
lex(john, np(L,R), L, R, john).
lex(wendy, np(L,R), L, R, wendy).

lex(up, at(up, [L,R]), L, R, up).
lex(rang, forall(C,forall(D,impl(at(up, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(ring_up,Y),X))))).
lex(home, at(home, [L,R]), L, R, home).
lex(took, forall(C,forall(D,impl(at(home, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(take_home,Y),X))))).
lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tv(G,G),at(s, [R,F])), impl(impl(tv(A,B,C,D),at(s, [E,L])), impl(tv(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).

% = discontinuous gapping
test(1) :-
	parse([peter,rang,suzy,up], s).
test(2) :-
	parse([peter,rang,suzy,up,and,john,wendy], s).
test(3) :-
	parse([peter,took,suzy,home], s).
test(4) :-
	parse([peter,took,suzy,home,and,john,wendy], s).
