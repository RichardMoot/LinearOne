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
macro(inf(X,Y), at(inf, [X,Y])).
macro(to_inf(X,Y), at(to_inf, [X,Y])).
macro(tv(X,Y), forall(R,impl(at(np, [Y,R]),forall(L,impl(at(np, [L,X]), at(s, [L,R])))))).
% extracted (s/np)/np, with left position L
macro(tvie(L), forall(M,impl(at(np, [L,M]),forall(R,impl(at(np, [M,R]), at(s, [L,R])))))).
macro(tv(A,B,C,D), impl(np(B,C),forall(X,impl(np(X,A), s(X,D))))).
macro(tvi(A,B,C,D), impl(np(B,C),forall(X,impl(np(D,X), s(A,X))))).
macro(tvi(A,B,C,D,E,F), impl(np(B,C),impl(np(D,E), s(A,F)))).
macro(tv_to_inf(A,B,C,D), impl(np(B,C),to_inf(A,D))).

lex(peter, np(L,R), L, R, peter).
lex(suzy, np(L,R), L, R, suzy).
lex(susan, np(L,R), L, R, susan).
lex(john, np(L,R), L, R, john).
lex(wendy, np(L,R), L, R, wendy).
lex(jimmy, np(L,R), L, R, jimmy).
lex(jill, np(L,R), L, R, jill).

lex(up, at(up, [L,R]), L, R, up).
lex(rang, forall(C,forall(D,impl(at(up, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(ring_up,Y),X))))).
lex(home, at(home, [L,R]), L, R, home).
lex(took, forall(C,forall(D,impl(at(home, [C,D]), tv(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(take_home,Y),X))))).
lex(to_take, forall(C,forall(D,impl(at(home, [C,D]), tv_to_inf(L,R,C,D)))), L, R, lambda(_,lambda(Y,lambda(X,appl(appl(take_home,Y),X))))).
lex(should, forall(A,impl(np(R,A),forall(B,impl(inf(A,B),s(L,B))))), L, R, lambda(NP,lambda(INF,appl(should,appl(INF,NP))))).
lex(will, forall(A,impl(np(R,A),forall(B,impl(inf(A,B),s(L,B))))), L, R, lambda(NP,lambda(INF,appl(will,appl(INF,NP))))).
lex(i, np(L,R), L, R, i).
lex(me, np(L,R), L, R, me).
lex(you, np(L,R), L, R, you).
lex(call, forall(A,impl(np(R,A),inf(L,A))), L, R, call).
lex(greet, forall(A,impl(np(R,A),inf(L,A))), L, R, greet).
% the entry below scopes over the left conjunct of a gapping construction only, eg. for sentence 8
lex(first, forall(A,impl(s(A,L),s(A,R))), L, R, first).
% the entry below fails to derive sentence 8 at all
%lex(first, forall(A,impl(inf(A,L),inf(A,R))), L, R, lambda(INF,lambda(X,appl(first,appl(INF,X))))).
lex(asked, forall(B,impl(np(R,B),forall(C,impl(to_inf(B,C),forall(A,impl(np(A,L),s(A,C))))))), L, R, lambda(O,lambda(INF,lambda(S,appl(appl(appl(ask,O),appl(INF,O)),S))))).

% gapping lexical entries
% gapping of (np\s)|np 
lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tv(G,G),at(s, [R,F])), impl(impl(tv(A,B,C,D),at(s, [E,L])), impl(tv(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).
lex(or, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tv(G,G),at(s, [R,F])), impl(impl(tv(A,B,C,D),at(s, [E,L])), impl(tv(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),\/,appl(P,TV)))))).
% gapping of (s/np)|np
lex(and, forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tvie(G),s(R,F)), impl(impl(tvi(A,B,C,D),s(E,L)), impl(tvi(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),&,appl(P,TV)))))).
lex(or,  forall(A,forall(B,forall(C,forall(D,forall(E,forall(F,forall(G,impl(impl(tvie(G),s(R,F)), impl(impl(tvi(A,B,C,D),s(E,L)), impl(tvi(A,B,C,D), s(E,F))))))))))), L, R, lambda(P,lambda(Q,lambda(TV,bool(appl(Q,TV),\/,appl(P,TV)))))).

% = discontinuous gapping
test(1) :-
	parse([peter,rang,suzy,up], s).
test(2) :-
	parse([peter,rang,suzy,up,and,john,wendy], s).
test(3) :-
	parse([peter,took,suzy,home], s).
test(4) :-
	parse([peter,took,suzy,home,and,john,wendy], s).
%
test(5) :-
	parse([should,i,call,you], s).
%
test(6) :-
	parse([should,i,call,you,or,you,me], s).
test(7) :-
	parse([will,jimmy,greet,jill,first], s).
% fails (verify why)
test(8) :-
	parse([will,jimmy,greet,jill,first,or,jill,jimmy], s).
test(9) :-
	parse([i,asked,peter,to_take,susan,home], s).
% two readings, both using the (np\s)|np assignment, is it possible to get the third using the (s/np)|np assignment?
% v 1) I asked Peter to take Susan home and           John [asked Peter to take] Wendy [home]
% v 2) I asked Peter to take Susan home and           John [asked]               Wendy [to take Susan home]
% x 3) I asked Peter to take Susan home and [I asked] John [to take]             Wendy [home]
test(10) :-
	parse([i,asked,peter,to_take,susan,home,and,john,wendy], s).
