% =================================
% =          ACG grammar          =
% =================================

% This grammar contains some examples from the following articles.
%
% Makoto Kanazawa (2015) Syntactic Features for Regular Constraints and an Approximation of Directional
% Slashes in Abstract Categorial Grammars, in Yusuke Kubota and Robert Levine (eds) Proceedings of
% Empirical Advances in Categorial Grammars, pp. 34-70.

% define operators to allow for easier specification of
% hybrid type-logical grammar lexical entries.
%
% WARNING: in case of doubt, use parentheses to disambiguate!
% I have deliberately not changed the definitions of standard
% mathematical and logical operations of Prolog, notably |
% (alternative of ; for use in DCG), ^, /, * and +.
%
% This means for example that:
% c/d*b/c = ((c/d)*b)/c
% which corresponds to a left-to-right evaluation of the
% mathematical functions of division and multiplication.
%
% It also means that (s|s|np) = (s|(s|np))
%
% However, we do have the familiar a/b/c = (a/b)/c and
% c\b\a = (c\(b\a) and even a\b/c = (a\b)/c.
%
% For lambda terms, X^M is short for lambda(X,M) and M@N
% is short for appl(M,N). As expected, X^Y^Z^X@Y@Z is
% short for lambda(X,lambda(Y,lambda(Z,appl(appl(X,Y),Z))))
% though be warned that X@Y+V@Z corresponds to (X@Y)+(V@Z)

:- op(400, xfy, \).
:- op(190, yfx, @).

:- abolish(lex/3), abolish(lex/4), abolish(test/1), abolish(atomic_formula/3), abolish(atomic_formula/1), abolish(macro/2).

macro(tv_i, ((s(L,R)|np(L,0))|np(0,R))). 

atomic_formula(np(_,_)).
atomic_formula(s(_,_)).
atomic_formula(s1(_,_)).

lex(leslie, np(0,0), leslie, l).
lex(terry, np(0,0), terry, t).
lex(bill, np(0,0), bill, b).
lex(robin, np(0,0), robin, r).
lex(likes, tv_i, lambda(P,lambda(Q,Q+likes+P)), like).
lex(hates, tv_i, lambda(P,lambda(Q,Q+hates+P)), hate).
lex(and, (((s(A,B)|np(A,B))|(s(C,1)|np(C,1)))|(s(D,1)|np(D,1))), lambda(P1,lambda(P2,lambda(Z,appl(P2,epsilon)+and+appl(P1,epsilon)+Z))), lambda(Z1,lambda(Z2,lambda(X,bool(appl(Z1,X),&,appl(Z2,X)))))).
lex(and, (((np(0,R1)->(np(L1,0)->s(L1,R1)))->s(0,R))->(((np(0,R2)->(np(L2,0)->s(L2,R2)))->s(L,0))->((np(0,1)->(np(1,0)->s(1,1)))->s1(L,R)))),
    lambda(P1,lambda(P2,lambda(P3,appl(P2,lambda(X1,lambda(Y1,X1+appl(appl(P3,epsilon),epsilon)+Y1)))+and+appl(P1,lambda(X2,lambda(Y2,X2+Y2)))))),
    lambda(Z1,lambda(Z2,lambda(Z3,bool(appl(Z1,lambda(Y,lambda(X,appl(appl(Z3,X),Y)))),&,appl(Z2,lambda(V,lambda(W,appl(appl(Z3,W),V))))))))).
lex(everyone, ((np(L,R)->s(L,R))->s(L,R)), lambda(P,appl(P,everyone)), lambda(P,quant(forall,X,bool(appl(person,X),->,appl(P,X))))).
lex(someone, ((np(L,R)->s(L,R))->s(L,R)), lambda(P,appl(P,everyone)), lambda(P,quant(exists,X,bool(appl(person,X),&,appl(P,X))))).

test(1) :-
	parse([leslie,likes,terry], s(_,_)).
test(2) :-
	parse([terry,hates,and,robin,likes,leslie], s(_,_)).
test(3) :-
	parse([terry,hates,robin,and,bill,leslie], s1(_,_)).
test(4) :-
	parse([everyone,likes,terry], s(_,_)).
test(5) :-
	parse([everyone,likes,someone], s(_,_)).
test(6) :-
	parse([terry,hates,someone,and,bill,everyone], s1(_,_)).