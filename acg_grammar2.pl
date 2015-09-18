% =================================
% =          ACG grammar          =
% =================================

% This grammar contains some examples from the following articles.
%
% Makoto Kanazawa (2015) Syntactic Features for Regular Constraints and an Approximation of Directional
% Slashes in Abstract Categorial Grammars, in Yusuke Kubota and Robert Levine (eds) Proceedings of
% Empirical Advances in Categorial Grammars, pp. 34-70.
%
% This grammar adds ditransitive verbs to acg_grammar.pl, and this rather complicates the system
% (more realistic grammars in the style of CCGbank and TLGbank require at least two arguments to the
% left and two arguments to the right).

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

atomic_formula(n(_,_)).
atomic_formula(np(_,_)).
atomic_formula(s(_,_)).
atomic_formula(s1(_,_)).

lex(leslie, np(0,0), leslie, l).
lex(terry, np(0,0), terry, t).
lex(bill, np(0,0), bill, b).
lex(robin, np(0,0), robin, r).
lex(book, n(0,0), book, book).
lex(gave, (np(0,0)->(np(0,0)->(np(L,0)->s(L,0)))), lambda(P,lambda(Q,lambda(R,R+gave+P+Q))), give).
lex(gave, (np(0,0)->(np(0,1)->(np(L,0)->s(L,1)))), lambda(P,lambda(Q,lambda(R,R+gave+P+Q))), give).
lex(gave, (np(0,1)->(np(0,3)->(np(L,0)->s(L,3)))), lambda(P,lambda(Q,lambda(R,R+gave+P+Q))), give).
lex(promised, (np(0,0)->(np(0,0)->(np(L,0)->s(L,0)))), lambda(P,lambda(Q,lambda(R,R+promised+P+Q))), promise).
lex(promised, (np(0,0)->(np(0,1)->(np(L,0)->s(L,1)))), lambda(P,lambda(Q,lambda(R,R+promised+P+Q))), promise).
lex(promised, (np(0,1)->(np(0,3)->(np(L,0)->s(L,3)))), lambda(P,lambda(Q,lambda(R,R+promised+P+Q))), promise).
lex(likes, (np(0,0)->(np(L,0)->s(L,0))), lambda(P,lambda(Q,Q+likes+P)), like).
lex(likes, (np(0,1)->(np(L,0)->s(L,1))), lambda(P,lambda(Q,Q+likes+P)), like).
lex(likes, (np(0,3)->(np(L,0)->s(L,3))), lambda(P,lambda(Q,Q+likes+P)), like).
lex(loves, (np(0,0)->(np(L,0)->s(L,0))), lambda(P,lambda(Q,Q+loves+P)), love).
lex(loves, (np(0,1)->(np(L,0)->s(L,1))), lambda(P,lambda(Q,Q+loves+P)), love).
lex(loves, (np(0,3)->(np(L,0)->s(L,3))), lambda(P,lambda(Q,Q+loves+P)), love).
lex(hates, (np(0,0)->(np(L,0)->s(L,0))), lambda(P,lambda(Q,Q+hates+P)), hate).
lex(hates, (np(0,1)->(np(L,0)->s(L,1))), lambda(P,lambda(Q,Q+hates+P)), hate).
lex(hates, (np(0,3)->(np(L,0)->s(L,3))), lambda(P,lambda(Q,Q+hates+P)), hate).
% right-node-raising
lex(and, (((s(A,B)|np(A,B))|(s(C,1)|np(C,1)))|(s(D,1)|np(D,1))), lambda(P1,lambda(P2,lambda(Z,appl(P2,epsilon)+and+appl(P1,epsilon)+Z))), lambda(Z1,lambda(Z2,lambda(X,bool(appl(Z1,X),&,appl(Z2,X)))))).
% tv conjunction
lex(and, ((np(0,1)->np(1,0)->s(1,1))->(np(0,1)->np(1,0)->s(1,1))->(np(0,R)->np(L,0)->s(L,R))), lambda(P1,lambda(P2,lambda(Z,lambda(V,V+appl(appl(P2,epsilon),epsilon)+and+appl(appl(P1,epsilon),epsilon)+Z)))), lambda(Z1,lambda(Z2,lambda(X,lambda(Y,bool(appl(appl(Z1,X),Y),&,appl(appl(Z2,X),Y))))))).
% across the board extraction
lex(and2, ((np(0,0)->s(0,R))->(np(0,0)->s(L,0))->(np(0,0)->s1(L,R))), lambda(P1,lambda(P2,lambda(Z,appl(P2,epsilon)+and2+appl(P1,Z)))), lambda(Z1,lambda(Z2,lambda(X,bool(appl(Z1,X),&,appl(Z2,X)))))).
%lex(and2, ((np(0,0)->s(0,0))->(np(0,0)->s(L,0))->(np(0,R)->s1(L,R))), lambda(P1,lambda(P2,lambda(Z,appl(P2,epsilon)+and2+appl(P1,epsilon)+Z))), lambda(Z1,lambda(Z2,lambda(X,bool(appl(Z1,X),&,appl(Z2,X)))))).
%lex(and2, ((np(0,0)->s(0,R))->(np(0,0)->s(0,0))->(np(L,0)->s1(L,R))), lambda(P1,lambda(P2,lambda(Z,Z+appl(P2,epsilon)+and2+appl(P1,epsilon)))), lambda(Z1,lambda(Z2,lambda(X,bool(appl(Z1,X),&,appl(Z2,X)))))).
% tv gapping
lex(and, (((np(0,R1)->(np(L1,0)->s(L1,R1)))->s(0,R))->(((np(0,R2)->(np(L2,0)->s(L2,R2)))->s(L,0))->((np(0,1)->(np(1,0)->s(1,1)))->s1(L,R)))),
    lambda(P1,lambda(P2,lambda(P3,appl(P2,lambda(X1,lambda(Y1,X1+appl(appl(P3,epsilon),epsilon)+Y1)))+and+appl(P1,lambda(X2,lambda(Y2,X2+Y2)))))),
    lambda(Z1,lambda(Z2,lambda(Z3,bool(appl(Z1,lambda(Y,lambda(X,appl(appl(Z3,X),Y)))),&,appl(Z2,lambda(V,lambda(W,appl(appl(Z3,W),V))))))))).
% argument cluster coordination
% TODO: complete
lex(and, (((np(0,R1)->(np(L1,0)->s(L1,R1)))->s(0,R))->(((np(0,R2)->(np(L2,0)->s(L2,R2)))->s(L,0))->((np(0,1)->(np(1,0)->s(1,1)))->s1(L,R)))),
    lambda(P1,lambda(P2,lambda(P3,appl(P2,lambda(X1,lambda(Y1,X1+Y1)))+and+appl(P1,lambda(X2,lambda(Y2,X2+Y2)))))),
    lambda(Z1,lambda(Z2,lambda(Z3,bool(appl(Z1,lambda(Y,lambda(X,appl(appl(Z3,X),Y)))),&,appl(Z2,lambda(V,lambda(W,appl(appl(Z3,W),V))))))))).
%lex(and, (((np(0,R1)->(np(L1,0)->s(L1,R1)))->s(0,R))->(((np(0,R2)->(np(L2,0)->s(L2,R2)))->s(L,0))->((np(0,1)->(np(1,0)->s(1,1)))->s1(L,R)))),
%    lambda(P1,lambda(P2,lambda(P3,appl(appl(P2,epsilon),epsilon)+and+appl(appl(P1,lambda(X2,lambda(Y2,X2+Y2)))))),
%    lambda(Z1,lambda(Z2,lambda(Z3,bool(appl(Z1,lambda(Y,lambda(X,appl(appl(Z3,X),Y)))),&,appl(Z2,lambda(V,lambda(W,appl(appl(Z3,W),V))))))))).
lex(everyone, ((np(0,0)->s(L,R))->s(L,R)), lambda(P,appl(P,everyone)), lambda(P,quant(forall,X,bool(appl(person,X),->,appl(P,X))))).
lex(someone, ((np(0,0)->s(L,R))->s(L,R)), lambda(P,appl(P,someone)), lambda(P,quant(exists,X,bool(appl(person,X),&,appl(P,X))))).
lex(a_present, ((np(0,0)->s(L,R))->s(L,R)), lambda(P,appl(P,a_present)), lambda(P,quant(exists,X,bool(appl(present,X),&,appl(P,X))))).
lex(which, ((np(0,R)->s1(0,R))->(n(L,0)->n(L,R))), lambda(P,lambda(Q,Q+which+appl(P,epsilon))), lambda(X,lambda(Y,lambda(Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(passionately, (s(L,0)->s(L,0)), lambda(P,P+passionately), passionately).
lex(madly, (s(L,0)->s(L,0)), lambda(P,P+madly), madly).
lex(himself, ((np(0,0)->(np(1,0)->s(1,0)))->(np(L,0)->s(L,0))), lambda(P,lambda(X,X+appl(appl(P,himself),epsilon))), lambda(R1,lambda(Y,appl(appl(R1,Y),Y)))).
lex(himself, ((np(0,0)->(np(1,0)->s(1,1)))->(np(L,0)->s(L,1))), lambda(P,lambda(X,X+appl(appl(P,himself),epsilon))), lambda(R1,lambda(Y,appl(appl(R1,Y),Y)))).
lex(himself, ((np(0,0)->(np(1,0)->s(1,3)))->(np(L,0)->s(L,3))), lambda(P,lambda(X,X+appl(appl(P,himself),epsilon))), lambda(R1,lambda(Y,appl(appl(R1,Y),Y)))).

test(1) :-
	parse([terry,hates,leslie], s(0,0)).
test(2) :-
	parse([terry,gave,everyone,a_present], s(0,0)).
test(3) :-
	parse([terry,hates,and,robin,likes,leslie], s(0,0)).
test(4) :-
	parse([terry,gave,leslie,and,bill,promised,robin,a_present], s(0,0)).
test(5) :-
	parse([everyone,likes,terry], s(0,0)).
test(6) :-
	parse([everyone,likes,someone], s(0,0)).
test(7) :-
	parse([terry,hates,someone,and,bill,everyone], s1(0,0)).
% = overgenerates (generates a reading where Bill loves *Terry*)
test(8) :-
	parse([book,which,bill,likes,and2,terry,hates], n(0,0)).
% = overgenerates (generates a reading where Bill madly loves *Terry*)
test(9) :-
	parse([book,which,bill,loves,madly,and2,terry,hates,passionately], n(0,0)).
% = overgenerates (generates a reading where Terry hates *Robin*)
test(10) :-
	parse([terry,hates,and2,robin,likes,leslie], s1(0,0)).
% unparsed (no assignment for VP conjunction yet)
test(11) :-
	parse([terry,hates,robin,and2,likes,leslie], s1(0,0)).
test(12) :-
	parse([robin,likes,himself], s(0,0)).
% unparsed
test(13) :-
	parse([terry,hates,and,robin,likes,himself], s(0,0)).
% = only wrong reading (where Terry hates *Robin*)
test(14) :-
	parse([terry,hates,and2,robin,likes,himself], s1(0,0)).
test(15) :-
	parse([terry,hates,and,robin,likes,everyone], s(0,0)).
test(16) :-
	parse([terry,loves,and,hates,everyone], s(0,0)).
% = *three* derivations of the same reading (verify!)
test(17) :-
	parse([terry,promised,robin,and,gave,himself,a_present], s(0,0)).
% = *three* derivations of the same reading (verify!)
test(18) :-
	parse([terry,gave,himself,and,promised,robin,a_present], s(0,0)).
test(19) :-
	parse([terry,gave,a_present,himself], s(0,0)).